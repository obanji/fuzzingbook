import sys
sys.path.extend(['/home/admin1/Desktop/fuzzingbook/notebooks', '/home/admin1/anaconda3/lib/python37.zip', '/home/admin1/anaconda3/lib/python3.7', '/home/admin1/anaconda3/lib/python3.7/lib-dynload', '/home/admin1/.local/lib/python3.7/site-packages', '/home/admin1/anaconda3/lib/python3.7/site-packages', '/home/admin1/anaconda3/lib/python3.7/site-packages/pyelftools-0.25-py3.7.egg', '/home/admin1/anaconda3/lib/python3.7/site-packages/IPython/extensions', '/home/admin1/.ipython'])
sys.path.append('.')
import matplotlib.pyplot
matplotlib.pyplot._IP_REGISTERED = True # Hack
import fuzzingbook_utils
from GrammarMiner import GrammarMiner, Context, Tracer, Coverage, ScopedGrammarMiner, AssignmentVars, readable, flatten
import jsonpickle
import os
import gdb
import re

class Debugger(object):
    def break_at(self, line):
        raise NotImplementedError()

    def event_loop(self):
        raise NotImplementedError()

    def run(self):
        raise NotImplementedError()

    def start_program(self, inp, binary):
        raise NotImplementedError()

    def step(self):
        raise NotImplementedError()
class GDBContext(Context):
    def extract_vars(self, frame):
        vals = {}
        extractor = VarExtractor(frame)

        symbols = [
            sym for sym in frame.block() if sym.is_variable or sym.is_argument
        ]
        for symbol in symbols:
            if symbol.type.code == gdb.TYPE_CODE_INT:
                vals[symbol.name] = extractor.extract_int_val(symbol)

            elif symbol.type.code == gdb.TYPE_CODE_PTR:
                vals[symbol.name] = extractor.extract_pointer_val(symbol)

        return {k1: v1 for k, v in vals.items() for k1, v1 in flatten(k, v)}

    def get_arg_names(self, frame):
        return [symbol.name for symbol in frame.block() if symbol.is_argument]

    def __init__(self, frame):
        self.method = frame.name()
        self.parameter_names = self.get_arg_names(frame)
        self.line_no = frame.find_sal().line
        self.file_name = frame.find_sal().symtab.fullname()
class GDBTracer(Tracer):
    def create_context(self, frame):
        return GDBContext(frame)
class VarExtractor(object):
    def extract_pointer_val(self, symbol):
        true_value = self.dereference_pointer_type(symbol)

        if true_value.type.code == gdb.TYPE_CODE_INT:
            return '{}'.format(true_value.address).strip('"')

        elif true_value.type.code == gdb.TYPE_CODE_STRUCT:
            return self.extract_struct_val(true_value)

    def extract_struct_val(self, struct):
        return {
            f.name: str(struct[f]).strip('"')
            for f in struct.type.fields()
        }

    def dereference_pointer_type(self, symbol):
        return symbol.value(self.frame).dereference()

    def extract_int_val(self, symbol):
        return '{}'.format(symbol.value(self.frame))

    def __init__(self, frame):
        self.frame = frame
class GDBDebugger(Debugger):
    def event_loop(self):
        self.start_program(self.inp, self.binary)
        self.break_at('main')
        frame = self.gdb.selected_frame()
        try:
            while frame.is_valid():
                if self.gdb.selected_frame() != frame:
                    self.step()
                    current_frame = self.gdb.selected_frame()
                    if not self.in_context(current_frame):
                        # simply finish the current function execution.
                        self.gdb.execute('finish')
                        continue
                    event = self.get_event(current_frame)
                    self.tracer.traceit(current_frame, event, None)
                else:
                    self.step()
                    if not self.in_context(self.gdb.selected_frame()):
                        self.gdb.execute('finish')
        except gdb.error:
            return
    def get_event(self, frame):
        fname = frame.name()
        if fname not in self.frames:
            self.frames.append(fname)
            return 'call'
        elif fname == self.frames[-1]:
            return 'line'
        else:
            self.frames.pop()
            return 'return'
    def in_context(self, frame):
        file_name = frame.find_sal().symtab.fullname()
        return any(file_name.endswith(f) for f in self.files)
    def options(self, kwargs):
        self.files = kwargs.get('files', [])
        self.printer = kwargs.get('printer', True)
    def _skip_std_files(self):
        self.gdb.execute('skip -gfi *.S')
    def _set_logger(self):
        self.gdb.execute('set logging overwrite on')
        self.gdb.execute('set logging redirect on')
        self.gdb.execute('set logging on')
    def _set_printer(self):
        if not self.printer:
            self.gdb.execute('set print address off')
    def start_program(self, inp, binary):
        self.gdb.execute("set args '%s'" % inp)
        self.gdb.execute("file %s" % binary)
    def break_at(self, line):
        self.gdb.execute("break '%s'" % line)
        self.run()
    def step(self):
        self.gdb.execute('step')
    def run(self):
        self.gdb.execute('run')
    def __init__(self, gdb, binary, inp, **kwargs):
        self.options(kwargs)
        self.gdb, self.binary, self.inp = gdb, binary, inp
        self.frames = []

        self._set_printer()
        self._set_logger()
        self._skip_std_files()
        self.tracer = GDBTracer(self.inp, files=self.files)

CALL = 'callq'
RETURN = 'retq'
LINE = 'line'
ARG_REGISTERS = ['rax',  'rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']

ADDR_COUNTER_ = 0
F_ADDR_COUNTER_ = 0
L_ADDR_COUNTER = 0

ADDR_STORE = {}
F_ADDR_STORE = {}
L_ADDR_STORE = {}


def get_addr(addr):
    global ADDR_COUNTER_
    if addr in ADDR_STORE: return ADDR_STORE[addr]
    ADDR_COUNTER_ += 1
    ADDR_STORE[addr] = ADDR_COUNTER_
    return ADDR_STORE[addr]
def get_fn_addr(addr):
    global F_ADDR_COUNTER_
    if addr in F_ADDR_STORE: return F_ADDR_STORE[addr]
    F_ADDR_COUNTER_ += 1
    F_ADDR_STORE[addr] = F_ADDR_COUNTER_
    return F_ADDR_STORE[addr]
def get_fn(fnaddr):
    aid = get_fn_addr(fnaddr)
    return "fn_%d" % aid
def get_var(varaddr):
    aid = get_addr(varaddr)
    return "var_%d" % aid
def get_lno(addr):
    global L_ADDR_COUNTER
    if addr in L_ADDR_STORE: return 'a_%d' % (L_ADDR_STORE[addr])
    L_ADDR_COUNTER += 1
    L_ADDR_STORE[addr] = L_ADDR_COUNTER
    s = 'a_%d' % (L_ADDR_STORE[addr])
    return s

class StrippedContext(GDBContext):
    def __init__(self, frame):
        self.method = frame.function
        self.parameter_names = [k for k,v in frame.arguments.items()]
        self.line_no = frame.line_no
        self.file_name = frame.file_name
    def extract_vars(self, frame):
        return {k1: v1 for k, v in frame.locals_vars.items() for k1, v1 in flatten(k, v)}
class StrippedTracer(GDBTracer):
    def create_context(self, frame):
        return StrippedContext(frame)

class Frame:
    _gdb = gdb
    def __init__(self, instr, inp):
        self.inp = inp
        self._instr = instr
        self.arguments = []
        self.locals_vars = {}
        self.line_no = None
        self.file_name = None
        self.function = None
        self.reassignment = AssignmentVars('')
        self._parse()  
class Frame(Frame):
    def _read_register(self, r, l_no):
        val = self._gdb.execute('x/s $%s' % r, to_string=True)
        val = re.sub('\s+', '', val)
        try:
            v = None
            for i, j in enumerate(val):
                if j == ':':
                    v = val[i + 1:]
                    break
            var = get_var(l_no)
            return (var, v.strip('"'))
        except Exception:
            return     
class Frame(Frame):
    def _read_arg_register(self):
        kv_pair = []
        vals = [
            self._read_register(reg, self.line_no) for reg in ARG_REGISTERS
        ]
        return {
            key: val
            for key, val in filter(None, vals) if val in self.inp and val != ''
        }
class Frame(Frame):
    def _parse(self):
        self.function = get_fn(self._instr.pointed_address)
        self.line_no = get_lno(self._instr.current_address.strip(':'))
        self.arguments = self._read_arg_register()
        self.file_name = "a.out"  
        self.locals_vars.update(self.arguments)
class Frame(Frame):
    def update(self, instr):
        self.line_no = get_lno(instr.current_address.strip(':'))
        x = instr.dest_reg
        
        try:
            addr, val = self._read_register(x, self.line_no) 
            if addr in self.locals_vars.keys() and self.locals_vars[addr] != val:
                self.reassignment[addr] = val
                for k, v in self.reassignment.defs.items():
                    if v == val:
                        nv = '%s_%d' % k
                        self.locals_vars[nv] = val
            else:
                self.locals_vars[addr] = val       
        except:
            return
class Instruction:
    def __init__(self, instr):
        self.symbol_name = None
        self.pointed_address = None
        self.dest_reg = None
        self._parse(instr)
class Instruction(Instruction):
    def _parse(self, instr):
        instr_list = instr.split()
        instr_list.pop(0)

        self.current_address = instr_list[0]
        self.instr_type = instr_list[1]

        if 'mov' in self.instr_type:
            d = instr_list[2]
            if d[-1] != ')':
                self.dest_reg = d[-3:]
            elif re.match(r',\d\)', d[-3:]):
                self.dest_reg = d[-6:-3]
            else:
                self.dest_reg = d[-4:-1]

        elif self.instr_type == 'callq':
            self.pointed_address = instr_list[2]
            if len(instr_list) > 3:
                self.symbol_name = instr_list[-1]

        elif self.instr_type == 'push':
            d = instr_list[2]
            self.dest_reg = d[1:]

        elif self.instr_type == 'cmpq':
            d = instr_list[2]
            self.dest_reg = d[-4:-1]
class StrippedBinaryDebugger(GDBDebugger):
    def __init__(self, gdb, binary, inp, **kwargs):
        super().__init__(gdb, binary, inp, **kwargs)
        self.tracer = StrippedTracer(self.inp, files=self.files)
class StrippedBinaryDebugger(StrippedBinaryDebugger):
    def event_loop(self):
        main = self.get_main()
        self.break_at(main)
        self.resume()
        
        start, end = self.get_address_range()
        nexti = ''
        current_frame = None
        while True:
            try:
                self.step()
                nexti = self.get_instruction()
                if self.in_scope(nexti, start, end):
                    h = Instruction(nexti)
                    if h.instr_type == 'callq':
                        if h.symbol_name != None:
                            self.nexti()
                            continue
                        else:
                            current_frame = Frame(h, self.inp)
                    else:
                        if current_frame != None:
                            current_frame.update(h)
                        else:
                            continue
                    event = self.get_event(current_frame)
                    self.tracer.traceit(current_frame, event, None)
                else:
                    self.finish()
            except gdb.error:
                break
    def get_event (self, frame):
        fname = frame.function
        if fname not in self.frames:
            self.frames.append(fname)
            return 'call'
        elif fname == self.frames[-1]:
            return 'line'
        else:
            self.frames.pop()
            return 'return'
    def get_main(self):
        entry_addr = self.get_entry_point()
        self.break_at(entry_addr)
        self.run()

        instructions = []
        while True:
            next_i = self.get_instruction()
            if CALL in next_i:
                break
            instructions.append(next_i)
            self.step()

        instr = instructions[-1].split()
        return instr[-1]
    def get_instruction(self):
        return self.gdb.execute('x/i $rip', to_string=True)
    def get_entry_point(self):
        self.gdb.execute("set args '%s'" % self.inp)
        self.gdb.execute("file %s" % self.binary)
        self.run()

        info_file = self.gdb.execute('info file', to_string=True)
        e = info_file.splitlines()[3]
        entry_address = e.split(':')[1]
        return entry_address
    def break_at(self, address):
        self.gdb.execute("break *%s" % address)
    def finish(self):
        self.gdb.execute('finish')
    def step(self):
        self.gdb.execute('stepi')
    def resume(self):
        self.gdb.execute('continue')
    def nexti(self):
        self.gdb.execute('nexti')
    def get_address_range(self):
        start_addr = None
        end_addr = None
        mappings = self.gdb.execute('info proc mappings', to_string=True)
        i = 1
        for line in mappings.splitlines():
            if i == 5:
                start_addr = line.split()[0]
            elif i ==7:
                end_addr = line.split()[1]
            i += 1
        return (start_addr, end_addr)
    def in_scope(self, instr, start, end):
        instr= instr.split()
        del instr[0]

        current_addr = instr[0].strip(':')
        hex_val = int(current_addr, 16)
        if hex_val in range(int(start, 16), int(end, 16)):
            return True
        else:
            return False         

file_name = 'gdbtrace'
def recover_trace(f, inp, **kwargs):
    d = StrippedBinaryDebugger(gdb, f, inp, **kwargs)
    d.event_loop()
    with open(file_name, 'w+') as f:
        print(jsonpickle.encode(d.tracer.trace), file=f)
binary = 'a.out'
recover_trace(binary, arg0, files=[binary])
