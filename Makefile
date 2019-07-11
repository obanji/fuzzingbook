# Fuzzingbook Makefile

# Get chapter files
CHAPTERS_MAKEFILE = Chapters.makefile
include $(CHAPTERS_MAKEFILE)

# These chapters will show up in the "public" version
PUBLIC_CHAPTERS = \
	$(INTRO_PART) \
	$(LEXICAL_PART) \
	$(SYNTACTICAL_PART) \
	$(SEMANTICAL_PART) \
	$(DOMAINS_PART) \
	$(MANAGEMENT_PART)

# These chapters will show up in the "beta" version
CHAPTERS = \
	$(INTRO_PART) \
	$(INTRO_PART_READY) \
	$(INTRO_PART_TODO) \
	$(LEXICAL_PART) \
	$(LEXICAL_PART_READY) \
	$(LEXICAL_PART_TODO) \
	$(SYNTACTICAL_PART) \
	$(SYNTACTICAL_PART_READY) \
	$(SYNTACTICAL_PART_TODO) \
	$(SEMANTICAL_PART) \
	$(SEMANTICAL_PART_READY) \
	$(SEMANTICAL_PART_TODO) \
	$(DOMAINS_PART) \
	$(DOMAINS_PART_READY) \
	$(DOMAINS_PART_TODO) \
	$(MANAGEMENT_PART) \
	$(MANAGEMENT_PART_READY) \
	$(MANAGEMENT_PART_TODO)
	
READY_CHAPTERS = \
	$(INTRO_PART_READY) \
	$(LEXICAL_PART_READY) \
	$(SYNTACTICAL_PART_READY) \
	$(SEMANTICAL_PART_READY) \
	$(DOMAINS_PART_READY) \
	$(MANAGEMENT_PART_READY)

TODO_CHAPTERS = \
	$(INTRO_PART_TODO) \
	$(LEXICAL_PART_TODO) \
	$(SYNTACTICAL_PART_TODO) \
	$(SEMANTICAL_PART_TODO) \
	$(DOMAINS_PART_TODO) \
	$(MANAGEMENT_PART_TODO)

# All source notebooks
SOURCE_FILES = \
	$(FRONTMATTER) \
	$(CHAPTERS) \
	$(APPENDICES) \
	$(EXTRAS)

# The bibliography file
BIB = fuzzingbook.bib

# The utilities in fuzzingbook_utils
UTILITY_FILES = \
	__init__.py \
	PrettyTable.py \
	README.md \
	export_notebook_code.py \
	import_notebooks.py \
	set_fixed_seed.py

# Where the notebooks are
NOTEBOOKS = notebooks

# Derived versions including HTML, SVG, and text output cells (for Web)
FULL_NOTEBOOKS = full_notebooks

# Derived versions including PNG and text output cells (for LaTeX and PDF)
RENDERED_NOTEBOOKS = rendered


# Git repo
GITHUB_REPO = https://github.com/uds-se/fuzzingbook/
BINDER_URL = https://mybinder.org/v2/gh/uds-se/fuzzingbook/master?filepath=docs/beta/notebooks/00_Table_of_Contents.ipynb

# Sources in the notebooks folder
SOURCES = $(SOURCE_FILES:%=$(NOTEBOOKS)/%)
CHAPTER_SOURCES = $(CHAPTERS:%=$(NOTEBOOKS)/%)
PUBLIC_SOURCES = $(PUBLIC_CHAPTERS:%=$(NOTEBOOKS)/%)
READY_SOURCES = $(READY_CHAPTERS:%=$(NOTEBOOKS)/%)
TODO_SOURCES = $(TODO_CHAPTERS:%=$(NOTEBOOKS)/%)
NEW_SOURCES = $(NEW_CHAPTERS:%=$(NOTEBOOKS)/%)
APPENDICES_SOURCES = $(APPENDICES:%=$(NOTEBOOKS)/%)

# Where to place the pdf, html, slides
PDF_TARGET      = pdf/
HTML_TARGET     = html/
SLIDES_TARGET   = slides/
CODE_TARGET     = code/
MARKDOWN_TARGET = markdown/
WORD_TARGET     = word/
EPUB_TARGET     = epub/
DEPEND_TARGET   = .depend/
DOCS_TARGET     = docs/

# If BETA=y, we create files in the "beta" subdir.  Use 'make docs-beta', 'make html-beta' to invoke
ifdef BETA
DOCS_TARGET    := docs/beta/
HTML_TARGET    := beta/$(HTML_TARGET)
SLIDES_TARGET  := beta/$(SLIDES_TARGET)
CODE_TARGET    := beta/$(CODE_TARGET)
BETA_FLAG = --include-ready --include-todo
endif
ifndef BETA
# Avoid warning: undefined variable `BETA_FLAG'
BETA_FLAG = 
endif

# Files to appear in the table of contents
ifndef BETA
TOC_CHAPTERS := $(PUBLIC_CHAPTERS)
TOC_APPENDICES = $(APPENDICES)
CHAPTER_SOURCES := $(PUBLIC_CHAPTERS:%=$(NOTEBOOKS)/%)
endif
ifdef BETA
TOC_CHAPTERS := $(CHAPTERS)
TOC_APPENDICES = $(APPENDICES)
endif

# Files to appear on the Web page
DOCS = \
	$(FRONTMATTER:%.ipynb=%) \
	$(TOC_CHAPTERS:%.ipynb=%) \
	$(APPENDICES:%.ipynb=%) \
	$(EXTRAS:%.ipynb=%)


# Various derived files
TEXS      = $(SOURCE_FILES:%.ipynb=$(PDF_TARGET)%.tex)
PDFS      = $(SOURCE_FILES:%.ipynb=$(PDF_TARGET)%.pdf)
HTMLS     = $(SOURCE_FILES:%.ipynb=$(HTML_TARGET)%.html)
SLIDES    = $(SOURCE_FILES:%.ipynb=$(SLIDES_TARGET)%.slides.html)
PYS       = $(SOURCE_FILES:%.ipynb=$(CODE_TARGET)%.py) \
				$(CODE_TARGET)setup.py \
				$(CODE_TARGET)__init__.py
WORDS     = $(SOURCE_FILES:%.ipynb=$(WORD_TARGET)%.docx)
MARKDOWNS = $(SOURCE_FILES:%.ipynb=$(MARKDOWN_TARGET)%.md)
EPUBS     = $(SOURCE_FILES:%.ipynb=$(EPUB_TARGET)%.epub)
FULLS     = $(FULL_NOTEBOOKS)/fuzzingbook_utils \
				$(UTILITY_FILES:%=$(FULL_NOTEBOOKS)/fuzzingbook_utils/%) \
				$(SOURCE_FILES:%.ipynb=$(FULL_NOTEBOOKS)/%.ipynb) 
RENDERS = $(SOURCE_FILES:%.ipynb=$(RENDERED_NOTEBOOKS)/%.ipynb)

DEPENDS   = $(SOURCE_FILES:%.ipynb=$(DEPEND_TARGET)%.makefile)

CHAPTER_PYS = $(CHAPTERS:%.ipynb=$(CODE_TARGET)%.py)

PDF_FILES     = $(SOURCE_FILES:%.ipynb=$(PDF_TARGET)%_files)
HTML_FILES    = $(SOURCE_FILES:%.ipynb=$(HTML_TARGET)%_files)
SLIDES_FILES  = $(SOURCE_FILES:%.ipynb=$(SLIDES_TARGET)%_files)

SITEMAP_SVG = $(NOTEBOOKS)/PICS/Sitemap.svg


# Configuration
# The site
SITE = https://www.fuzzingbook.org

# What we use for production: nbpublish (preferred), bookbook, or nbconvert
PUBLISH ?= nbpublish

# What we use for LaTeX: latexmk (preferred), or pdflatex
LATEX ?= latexmk

## Tools
# Python
PYTHON ?= python3

# Jupyter
JUPYTER ?= jupyter

# The nbpublish tool (preferred; https://github.com/chrisjsewell/ipypublish)
# (see nbpublish -h for details)
NBPUBLISH ?= nbpublish

# The bookbook tool (okay for chapters and books; but no citations yet)
# https://github.com/takluyver/bookbook
BOOKBOOK_LATEX ?= $(PYTHON) -m bookbook.latex
BOOKBOOK_HTML  ?= $(PYTHON) -m bookbook.html

# The nbconvert alternative (okay for chapters; doesn't work for book; no citations)
NBCONVERT ?= $(JUPYTER) nbconvert

# Notebook merger
NBMERGE = $(PYTHON) utils/nbmerge.py

# LaTeX
PDFLATEX ?= pdflatex
XELATEX ?= xelatex
BIBTEX ?= bibtex
LATEXMK ?= latexmk
LATEXMK_OPTS ?= -xelatex -quiet -f -interaction=nonstopmode

# Word
PANDOC ?= pandoc

# Markdown (see https://github.com/aaren/notedown)
NOTEDOWN ?= notedown

# Style checks
PYCODESTYLE ?= pycodestyle
PYCODESTYLE_CFG = code/pycodestyle.cfg

AUTOPEP8 ?= autopep8
AUTOPEP8_CFG = code/autopep8.cfg
AUTOPEP8_OPTIONS = --global-config $(AUTOPEP8_CFG) --aggressive --in-place
NBAUTOPEP8 = $(PYTHON) utils/nbautopep8.py

# Program to open files after creating, say OPEN=open (default: ignore; "true" does nothing)
OPEN ?= true

# Make directory
MKDIR = mkdir -p

ifndef PUBLISH
# Determine publishing program
OUT := $(shell which $(NBPUBLISH) > /dev/null && echo yes)
ifeq ($(OUT),yes)
# We have nbpublish
PUBLISH = nbpublish
else
# Issue a warning message
OUT := $(shell $(NBPUBLISH) -h > /dev/null)
# We have nbconvert
PUBLISH = nbconvert
PUBLISH_PLUGINS = 
endif
endif

ifndef LATEX
# Determine publishing program
OUT := $(shell which $(LATEXMK) > /dev/null && echo yes)
ifeq ($(OUT),yes)
# We have latexmk
LATEX = $(LATEXMK)
else
# Issue a warning message
OUT := $(shell $(LATEXMK) -h > /dev/null)
# We have pdflatex
LATEX = $(PDFLATEX)
endif
endif


# Book base name
BOOK = fuzzingbook

ifeq ($(PUBLISH),bookbook)
# Use bookbook
CONVERT_TO_HTML   = $(NBCONVERT) --to html --output-dir=$(HTML_TARGET)
CONVERT_TO_TEX    = $(NBCONVERT) --to latex --template fuzzingbook.tplx --output-dir=$(PDF_TARGET)
BOOK_TEX    = $(PDF_TARGET)$(BOOK).tex
BOOK_PDF    = $(PDF_TARGET)$(BOOK).pdf
BOOK_HTML   = $(HTML_TARGET)$(BOOK).html
BOOK_HTML_FILES = $(HTML_TARGET)$(BOOK)_files
BOOK_PDF_FILES  = $(PDF_TARGET)$(BOOK)_files
PUBLISH_PLUGINS = 
else
ifeq ($(PUBLISH),nbpublish)
# Use nbpublish
CONVERT_TO_HTML   = $(NBPUBLISH) -f html_ipypublish_chapter --outpath $(HTML_TARGET)
CONVERT_TO_TEX    = $(NBPUBLISH) -f latex_ipypublish_chapter --outpath $(PDF_TARGET)
# CONVERT_TO_SLIDES = $(NBPUBLISH) -f slides_ipypublish_all --outpath $(SLIDES_TARGET)
BOOK_TEX    = $(PDF_TARGET)$(BOOK).tex
BOOK_PDF    = $(PDF_TARGET)$(BOOK).pdf
BOOK_HTML   = $(HTML_TARGET)$(BOOK).html
BOOK_HTML_FILES = $(HTML_TARGET)$(BOOK)_files
BOOK_PDF_FILES  = $(PDF_TARGET)$(BOOK)_files
PUBLISH_PLUGINS = \
    ipypublish_plugins/html_ipypublish_chapter.py \
	ipypublish_plugins/latex_ipypublish_book.py \
	ipypublish_plugins/latex_ipypublish_chapter.py
else
# Use standard Jupyter tools
CONVERT_TO_HTML   = $(NBCONVERT) --to html --output-dir=$(HTML_TARGET)
CONVERT_TO_TEX    = $(NBCONVERT) --to latex --template fuzzingbook.tplx --output-dir=$(PDF_TARGET)
# CONVERT_TO_SLIDES = $(NBCONVERT) --to slides --output-dir=$(SLIDES_TARGET)
BOOK_TEX   = 
BOOK_PDF   = 
BOOK_HTML  = 
BOOK_HTML_FILES = 
BOOK_PDF_FILES  = 
PUBLISH_PLUGINS = 
endif
endif

# For Python, we use our own script that takes care of distinguishing 
# main (script) code from definitions to be imported
EXPORT_NOTEBOOK_CODE = $(NOTEBOOKS)/fuzzingbook_utils/export_notebook_code.py 
CONVERT_TO_PYTHON = $(PYTHON) $(EXPORT_NOTEBOOK_CODE)

# This would be the Jupyter alternative
# CONVERT_TO_PYTHON = $(NBCONVERT) --to python --output-dir=$(CODE_TARGET)

# For slides, we use the standard Jupyter tools
# Main reason: Jupyter has a neat interface to control slides/sub-slides/etc
CONVERT_TO_SLIDES = $(NBCONVERT) --to slides --output-dir=$(SLIDES_TARGET)
REVEAL_JS = $(SLIDES_TARGET)reveal.js

# For Word .docx files, we start from the HTML version
CONVERT_TO_WORD = $(PANDOC) 

# For Markdown .md files, we use markdown
# Note: adding --run re-executes all code
# CONVERT_TO_MARKDOWN = $(NOTEDOWN) --to markdown
CONVERT_TO_MARKDOWN = $(NBCONVERT) --to markdown --output-dir=$(MARKDOWN_TARGET)

# Run
# WhenToStopFuzzing needs about 120 seconds to render
EXECUTE_TIMEOUT = 140
EXECUTE_OPTIONS = --ExecutePreprocessor.timeout=$(EXECUTE_TIMEOUT)
EXECUTE_NOTEBOOK = $(NBCONVERT) $(EXECUTE_OPTIONS) --to notebook --execute --output-dir=$(FULL_NOTEBOOKS)

# Render
RENDER_NOTEBOOK = RENDER_HTML=1 $(NBCONVERT) $(EXECUTE_OPTIONS) --to notebook --execute --output-dir=$(RENDERED_NOTEBOOKS)


# Zip
ZIP ?= zip
ZIP_OPTIONS = -r


# Short targets
# Default target is "chapters", as that's what you'd typically like to recreate after a change
.PHONY: chapters default
chapters default: html code

# The book is recreated after any change to any source
.PHONY: book all and more
book fuzzingbook:	book-html book-pdf
all:	chapters pdf code slides book
and more:	word markdown epub

# Individual targets
.PHONY: html pdf python code slides word doc docx md markdown epub
.PHONY: full-notebooks full fulls rendered-notebooks rendered renders book-pdf book-html
html:	ipypublish-chapters $(HTMLS)
pdf:	ipypublish-chapters $(PDFS)
python code:	$(PYS)
slides:	$(SLIDES) $(REVEAL_JS)
word doc docx: $(WORDS)
md markdown: $(MARKDOWNS)
epub: $(EPUBS)
full-notebooks full fulls: $(FULLS)
rendered-notebooks rendered renders: $(RENDERS)

book-pdf fuzzingbook-pdf:  ipypublish-book $(BOOK_PDF)
book-html fuzzingbook-html: ipypublish-book $(BOOK_HTML)

.PHONY: ipypublish-book ipypublish-chapters
ifeq ($(PUBLISH),bookbook)
ipypublish-book:
ipypublish-chapters:
else
ifeq ($(PUBLISH),nbpublish)
ipypublish-book:
ipypublish-chapters:
else
ipypublish-book:
	@echo "To create the book, you need the 'nbpublish' program."
	@echo "This is part of the 'ipypublish' package"
	@echo "at https://github.com/chrisjsewell/ipypublish"
ipypublish-chapters:
	@echo "Warning: Using '$(NBCONVERT)' instead of '$(NBPUBLISH)'"
	@echo "Documents will be created without citations and references"
	@echo "Install the 'ipypublish' package"
	@echo "from https://github.com/chrisjsewell/ipypublish"
endif
endif

.PHONY: edit jupyter lab notebook
# Invoke notebook and editor: `make jupyter lab`
edit notebook:
	$(JUPYTER) notebook

lab:
	$(JUPYTER) lab
	
jupyter:


# Help
.PHONY: help
help:
	@echo "Welcome to the 'fuzzingbook' Makefile!"
	@echo ""
	@echo "* make chapters (default) -> HTML and code for all chapters (notebooks)"
	@echo "* make (pdf|html|code|slides|word|markdown) -> given subcategory only"
	@echo "* make book -> entire book in PDF and HTML"
	@echo "* make all -> all inputs in all output formats"
	@echo "* make reformat -> reformat notebook Python code according to PEP8 guidelines"
	@echo "* make style -> style checker"
	@echo "* make crossref -> cross reference checker"
	@echo "* make stats -> report statistics"
	@echo "* make clean -> delete all derived files"
	@echo ""
	@echo "Created files end here:"
	@echo "* PDFs -> '$(PDF_TARGET)', HTML -> '$(HTML_TARGET)', Python code -> '$(CODE_TARGET)', Slides -> '$(SLIDES_TARGET)'"
	@echo "* Web site files -> '$(DOCS_TARGET)'"
	@echo ""
	@echo "Publish:"
	@echo "* make docs -> Create public version of current documents" 
	@echo "* make beta -> Create beta version of current documents" 
	@echo "* make publish-all -> Add docs to git, preparing for publication" 
	@echo ""
	@echo "Settings:"
	@echo "* Use make PUBLISH=(nbconvert|nbpublish|bookbook) to choose a converter"
	@echo "  (default: automatic)"
	
# Run a notebook, (re)creating all output cells
ADD_METADATA = utils/add_metadata.py
NBAUTOSLIDE = utils/nbautoslide.py
NBSYNOPSIS = utils/nbsynopsis.py

$(FULL_NOTEBOOKS)/%.ipynb: $(NOTEBOOKS)/%.ipynb $(DEPEND_TARGET)%.makefile $(ADD_METADATA) $(NBAUTOSLIDE) $(NBSYNOPSIS)
	$(EXECUTE_NOTEBOOK) $<
	$(PYTHON) $(ADD_METADATA) $@ > $@~ && mv $@~ $@
	$(PYTHON) $(NBAUTOSLIDE) --in-place $@
	$(PYTHON) $(NBSYNOPSIS) --update $@
	
$(RENDERED_NOTEBOOKS)/%.ipynb: $(NOTEBOOKS)/%.ipynb $(DEPEND_TARGET)%.makefile $(ADD_METADATA) $(NBAUTOSLIDE) $(NBSYNOPSIS) $(NOTEBOOKS)/fuzzingbook_utils/__init__.py
	$(RENDER_NOTEBOOK) $<
	$(PYTHON) $(ADD_METADATA) $@ > $@~ && mv $@~ $@
	$(PYTHON) $(NBAUTOSLIDE) --in-place $@
	RENDER_HTML=1 $(PYTHON) $(NBSYNOPSIS) --update $@

$(FULL_NOTEBOOKS)/fuzzingbook_utils:
	$(MKDIR) $(FULL_NOTEBOOKS)/fuzzingbook_utils

$(FULL_NOTEBOOKS)/fuzzingbook_utils/%: $(NOTEBOOKS)/fuzzingbook_utils/%
	@test -d $(FULL_NOTEBOOKS)/fuzzingbook_utils || \
		$(MKDIR) $(FULL_NOTEBOOKS)/fuzzingbook_utils
	cp -pr $< $@



# Conversion rules - chapters
ifeq ($(LATEX),pdflatex)
# Use PDFLaTeX
$(PDF_TARGET)%.pdf:	$(PDF_TARGET)%.tex $(BIB)
	@echo Running LaTeX...
	@-test -L $(PDF_TARGET)PICS || ln -s ../$(NOTEBOOKS)/PICS $(PDF_TARGET)
	cd $(PDF_TARGET) && $(PDFLATEX) $*
	-cd $(PDF_TARGET) && $(BIBTEX) $*
	cd $(PDF_TARGET) && $(PDFLATEX) $*
	cd $(PDF_TARGET) && $(PDFLATEX) $*
	@cd $(PDF_TARGET) && $(RM) $*.aux $*.bbl $*.blg $*.log $*.out $*.toc $*.frm $*.lof $*.lot $*.fls
	@cd $(PDF_TARGET) && $(RM) -r $*_files
	@echo Created $@
	@$(OPEN) $@
else
# Use LaTeXMK
$(PDF_TARGET)%.pdf:	$(PDF_TARGET)%.tex $(BIB)
	@echo Running LaTeXMK...
	@-test -L $(PDF_TARGET)PICS || ln -s ../$(NOTEBOOKS)/PICS $(PDF_TARGET)
	cd $(PDF_TARGET) && $(LATEXMK) $(LATEXMK_OPTS) $*
	@cd $(PDF_TARGET) && $(RM) $*.aux $*.bbl $*.blg $*.log $*.out $*.toc $*.frm $*.lof $*.lot $*.fls $*.fdb_latexmk $*.xdv
	@cd $(PDF_TARGET) && $(RM) -r $*_files
	@echo Created $@
	@$(OPEN) $@
endif

$(PDF_TARGET)%.tex:	$(RENDERED_NOTEBOOKS)/%.ipynb $(BIB) $(PUBLISH_PLUGINS) $(ADD_METADATA)
	$(eval TMPDIR := $(shell mktemp -d))
	$(PYTHON) $(ADD_METADATA) --titlepage $< > $(TMPDIR)/$(notdir $<)
	cp -pr $(NOTEBOOKS)/PICS fuzzingbook.* $(TMPDIR)
	$(CONVERT_TO_TEX) $(TMPDIR)/$(notdir $<)
	@-$(RM) -fr $(TMPDIR)
	@cd $(PDF_TARGET) && $(RM) $*.nbpub.log


POST_HTML_OPTIONS = $(BETA_FLAG) \
	--public-chapters="$(CHAPTER_SOURCES) $(APPENDICES_SOURCES)" \
	--ready-chapters="$(READY_SOURCES)" \
	--todo-chapters="$(TODO_SOURCES)" \
	--new-chapters="$(NEW_SOURCES)" \
	
HTML_DEPS = $(BIB) $(PUBLISH_PLUGINS) utils/post_html.py $(CHAPTERS_MAKEFILE)

# index.html comes with relative links (html/) such that the beta version gets the beta menu
$(DOCS_TARGET)index.html: \
	$(FULL_NOTEBOOKS)/index.ipynb $(HTML_DEPS)
	@test -d $(DOCS_TARGET) || $(MKDIR) $(DOCS_TARGET)
	@test -d $(HTML_TARGET) || $(MKDIR) $(HTML_TARGET)
	$(CONVERT_TO_HTML) $<
	mv $(HTML_TARGET)index.html $@
	@cd $(HTML_TARGET) && $(RM) -r index.nbpub.log index_files
	$(PYTHON) utils/post_html.py --menu-prefix=html/ --home $(POST_HTML_OPTIONS)$(HOME_POST_HTML_OPTIONS) $@
	@$(OPEN) $@

# 404.html comes with absolute links (/html/) such that it works anywhare
# https://help.github.com/articles/creating-a-custom-404-page-for-your-github-pages-site/
$(DOCS_TARGET)404.html: $(FULL_NOTEBOOKS)/404.ipynb $(HTML_DEPS)
	@test -d $(DOCS_TARGET) || $(MKDIR) $(DOCS_TARGET)
	@test -d $(HTML_TARGET) || $(MKDIR) $(HTML_TARGET)
	$(CONVERT_TO_HTML) $<
	mv $(HTML_TARGET)404.html $@
	@cd $(HTML_TARGET) && $(RM) -r 404.nbpub.log 404_files
	$(PYTHON) utils/post_html.py --menu-prefix=/html/ --home $(POST_HTML_OPTIONS) $@
	(echo '---'; echo 'permalink: /404.html'; echo '---'; cat $@) > $@~ && mv $@~ $@
	@$(OPEN) $@

$(DOCS_TARGET)html/00_Index.html: $(DOCS_TARGET)notebooks/00_Index.ipynb $(HTML_DEPS)
	$(CONVERT_TO_HTML) $<
	@cd $(HTML_TARGET) && $(RM) -r 00_Index.nbpub.log 00_Index_files
	@cd $(DOCS_TARGET)html && $(RM) -r 00_Index.nbpub.log 00_Index_files
	mv $(HTML_TARGET)00_Index.html $@
	$(PYTHON) utils/post_html.py $(POST_HTML_OPTIONS) $@

$(DOCS_TARGET)html/00_Table_of_Contents.html: $(DOCS_TARGET)notebooks/00_Table_of_Contents.ipynb $(SITEMAP_SVG)
	$(CONVERT_TO_HTML) $<
	@cd $(HTML_TARGET) && $(RM) -r 00_Table_of_Contents.nbpub.log 00_Table_of_Contents_files
	@cd $(DOCS_TARGET)html && $(RM) -r 00_Table_of_Contents.nbpub.log 00_Table_of_Contents_files
	mv $(HTML_TARGET)00_Table_of_Contents.html $@
	$(PYTHON) utils/post_html.py $(POST_HTML_OPTIONS) $@
	@$(OPEN) $@

$(HTML_TARGET)%.html: $(FULL_NOTEBOOKS)/%.ipynb $(HTML_DEPS)
	@test -d $(HTML_TARGET) || $(MKDIR) $(HTML_TARGET)
	$(CONVERT_TO_HTML) $<
	@cd $(HTML_TARGET) && $(RM) $*.nbpub.log $*_files/$(BIB)
	$(PYTHON) utils/post_html.py $(POST_HTML_OPTIONS) $@
	@-test -L $(HTML_TARGET)PICS || ln -s ../$(NOTEBOOKS)/PICS $(HTML_TARGET)
	@$(OPEN) $@

$(SLIDES_TARGET)%.slides.html: $(FULL_NOTEBOOKS)/%.ipynb $(BIB)
	@test -d $(SLIDES_TARGET) || $(MKDIR) $(SLIDES_TARGET)
	$(eval TMPDIR := $(shell mktemp -d))
	sed 's/\.ipynb)/\.slides\.html)/g' $< > $(TMPDIR)/$(notdir $<)
	$(CONVERT_TO_SLIDES) $(TMPDIR)/$(notdir $<)
	@cd $(SLIDES_TARGET) && $(RM) $*.nbpub.log $*_files/$(BIB)
	@-test -L $(HTML_TARGET)PICS || ln -s ../$(NOTEBOOKS)/PICS $(HTML_TARGET)
	@-$(RM) -fr $(TMPDIR)
	@$(OPEN) $@

# Rules for beta targets
.FORCE:
ifndef BETA
beta/%: .FORCE
	$(MAKE) BETA=beta $(@:beta/=)

$(DOCS_TARGET)beta/%: .FORCE
	$(MAKE) BETA=beta $(@:beta/=)

%-beta: .FORCE
	$(MAKE) BETA=beta $(@:-beta=)

%-all: % %-beta
	@true

.PHONY: beta
beta: docs-beta
endif


# Reconstructing the reveal.js dir
$(REVEAL_JS):
	git submodule update --init


$(CODE_TARGET)setup.py: $(CODE_TARGET)setup.py.in
	cat $< > $@
	chmod +x $@

$(CODE_TARGET)__init__.py: $(CODE_TARGET)__init__.py.in
	cat $< > $@
	chmod +x $@

# For code, we comment out fuzzingbook imports, 
# ensuring we import a .py and not the .ipynb file
$(CODE_TARGET)%.py: $(NOTEBOOKS)/%.ipynb $(EXPORT_NOTEBOOK_CODE)
	@test -d $(CODE_TARGET) || $(MKDIR) $(CODE_TARGET)
	$(CONVERT_TO_PYTHON) $< > $@~ && mv $@~ $@
	# $(AUTOPEP8) $(AUTOPEP8_OPTIONS) $@
	-chmod +x $@


# Markdown
$(MARKDOWN_TARGET)%.md:	$(RENDERED_NOTEBOOKS)/%.ipynb $(BIB)
	$(RM) -r $(MARKDOWN_TARGET)$(basename $(notdir $<)).md $(MARKDOWN_TARGET)$(basename $(notdir $<))_files
	$(CONVERT_TO_MARKDOWN) $<

# For word, we convert from the HTML file
$(WORD_TARGET)%.docx: $(HTML_TARGET)%.html $(WORD_TARGET)pandoc.css
	$(PANDOC) --css=$(WORD_TARGET)pandoc.css $< -o $@

# Epub comes from the markdown file
$(EPUB_TARGET)%.epub: $(MARKDOWN_TARGET)%.md
	cd $(MARKDOWN_TARGET); $(PANDOC) -o ../$@ ../$<

# Conversion rules - entire book
# We create a fuzzingbook/ folder with the chapters ordered by number, 
# and let the fuzzingbook converters run on this
ifeq ($(PUBLISH),nbpublish)
# With nbpublish
$(PDF_TARGET)$(BOOK).tex: $(RENDERS) $(BIB) $(PUBLISH_PLUGINS) $(CHAPTERS_MAKEFILE)
	-$(RM) -r $(BOOK)
	$(MKDIR) $(BOOK)
	chapter=0; \
	for file in $(SOURCE_FILES); do \
		chnum=$$(printf "%02d" $$chapter); \
	    ln -s ../$(RENDERED_NOTEBOOKS)/$$file $(BOOK)/$$(echo $$file | sed 's/.*/Ch'$${chnum}'_&/g'); \
		chapter=$$(expr $$chapter + 1); \
	done
	ln -s ../$(BIB) $(BOOK)
	$(NBPUBLISH) -f latex_ipypublish_book --outpath $(PDF_TARGET) $(BOOK)
	$(RM) -r $(BOOK)
	cd $(PDF_TARGET) && $(RM) $(BOOK).nbpub.log
	@echo Created $@

$(HTML_TARGET)$(BOOK).html: $(FULLS) $(BIB) utils/post_html.py
	-$(RM) -r $(BOOK)
	$(MKDIR) $(BOOK)
	chapter=0; \
	for file in $(SOURCE_FILES); do \
		chnum=$$(printf "%02d" $$chapter); \
	    ln -s ../$(FULL_NOTEBOOKS)/$$file $(BOOK)/$$(echo $$file | sed 's/.*/Ch'$${chnum}'_&/g'); \
		chapter=$$(expr $$chapter + 1); \
	done
	ln -s ../$(BIB) $(BOOK)
	$(CONVERT_TO_HTML) $(BOOK)
	$(PYTHON) utils/nbmerge.py $(BOOK)/Ch*.ipynb > notebooks/$(BOOK).ipynb
	$(PYTHON) utils/post_html.py $(BETA_FLAG) $(POST_HTML_OPTIONS) $@
	$(RM) -r $(BOOK) notebooks/$(BOOK).ipynb
	cd $(HTML_TARGET) && $(RM) $(BOOK).nbpub.log $(BOOK)_files/$(BIB)
	@echo Created $@
else
# With bookbook
$(PDF_TARGET)$(BOOK).tex: $(RENDERS) $(BIB) $(PUBLISH_PLUGINS) $(CHAPTERS_MAKEFILE)
	-$(RM) -r $(BOOK)
	$(MKDIR) $(BOOK)
	chapter=0; \
	for file in $(SOURCE_FILES); do \
		chnum=$$(printf "%02d" $$chapter); \
		ln -s ../$(RENDERED_NOTEBOOKS)/$$file book/$$(echo $$file | sed 's/.*/'$${chnum}'-&/g'); \
		chapter=$$(expr $$chapter + 1); \
	done
	cd book; $(BOOKBOOK_LATEX)
	mv book/combined.tex $@
	$(RM) -r book
	@echo Created $@

$(HTML_TARGET)book.html: $(FULLS) $(BIB) $(PUBLISH_PLUGINS)
	-$(RM) -r book
	$(MKDIR) book
	for file in $(SOURCE_FILES); do \
	    ln -s ../$(FULL_NOTEBOOKS)/$$file book/$$(echo $$file | sed 's/[^-0-9]*\([-0-9][0-9]*\)_\(.*\)/\1-\2/g'); \
	done
	cd book; $(BOOKBOOK_HTML)
	mv book/html/index.html $@
	mv book/html/*.html $(HTML_TARGET)
	$(RM) -r book
	@echo Created $@
endif


## Some checks

# Style checks
.PHONY: style check-style checkstyle
style check-style checkstyle: $(PYS) $(PYCODESTYLE_CFG)
	$(PYCODESTYLE) --config $(PYCODESTYLE_CFG) $(PYS)
	@echo "All style checks passed."
	
# Automatic formatting
.PHONY: autopep8 reformat
autopep8 reformat: $(PYCODESTYLE_CFG)
	$(NBAUTOPEP8) --split-cells --jobs -1 $(AUTOPEP8_OPTIONS) $(SOURCES)
	@echo "Code reformatting complete.  Use 'make full' to re-execute and test notebooks."


# List of Cross References
.PHONY: check-crossref crossref xref
check-crossref crossref xref: $(SOURCES)
	@echo "Referenced notebooks (* = missing)"
	@files=$$(grep '\.ipynb)' $(SOURCES) | sed 's/.*[(]\([a-zA-Z0-9_][a-zA-Z0-9_-]*\.ipynb\)[)].*/\1/' | grep -v http | sort | uniq); \
	for file in $$files; do \
		if [ -f $(NOTEBOOKS)/$$file ]; then \
		    echo '  ' $$file; \
		else \
			echo '* ' $$file "- in" $$(cd $(NOTEBOOKS); grep -l $$file $(SOURCE_FILES)); \
		fi \
	done


# Stats
.PHONY: stats
stats: $(SOURCES)
	@cd $(NOTEBOOKS); ../utils/nbstats.py $(SOURCE_FILES)

# Run all code.  This should produce no failures.
PY_SUCCESS_MAGIC = "--- Code check passed ---"
PYS_OUT = $(SOURCE_FILES:%.ipynb=$(CODE_TARGET)%.py.out)
# PYS_OUT = $(PUBLIC_SOURCES:%.ipynb=$(CODE_TARGET)%.py.out)
$(CODE_TARGET)%.py.out:	$(CODE_TARGET)%.py
	@echo Running $<...
	@if $(PYTHON) $< > $@ 2>&1; then \
		echo $(PY_SUCCESS_MAGIC) >> $@; \
		exit 0; \
	else \
		echo "Error while running $<" >> $@; \
		tail $@; \
		touch -r $< $@; \
		touch -A -010000 $@; \
		exit 1; \
	fi

.PHONY: check-code
check-code: code $(PYS_OUT)
	@files_with_errors=$$(grep --files-without-match -- $(PY_SUCCESS_MAGIC) $(PYS_OUT)); \
	if [ -z "$$files_with_errors" ]; then \
		echo "All code checks passed."; \
	else \
		echo "Check these files for errors: $$files_with_errors"; \
		exit 1; \
	fi

# Import all code.  This should produce no output (or error messages).
IMPORTS = $(subst .ipynb,,$(CHAPTERS) $(APPENDICES))
.PHONY: check-import check-imports
check-import check-imports: code
	@echo "#!/usr/bin/env $(PYTHON)" > $(CODE_TARGET)import_all.py
	@(for file in $(IMPORTS); do echo import $$file; done) | grep -v '^import [0-9][0-9]' >> $(CODE_TARGET)import_all.py
	cd $(CODE_TARGET); $(PYTHON) import_all.py 2>&1 | tee import_all.py.out
	@test ! -s $(CODE_TARGET)import_all.py.out && echo "All import checks passed."
	@$(RM) $(CODE_TARGET)import_all.py*
	
# Same as above, but using Python standard packages only; import should work too
check-standard-imports: code
	PYTHONPATH= $(MAKE) check-imports

check-package: code
	@echo "#!/usr/bin/env $(PYTHON)" > import_packages.py
	@(for file in $(IMPORTS); do echo import code.$$file; done) | grep -v '^import code.[0-9][0-9]' >> import_packages.py
	$(PYTHON) import_packages.py 2>&1 | tee import_packages.py.out
	@test ! -s import_packages.py.out && echo "Package check passed."
	@$(RM) import_packages.py*


.PHONY: run
run: check-imports check-standard-imports check-package check-code

# Todo checks
check-todo todo:
	@grep '\\todo' $(PUBLIC_SOURCES) $(READY_SOURCES); \
	if [ $$? = 0 ]; then exit 1; else \
	echo "No todos in $(PUBLIC_CHAPTERS:%.ipynb=%) $(READY_CHAPTERS:%.ipynb=%)"; exit 0; fi

# Spell checks
NBSPELLCHECK = utils/nbspellcheck.py
.PHONY: spell spellcheck check-spell
spell spellcheck check-spell:
	$(NBSPELLCHECK) $(SOURCES)


# All checks
.PHONY: check check-all
check check-all: check-import check-package check-code check-style check-crossref check-todo
	
# Add notebook metadata (add table of contents, bib reference, etc.)
.PHONY: metadata
metadata: $(ADD_METADATA)
	@for notebook in $(SOURCES); do \
		echo "Adding metadata to $$notebook...\c"; \
		$(PYTHON) $(ADD_METADATA) $$notebook > $$notebook~ || exit 1; \
		if diff $$notebook $$notebook~; then \
			echo "unchanged."; \
		else \
		    mv $$notebook~ $$notebook; \
			echo "done."; \
		fi; \
		$(RM) $$notebook~; \
	done


## Publishing
.PHONY: docs
docs: publish-notebooks publish-index publish-html publish-code publish-dist \
	publish-slides publish-pics \
	$(DOCS_TARGET)index.html $(DOCS_TARGET)404.html README.md binder/postBuild
	@echo "Now use 'make publish-all' to commit changes to docs."

# github does not like script tags;
# links to notebooks need to get adapted
README.md: $(MARKDOWN_TARGET)index.md Makefile
	sed 's!<script.*</script>!!g' $< | \
	sed 's!(\([_a-zA-Z0-9]*\).ipynb)!($(SITE)/html/\1.html)!g'> $@

.PHONY: publish
publish: run docs
	git add $(DOCS_TARGET)* binder/postBuild README.md
	-git status
	-git commit -m "Doc update" $(DOCS_TARGET) binder README.md
	@echo "Now use 'make push' to place docs on website and trigger a mybinder update"

# Add/update HTML code in Web pages
.PHONY: publish-html publish-html-setup
publish-html: html publish-html-setup \
	$(DOCS_TARGET)html/00_Index.html \
	$(DOCS_TARGET)html/00_Table_of_Contents.html \
	$(DOCS_TARGET)html/custom.css \
	$(DOCS_TARGET)html/favicon \
	$(DOCS:%=$(DOCS_TARGET)html/%.html) \
	$(DOCS:%=$(DOCS_TARGET)html/%_files)
	
publish-html-setup:
	@test -d $(DOCS_TARGET) || $(MKDIR) $(DOCS_TARGET)
	@test -d $(DOCS_TARGET)html || $(MKDIR) $(DOCS_TARGET)html
	
$(DOCS_TARGET)html/%: $(HTML_TARGET)%
	cp -pr $< $@

# Add/update Python code on Web pages
.PHONY: publish-code publish-code-setup
publish-code: code publish-code-setup \
	$(DOCS_TARGET)code/LICENSE.md \
	$(DOCS_TARGET)code/README.md \
	$(DOCS_TARGET)code/setup.py \
	$(DOCS_TARGET)code/__init__.py \
	$(UTILITY_FILES:%=$(DOCS_TARGET)code/fuzzingbook_utils/%) \
	$(PUBLIC_CHAPTERS:%.ipynb=$(DOCS_TARGET)code/%.py) \
	$(APPENDICES:%.ipynb=$(DOCS_TARGET)code/%.py)

publish-code-setup:
	@test -d $(DOCS_TARGET) \
		|| $(MKDIR) $(DOCS_TARGET)
	@test -d $(DOCS_TARGET)code \
		|| $(MKDIR) $(DOCS_TARGET)code
	@test -d $(DOCS_TARGET)code/fuzzingbook_utils \
		|| $(MKDIR) $(DOCS_TARGET)code/fuzzingbook_utils
	
$(DOCS_TARGET)code/%: $(CODE_TARGET)%
	cp -pr $< $@

.PHONY: dist publish-dist
dist publish-dist: check-import check-package check-code publish-code toc \
	$(DOCS_TARGET)dist/fuzzingbook-code.zip \
	$(DOCS_TARGET)dist/fuzzingbook-notebooks.zip

DIST_CODE_FILES = \
	$(DOCS_TARGET)code/README.md \
	$(DOCS_TARGET)code/LICENSE.md \
	$(DOCS_TARGET)code/setup.py \
	$(DOCS_TARGET)code/__init__.py
	
check-fuzzingbook-install:
	@-$(PYTHON) -c 'import fuzzingbook' 2> /dev/null; \
	if [ $$? = 0 ]; then \
		echo "Error: Installed fuzzingbook package conflicts with package creation" >&2; \
		echo "Please uninstall it; e.g. with 'pip uninstall fuzzingbook'." >&2; \
		exit 1; \
	else \
		exit 0; \
	fi

$(DOCS_TARGET)dist/fuzzingbook-code.zip: \
	$(PYS) $(DIST_CODE_FILES) $(CHAPTERS_MAKEFILE) check-fuzzingbook-install
	@-mkdir $(DOCS_TARGET)dist
	$(RM) -r $(DOCS_TARGET)dist/*
	$(RM) -r $(DOCS_TARGET)fuzzingbook
	mkdir $(DOCS_TARGET)fuzzingbook
	ln -s ../code $(DOCS_TARGET)fuzzingbook/fuzzingbook
	mv $(DOCS_TARGET)fuzzingbook/fuzzingbook/setup.py $(DOCS_TARGET)fuzzingbook
	mv $(DOCS_TARGET)fuzzingbook/fuzzingbook/README.md $(DOCS_TARGET)fuzzingbook
	cd $(DOCS_TARGET)fuzzingbook; PYTHONPATH= $(PYTHON) ./setup.py sdist
	mv $(DOCS_TARGET)fuzzingbook/dist/* $(DOCS_TARGET)dist
	$(RM) -r $(DOCS_TARGET)fuzzingbook/*.egg-info
	$(RM) -r $(DOCS_TARGET)fuzzingbook/dist $(DOCS_TARGET)fuzzingbook/build
	cd $(DOCS_TARGET); $(ZIP) $(ZIP_OPTIONS) fuzzingbook-code.zip fuzzingbook
	mv $(DOCS_TARGET)fuzzingbook-code.zip $(DOCS_TARGET)dist
	$(RM) -r $(DOCS_TARGET)fuzzingbook $(DOCS_TARGET)code/fuzzingbook
	$(RM) -r $(DOCS_TARGET)code/dist $(DOCS_TARGET)code/*.egg-info
	@echo "Created code distribution files in $(DOCS_TARGET)dist"
	
$(DOCS_TARGET)dist/fuzzingbook-notebooks.zip: $(FULLS) $(CHAPTERS_MAKEFILE)
	$(RM) -r $(DOCS_TARGET)notebooks/fuzzingbook_utils/__pycache__
	cd $(DOCS_TARGET); ln -s notebooks fuzzingbook-notebooks
	cd $(DOCS_TARGET); \
		$(ZIP) $(ZIP_OPTIONS) fuzzingbook-notebooks.zip fuzzingbook-notebooks
	$(RM) $(DOCS_TARGET)/fuzzingbook-notebooks
	cd $(DOCS_TARGET); \
		for file in $(EXTRAS); do \
			$(ZIP) fuzzingbook-notebooks.zip -d fuzzingbook-notebooks/$$file; \
		done
	mv $(DOCS_TARGET)fuzzingbook-notebooks.zip $@
	@echo "Created notebook distribution files in $(DOCS_TARGET)dist"


# Add/update slides on Web pages
.PHONY: publish-slides publish-slides-setup
publish-slides: slides publish-slides-setup \
	$(PUBLIC_CHAPTERS:%.ipynb=$(DOCS_TARGET)slides/%.slides.html) \
	$(APPENDICES:%.ipynb=$(DOCS_TARGET)slides/%.slides.html)
	
publish-slides-setup:
	@test -d $(DOCS_TARGET) || $(MKDIR) $(DOCS_TARGET)
	@test -d $(DOCS_TARGET)slides || $(MKDIR) $(DOCS_TARGET)slides

$(DOCS_TARGET)slides/%: $(SLIDES_TARGET)%
	cp -pr $< $@


# Add/update notebooks on Web pages
.PHONY: publish-notebooks publish-notebooks-setup
publish-notebooks: full-notebooks publish-notebooks-setup \
	$(DOCS_TARGET)notebooks/custom.css \
	$(DOCS_TARGET)notebooks/fuzzingbook.bib \
	$(DOCS_TARGET)notebooks/LICENSE.md \
	$(DOCS_TARGET)notebooks/README.md \
	$(DOCS:%=$(DOCS_TARGET)notebooks/%.ipynb) \
	$(UTILITY_FILES:%=$(DOCS_TARGET)notebooks/fuzzingbook_utils/%)
	
publish-notebooks-setup:
	@test -d $(DOCS_TARGET) \
		|| $(MKDIR) $(DOCS_TARGET)
	@test -d $(DOCS_TARGET)notebooks \
		|| $(MKDIR) $(DOCS_TARGET)notebooks
	@test -d $(DOCS_TARGET)notebooks/fuzzingbook_utils \
		|| $(MKDIR) $(DOCS_TARGET)notebooks/fuzzingbook_utils

$(DOCS_TARGET)notebooks/%: $(FULL_NOTEBOOKS)/%
	cp -pr $< $@



.PHONY: publish-index
publish-index: $(DOCS_TARGET)notebooks/00_Index.ipynb


# Add/update pics on Web pages
.PHONY: publish-pics publish-pics-setup
publish-pics: publish-pics-setup $(NOTEBOOKS)/PICS
	cp -pr $(NOTEBOOKS)/PICS $(DOCS_TARGET)notebooks

publish-pics-setup:
	@test -d $(DOCS_TARGET) || $(MKDIR) $(DOCS_TARGET)
	@test -d $(DOCS_TARGET)PICS || $(MKDIR) $(DOCS_TARGET)PICS
	$(RM) -fr $(DOCS_TARGET)html/PICS; ln -s ../$(NOTEBOOKS)/PICS $(DOCS_TARGET)html
	$(RM) -fr $(DOCS_TARGET)slides/PICS; ln -s ../$(NOTEBOOKS)/PICS $(DOCS_TARGET)slides


# Table of contents
.PHONY: toc
toc: $(DOCS_TARGET)notebooks/00_Table_of_Contents.ipynb
$(DOCS_TARGET)notebooks/00_Table_of_Contents.ipynb: utils/nbtoc.py \
	$(TOC_CHAPTERS:%=$(DOCS_TARGET)notebooks/%) \
	$(TOC_APPENDICES:%=$(DOCS_TARGET)notebooks/%) \
	$(CHAPTERS_MAKEFILE) \
	$(SITEMAP_SVG)
	$(RM) $@
	$(PYTHON) utils/nbtoc.py \
		--chapters="$(TOC_CHAPTERS:%=$(DOCS_TARGET)notebooks/%)" \
		--appendices="$(TOC_APPENDICES:%=$(DOCS_TARGET)notebooks/%)" > $@
	$(EXECUTE_NOTEBOOK) $@ && mv $(FULL_NOTEBOOKS)/00_Table_of_Contents.ipynb $@
	$(PYTHON) $(ADD_METADATA) $@ > $@~ && mv $@~ $@
	$(JUPYTER) trust $@
	@$(OPEN) $@

		
# Index
.PHONY: index
index: $(DOCS_TARGET)/notebooks/00_Index.ipynb $(DOCS_TARGET)/html/00_Index.html
$(DOCS_TARGET)notebooks/00_Index.ipynb: utils/nbindex.py \
	$(TOC_CHAPTERS:%=$(DOCS_TARGET)notebooks/%) \
	$(TOC_APPENDICES:%=$(DOCS_TARGET)notebooks/%) \
	$(CHAPTERS_MAKEFILE)
	(cd $(NOTEBOOKS); $(PYTHON) ../utils/nbindex.py $(TOC_CHAPTERS) $(APPENDICES)) > $@
	@$(OPEN) $@
	

## Synopsis
update-synopsis:
	$(PYTHON) $(NBSYNOPSIS) --update $(CHAPTER_SOURCES)

no-synopsis:
	@echo Chapters without synopsis:
	@grep -L '## Synopsis' $(CHAPTER_SOURCES) | grep -v '[0-9]'


## Python packages
# After this, you can do 'pip install fuzzingbook' 
# and then 'from fuzzingbook.Fuzzer import Fuzzer' :-)
.PHONY: upload-dist
upload-dist: dist
	@echo "Use your pypi.org password to upload"
	cd $(DOCS_TARGET); twine upload dist/*.tar.gz



## Binder services
# Make sure we have our custom.css in Binder, too
binder/postBuild: binder/postBuild.template $(HTML_TARGET)custom.css
	cat binder/postBuild.template $(HTML_TARGET)custom.css > $@
	echo END >> $@
	chmod +x $@

# Force recreation of binder service; avoids long waiting times for first user
.PHONY: binder
binder: .FORCE
	open $(BINDER_URL)

# After a git push, we want binder to update; "make push" does this
.PHONY: push
push: .FORCE
	git push
	open $(BINDER_URL)

# Debugging binder
# This is the same system as mybinder uses, but should be easier to debug
# See https://repo2docker.readthedocs.io/en/latest/
.PRECIOUS: binder/binder.log
.PHONY: binder-local debug-binder
binder-local debug-binder: binder/binder.log binder/postBuild
binder/binder.log: .FORCE
	@echo Writing output to $@
	@docker version > /dev/null
	jupyter-repo2docker --debug $(GITHUB_REPO) 2>&1 | tee $@


## Docker services (experimental)
docker:
	docker pull fuzzingbook/student
	-docker run -d -p 8888:8888 --name fuzzing-book-instance fuzzingbook/student

docker-start:
	docker start fuzzing-book-instance
	sleep 2
	@URL=$$(docker exec -it fuzzing-book-instance jupyter notebook list | grep http | awk '{ print $$1 }'); echo $$URL; open $$URL

docker-stop:
	docker stop fuzzing-book-instance
	

## Getting rid of stray processes
kill:
	-pkill -HUP -l -f jupyter-lab Firefox.app firefox-bin runserver

## Cleanup
AUX = *.aux *.bbl *.blg *.log *.out *.toc *.frm *.lof *.lot *.fls *.fdb_latexmk \
	  $(PDF_TARGET)*.aux \
	  $(PDF_TARGET)*.bbl \
	  $(PDF_TARGET)*.blg \
	  $(PDF_TARGET)*.log \
	  $(PDF_TARGET)*.out \
	  $(PDF_TARGET)*.toc \
	  $(PDF_TARGET)*.frm \
	  $(PDF_TARGET)*.lof \
	  $(PDF_TARGET)*.lot \
	  $(PDF_TARGET)*.fls \
	  $(PDF_TARGET)*.xdv \
	  $(PDF_TARGET)*.fdb_latexmk

.PHONY: clean-code clean-chapters clean-book clean-aux clean-pdf
clean-code:
	$(RM) $(PYS) $(PYS_OUT)

clean-chapters:
	$(RM) $(TEXS) $(PDFS) $(HTMLS) $(SLIDES) $(WORDS) $(MARKDOWNS)
	$(RM) -r $(PDF_FILES) $(HTML_FILES) $(SLIDES_FILES)

clean-book:
	$(RM) $(BOOK_TEX) $(BOOK_PDF) $(BOOK_HTML)
	$(RM) -r $(BOOK_HTML_FILES) $(BOOK_PDF_FILES)

clean-aux clean-pdf:
	$(RM) $(AUX)

.PHONY: clean-full-notebooks clean-full clean-fulls 
.PHONY: clean-rendered-notebooks clean-rendered clean-renders
.PHONY: clean-docs clean realclean
clean-full-notebooks clean-full clean-fulls:
	$(RM) $(FULLS)

clean-rendered-notebooks clean-rendered clean-renders:
	$(RM) $(RENDERS)

clean-docs:
	$(RM) -r $(DOCS_TARGET)html $(DOCS_TARGET)code \
	 	$(DOCS_TARGET)slides $(DOCS_TARGET)index.html $(DOCS_TARGET)404.html \ 		$(DOCS_TARGET)PICS $(DOCS_TARGET)notebooks

clean: clean-code clean-chapters clean-book clean-aux clean-docs clean-fulls clean-renders
	@echo "All derived files deleted"

realclean: clean
	cd $(PDF_TARGET); $(RM) *.pdf
	cd $(HTML_TARGET); $(RM) *.html; $(RM) -r *_files
	cd $(SLIDES_TARGET); $(RM) *.html
	cd $(CODE_TARGET); $(RM) *.py *.py.out
	cd $(WORD_TARGET); $(RM) *.docx
	cd $(MARKDOWN_TARGET); $(RM) *.md
	@echo "All old files deleted"


## A bit of Makefile debugging
# See http://www.drdobbs.com/tools/debugging-makefiles/197003338#

# Use "make print-VAR" to see the value of VAR, e.g. "make print-NBDEPEND"
print-%: ; @$(error $* = $($*) (defined as $* = $(value $*) from $(origin $*)))

# Use "make DEBUG=1" to get better diagnostics why a command gets executed
ifdef DEBUG
OLD_SHELL := $(SHELL)
SHELL = $(warning creating $@ from $^: $? is newer)$(OLD_SHELL)
endif


## Dependencies as graph
NBDEPEND = utils/nbdepend.py
SITEMAP_OPTIONS = --graph --transitive-reduction # --cluster-by-parts

sitemap: $(SITEMAP_SVG)
$(SITEMAP_SVG): $(CHAPTER_SOURCES) $(NBDEPEND)
	$(PYTHON) $(NBDEPEND) $(SITEMAP_OPTIONS) $(CHAPTER_SOURCES) > $@~ && mv $@~ $@
	@$(OPEN) $@

$(FULL_NOTEBOOKS)/Tours.ipynb: $(SITEMAP_SVH)	
$(RENDERED_NOTEBOOKS)/Tours.ipynb: $(SITEMAP_SVH)	

$(FULL_NOTEBOOKS)/00_Table_of_Contents.ipynb: $(SITEMAP_SVH)	
$(RENDERED_NOTEBOOKS)/00_Table_of_Contents.ipynb: $(SITEMAP_SVH)	


## Dependencies - should come at the very end
# See http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/ for inspiration
$(DEPEND_TARGET)%.makefile: $(NOTEBOOKS)/%.ipynb
	@echo "Rebuilding $@"
	@test -d $(DEPEND_TARGET) || $(MKDIR) $(DEPEND_TARGET)
	@for import in $$($(PYTHON) $(NBDEPEND) $<); do \
		if [ -f $(NOTEBOOKS)/$$import.ipynb ]; then \
			notebooks="$$notebooks $$""(NOTEBOOKS)/$$import.ipynb"; \
			imports="$$imports $$""(CODE_TARGET)$$import.py"; \
		fi; \
	done; \
	( \
		echo '# $(basename $(notdir $<)) dependencies'; \
		echo ''; \
		echo '$$''(FULL_NOTEBOOKS)/$(notdir $<):' $$notebooks; \
		echo ''; \
		echo '$$''(RENDERED_NOTEBOOKS)/$(notdir $<):' $$notebooks; \
		echo ''; \
		echo '$$''(CODE_TARGET)$(notdir $(<:%.ipynb=%.py.out)):' $$imports; \
	) > $@


.PHONY: depend
depend: $(DEPENDS)

include $(wildcard $(DEPENDS))
