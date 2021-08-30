# This file is essentially a copy of the Makefile in the agda-categories library by Jacques Carette.
# The only difference is that this version works with .lagda files instead of .agda files.
# The original Makefile from agda-categories is https://github.com/agda/agda-categories/blob/master/Makefile

.PHONY: test Everything.agda clean md html profile latex pandoc

OTHEROPTS=
RTSARGS = +RTS -M6G -A128M ${OTHEROPTS} -RTS

# Locations
SRCDIR := src
TEXDIR := tex
LATEXDIR := latex
HTMLDIR := html
INCLDIR := _includes

# File names
SRC := $(shell find $(SRCDIR) -name "*.lagda")
MODULES := $(shell find $(SRCDIR) -name "*.lagda" | sed -e 's|^src/[/]*||' -e 's|/|.|g')

TEXFILES = $(shell find . -name "*.tex")
TEXMDFILES = $(wildcard $(HTMLDIR)/*.tex)
MDFILES = $(TEXMDFILES:.tex=.md)
LINKFILE = $(INCLDIR)/UALib.Links.md

default: Everything.agda

all: html Everything.agda md $(MDFILES)
	@echo "target: $@ prereq: $<"

test: Everything.agda
	@echo "target: $@ prereq: $<"
	agda ${RTSARGS} $(SRCDIR)/Everything.agda

Everything.agda:
	@echo "target: $@ prereq: $<"
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.lagda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.lagda//' -e '/import Everything/d' | LC_COLLATE='C' sort > $(SRCDIR)/Everything.agda

# Make markdown files for html documentation served by jekyll
md: html $(MDFILES)
	@echo "target: $@ prereq: $<"

docs: html $(HTMLDIR)/index.markdown $(TEXDIR)/agda-algebras.tex
	@echo "target: $@ prereq: $<"

html: Everything.agda
	@echo "target: $@ prereq: $<"
	@echo $@
	agda ${RTSARGS} --html --html-highlight=code $(SRCDIR)/Everything.agda

$(HTMLDIR)/index.markdown: $(HTMLDIR)/agda-algebras.md
	@echo "target: $@ prereq: $<"
	cp $< $@

## Rule for converting all the agda generated markdown files from .tex to .md
$(MDFILES): $(TEXMDFILES)
	@echo "target: $@ prereq: $<"
	mv $< $@

clean:
	find . -name '*.agdai' -exec rm \{\} \;

profile: Everything.agda
	@echo "target: $@ prereq: $<"
	agda ${RTSARGS} -v profile:7 -v profile.definitions:15 $(SRCDIR)/Everything.agda



# ## default rule for converting a markdown file to a latex file
# %.tex: %.md
# 	@echo "target: $@ prereq: $<"
# 	cat $(LINKFILE) >> $<              ## first add links to bottom of md so pandoc can insert them as \hrefs
# 	pandoc -f markdown -t latex $< -o $@

