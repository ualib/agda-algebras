MAIN := agda-algebras

# directory locations
AUXDIR := aux
TEXDIR := ../latex
BIBTEXDIR := bib
BUILDDIR := _build

# file names
PDFTARGET := $(MAIN).pdf
SOURCES = $(wildcard $(TEXDIR)/*.tex)
MAINSRC := $(PDFTARGET:.pdf=.tex)

# commands
LATEXCMD := latexrun
BIBTEXCMD := bibtex
export TEXINPUTS="$(abspath $(AUXDIR)):$(abspath $(TEXDIR))"
LATEXRUN := $(LATEXCMD) -O $(BUILDDIR) --bibtex-cmd=$(BIBTEXCMD)

.PHONY: all

all: $(BUILDDIR) $(BUILDDIR)/count.log $(PDFTARGET) $(BIBTEXDIR)
	@echo -n "word count: "
	@cat $(BUILDDIR)/count.log

.PHONY: diff
diff: $(TARGET:.pdf=-diff.pdf)

$(BUILDDIR):
	mkdir -p $(BUILDDIR)

.PHONY: FORCE
$(BUILDDIR)/count.log: FORCE
	@texcount -brief -sum $(SOURCES) tex/* | tail -n 1 | sed -e 's/:.*//' \
		> $(BUILDDIR)/count.log

%.pdf: %.tex FORCE
	$(LATEXRUN) $< -o $@

%-screen.pdf: %.pdf
	pdfcrop --margins 10 $< $@

%-diff.tex: %.tex $(BUILDDIR) $(BUILDDIR)/count.log FORCE
	git fetch origin $(BEFORE)
	git fetch --tags
	$(eval BFR := $(shell git describe --tags --always origin/$(BEFORE)))
	sed -i "1s/^/$(BFR)-diff-/" $(BUILDDIR)/gitversion.log
	$(eval TMPWORKTREE := $(shell mktemp -d))
	git worktree add $(TMPWORKTREE) $(BFR)
	-latexdiff -c resources/ld.cfg --flatten --math-markup=0 --exclude-safecmd="textcite" --exclude-textcmd="title,section,subsection,subsubsection" \
		$(TMPWORKTREE)/$(SOURCE) $(SOURCE) > $(TARGET:.pdf=-diff.tex)
	rm -rf $(TMPWORKTREE)
	git worktree prune

.PHONY: clean
clean:
	$(LATEXRUN) --clean-all
	rm -rf $(BUILDDIR)
