AGDA := agda
LATEX := xelatex

SRCDIR := UALib
HTMLDIR := html

MAIN := UALib Preface
MODS := Overture Relations Algebras Homomorphisms Terms Subalgebras Varieties

# UALib.lagda Preface.lagda
AGDA_MAIN := $(foreach name,$(MAIN),$(SRCDIR)/$(name).lagda)

# e.g., Overture.lagda Relations.lagda Algebras.lagda ...
AGDA_MODS := $(foreach name,$(MODS),$(SRCDIR)/$(name).lagda)

# e.g., Overture/Preliminaries.lagda Overture/Equality.lagda ...
AGDA_SUBMODS := $(wildcard $(foreach name,$(MODS),$(SRCDIR)/$(name)/*.lagda))

AGDA_FILES := $(AGDA_MAIN) $(AGDA_MODS) $(AGDA_SUBMODS)

MD_MAIN := $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MAIN:.lagda=.md))
MD_MODS := $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MODS:.lagda=.md))
MD_SUBMODS := $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_SUBMODS:.lagda=.md))

# TEX_SUBMODS := $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_SUBMODS:.lagda=.tex))
# MD_SUBMODS := $(subst $(SRCDIR).,,$(subst /,.,$(AGDA_SUBMODS:.lagda=.md)))

# all: $(MD_MAIN) $(MD_MODS) $(MD_SUBMODS) $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MAIN:.lagda=.tex))
all: $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MAIN:.lagda=.tex)) \
     $(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MODS:.lagda=.tex)) \
     $(subst UALib.,UALib/,$(subst $(SRCDIR)/,$(HTMLDIR)/,$(subst /,.,$(AGDA_SUBMODS:.lagda=.tex))))

$(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MAIN:.lagda=.tex)): $(AGDA_MAIN)
	@echo $@ $($@:.tex=.md)
# $(AGDA) --html --html-highlight=code $<

$(subst $(SRCDIR)/,$(HTMLDIR)/,$(AGDA_MODS:.lagda=.tex)): $(AGDA_MODS)
	@echo "target:   $@    prereq:  $<      mv arg: $($@:.tex=.md)"

$(subst UALib.,UALib/,$(subst $(SRCDIR)/,$(HTMLDIR)/,$(subst /,.,$(AGDA_SUBMODS:.lagda=.tex)))): $(AGDA_SUBMODS)
	@echo "target:   $@    prereq:  $<      mv arg: $($@:.tex=.md)"

# $(MD_MAIN): $(subst html/,UALib/,$(@:.md=.lagda))
# 	@echo "target: $@ prereq: $<"
# # agda --html --html-highlight=code UALib.lagda

# # mv html/Empty-Type.{tex,md}
# $(MD_MODS): %.md: %.lagda
# 	@echo "target: $@ prereq: $<"

# $(MD_SUBMODS): %.md: %.lagda
# 	@echo "target: $@ prereq: $<"

.PHONY: $(MD_MAIN:.md=.lagda) $(MD_MODS:.md=.lagda) $(MD_SUBMODS:.md=.lagda)

# $(MD_MODS):
# 	@echo $@

# $(MD_SUBMODS):
# 	@echo $@

# $(ALL_MD_FILES):
# 	echo $@

# index.md :

# 	cp $(HTMLDIR)/UALib.md $@

# html/UALib.md : agda --html --html-highlight=code UALib.lagda

# gen-tex: $(lagda)
# 	for f in $(lagda); do agda --latex $$f; done

# $(tex): %.tex: %.lagda $(lagda)
# 	agda --latex $<

# %.tex: %.lagda
# 	@echo $<
# FIGURES_SVG=$(wildcard figures/svg/*.svg)
# FIGURES_PDF=$(subst svg/,pdf/,$(FIGURES_SVG:.svg=.pdf))
# FIGURES_PNG=$(subst figures/svg/,defense/images/,$(FIGURES_SVG:.svg=.png))

# all: $(INPUTS) $(FIGURES_PNG)  ## Build full thesis (LaTeX + figures)
#     $(LATEX) $(MAIN)                # main run
#     bibtex $(MAIN:.tex=)            # bibliography
#     makeglossaries $(MAIN:.tex=)    # list of abbreviations, nomenclature
#     $(LATEX) $(MAIN)                # incremental run
#
# clean:  ## Clean LaTeX and output figure files
#     rubber --clean $(MAIN)
#     rm -f $(FIGURES_PDF) $(FIGURES_PNG)
# figures/pdf/%.pdf: figures/svg/%.svg  ## Figures for the manuscript
#     inkscape -C -z --file=$< --export-pdf=$@
#
# defense/images/%.png: figures/svg/%.svg  ## Figures for my defense slides
#     inkscape -C -z --file=$< --export-png=$@
#
# watch:  ## Recompile on any update of LaTeX or SVG sources
#     @while [ 1 ]; do;          \
#         inotifywait $(ALL);    \
#         sleep 0.01;            \
#         make all;              \
#         echo "\n----------\n"; \
#         done
#
# help:  # http://marmelab.com/blog/2016/02/29/auto-documented-makefile.html
#     @grep -P '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'
# .DEFAULT_GOAL := help
# .PHONY: help
