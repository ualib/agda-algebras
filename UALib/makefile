TOP = ..

include $(TOP)/mk/paths.mk

default: UALib

AGDA = agda --html --html-highlight=code


MGS=Empty-Type \
    Identity-Type \
    MGS-Basic-UF \
    MGS-Embeddings \
    MGS-Equivalence-Induction \
    MGS-Equivalences \
    MGS-FunExt-from-Univalence \
    MGS-HAE \
    MGS-hlevels \
    MGS-MLTT \
    MGS-More-FunExt-Consequences \
    MGS-Powerset \
    MGS-Retracts \
    MGS-Solved-Exercises \
    MGS-Subsingleton-Theorems \
    MGS-Subsingleton-Truncation \
    MGS-Unique-Existence \
    MGS-Univalence \
    Natural-Numbers-Type \
    Plus-Type \
    Sigma-Type \
    Unit-Type \
    Universes

UALIB=UALib \
      Preface \
      Overture \
      Overture.Preliminaries \
      Overture.Equality \
      Overture.Inverses \
      Overture.Extensionality \
      Overture.Lifts \
      Relations \
      Relations.Discrete \
      Relations.Continuous \
      Relations.Quotients \
      Relations.Truncation \
      Algebras \
      Algebras.Signatures \
      Algebras.Algebras \
      Algebras.Products \
      Algebras.Congruences \
      Homomorphisms \
      Homomorphisms.Basic \
      Homomorphisms.Noether \
      Homomorphisms.Isomorphisms \
      Homomorphisms.HomomorphicImages \
      Terms \
      Terms.Basic \
      Terms.Operations \
      Subalgebras \
      Subalgebras.Subuniverses \
      Subalgebras.Subalgebras \
      Subalgebras.Univalent \
      Varieties \
      Varieties.EquationalLogic \
      Varieties.Varieties \
      Varieties.Preservation \
      Varieties.FreeAlgebras

MODULE_NAMES := Preface Overture Relations Algebras Homomorphisms Terms Subalgebras Varieties


UALib : $(HTML_DIR)/UALib.md

$(HTML_DIR)/UALib.md: $(HTML_DIR)/UALib.tex
	cp $< $@
	for f in $(UALIB); do cp $(HTML_DIR)/$$f.tex $(HTML_DIR)/$$f.md; done
	for f in $(MGS); do cp $(HTML_DIR)/$$f.tex $(HTML_DIR)/$$f.html; done

$(HTML_DIR)/UALib.tex: UALib.lagda $(MODULE_NAMES)
	$(AGDA) UALib.lagda

Preface: Preface.lagda

Overture: $(wildcard Overture/*.lagda)

Relations: $(wildcard Relations/*.lagda)

Algebras: $(wildcard Algebras/*.lagda)

Homomorphisms: $(wildcard Homomorphisms/*.lagda)

Terms: $(wildcard Terms/*.lagda)

Subalgebras: $(wildcard Subalgebras/*.lagda)

Varieties: $(wildcard Varieties/*.lagda)



# #### Varieties #################################################3
# DEPS := $(NAME)
# NAME := Varieties
# LAGDA := $(wildcard $(NAME)/*.lagda)
# MD := $(addprefix $(HTML_DIR)/,$(subst /,.,$(LAGDA:.lagda=.md)))
# TEX := $(addprefix $(HTML_DIR)/,$(subst /,.,$(LAGDA:.lagda=.tex)))
# $(NAME): $(MD) $(DEPS)
# $(MD): %.md: %.tex
# 	cp $< $@
# $(TEX): $(LAGDA)
# 	for f in $(LAGDA); do $(AGDA) $$f; done
