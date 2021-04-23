TOP = ..

include $(TOP)/mk/paths.mk

default: UniversalAlgebra

AGDA = agda --html --html-highlight=code

AGDADATA = Agda.Builtin.Bool \
           Agda.Builtin.Equality \
           Agda.Builtin.Sigma \
           Agda.Builtin.Strict \
           Agda.Builtin.Unit \
           Agda.Primitive.Cubical \
           Agda.Primitive \
           Data.Bool.Base \
           Data.Empty \
           Data.Empty.Irrelevant \
           Data.Maybe.Base \
           Data.Product \
           Data.Sum.Base \
           Data.Sum \
           Data.These.Base \
           Data.Unit.Base

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

UALIBDOTS=UniversalAlgebra \
          Preface \
          Overture \
          Overture.Preliminaries \
          Overture.Equality \
          Overture.Inverses \
          Overture.FunExtensionality \
          Overture.Lifts \
          Relations \
          Relations.Discrete \
          Relations.Continuous \
          Relations.Quotients \
          Relations.Truncation \
          Relations.Extensionality \
          Algebras \
          Algebras.Basic \
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

UALIB=UALib \
      Preface \
      Overture \
      Overture/Preliminaries \
      Overture/Equality \
      Overture/Inverses \
      Overture/FunExtensionality \
      Overture/Lifts \
      Relations \
      Relations/Discrete \
      Relations/Continuous \
      Relations/Quotients \
      Relations/Truncation \
      Relations/Extensionality \
      Algebras \
      Algebras/Basic \
      Algebras/Products \
      Algebras/Congruences \
      Homomorphisms \
      Homomorphisms/Basic \
      Homomorphisms/Noether \
      Homomorphisms/Isomorphisms \
      Homomorphisms/HomomorphicImages \
      Terms \
      Terms/Basic \
      Terms/Operations \
      Subalgebras \
      Subalgebras/Subuniverses \
      Subalgebras/Subalgebras \
      Subalgebras/Univalent \
      Varieties \
      Varieties/EquationalLogic \
      Varieties/Varieties \
      Varieties/Preservation \
      Varieties/FreeAlgebras

MODULE_NAMES := Preface Overture Relations Algebras Homomorphisms Terms Subalgebras Varieties


UALib : $(HTML_DIR)/UALib.md

$(HTML_DIR)/UniversalAlgebra.md: $(HTML_DIR)/UniversalAlgebra.tex
	cp $< $@
	for f in $(UALIBDOTS); do cp $(HTML_DIR)/$$f.tex $(HTML_DIR)/$$f.md; done
	for f in $(AGDADATA); do rm $(HTML_DIR)/$$f.html; done

$(HTML_DIR)/UniversalAlgebra.tex: UniversalAlgebra.lagda $(MODULE_NAMES)
	$(AGDA) UniversalAlgebra.lagda


# To make the raw .tex source files, do `make tex`
tex: UniversalAlgebra.lagda $(MODULE_NAMES)
	for f in $(UALIB); do \
      echo "Checking $$f.lagda"; \
      agda --latex $$f.lagda; \
      mv latex/$$f.tex latex/$$f.md; \
      pandoc --latex-engine=xelatex -f markdown -t latex latex/$$f.md -o latex/$$f.tex; \
  done



Preface: Preface.lagda

Overture: $(wildcard Overture/*.lagda)

Relations: $(wildcard Relations/*.lagda)

Algebras: $(wildcard Algebras/*.lagda)

Homomorphisms: $(wildcard Homomorphisms/*.lagda)

Terms: $(wildcard Terms/*.lagda)

Subalgebras: $(wildcard Subalgebras/*.lagda)

Varieties: $(wildcard Varieties/*.lagda)

