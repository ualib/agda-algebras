# =============================================================================
# agda-algebras — Makefile
# =============================================================================
#
# Run from repo root inside `nix develop` so `agda` and the pinned stdlib
# are on PATH.  If running outside the Nix shell, ensure your Agda and
# standard-library versions match the targets declared in flake.nix and
# agda-algebras.agda-lib.
#
# Primary targets:
#   make              Regenerate src/Everything.agda from the current tree.
#   make check        Type-check the entire library (what CI runs).
#   make test         Alias for `make check`.
#   make html         Generate clickable HTML (in ./html/).
#   make profile      Type-check with Agda profiling enabled.
#   make clean        Remove .agdai artifacts and the generated Everything.
#
# Notes:
#   +  Everything.agda is a PHONY target — always regenerated — so that
#      adding or removing a module is picked up without the user having
#      to remember.
#   +  We use `find` rather than `git ls-tree` so that untracked-but-present
#      files in the working tree are included.  This matters during active
#      development.
#   +  The sed pipeline strips ONLY the trailing `.agda` extension
#      (anchored with `$` and an escaped `\.`), avoiding a class of bugs
#      where a path segment happens to contain the substring `agda`.
# =============================================================================

.PHONY: default all check test clean html profile Everything.agda

# -- Configuration -----------------------------------------------------------
SRCDIR    := src
AGDA      ?= agda
RTS_OPTS  := +RTS -M6G -A128M -RTS
AGDA_OPTS ?=

# -- Targets -----------------------------------------------------------------

default: Everything.agda

Everything.agda:
	@echo "target: $@"
	@{ \
	  echo "{-# OPTIONS --cubical-compatible --safe #-}"; \
	  echo ""; \
	  echo "module Everything where"; \
	  echo ""; \
	  find $(SRCDIR) -name '*.agda' \
	      ! -name 'Everything.agda' \
	      ! -path '$(SRCDIR)/Legacy/*' \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	} > $(SRCDIR)/Everything.agda
	@echo "  wrote $(SRCDIR)/Everything.agda ($$(grep -c '^import' $(SRCDIR)/Everything.agda) modules)"

check test: Everything.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/Everything.agda

html: Everything.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) --html --html-highlight=code $(SRCDIR)/Everything.agda

profile: Everything.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) -v profile:7 -v profile.definitions:15 $(SRCDIR)/Everything.agda

clean:
	@echo "target: $@"
	find . -name '*.agdai' -delete
	rm -f $(SRCDIR)/Everything.agda
