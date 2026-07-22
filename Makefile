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
#   make site         Build the MkDocs documentation site (in ./site/).
#   make serve        Preview the docs site locally (http://127.0.0.1:8000).
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

.PHONY: default all check test clean site serve serve-full html agda-md site-full profile project-plan unused-imports unused-imports-test flrp-test Everything.agda

# -- Configuration -----------------------------------------------------------
SRCDIR    := src
AGDA      ?= agda
RTS_OPTS  := +RTS -M6G -A128M -RTS
AGDA_OPTS ?=
REPO      ?= ualib/agda-algebras

# -- Targets -----------------------------------------------------------------

default: Everything.agda

# The canonical library aggregator.  Excludes Legacy/.  Feeds HTML rendering
# and is the natural entry point for downstream consumers.
Everything.agda:
	@echo "target: $@"
	@{ \
	  echo "{-# OPTIONS --cubical-compatible --safe #-}"; \
	  echo ""; \
	  echo "module Everything where"; \
	  echo ""; \
	  find $(SRCDIR) \
	      \( -name '*.lagda.md' -o -name '*.agda' \) \
	      ! -name 'Everything.agda' \
	      ! -name 'EverythingLegacy.agda' \
	      ! -path '$(SRCDIR)/Legacy/*' \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.lagda\.md$$||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	} > $(SRCDIR)/Everything.agda
	@echo "  wrote $(SRCDIR)/Everything.agda ($$(grep -c '^import' $(SRCDIR)/Everything.agda) modules)"

# CI gate over the frozen Legacy/ tree.  Not part of the canonical library;
# not rendered to HTML.  Exists so that make check catches any breakage in
# Legacy/Base/* introduced by changes to its dependencies (most importantly,
# Setoid/* modules whose definitions Legacy.Base depends on transitively).
# See docs/adr/001-setoid-as-canonical.md and src/Legacy/Base/DEPRECATED.md.
EverythingLegacy.agda:
	@echo "target: $@"
	@{ \
	  echo "{-# OPTIONS --cubical-compatible --safe #-}"; \
	  echo ""; \
	  echo "-- This file exists to gate CI on the Legacy/ tree."; \
	  echo "-- It is NOT part of the canonical library and is NOT rendered to HTML."; \
	  echo "-- See docs/adr/001-setoid-as-canonical.md and src/Legacy/Base/DEPRECATED.md."; \
	  echo ""; \
	  echo "module EverythingLegacy where"; \
	  echo ""; \
	  find $(SRCDIR)/Legacy \
	      \( -name '*.lagda.md' -o -name '*.agda' \) \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.lagda\.md$$||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	} > $(SRCDIR)/EverythingLegacy.agda
	@echo "  wrote $(SRCDIR)/EverythingLegacy.agda ($$(grep -c '^import' $(SRCDIR)/EverythingLegacy.agda) modules)"

check test: Everything.agda EverythingLegacy.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/Everything.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/EverythingLegacy.agda

# Build the documentation site (ADR-007).  MkDocs reads the `.lagda.md`
# sources directly via scripts/python/mkdocs_gen_library.py.  Output goes to
# ./site (gitignored).  Run inside `nix develop` so mkdocs and the Material
# theme + plugins pinned in flake.nix are on PATH.
#
#   make site        Fast build: code blocks are plain monospace unless
#                    `make agda-md` has already produced highlighted output.
#   make agda-md     agda --html --html-highlight=code -> .agda-html/md
#                    (highlighted, hyperlinked code blocks for the site, #3a).
#   make html        Classic clickable HTML (agda-categories style) -> ./html,
#                    Everything.html as index; also published at /classic/ (#1).
#   make site-full   html + agda-md + site: the fully-featured published site
#                    (what CI builds and deploys).
MKDOCS    ?= mkdocs
AGDA_HTML := .agda-html

site:
	@echo "target: $@"
	@test -d $(AGDA_HTML)/md || echo "  note: code blocks will be PLAIN — run 'make site-full' for agda --html highlighting + /classic/."
	$(MKDOCS) build --strict --clean

# Live-reloading local preview at http://127.0.0.1:8000 (Ctrl-C to stop).
# Plain code blocks unless the agda --html output already exists; use
# `make serve-full` for the fully-rendered preview (highlighting + /classic/).
serve:
	@echo "target: $@"
	@test -d $(AGDA_HTML)/md && test -d html || echo "  note: code blocks PLAIN and /classic/ absent — run 'make serve-full' for the full preview."
	$(MKDOCS) serve

# Full local preview: build the agda --html outputs first, then live-serve.
serve-full:
	@echo "target: $@"
	$(MAKE) html
	$(MAKE) agda-md
	$(MKDOCS) serve

# Classic agda --html site: full-page HTML with token highlighting + per-token
# hyperlinks, Everything.html as the index.  Standalone in ./html (gitignored);
# gen-files also publishes it at /classic/ and points the highlighted code's
# stdlib links there.  Type-checks (warm .agdai cache makes it quick).
html: Everything.agda EverythingLegacy.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-dir=html $(SRCDIR)/Everything.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-dir=html $(SRCDIR)/EverythingLegacy.agda

# Highlighted Markdown for embedding in the MkDocs pages (#3a).
agda-md: Everything.agda EverythingLegacy.agda
	@echo "target: $@"
	rm -rf $(AGDA_HTML)/md
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-highlight=code --html-dir=$(AGDA_HTML)/md $(SRCDIR)/Everything.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-highlight=code --html-dir=$(AGDA_HTML)/md $(SRCDIR)/EverythingLegacy.agda

# The fully-featured published site.  Recursive make keeps the steps ordered
# even under `make -j`.
site-full:
	@echo "target: $@"
	$(MAKE) html
	$(MAKE) agda-md
	$(MAKE) site

profile: Everything.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) -v profile:7 -v profile.definitions:15 $(SRCDIR)/Everything.agda

clean:
	@echo "target: $@"
	find . -name '*.agdai' -delete
	rm -f $(SRCDIR)/Everything.agda $(SRCDIR)/EverythingLegacy.agda
	rm -rf site html .agda-html .cache

# Regenerate the issue listings in docs/GITHUB_PROJECT.md from current
# GitHub state.  Hand-edited prose outside the BEGIN/END GENERATED markers
# is preserved verbatim.  Requires the `gh` CLI authenticated against $(REPO).
project-plan:
	@echo "target: $@"
	python3 scripts/python/gh_project_render.py docs/GITHUB_PROJECT.md --repo $(REPO)

# Report import/open statements that bring in names the module never uses.
# Scans $(SRCDIR) (skipping the frozen Legacy tree); exits non-zero when
# anything is flagged, so it can gate CI.  Run `make unused-imports-test` to
# exercise the analyzer's own test suite.
unused-imports:
	@echo "target: $@"
	python3 scripts/python/unused_imports.py $(SRCDIR)

unused-imports-test:
	@echo "target: $@"
	python3 scripts/python/test_unused_imports.py

# Test the FLRP certificate emitter (scripts/python/flrp/): engine unit tests, a
# Python mirror of the Agda checker's obligations as a regression tripwire,
# and golden round-trip tests re-emitting the committed pilot byte for byte.
# The Agda side needs no separate harness: the emitted pilot module is part
# of the library, so `make check` is the end-to-end verification.
# Also tests the search side (eqsearch.py): partition kernel against brute
# force, the L7 session census (issue #484), and the search-to-certificate
# loop; set FLRP_EQSEARCH_SLOW=1 to include the Eq(7) sweep (~5 minutes).
flrp-test:
	@echo "target: $@"
	python3 scripts/python/flrp/test_flrp.py
	python3 scripts/python/flrp/test_eqsearch.py
