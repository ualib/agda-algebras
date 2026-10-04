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
#   make                     Regenerate the aggregators from the current tree.
#   make check               Type-check the library and the Legacy tree.
#   make test                Alias for `make check`.
#   make site                Build the MkDocs documentation site (in ./site/).
#   make serve               Preview the docs site locally (http://127.0.0.1:8000).
#   make profile             Type-check with Agda profiling enabled.
#   make clean               Remove .agdai artifacts and the generated aggregators.
#
# The two aggregators:
#   +  Everything.agda              the canonical library.
#   +  EverythingLegacy.agda        the frozen Legacy/ tree.
#
# Notes:
#   +  The aggregators are PHONY targets — always regenerated — so that
#      adding or removing a module is picked up without the user having
#      to remember.
#   +  We use `find` rather than `git ls-tree` so that untracked-but-present
#      files in the working tree are included.  This matters during active
#      development.
#   +  The sed pipeline strips ONLY the trailing `.agda` extension
#      (anchored with `$` and an escaped `\.`), avoiding a class of bugs
#      where a path segment happens to contain the substring `agda`.
# =============================================================================

.PHONY: default all check test clean site serve serve-full html agda-md site-full profile project-plan unused-imports unused-imports-test check-links check-links-test gen-links corpus-stats corpus-stats-check corpus-stats-test docstrings docstrings-test docstrings-list docstrings-unused docstrings-json groups-test playground playground-check playground-test Everything.agda EverythingLegacy.agda

# -- Configuration -----------------------------------------------------------
SRCDIR    := src
AGDA      ?= agda
RTS_OPTS  := +RTS -M6G -A128M -RTS
AGDA_OPTS ?=
REPO      ?= ualib/agda-algebras

# The docstring-coverage ratchet (issue #268).  `make docstrings` fails only
# when the number of public definitions lacking a prose block exceeds this
# ceiling, so the backlog can only shrink while the per-subtree prose PRs land.
# Lower it whenever a PR clears definitions; never raise it.
DOCSTRING_MAX_GAPS ?= 7
# The other half of the bar ADR-010 states: modules whose header is only the
# boilerplate sentence.  Ratcheted the same way; never raise it.
DOCSTRING_MAX_WEAK_HEADERS ?= 0

# -- Targets -----------------------------------------------------------------

# Bare `make` refreshes both aggregators, so that adding or removing a module
# anywhere is picked up in one command.
default: Everything.agda EverythingLegacy.agda

# On the OPTIONS pragma the two aggregators emit: `--exact-split` is
# deliberately absent.  It constrains *definitions* (it requires a definition's
# clauses to hold as definitional equalities), and an aggregator contains
# nothing but imports, so the flag has nothing to check here.  It is neither
# infective nor coinfective, so omitting it does not weaken the modules being
# imported: each library module carries `--exact-split` in its own header and is
# checked under it.  Both aggregators therefore share one pragma.

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
#   make site-full   html + agda-md + playground + site: the fully-featured
#                    published site (what CI builds and deploys).
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
	$(MAKE) playground
	$(MAKE) site

# Profile a whole-library type-check.  Agda accepts one profiling mode at a time,
# so override PROFILE to choose:
#   internal     phases (Coverage, Serialization, InterfaceInstantiateFull, ...)
#                — the one that says *what to fix*; the cost is rarely the typing
#   modules      per-module ranking — says *which module* to look at
#   definitions  per-definition attribution (its `Miscellaneous` line absorbs
#                everything not attributable to a definition, and is often the
#                largest)
# Measure from an empty build (`make clean`), or only stale modules are timed.
# (The pre-2.8 spelling `-v profile:7 -v profile.definitions:15` prints nothing.)
PROFILE ?= modules

profile: Everything.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) --profile=$(PROFILE) $(SRCDIR)/Everything.agda

clean:
	@echo "target: $@"
	find . -name '*.agdai' -delete
	rm -f $(SRCDIR)/Everything.agda $(SRCDIR)/EverythingLegacy.agda
	rm -rf site html .agda-html .cache .playground

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

# Guard the site's reference-style cross-links (ADR-007), the recurring
# broken-link failure mode: undefined `[label][]` references render as literal
# text and slip past `mkdocs build --strict`.  Two pure-Python checks, no Agda or
# MkDocs needed, so CI runs them cheaply and they point at the offending source:
#   1. gen_links.py --check — docs/_links.md's generated module + ADR sections
#      are exactly what the src/ and docs/adr/ trees imply (no hand-drift);
#   2. check_links.py — every reference used in the rendered corpus resolves.
# Run `make gen-links` to regenerate _links.md after adding a module or an ADR.
check-links:
	@echo "target: $@"
	python3 scripts/python/gen_links.py --check
	python3 scripts/python/check_links.py

check-links-test:
	@echo "target: $@"
	python3 scripts/python/test_check_links.py

gen-links:
	@echo "target: $@"
	python3 scripts/python/gen_links.py

# The landing page's headline figures (issue #575).  docs/index.md advertises a
# module count, a line count, a machine-checked share, and the pinned toolchain;
# every one is a fact about this repository, so scripts/python/corpus_stats.py
# counts them (from src/ minus Legacy/, and from the toolchain pins) and writes
# them into the page's `ualib:stat` markers.  The MkDocs hook substitutes the
# same values at build time, but it rewrites only the *rendered* page: before
# this gate, nothing refreshed the committed values, which are the ones GitHub
# renders, and they sat at July's numbers for six weeks while the library grew
# 12.7%.  The check is therefore the point: a PR that moves a number cannot
# merge without refreshing the page.
#   corpus-stats        refresh docs/index.md from the tree
#   corpus-stats-check  fail (with a diff) if a committed value has drifted
#   corpus-stats-test   the tool's own test suite
corpus-stats:
	@echo "target: $@"
	python3 scripts/python/corpus_stats.py

corpus-stats-check:
	@echo "target: $@"
	python3 scripts/python/corpus_stats.py --check

corpus-stats-test:
	@echo "target: $@"
	python3 scripts/python/test_corpus_stats.py

# Audit the prose block attached to every public definition (STYLE_GUIDE
# § "Every public definition has a prose comment block", issue #268, ADR-010).
# A grep cannot do this: the corpus documents definitions in Markdown *outside*
# the ```agda fences, so the check has to parse literate structure and Agda's
# layout rule.  The report's last two columns are advisory rather than gated --
# `named` is the share of definitions their own prose mentions by name, `used`
# the share referenced anywhere in the live trees (which is where documentation
# effort pays off, not a dead-code measure: a terminal theorem is correctly
# unreferenced).
#   docstrings         the CI gate; holds both halves of the bar ADR-010 states,
#                      at DOCSTRING_MAX_GAPS and DOCSTRING_MAX_WEAK_HEADERS
#   docstrings-list    name every definition missing a prose block
#   docstrings-unused  name every definition nothing references
#   docstrings-json    harvest (qname, prose, used) records for the training
#                      corpus (issue #275)
#   docstrings-test    the analyzer's own test suite
docstrings:
	@echo "target: $@"
	python3 scripts/python/docstring_audit.py --modules --max-gaps $(DOCSTRING_MAX_GAPS) \
	  --max-weak-headers $(DOCSTRING_MAX_WEAK_HEADERS) $(SRCDIR)

docstrings-list:
	@echo "target: $@"
	python3 scripts/python/docstring_audit.py --list --exit-zero $(SRCDIR)

docstrings-unused:
	@echo "target: $@"
	python3 scripts/python/docstring_audit.py --unused --exit-zero $(SRCDIR)

docstrings-json:
	@echo "target: $@"
	python3 scripts/python/docstring_audit.py --json $(SRCDIR)

docstrings-test:
	@echo "target: $@"
	python3 scripts/python/test_docstring_audit.py

# Test the generator of the certified A5 tables (scripts/python/groups/): the
# group construction, an engine-side replay of the certificate, and a golden test
# that re-emits the committed
# src/Examples/Classical/Groups/AlternatingGroup5/Tables.lagda.md byte for byte.
# The Agda side needs no separate harness: the tables module is part of the
# library, so `make check` replays every claim in it.
groups-test:
	@echo "target: $@"
	python3 scripts/python/groups/test_a5_simple_cert.py

# The playground (ADR-011, docs/playground.md): Agda 2.8.0 compiled to
# WebAssembly, run in the reader's browser on exercises from this library.
#   playground        build the checker and the filesystem images into
#                     $(PLAYGROUND_OUT) (gitignored), where the site build
#                     publishes them from.  The library's closures are
#                     type-checked by the native Agda the flake pins, then every
#                     exercise is checked under the shipped WebAssembly, and the
#                     build fails unless each check type-checks exactly one
#                     module: the images' interfaces were accepted.  About a
#                     minute, most of it the WebAssembly proving the largest
#                     image.  PLAYGROUND_FLAGS=--allow-dirty builds with
#                     uncommitted library or exercise files, and the manifest
#                     then says so.
#   playground-check  the built assets are what their manifest says, offline
#   playground-test   the builder's and the hook's tests, and the page's
#                     JavaScript under node (the tar reader, the WASI host, the
#                     protocol, the edits, the session plan, the painter)
# The three inputs come from the flake on first use, so nothing here costs a
# fetch unless these targets run.
PLAYGROUND_OUT   ?= .playground
PLAYGROUND_FLAGS ?=
PLAYGROUND_DIST  ?= $(shell nix build --no-link --print-out-paths .\#agda-wasm-dist)
PLAYGROUND_STDLIB ?= $(shell nix build --no-link --print-out-paths .\#standard-library)
WASMTIME         ?= $(shell nix build --no-link --print-out-paths .\#wasmtime)/bin/wasmtime

playground:
	@echo "target: $@"
	python3 scripts/python/playground/build_assets.py --out $(PLAYGROUND_OUT) \
	  --dist "$(PLAYGROUND_DIST)" --stdlib "$(PLAYGROUND_STDLIB)" \
	  --wasmtime "$(WASMTIME)" --agda "$(AGDA)" $(PLAYGROUND_FLAGS)

playground-check:
	@echo "target: $@"
	python3 scripts/python/playground/build_assets.py --check --out $(PLAYGROUND_OUT)

playground-test:
	@echo "target: $@"
	python3 scripts/python/playground/test_build_assets.py
	python3 scripts/python/playground/test_mkdocs_hook.py
	@command -v node >/dev/null || { echo "error: node is required for the JavaScript tests"; exit 1; }
	node scripts/js/playground/test_tar.mjs
	node scripts/js/playground/test_wasi.mjs
	node scripts/js/playground/test_protocol.mjs
	node scripts/js/playground/test_edits.mjs
	node scripts/js/playground/test_session.mjs
	node scripts/js/playground/test_paint.mjs
	node scripts/js/playground/test_input.mjs
