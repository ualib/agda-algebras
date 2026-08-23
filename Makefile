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
#   make check-certificates  Type-check the small-lattice certificate census.
#   make check-all           Both of the above — everything under src/.
#   make test                Alias for `make check`.
#   make site                Build the MkDocs documentation site (in ./site/).
#   make serve               Preview the docs site locally (http://127.0.0.1:8000).
#   make profile             Type-check with Agda profiling enabled.
#   make clean               Remove .agdai artifacts and the generated aggregators.
#
# The three tiers (issue #515):
#   +  Everything.agda              the canonical library.
#   +  EverythingLegacy.agda        the frozen Legacy/ tree.
#   +  EverythingCertificates.agda  the small-lattice representation
#      certificates of `src/FLRP/Certificates/SmallLatticeReps/` — generated
#      artifacts specific to the FLRP research track and the fin-lat-rep
#      manuscript, which cost 44% of a clean full type-check (175 s of 395 s,
#      measured with `agda --profile=modules`).  No module imports them, so
#      they are checked by their own aggregator and their own CI job rather
#      than on every `make check`.  `make check-all` is the whole tree.
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

.PHONY: default all check check-certificates check-all test clean site serve serve-full html agda-md site-full profile project-plan unused-imports unused-imports-test check-links check-links-test gen-links docstrings docstrings-test docstrings-list docstrings-unused docstrings-json flrp-test flrp-slr gap-smoke Everything.agda EverythingLegacy.agda EverythingCertificates.agda

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
DOCSTRING_MAX_GAPS ?= 201
# The other half of the bar ADR-010 states: modules whose header is only the
# boilerplate sentence.  Ratcheted the same way; never raise it.
DOCSTRING_MAX_WEAK_HEADERS ?= 50

# The certificate census: generated representation certificates for the FLRP
# research track (issue #515).  Excluded from Everything.agda and checked by
# EverythingCertificates.agda instead.
CERTDIR   := $(SRCDIR)/FLRP/Certificates/SmallLatticeReps

# -- Targets -----------------------------------------------------------------

# Bare `make` refreshes every tier's index, so that adding or removing a module
# anywhere is picked up in one command.  The individual check targets depend on
# just the aggregators they need.
default: Everything.agda EverythingLegacy.agda EverythingCertificates.agda

# On the OPTIONS pragma the three aggregators emit: `--exact-split` is
# deliberately absent.  It constrains *definitions* (it requires a definition's
# clauses to hold as definitional equalities), and an aggregator contains
# nothing but imports, so the flag has nothing to check here.  It is neither
# infective nor coinfective, so omitting it does not weaken the modules being
# imported: each library module carries `--exact-split` in its own header and is
# checked under it.  All three aggregators therefore share one pragma.

# The canonical library aggregator.  Excludes Legacy/ and the certificate
# census (see the tier note in the header).  Feeds HTML rendering and is the
# natural entry point for downstream consumers.
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
	      ! -name 'EverythingCertificates.agda' \
	      ! -path '$(SRCDIR)/Legacy/*' \
	      ! -path '$(CERTDIR)/*' \
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

# CI gate over the certificate census.  These are generated representation
# certificates for the FLRP research track and the fin-lat-rep manuscript: no
# module imports them, they are 44% of a clean full type-check, and they grow
# with the census (issues #483, #485).  They are checked by their own target and
# their own CI job so that `make check` stays fast for everyone else, and they
# are still rendered to HTML so the published site keeps their pages.
# See issue #515.
EverythingCertificates.agda:
	@echo "target: $@"
	@{ \
	  echo "{-# OPTIONS --cubical-compatible --safe #-}"; \
	  echo ""; \
	  echo "-- This file exists to gate CI on the small-lattice certificate census."; \
	  echo "-- It is NOT part of the canonical library aggregator; see issue #515."; \
	  echo ""; \
	  echo "module EverythingCertificates where"; \
	  echo ""; \
	  find $(CERTDIR) \
	      \( -name '*.lagda.md' -o -name '*.agda' \) \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.lagda\.md$$||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	} > $(SRCDIR)/EverythingCertificates.agda
	@echo "  wrote $(SRCDIR)/EverythingCertificates.agda ($$(grep -c '^import' $(SRCDIR)/EverythingCertificates.agda) modules)"

check test: Everything.agda EverythingLegacy.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/Everything.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/EverythingLegacy.agda

# The certificate tier on its own (what the dedicated CI job runs).
check-certificates: EverythingCertificates.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/EverythingCertificates.agda

# Everything under src/, in one command.  Use this before a release, and when
# touching anything the certificates depend on (the checkers of
# `Setoid.Congruences.Certificates` and `FLRP.Certificates`).
check-all:
	@echo "target: $@"
	$(MAKE) check
	$(MAKE) check-certificates

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
# All three tiers are rendered: the published site must keep every page it has
# today, certificates included, even though they are not in the library
# aggregator (issue #515).
html: Everything.agda EverythingLegacy.agda EverythingCertificates.agda
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-dir=html $(SRCDIR)/Everything.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-dir=html $(SRCDIR)/EverythingLegacy.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-dir=html $(SRCDIR)/EverythingCertificates.agda

# Highlighted Markdown for embedding in the MkDocs pages (#3a).
agda-md: Everything.agda EverythingLegacy.agda EverythingCertificates.agda
	@echo "target: $@"
	rm -rf $(AGDA_HTML)/md
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-highlight=code --html-dir=$(AGDA_HTML)/md $(SRCDIR)/Everything.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-highlight=code --html-dir=$(AGDA_HTML)/md $(SRCDIR)/EverythingLegacy.agda
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-highlight=code --html-dir=$(AGDA_HTML)/md $(SRCDIR)/EverythingCertificates.agda

# The fully-featured published site.  Recursive make keeps the steps ordered
# even under `make -j`.
site-full:
	@echo "target: $@"
	$(MAKE) html
	$(MAKE) agda-md
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
	rm -f $(SRCDIR)/Everything.agda $(SRCDIR)/EverythingLegacy.agda \
	      $(SRCDIR)/EverythingCertificates.agda
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

# Audit the prose block attached to every public definition (STYLE_GUIDE
# § "Every public definition has a prose comment block", issue #268, ADR-010).
# A grep cannot do this: the corpus documents definitions in Markdown *outside*
# the ```agda fences, so the check has to parse literate structure and Agda's
# layout rule.  The report's last two columns are advisory rather than gated --
# `named` is the share of definitions their own prose mentions by name, `used`
# the share referenced anywhere in the live trees (which is where documentation
# effort pays off, not a dead-code measure: a terminal theorem is correctly
# unreferenced).
#   docstrings         the CI gate; holds the line at DOCSTRING_MAX_GAPS
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

# Test the FLRP certificate emitter (scripts/python/flrp/): engine unit tests, a
# Python mirror of the Agda checker's obligations as a regression tripwire,
# and golden round-trip tests re-emitting the committed pilot byte for byte.
# The Agda side needs no separate harness: the emitted pilot module is part
# of the library, so `make check` is the end-to-end verification.
# Also tests the search side (eqsearch.py): partition kernel against brute
# force, the L7 session census (issue #484), and the search-to-certificate
# loop; set FLRP_EQSEARCH_SLOW=1 to include the Eq(7) sweep (~5 minutes).
# The numpy backend's tests (eqfast.py: table/report parity with the pure
# engine, the Eq(7) census, and — behind the same slow flag — the Eq(8)
# sweep against the committed report) skip cleanly when numpy is absent;
# the nix dev shell ships numpy (flake.nix), so under `nix develop` they run.
flrp-test:
	@echo "target: $@"
	python3 scripts/python/flrp/test_flrp.py
	python3 scripts/python/flrp/test_eqsearch.py
	python3 scripts/python/flrp/test_slr_catalog.py
	python3 scripts/python/flrp/test_eqfast.py
	python3 scripts/python/flrp/test_gap_interval.py

# Regenerate the SmallLatticeReps catalog artifacts (issue #485) from the
# manuscript source: claim files under scripts/python/flrp/inputs/slr/, audit
# JSONs under scripts/python/flrp/out/slr/, and the certificate modules under
# src/FLRP/Certificates/SmallLatticeReps/.  Deterministic; the committed
# copies must re-derive byte for byte (checked by flrp-test).
flrp-slr:
	@echo "target: $@"
	python3 scripts/python/flrp/slr_catalog.py --write-inputs --emit

# Smoke-test the GAP subgroup-interval engine (scripts/gap/flrp/, issue #487):
# confirm the group libraries it depends on load (SmallGroup(216,153) and
# TransitiveGroup(8,1)) and the JSON/provenance helpers work.  Requires the
# dedicated GAP devshell (`nix develop .#gap`); GAP is an untrusted engine, so
# this is deliberately NOT a dependency of `check` or `flrp-test`, which stay
# GAP-free.  Run from the repo root.
gap-smoke:
	@echo "target: $@"
	gap -A -q -b scripts/gap/flrp/bin/smoke.g
