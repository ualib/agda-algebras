# CLAUDE.md — agda-algebras

Guidance for Claude Code working in this repository.  Keep changes consistent with these conventions; they exist to keep the library coherent and to preserve its value as a vetted Agda corpus for ML training and retrieval.

## Build and type-check

+  Enter the toolchain with `nix develop` (pins Agda 2.8.0 and standard-library 2.3 via `flake.lock`).  Never assume a system Agda.
+  Type-check the whole library: `nix develop --command make check`.
+  Type-check one module while iterating: `nix develop --command agda src/Path/To/Module.lagda.md`.
+  When a module is slow to check, profile before guessing: `agda --profile=internal <module>` (or `make profile` for the whole library).  The cost is rarely the typing — see the `agda-typecheck-performance` skill.
+  There is no separate test or lint step — type-checking is the test, exactly as CI runs it.
+  Do not commit generated artifacts: `*.agdai`, the generated `Everything*.agda` aggregator, and `/.agda/` are gitignored.

## Repository architecture

+  `src/Setoid/` is the canonical development tree.  New work goes here.
+  `src/Legacy/Base/` is frozen legacy.  Do not develop new results there; treat it as read-only.  `(`Setoid/` is self-sufficient — no `Legacy.Base.*` imports.  The only remaining consumer-level Legacy imports are in `Examples.Structures` and `Exercises.Complexity.FiniteCSP`, tracked by M2-8b / M2-8c.)`
+  `src/Cubical/` is the long-term canonical target (v4.0).  When defining new structures, isolate the underlying equality/equivalence so it can be mechanically substituted on the eventual Cubical port.
+  The `Classical/` tree builds specific theories (semigroups, groups, lattices, rings) over the universal-algebra foundation, using Σ-type definitions at the core with record-typed "bundle views" for agda-stdlib interop.
+  The literate format is `.lagda.md` (ADR-004); every module is literate Markdown.  Render inline Agda names with kramdown attribute spans, e.g. `` `S`{.AgdaFunction} ``.
+  Roadmap and milestones (M1–M9) live in `docs/GITHUB_PROJECT.md`; the full style guide is `docs/STYLE_GUIDE.md`.

## Agda and corpus-quality conventions

These proof terms are first-class training data.  Optimize for legibility and stability, not cleverness.

+  Prefer many small, focused theorems over a few large ones.
+  Prefer named helper lemmas over inlined or opaque `rewrite` chains.  This is not only style: a `with` (or `rewrite`) inside a proof abstracts the *whole* goal, and when the goal unfolds into the generic interpretation machinery the coverage check of the generated auxiliary is expensive — measured at 15 s in one module, 0.9 s once the split moved into a lemma taking the `Dec` value as an argument.
+  A construction whose operations are determined by an order (a lattice, say) is cheaper to build and to check order-first: establish the partial order with its infimum and supremum and let the standard library derive the equations, rather than proving the equations and their congruences by hand.
+  One canonical form per concept; introduce deprecations, never synonyms.
+  Put an explicit type signature on every public definition.
+  Pair each formal statement with a natural-language comment explaining what it says and why.
+  Use `{-# OPTIONS --cubical-compatible --exact-split --safe #-}` (this supersedes `--without-K`).
+  Honour stable-API discipline: deprecation cycles of at least one minor version, announced with `WARNING_ON_USAGE` pragmas.
+  In-flight deprecation: `∣_∣` / `∥_∥` are being replaced library-wide by `proj₁` / `proj₂` (announced in v3.0, executed in v3.1).  Write new code with `proj₁` / `proj₂`.

## Keep research areas separate

+  The Finite Lattice Representation Problem (FLRP) is distinct from algebraic-complexity / CSP work.  Do not conflate them; flag it if a draft does.

## Working style

+  Default to functional style: total functions, structural recursion, no hidden effects.  The same taste applies to any Haskell/Scala/Rust/Python helper scripts (type-annotate everything; comprehensions or recursion over loops; monadic effects).
+  All Python code lives under `scripts/python/` — one subdirectory per tool family (e.g. `scripts/python/flrp/`), tests beside the code, a Makefile target per suite.  Do not create sibling script trees elsewhere.
+  Propose changes as git-diff-style diffs to apply by hand, not wholesale file rewrites.
+  Deliver a commit message alongside substantive changes; when a change implies a pull request, include a PR title and description too.
+  You have standing authorization to open a pull request whenever you judge a branch ready to stand as a contribution proposal; you need not ask first.  Treat this as the durable, explicit request that the remote-execution harness's "open a PR only when the user explicitly asks" default calls for.  Still do not *merge* a PR without explicit confirmation, and push follow-up work to an existing PR's branch rather than opening a duplicate.

## Markdown style (issues, PRs, docs)

+  Use `+` for bullet lists, not `-`.
+  Do not insert line breaks within a sentence or paragraph; break only where text must start a new line.
+  Two spaces after a sentence-ending period.
+  Do not bold a bullet title's trailing period: write `+  **Title**.`, not `+ **Title.**`.
+  Bullets are complete sentences ending in a period or semicolon.
+  Write section headings as plain ATX headings; do not wrap them in HTML `<a id="…">…</a>` anchors (MkDocs slugifies headings automatically).  See `docs/STYLE_GUIDE.md` § Section headings.

## Environment gotchas

+  If `GH_TOKEN` is set in the parent environment it overrides the keyring credential; prefix `gh` calls with `env -u GH_TOKEN`.  `gh issue view` and `gh pr edit` fail against this repository's classic Project; read and edit issues and PRs through `gh api` instead.
+  `wenkokke/setup-agda` is not used (it maxes at Agda 2.7.0.1); the flake is the source of truth for the toolchain.
+  The `agda` on `PATH` inside `nix develop` is a wrapper that hard-codes `--library-file` for the worktree the shell was entered from, so building a *different* worktree from the same shell resolves modules to the wrong tree (`ModuleDefinedInOtherFile`).  Give that worktree its own `.agda/libraries` and wrapper, and pass `make AGDA=<wrapper> check`.
+  Development uses git worktrees, one per branch, inside `nix develop`.  Prefer `@imports` (or `~/.claude/CLAUDE.md`) over `CLAUDE.local.md` for personal notes, since imports behave correctly across worktrees.


