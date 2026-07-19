<!-- File: docs/notes/adr-009-migration-brief.md -->

# ADR-009 migration brief: sweep parametrized `Setoid/` modules to generalized `𝑆`

This is the execution brief for the migration mandated by ADR-009 (`docs/adr/009-signature-genericity-generalized-variables.md`): convert the generic `Setoid/` core from signature-*parametrized modules* (`module M {𝑆 : Signature 𝓞 𝓥} where`) to *generalized-variable* form (`module M where`, with `𝑆` a generalized `variable`).  It is written to be executed in a **fresh session** pointed at the tracking issue; it depends on no prior conversation.  Read ADR-009 first — it is the *why*; this brief is the *how*.

## Precondition

Do not start until PR #471 (WP-4, `FLRP.Enforceable`) has merged.  A tree-wide change rebased under an open code PR is painful, and #471 is the last one in flight.  Once it is on `master`, its new modules (`FLRP.Enforceable`, `Classical.Structures.Group.Product`) are also in scope for whichever style they use — fold them in.

## Scope (measured on `master`, 2026-07-19)

+  **35 parametrized `Setoid/` modules** to convert, every one with *exactly* the binder `{𝑆 : Signature 𝓞 𝓥}` and no other module parameter — so the header edit is perfectly uniform.  Distribution: Algebras 2, Categories 1, Congruences 6, Congruences/Finite 2, Homomorphisms 2, Subalgebras 5, Subalgebras/Subdirect 4, Terms 4, Varieties 9.
+  **127 application sites** `open import Setoid.X {𝑆 = 𝑆}` across **42 files** that must have the `{𝑆 = 𝑆}` dropped when their target converts.  Roughly 75 are generic (`{𝑆 = 𝑆}`, purely mechanical) and **52 are concrete-signature** (`{𝑆 = Sig-Group}`, `{𝑆 = Sig-Lattice}`, …) in the `Classical/` and `Examples/` layers — the judgment cases (§ 4).
+  44 `Setoid/` modules are already in generalized form, so this *finishes* a migration that is already the majority of the tree — the "drift" ADR-009 records.

## 1. Add the generalized variable (slice S0, do first)

`Overture.Signatures` declares `variable 𝓞 𝓥 : Level` but not `𝑆`.  Add, co-located with `Signature` and the existing level variables, a **public** declaration:

    variable 𝑆 : Signature 𝓞 𝓥

Public, not `private` — mirroring ADR-005's treatment of `𝓞`/`𝓥`, so downstream modules import it by name (`open import Overture using ( 𝓞 ; 𝓥 ; Signature ; 𝑆 )`).  This slice is backward-compatible on its own: adding a variable breaks nothing, existing `{𝑆}` module parameters keep working, so S0 can merge before any conversion.  Update the `docs/STYLE_GUIDE.md` "`𝓞`/`𝓥` convention" section to cover `𝑆` in the same breath (or defer to the final slice — your call, but do it once).

## 2. The mechanical transformation (per module)

For each parametrized `Setoid/` module `M`:

+  **Header**: `module M {𝑆 : Signature 𝓞 𝓥} where` → `module M where`.  Nothing else on that line changes (no module has extra parameters — verified).
+  **Bring `𝑆` into scope**: ensure the module's `open import Overture using ( … )` list includes `𝑆` (add it next to `𝓞 ; 𝓥 ; Signature`).  If the module did not import those names, it relied on the module parameter; add the import.
+  **Body**: usually unchanged — `𝑆` now generalizes per definition exactly as `α`/`ρ` already do.  A definition whose `𝑆` is genuinely uninferable (a signature-dependent construction with no signature-carrying argument) takes `{𝑆}` explicitly at that definition; this is rare and is *not* a reason to keep the module parametrized.

For each **importer** of a converted module (the 127 sites):

+  `open import Setoid.X {𝑆 = 𝑆} using ( … )` → `open import Setoid.X using ( … )` — drop only the `{𝑆 = 𝑆}`, preserve the `using`/`renaming`/`public`/`as` tail.  Barrels: `open import Setoid.X {𝑆 = 𝑆} public` → `open import Setoid.X public`.
+  A `{𝑆 = 𝑆}` application to a module that is *not* being converted in this slice stays untouched until that module's slice.  Each application line points at exactly one module, so no two slices edit the same line; files overlap across slices but lines do not.

## 3. Barrels

A barrel and the submodules it re-exports must end up in one style (ADR-009's no-mixing rule — the source of every `ModuleArityMismatch` we hit).  After conversion every `Setoid/` barrel re-exports with bare `open import Sub public`; confirm no `{𝑆 = 𝑆}` survives on any `Setoid/` re-export line.

## 4. The judgment part: concrete-signature applications in `Classical/` and `Examples/`

The ~52 sites of the form `open import Setoid.Algebras {𝑆 = Sig-Group}` (and `Sig-Magma`, `Sig-Lattice`, `Sig-Monoid`, `Sig-Ring`) exist so a `Classical/` or `Examples/` module can work over one fixed signature with unqualified names (`Algebra`, `Con`, …) defaulting to it.  When the target `Setoid` module generalizes, the application is rejected (`ModuleArityMismatch`), so it must go — but dropping it means `𝑆` is no longer pinned for that scope.  Resolution, in order of preference:

+  **Let inference resolve it.**  Most uses have a concrete algebra/structure over `Sig-Foo` in hand, from which `𝑆` is inferred; dropping the application then just works.  Try this first and lean on `make check`.
+  **Supply `{Sig-Foo}` at the rare type-level use** that has no inferable `𝑆` (e.g. a bare `Con` in a signature).  Local, explicit, minimal.
+  **Keep the fix-once ergonomics deliberately, at the Classical layer** — ADR-009 explicitly permits `Classical/` modules to fix a signature.  If a module is genuinely about one signature throughout and inference makes it noisy, wrap the signature-fixing in that module rather than reintroducing a parameter on the generic `Setoid` module.  Prefer the first two options; use this only where it earns its keep.

These 52 sites cluster on `Setoid.Algebras`/`Setoid.Algebras.Basic`, so most of the judgment work lands in the Algebras slice (S1); later slices are lighter and more mechanical.

## 5. Slicing plan (sequential, one session)

Do S0 first (independently mergeable), then convert in forward-dependency order so each slice's importer-fixes land with the header change that necessitates them.  Each slice = {convert that subtree's module headers} + {drop `{𝑆 = 𝑆}` at every tree-wide importer of those modules} + {handle any concrete-sig sites per § 4} + {`make check` green}.  Run sequentially, each rebased on the prior (line-disjoint, so no self-conflicts).

+  **S0** — `Overture.Signatures`: add `variable 𝑆`.  (Mergeable alone.)
+  **S1** — `Setoid/Algebras` (2 modules).  The heavy slice: carries most of the § 4 concrete-signature judgment cases.
+  **S2** — `Setoid/Terms` (4).
+  **S3** — `Setoid/Homomorphisms` (2) + `Setoid/Categories` (1).
+  **S4** — `Setoid/Congruences` (6) + `Setoid/Congruences/Finite` (2).
+  **S5** — `Setoid/Subalgebras` (5) + `Setoid/Subalgebras/Subdirect` (4).
+  **S6** — `Setoid/Varieties` (9).
+  **S7** — `docs/STYLE_GUIDE.md` convention update (if not folded into S0) + the final verification greps (§ 7).

One atomic PR is an acceptable alternative if the executing session prefers a single `make check` gate over incremental checkpoints; the slices above are the recommended default because they localize any breakage and keep each diff reviewable.

## 6. Validation protocol (per slice — hardened this session, non-negotiable)

Local `make check` has twice passed on stale interfaces and then failed CI.  For every slice:

+  Purge the affected interface cone: delete the `.agdai` under `_build` for the subtree(s) touched (and their importers) before checking.
+  Type-check the deepest affected modules under the CI heap cap, confirming the `Checking <module>` line actually appears (proof of genuine re-elaboration, not a cache hit): `nix develop --command agda +RTS -M6G -A128M -RTS <path>`.
+  Finish with `nix develop --command make check` → exit 0, only pre-existing `Legacy/` deprecation warnings acceptable.

## 7. Done-ness verification (run at the end)

+  `git grep -lE '^module Setoid[^ ]* +\{ *𝑆 +:' -- 'src/Setoid/**/*.lagda.md'` → **empty** (no parametrized `Setoid` module remains).
+  `git grep -nE 'import +Setoid[A-Za-z.]* +\{ *𝑆 *=' -- 'src/**/*.lagda.md'` → **empty** (no application of `𝑆` to any `Setoid` module remains, generic or concrete).
+  `make check` exit 0 from a clean `_build`.
+  `docs/STYLE_GUIDE.md` states the convention (generic `Setoid/` core generalizes `𝑆`; `Classical/` may fix it selectively).

## 8. Delivery conventions

Commit messages: imperative summary, body noting the ADR-009 mandate and the two mechanical patterns, and EXACTLY these trailers:

    Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>
    Claude-Session: <the executing session's URL>

Push each slice to its own branch; do **not** force-push; on a non-fast-forward, `git fetch && git rebase` and re-`make check` if the rebase touched anything.  Open one PR per slice (or one for the atomic variant), referencing the tracking issue and ADR-009.  Do not merge without maintainer confirmation.

## Anticipated gotchas

+  A converted module whose body used the parameter `𝑆` inside a *nested* `module _` or a `where` block: generalization still applies, but double-check the nested scope still sees `𝑆`.
+  Qualified imports `import Setoid.X as Y` followed by `Y.foo {𝑆 = 𝑆}` at *use* sites (not just the import line): the application moves to the use site; grep for `{𝑆 = 𝑆}` broadly, not only on `import` lines.
+  `Examples/` modules over concrete signatures are the same judgment case as `Classical/` (§ 4) — treat them identically.
+  If a specific module resists clean conversion, **flag it and leave it parametrized rather than forcing it** — ADR-009's core/Classical split is a guideline; a genuinely signature-fixed generic module is a finding worth reporting, not a failure.
