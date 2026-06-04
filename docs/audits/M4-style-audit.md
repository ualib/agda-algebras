# M4-1 repo-wide style-guide violation audit

This is the audit deliverable for [M4-1d] (issue #370), the scripted sweep of
the live trees for `docs/STYLE_GUIDE.md` violations.  It feeds the M4-1
notation-migration PRs (#367, #368, #372), the M4-1c style-guide reconciliation
(#369), and the M4-2 per-subtree prose PRs (#268 and children).

+  **Scope**.  Live trees only: `Overture/`, `Setoid/`, `Classical/`, `Order/`, `Demos/`, `Examples/`, `Exercises/`.  `src/Legacy/` is frozen and excluded from every sweep below (`--glob '!src/Legacy/**'`).
+  **Baseline**.  Generated against `master` at commit `5c44d15` on 2026-06-04, toolchain Agda 2.8.0 / stdlib 2.3.
+  **Method**.  Each finding lists the exact `rg` command that produces it, so the audit is reproducible and the counts can be re-checked after each migration PR lands.

## Summary

| # | Finding | Raw count | Files | Fixing issue |
|---|---------|-----------|-------|--------------|
| 1a | Bracket projections `∣_∣` / `∥_∥` | `∣` 345, `∥` 132 | 40 / 32 | #367 |
| 1b | Interpretation `_̂_` (combining caret) | 73 | 15 | #368 |
| 1c | Code-fence blank-line-after-opener | 222 | 51 | #372 |
| 2a | Bare `open import` without `using` | aggregators only | — | none (compliant) |
| 2b | Cosmetic `renaming` | 1 dead rename | 1 | #367 |
| 3 | Minimal module headers | heuristic | — | M4-2 (#268) |
| 4 | HTML `<a id=…>` heading anchors | 300 | 111 | M4-2 (#268) |
| 5 | `is-x` predicate / synonym pairs | 0 violations | — | none (clean) |

The raw `∣` and `∥` glyph counts overcount the migration target; the carve-outs
are itemized in § 1a.  Findings 3 and 4 change only prose and rendered HTML, not
compiled code, so they are out of M4-1 scope and tracked under M4-2; they are
inventoried here because #370 asks the audit to enumerate them.

## 1. Notation

### 1a. Bracket projections `∣_∣` / `∥_∥` (#367)

```
rg -n '∣' src --glob '!src/Legacy/**'   # 345 hits / 40 files
rg -n '∥' src --glob '!src/Legacy/**'   # 132 hits / 32 files
```

The migration target is the *bracket projection* `∣_∣` / `∥_∥` defined in
`Overture.Basic` (and the prose that names it), per the STYLE_GUIDE Projections
table, which already marks `∣_∣` "deprecated: replace with `proj₁` in v3.0".  The
glyph `∣` (U+2223 DIVIDES) is overloaded, so the raw count includes false
positives that must **not** be rewritten.

**Carve-outs (legitimate non-projection uses of the glyph; leave untouched).**

+  `_∣≈_` — the compatibility predicate defined in `Setoid.Congruences.Basic` (`𝑨 ∣≈ R`).  18 occurrences across 8 files (`rg -n '∣≈' src --glob '!src/Legacy/**'`): `Setoid/Congruences/{Basic,Lattice,Generation,CompleteLattice}`, `Setoid/Homomorphisms/Kernels`, `Examples/Setoid/FiniteQuotient`, `Examples/FunctionTypeBijections`, `Overture/Relations`.
+  `Setoid/Complexity/CSP.lagda.md` — all 9 `∣` are mathematical prose, not Agda: cardinality `∣ 𝑎𝑠 ∣` and the polymorphism notation `∣: ⃖ R`, `F ⃗ ∣:`.  This file imports no bracket projection.
+  `_|:_` (the compatibility relation) uses ASCII pipe `|` (U+007C), not `∣`, so it never matches the sweep; noted to forestall confusion with `∣≈`.

Because of these carve-outs the acceptance grep proposed on #367 — "`rg '∣'
… matches only the definitions in `Overture.Basic`" — is **aspirational, not
literal**: bare `∣` legitimately survives in `_∣≈_`, in CSP prose, and in
`∥_∥`'s own type.  The operational exit test should instead be:

```
# after #367: no bracket-projection *application* outside the carve-outs
rg -n '∣ [^∣]* ∣' src --glob '!src/Legacy/**' --glob '!src/Setoid/Complexity/CSP.lagda.md'
```

evaluated against the definition site and the `_∣≈_` operator only.  This
refinement is the kind of guide-vs-reality gap #369 exists to reconcile.

**Substitution rules.**

+  Signature components: `∣ 𝑆 ∣` → `OperationSymbolsOf 𝑆`, `∥ 𝑆 ∥ f` → `ArityOf 𝑆 f` (the long forms from `Overture.Signatures`, already canonical in `Classical/`).
+  All other Σ-projections: `∣ e ∣` → `proj₁ e`, `∥ e ∥` → `proj₂ e` (stdlib `Data.Product`).

**Definition and special-case sites (handle individually, not by sed).**

| File | Role | Action |
|------|------|--------|
| `Overture/Basic.lagda.md` | definition site | keep `∣_∣` / `∥_∥`; decouple `∥_∥`'s type from `∣_∣` (`B (proj₁ z)`); add `WARNING_ON_USAGE` to both so `Legacy/` still compiles |
| `Overture/Signatures.lagda.md` | `OperationSymbolsOf` / `ArityOf` | rewrite both to `proj₁` / `proj₂`; drop the `Overture.Basic using (∣_∣ ; ∥_∥)` import; fix the stale `Base.Functions` cross-reference (line 101) and the per-tree prose (lines 102-129) |
| `Setoid/Terms/Basic.lagda.md:161` | `open Setoid … renaming (Carrier to ∣_∣)` | semantic re-use of the bracket glyph for a setoid carrier, **not** a Σ-projection; rename the local alias (e.g. to `Carrier` directly) so the bracket form disappears without changing meaning |
| `Setoid/Homomorphisms/Properties.lagda.md` | dead `renaming (proj₁ to fst ; proj₂ to snd)` | collapse the no-op rename while migrating (see § 2b) |
| `Demos/HSP.lagda.md:126-129` | self-contained local `∣_∣` / `∥_∥` (= `fst` / `snd`) | judgment call — see note below |

**`Demos/HSP.lagda.md` (self-contained).**  HSP is a single-file reproduction of
the Birkhoff HSP theorem and defines its own `∣_∣` / `∥_∥` (lines 126-129) and
`_̂_` (line 378) rather than importing them, so it trips no deprecation warning.
#267 nonetheless lists `Demos/` as a live tree in scope, and the #367/#368
acceptance greps do not exempt it, so the default is to migrate HSP's local
definitions and 61 `∣` / 26 `∥` / 13 `_̂_` call-sites to `proj₁` / `proj₂` /
`_^_`.  Because this rewrites a pedagogical artifact that mirrors a published
paper, it is called out here for an explicit decision before #367/#368 touch it.

**Import sites bringing in `∣_∣` / `∥_∥` (each needs per-file `using`-list surgery).**

`Demos/ContraX`, `Overture/Signatures`, `Overture/Terms`, `Setoid/Algebras/Basic`,
`Setoid/Algebras/Products`, `Setoid/Congruences/Basic`, `Setoid/Congruences/Generation`,
`Setoid/Functions/Inverses`, `Setoid/Homomorphisms/{Basic,Factor,HomomorphicImages,Isomorphisms,Kernels,Noether,Products,Properties}`,
`Setoid/Relations/Quotients`, `Setoid/Subalgebras/{Properties,Subalgebras,Subuniverses}`,
`Setoid/Terms/{Basic,Operations,Properties}`.  Additional modules use the brackets
through re-export or local scope and are swept alongside: `Setoid/Varieties/*`
(`FreeAlgebras`, `HSP`, `Properties`, `Preservation`, `SoundAndComplete`,
`EquationalLogic`), `Setoid/Functions/Surjective`, and the `Examples/Setoid/*`
demos (`FreeMagma`, `Presentation`, `FiniteQuotient`) plus
`Examples/FunctionTypeBijections`.

`Classical/` is already on `OperationSymbolsOf` / `ArityOf` and is clean.

### 1b. Interpretation `_̂_` → `_^_` (#368)

```
rg -n '̂' src --glob '!src/Legacy/**'    # 73 hits / 15 files
```

Every hit is a genuine `_̂_` operator use (no false positives — the combining
caret U+0302 is not otherwise used in the live trees).  The migration is **far
more partial than #368's prose suggests**: it is not just one Congruences module
but 14 files that still import or apply `_̂_`.

+  **Keep**: `Setoid/Algebras/Basic.lagda.md` — the `_̂_` definition plus its existing v3.0 `WARNING_ON_USAGE` and the `_^_` ASCII synonym.  This is the only `̂` the exit grep should match.
+  **Already migrated**: `Setoid/Algebras/Products.lagda.md` is on `_^_`.
+  **Migrate import + call-sites** (`f ̂ 𝑨` → `f ^ 𝑨`): `Setoid/Congruences/Basic`, `Setoid/Subalgebras/Subuniverses` (14 — the heaviest), `Setoid/Terms/{Basic,Operations,Properties}`, `Setoid/Homomorphisms/{Basic,Factor,HomomorphicImages,Isomorphisms,Kernels,Noether,Products,Properties}`.
+  **Self-contained**: `Demos/HSP.lagda.md` defines and uses its own `_̂_` (13 hits); migrate together with the § 1a HSP decision.

Note: #368 names the offender "`Setoid.Algebras.Congruences`", but the tree has
no such module; the live congruence code is `Setoid/Congruences/Basic.lagda.md`.

### 1c. Code-fence blank-line-after-opener (#372)

```
rg -U '```agda\n\n' src --glob '!src/Legacy/**'   # 222 hits / 51 files
```

The `.lagda` → `.lagda.md` conversion left a blank line between the
```` ```agda ```` opener and the first code line in 222 blocks across 51 files
(`Demos/HSP` alone has 63).  Pure whitespace, semantically null for both Agda and
kramdown; collapse with `perl -0pi -e 's/```agda\n\n+/```agda\n/g'` over the live
trees.  This is the lowest-risk task and a good first landing.

## 2. Imports

### 2a. Bare `open import` without `using`

```
rg -n '^open import [^(]*$' src --glob '!src/Legacy/**'
```

Every match is either (a) an umbrella/aggregator module re-exporting its children
with `public` (`Overture.lagda.md`, `Setoid.lagda.md`, `Classical/Bundles.lagda.md`,
`Order.lagda.md`, …) — which the STYLE_GUIDE "Umbrella modules re-export" rule
explicitly sanctions — or (b) the first physical line of a multi-line import whose
`using ( … )` clause sits on the next line (e.g. `open import Setoid.Algebras
{𝑆 = 𝑆}` followed by `using ( … )`).  No genuine "bare import without `using`"
violation exists in the live trees.

### 2b. Cosmetic `renaming` (#367)

```
rg -n 'renaming' src --glob '!src/Legacy/**'
```

The overwhelming majority are semantic and required: `renaming (Set to Type)`
(stdlib convention), `renaming (to to _⟨$⟩_)` (setoid-function application),
`renaming (Carrier to …)`, `renaming (IsSurjective to onto)`, the equational-
reasoning combinator renames, and so on.  The one cosmetic, no-op rename is the
dead `renaming (proj₁ to fst ; proj₂ to snd)` in
`Setoid/Homomorphisms/Properties.lagda.md`, which #367 already schedules for
collapse.  No other cosmetic renames found.

### 2c. Import-group ordering

The STYLE_GUIDE "Group imports by origin" rule (builtin, then stdlib, then
`agda-algebras`, each group alphabetized) cannot be machine-verified by a single
`rg`; it is checked per file as each module is touched.  No systematic violation
was observed in spot checks, and any local fix-ups ride along with the #367 /
#368 import surgery and the M4-2 per-subtree PRs rather than a separate sweep.

## 3. Minimal module headers (M4-2 / #268)

Detection heuristic: a module whose entire prose body between the YAML
front-matter and the first ```` ```agda ```` fence is the single boilerplate
sentence "This is the [X][] module of the [Agda Universal Algebra Library][]",
with no theoretical-background or motivation paragraph.  Precise enumeration
requires reading each module's prose and is therefore folded into the M4-2
per-subtree PRs (which rewrite headers anyway); this audit flags the dimension
rather than the per-file list, since header prose changes no compiled code and is
out of M4-1 scope.

## 4. HTML heading anchors (M4-2 / #268)

```
rg -n '<a id=' src --glob '!src/Legacy/**'   # 300 hits / 111 files
```

The STYLE_GUIDE "Section headings" rule forbids wrapping headings in
`<a id="…">…</a>`; MkDocs slugifies headings automatically.  300 such anchors
remain across 111 live-tree files (≈ 90 within `Setoid/`, matching the #370
estimate).  Heaviest offenders: `Demos/HSP` (37), `Overture/Preface` (11),
`Overture/Basic` (9), `Overture/Relations` (8), `Classical/Structures/{Ring,Lattice}`
(8, 7), `Setoid/Varieties/{Properties,Preservation}` (7), `Classical/Structures/{Monoid,Group}`
(6).  Anchor removal is mechanical but prose-only; it is M4-2 work and is
inventoried here only because #370 asks for the count.

## 5. Naming (clean)

```
rg -n '\bis-[a-zA-Z]' src/Setoid src/Classical
rg -rn 'is-homomorphism|\bHom\b' src/Setoid src/Classical   # empty
```

No `is-x` synonym predicates and no capital-`Hom` synonyms exist in the live
trees; the Setoid public API is already on `IsHom` / `hom`, `IsMon` / `mon`,
`IsEpi` / `epi`.  Every `is-…` hit is one of:

+  a descriptive lemma name — `⊙-is-hom`, `⊙-is-epi`, `lift-of-epi-is-epi`, `Lift-epi-is-epiˡ`, `id-is-injective`, `Lift-is-sub`, `hom𝔽[_]-is-epic`;
+  a canonical record field or predicate — `is-equivalence`, `is-compatible` (fields of `IsCongruence`), `is-variety` (the variety predicate in `Setoid/Varieties/Closure`).

These are correct and are **not** to be renamed.  The naming half of M4-1 is
therefore already discharged, as #267 states.

## Cross-cutting note for #369

The STYLE_GUIDE contradicts itself in three places this audit touches, all of
which #369 fixes:

+  The "Every public definition has a prose comment block" example (around line 539) writes a `-- |` docstring *inside* a fence and names a capital `Hom`, contradicting both "prose belongs in Markdown" and the Naming section's deprecation of `Hom` (line 275); rewrite to Markdown-prose-before-fence with lowercase `hom`.
+  The "Group imports by origin" example (line 249) imports `∣_∣ ; ∥_∥`, the very notation the Projections table deprecates; update it to `proj₁ ; proj₂` once #367 lands.
+  The Projections table (line 301) and the Interpretation table (line 378) describe the pre-migration trees; refresh them to match the post-#367 / post-#368 state.
