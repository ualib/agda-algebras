<!-- File: docs/STYLE_GUIDE.md -->

# agda-algebras Style Guide

This document specifies the conventions that agda-algebras follows.  It is opinionated: in places where reasonable people disagree, it takes a position and justifies it.  In places where the library's conventions are genuinely idiosyncratic (much of the notation), this document codifies the idiom rather than fighting it.

The document has two audiences.  The primary audience is contributors: people writing or reviewing agda-algebras code.  The secondary audience is consumers of the library's training corpus — machine-learning systems and mathematicians who will read large stretches of agda-algebras as a single body of work.  For the second audience, consistency is as important as correctness.

This is a living document.  When the library adopts a new convention, this file changes.  When the document describes a convention the library doesn't actually follow, *the code is the ground truth*, not this document — and the discrepancy is itself a bug, tracked under M4-1.

A note on forward references.  This document describes the 3.0 target.  Several paths referenced below (`src/Classical/`, `src/Cubical/`, `src/Legacy/Base/`) do not yet exist in the tree as of the writing of this document; they are created in Milestones 2 (M2), 3 (M3), and 5 (M5) respectively.  Rules that apply to those trees are effective when they land.

---

## Table of contents

+  [Guiding principles](#guiding-principles)
+  [File format](#file-format)
+  [Module structure and organization](#module-structure-and-organization)
+  [Imports](#imports)
+  [Naming](#naming)
+  [Notation and symbol table](#notation-and-symbol-table)
+  [Universe levels](#universe-levels)
+  [Record vs Σ](#record-vs-%CE%A3)
+  [Proof style](#proof-style)
+  [Comments and documentation](#comments-and-documentation)
+  [Deprecation policy](#deprecation-policy)
+  [Checklists](#checklists)

---

## Guiding principles

Five principles shape the specific rules below.  When a situation isn't covered by an explicit rule, fall back to these.

1.  **One canonical form per concept**.  The library has a history of parallel implementations of the same concept under slightly different names and shapes.  This doubles the maintenance cost, fragments the training corpus, and forces contributors to choose between equally-valid forms for reasons that have nothing to do with the mathematics.  New code introduces a new name only for a new concept.  Synonyms are tracked and deprecated.

2.  **Stdlib-compatible when possible, idiomatic when meaningful**.  The Agda standard library has its own naming and notation conventions.  Where our conventions can match stdlib's without sacrificing clarity, they do — this makes bridges and interop cheap.  Where our conventions meaningfully differ (extensive use of unicode, e.g., boldface variables for *algebras* and other *sets with structure*), the difference carries semantic weight and we keep it.

3.  **Proof terms are training data**.  Every definition, every lemma, every proof term is part of a corpus that downstream consumers will read.  Write with that in mind: small focused lemmas over large opaque ones; explicit type signatures over inferred ones; named helpers over `where`-clause one-offs; rich prose comments paired with formal statements.

4.  **Cubical portability by construction**.  `Setoid/` is canonical for the current version (v3.0); `Cubical/` is the canonical long-term target (v4.0).  The Setoid-to-Cubical port should be mechanical, which means definitions in the canonical development should be stated in terms of the `Algebra` record's `Domain` equivalence; avoid Setoid-specific gadgets that have no Cubical analog.

5.  **Document the mathematics, not just the code**.  A public definition's prose comment explains *what it means mathematically* and *when a mathematician would reach for it*, with citations to the literature where appropriate.  A comment that only restates the type signature in English fails the "why would I use this?" test.

---

## File format

### Pragma

Every Agda source file begins with the following pragma:

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
```

The flags, in order, mean the following:

+  `--cubical-compatible` requires definitions to be compatible with `Cubical/`'s canonical-target semantics; replaces the historical `--without-K`.
+  `--safe` prohibits `postulate`, `primitive`, unsafe `TERMINATING` pragmas, and other escape hatches; the library's theorems rest on a specific foundation; `--safe` ensures they're not silently dependent on ambient assumptions.
+  `--exact-split` requires every clause matches the type of the function being defined, preventing definitional-equality surprises that trip up proof automation and the training-corpus consumers.

**Exceptions**.  
+  `src/Legacy/Base/`, will retain its historical `--without-K` pragma; new contributions do not land in `Legacy/` (see [Milestone 2][`docs/GITHUB_PROJECT.md`]).
+  Generated files (`src/Everything.agda`); the pragma is still required, but the file is written by the Makefile and should not be hand-edited.

### Module header

Immediately after the pragma (possibly separated by imports required by the module header's own arguments), the module is declared.  The module name must match the filename under the `src/` include root, with `/` replaced by `.`; e.g.,

+  `src/Base.agda` → `module Base where`.
+  `src/Setoid/Algebras/Basic.agda` → `module Setoid.Algebras.Basic where`.
+  `src/Classical/Structures/Semigroup.agda` → `module Classical.Structures.Semigroup where`.

Parametrized modules declare their parameters in the header:

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Basic {𝑆 : Signature 𝓞 𝓥} where
```

The only imports allowed *before* the module header are those required to state the header's parameters (here, `Overture`'s `𝓞`, `𝓥`, `Signature`).  All other imports go after the header.

### Line length

Prefer lines of at most 100 characters.  This is a soft limit: breaking a long type signature to respect it is almost always worth the extra line, while breaking an equational-reasoning chain is usually not.

### Trailing whitespace and blank lines

+  Trailing whitespace is not allowed in Agda code, but is allowed in Markdown prose (to force a line break).
+  Files end in exactly one newline.
+  At most one consecutive blank line between top-level declarations.

(A `.editorconfig` file in the repo root would enforce these mechanically.  Until one exists, we try to catch violations in review.)

---

## Module structure and organization

### One concept per module, where feasible

A module named `Congruences` is about congruences.  A module named `Products` is about products.  When a module grows to the point where it spans multiple mathematical concepts, split it along the conceptual line rather than an implementation-convenience line.

### Umbrella modules re-export

A module whose name has no final segment past the conceptual theme (e.g. `Base.Homomorphisms`, `Setoid.Algebras`) acts as a barrel of submodules, which it re-exports (using the `public` keyword); e.g.,

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Algebras.Basic          {𝑆 = 𝑆} public
open import Setoid.Algebras.Products       {𝑆 = 𝑆} public
open import Setoid.Algebras.Congruences    {𝑆 = 𝑆} public
```

Downstream modules `open import Setoid.Algebras` to get the whole theme and `open import Setoid.Algebras.Basic` to get a specific submodule, but we strongly *prefer modules that import precisely what they need* — see [Imports](#imports) below. 

### Classical structures quintuple

In upcoming versions of agda-algebras (to land in [Milestone 3][`docs/GITHUB_PROJECT.md`]), each classical algebraic structure `X` will ship as a quintuple of modules under `src/Classical/`:

+  `Classical/Signatures/X.agda`: the signature (operation symbols + arities).
+  `Classical/Theories/X.agda`: the equational theory (the axioms as `Theory 𝑆ₓ`).
+  `Classical/Structures/X.agda`: the Σ-typed structure itself (polymorphic over levels).
+  `Classical/Bundles/X.agda`: the record-typed "bundle view" matching stdlib's `Algebra.Bundles.X`.
+  `Classical/Small/Structures/X.agda`: a level-fixed veneer at `ℓ₀` for the common case.

This pattern is to be ratified in ADR-002 (to land with [M3-1][`docs/GITHUB_PROJECT.md`]) and exemplified in `Classical/Structures/Semigroup.agda` (M3-2) as the pattern-setting first structure.

### Module headers have comment blocks

Every non-trivial module should have a prose comment block near the top — after the pragma and any module-header imports, but before the main body; e.g.,

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Basic {𝑆 : Signature 𝓞 𝓥} where

-- | Basic definitions for Setoid-based universal algebras.
-- |
-- | An `Algebra` over signature `𝑆` is a setoid (the domain) equipped with an
-- | interpretation of each operation symbol in `𝑆` as a function on the
-- | carrier that respects the setoid's equivalence relation.
-- |
-- | This module is the canonical entry point for the Setoid tree.  Related modules:
-- | `Setoid.Algebras.Products` for indexed products; `Setoid.Algebras.Congruences`
-- | for the congruence relations used to build quotients.  See also
-- | `Setoid.Homomorphisms.Basic` for homomorphisms between algebras.
```

The content of these blocks matters — see [Comments and documentation](#comments-and-documentation) below.

---

## Imports

### Use tight `using` clauses

Bare `open import X` brings every name from `X` into scope, which is convenient but obscures provenance and collides with other imports unpredictably.  Always use `using (...)` to name what you're importing; e.g.,

```agda
-- Preferred.
open import Data.Product  using ( _,_ ; _×_ ; Σ-syntax )
open import Level         using ( Level ; _⊔_ ; suc )

-- Avoid.
open import Data.Product
open import Level
```

### Group imports by origin

Imports are grouped into blocks with blank lines between.

1.  Agda primitives (`Agda.Primitive`).
2.  Standard library.
3.  Internal agda-algebras modules.

Within each block, alphabetize by module name; e.g.,

```agda
-- Imports from Agda primitives and the standard library.
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; _×_ ; Σ-syntax )
open import Level            using ( Level ; _⊔_ ; suc )
open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary   using ( _∈_ ; Pred )

-- Imports from the agda-algebras library.
open import Overture         using ( ∣_∣ ; ∥_∥ ; Op )
open import Base.Relations   using ( _|:_ ; _|:pred_ ; Rel ; compatible-Rel )
                             using ( REL ; compatible-REL )
```

### Prefer `renaming` for clarity, not obfuscation

`renaming` is appropriate when a stdlib name clashes with a local one, or when a stdlib name is awkward (`Set` → `Type` is our project-wide convention; `Rel` → `BinRel` disambiguates stdlib's `Relation.Binary.Rel` from our own `Base.Relations.Rel`).  Other `renaming` for cosmetic and stylistic preference is strongly discouraged.

---

## Naming

### The core decision: match stdlib's `IsX` / `x` idiom

Agda's standard library names predicates `IsSemigroup`, `IsMonoid`, `IsHomomorphism` and the corresponding Σ-or-record-typed structure `Semigroup`, `Monoid`, `Homomorphism`.  The `agda-algebras` Setoid tree has adopted this: `IsHom`, `IsMon`, `IsEpi` for the record/predicate forms, `hom`, `mon`, `epi` for the Σ-typed pairs.

**This is the canonical form going forward**.  It has three advantages.

1.  **Stdlib compatibility**.  Our bundle bridges to `Algebra.Bundles` interoperate naturally when our types share stdlib's idiom.
2.  **Disambiguation**.  `IsHom` (the property) is structurally a different kind of object from `hom` (the Σ of the function and the property), and the typographic difference makes that clear.
3.  **Established in canonical code**.  `Setoid/Homomorphisms/Basic.agda`, `Demos/HSP.lagda`, and the `Setoid/Varieties/` tree already use this form.

**Deprecated synonyms** (existing in `Base/` and some early `Setoid/`-ish code):

+  `is-hom` / `is-homomorphism` / `is-mon` / `is-epi` — the hyphen-case predicate forms; these stay in `Legacy/Base/` unchanged; anywhere else they are renamed during the M4-1 sweep with deprecation warnings.
+  Record-form synonyms that capitalize the Σ-form (`Hom` as a record-typed alias for `hom`).  Pick one; the lowercase Σ-form wins.

**Other naming rules**.

+  **Types** start with uppercase: `Algebra`, `Congruence`, `Homomorphism`, `Subalgebra`.
+  **Terms (definitions at `Type α`-level)** start with lowercase: `hom`, `mon`, `epi`, `compatible-map`.
+  **Level variables** are lowercase Greek: `α`, `β`, `γ`, `δ`, `ℓ`, `ρ`, `ρᵃ`, `ρᵇ`.  The superscript convention (`ρᵃ` for "the second level of `𝑨`") is idiomatic (in `agda-algebras`) and preserved.
+  **Mathematical italic/bold variables**.  Bold italic capitals `𝑨`, `𝑩`, `𝑪` for algebras; italic capital `𝑆` for signatures; italic lowercase `𝑓`, `𝑔` for operation symbols; script `𝒽` for homomorphisms; italic lowercase `𝑎`, `𝑏` optionally for algebra elements (plain ASCII `a`, `b` is the more common practice and remains acceptable).  Plain-text `A`, `B` is used for carrier types and stdlib-aligned names.
+  **Predicates on a single thing** use `IsX` (record-typed) when the predicate carries useful structure, or `is-x` (function-typed, Legacy-only) when it's a plain proposition.
+  **The type of things satisfying `IsX`** is `x` (the Σ-pair of the subject and its `IsX` proof).
+  **Relations** use symbolic names where they exist conventionally (`_≅_`, `_≈_`, `_≤_`).  Text-named relations follow the stdlib convention of `_IsXOf_` (e.g., `_IsSubalgebraOf_`, `_IsHomImageOf_`).

### Avoid Hungarian-style suffixes

Don't decorate names to indicate implementation/type choices; avoid suffixes like `SigmaRecord`, `AsRecord`, `Record`, `Sigma` (e.g., `AlgebraAsRecord` or `AlgebraAsSigma`).  If two forms exist (e.g., record and Σ), then use a different organizing principle — separate modules, or a `Bundles/` suffix for the record form and bare naming for the canonical Σ form.

---

## Notation and symbol table

`agda-algebras` uses Unicode heavily.  The following table catalogues the canonical notation.  New code uses these symbols; old code is migrated during M4-1.

### Projections and pair operations

| Symbol | Meaning | Source | Status/Plan |
|---|---|---|---|
| `∣_∣` | First projection of a Σ-type | `Overture.Basic` | **deprecated** : replace with `proj₁` in v3.0 |
| `∥_∥` | Second projection of a Σ-type | `Overture.Basic` | **deprecated** : replace with `proj₂` in v3.0 |
| `_,_` | Σ-type constructor | stdlib `Data.Product` | **standard** : retain in v3.0 |
| `Σ[_∈_]_` | Σ-type binder syntax | stdlib `Data.Product` | **standard** : retain in v3.0 |

In the upcoming release cycle we will replace `∣_∣` and `∥_∥` with the more standard `proj₁` and `proj₂` throughout.  The vertical-bars convention was an `agda-algebras` idiom carried over from earlier `TypeTopology`-style developments; they make the code *less* readable for mathematicians who typically reserve those symbols for absolute value and norm, and the stdlib names bridge more cleanly to `Data.Product`.

**Scope note**.  These projections are used pervasively throughout `src/` and `docs/lagda/` — this is the largest syntactic change in the 3.0 cycle.  The rationale and migration plan will be captured in a dedicated ADR (see M1-6), and the mechanical sweep is scheduled as part of M4-1.  Until then, existing `∣_∣` / `∥_∥` callsites remain valid; new code may use either notation, but `proj₁` / `proj₂` is preferred.


### Universe levels

| Symbol | Meaning |
|---|---|
| `𝓞` | Level of *operation-symbol* types in a signature |
| `𝓥` | Level of *arity* types in a signature |
| `α`, `β`, `γ`, `δ` | Generic level variables for algebra carriers |
| `ρ`, `ρᵃ`, `ρᵇ`, `ρᶜ` | Relation/equivalence levels (the "second level" of a setoid algebra) |
| `ℓ` | Generic level variable |

`𝓞` and `𝓥` are semantically charged; see the [Universe levels](#universe-levels) section below.

### Algebras and homomorphisms

| Symbol | Meaning |
|---|---|
| `𝑨`, `𝑩`, `𝑪` | Algebras (mathematical bold uppercase) |
| `𝑎`, `𝑏`, `𝑐` | Elements of an algebra's carrier |
| `𝑆` | A signature |
| `𝑓`, `𝑔` | Operation symbols, or (in `hom`-context) homomorphisms |
| `𝒽` | A homomorphism or family of homomorphisms |
| `𝒾𝒹` | Identity homomorphism |
| `𝓁𝒾𝒻𝓉`, `𝓁ℴ𝓌ℯ𝓇` | Universe-lifting homomorphism and its inverse |

Plain-text `A`, `B` denote carrier types; mathematical bold italic `𝑨`, `𝑩` denote models (e.g., algebraic or relational structures); italic `𝑆` denotes the signature.

### Equivalence, equality, isomorphism

| Symbol | Meaning |
|---|---|
| `_≡_` | Intensional propositional equality (stdlib) |
| `_≈_` | Setoid equivalence on the `Domain` of an algebra |
| `_≅_` | Isomorphism between algebras |
| `_≃_` | Reserved for Cubical equivalence (`Cubical/` tree only) |
| `_∙_` | Composition in the Setoid/Cubical contexts |

`_≃_` is held in reserve for the cubical tree so that `Setoid/` and `Cubical/` can later be unified without symbol collision.

### Orders and lattices

| Symbol | Meaning |
|---|---|
| `_≤_` | Subalgebra / partial order |
| `_≥_` | Superalgebra / reversed partial order |
| `⊥`, `⊤` | Lattice bottom and top |
| `_∧_`, `_∨_` | Lattice meet and join |

### Set-theoretic

| Symbol | Meaning |
|---|---|
| `_∈_` | Membership (stdlib `Relation.Unary`) |
| `_⊆_` | Subset (stdlib) |
| `Pred` | Unary predicate type (stdlib) |

### Products

| Symbol | Meaning |
|---|---|
| `⨅_` | Indexed product of algebras |
| `_×_` | Binary Cartesian product of types |
| `_^_` | Natural-number-indexed power (rare; prefer `⨅`) |

### Interpretation

| Symbol | Meaning |
|---|---|
| `_̂_` | interpretation of an operation symbol in an algebra or other structure (`𝑓 ̂ 𝑨`) |
| `Domain` | underlying setoid of an algebra or other structure |
| `Interp` | `Func`-typed interpretation of operations |

### Term algebra

| Symbol | Meaning |
|---|---|
| `𝑻 X` | The term algebra over generators `X` |
| `Term X` | The type of `𝑆`-terms over generators `X` |

### When to introduce new notation

Do not introduce new notation for a concept that already has notation elsewhere in the library.  If you're defining a new concept, consult this table and the `Setoid/Homomorphisms/Basic.agda` file for local conventions before picking a new symbol.  Prefer Unicode symbols already used in the Agda ecosystem (stdlib, `1Lab`, `cubical`, `TypeTopology`) over inventing new ones.

When you *do* introduce new notation, add it to this table in the same PR.

---

## Universe levels

### The `𝓞` / `𝓥` convention

`𝓞` and `𝓥` always denote the universe levels of *operation-symbol* types and *arity* types, respectively.  They are declared once, in `Overture.Signatures`:

```agda
variable 𝓞 𝓥 : Level
```

**Using `𝓞` or `𝓥` for anything else is a bug.**

Every signature-parametrized module imports these by name from `Overture`.  Never re-declare them as `variable` in a downstream module.

The design-discussion question of whether `𝓞` and `𝓥` should be `private variable` (forcing downstream modules to re-declare) or left as public `variable` is tracked in **M4-3**.  Until that issue is resolved, the rule is: leave `𝓞`/`𝓥` as public `variable`s in `Overture.Signatures` and import them by name.

### Other level variables

Level variables for algebra carriers and relations are declared `private` in each module that uses them:

```agda
private variable α β ρ : Level
```

This keeps them from leaking into the module's public interface.

### Minimal universe levels

When stating a type that involves levels, write the explicit level expression (e.g., `𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ`) rather than letting Agda infer a `Level`.  The explicit form is more informative for readers and for training-corpus consumers, and it catches universe-polymorphism bugs early.

---

## Record vs Σ

### The foundational decision

The core `Algebra` type is a **record**.  It has named projections (`Domain`, `Interp`) and is inhabited many times across the library; named projections make the code substantially more readable than anonymous Σ-components would.

**Classical algebraic structures** (`Semigroup`, `Monoid`, `Group`, `Ring`, `Lattice`, etc.), on the other hand, are **Σ-typed** at the core, with a **record-typed "bundle view"** in a parallel `Classical/Bundles/` module for stdlib interoperability; e.g.,

```agda
-- Classical/Structures/Semigroup.agda
module Classical.Structures.Semigroup where
open import Classical.Signatures.Semigroup using ( 𝑆ₛ )
open import Setoid.Algebras {𝑆 = 𝑆ₛ} using ( Algebra )
-- ...
Semigroup : (α ρ : Level) → Type _
Semigroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Eₛ

-- Classical/Bundles/Semigroup.agda
record SemigroupBundle α ρ : Type _ where ...
```

The reasoning, ratified in ADR-002 (landing with M3-1) is as follows: the mathematical reading "a semigroup *is* an algebra equipped with a proof it satisfies the semigroup theory" is exactly what a Σ-type expresses.  The record-typed bundle view exists for stdlib bridge compatibility.

### When to use which, in new code

A **record** is appropriate when
+  the structure has multiple meaningful named projections (three or more, typically);
+  the structure will be inhabited many times, and readers will benefit from named-projection access;
+  stdlib interop requires a matching record shape.

A **Σ-type** is appropriate when
+  the structure has a natural "bundled-together" mathematical reading; e.g., "X is a Y equipped with a proof that Y satisfies Z;"
+  you expect to project primarily with `proj₁` / `proj₂`;
+  the code is producing a canonical Classical structure.

### Don't create parallel record/Σ variants of the same concept

If the library already has a record for `Foo`, don't add a Σ version of `Foo` as a convenience.  Either convert the existing record to Σ (with deprecation cycle) or leave it.  The `Base/Structures/Basic` vs `Base/Structures/Sigma` split is an example of **what not to do** (and M2-2 will clean it up).

---

## Proof style

### Prefer many small theorems

A theorem whose proof is more than roughly 20 lines should usually be restructured as two or three named lemmas.  This serves two goals: the proof becomes easier to review, and the named lemmas become individually-retrievable artifacts in the training corpus.

### Named helpers over `where` clauses

When a proof needs a non-trivial helper, prefer defining it as a named module-level (or `private`) lemma rather than burying it in a `where` clause; e.g.,

```agda
-- Preferred.
hom-compose-cong : ∀ {𝑓} → ...
hom-compose-cong = ...

my-theorem : ...
my-theorem = ... hom-compose-cong ...

-- Avoid for non-trivial helpers.
my-theorem : ...
my-theorem = ... helper ...
  where
    helper = ...  -- A ten-line auxiliary proof hidden here.
```

A one-line `where`-bound value is fine.  A ten-line `where`-bound proof is a missed opportunity to name something potentially useful.

### Explicit type signatures

Every top-level definition has an explicit type signature, even when Agda can infer it.  Signatures document intent; inferred signatures require readers to type-check the definition mentally to know what they're reading.

### Equational reasoning

Use stdlib's `≡-Reasoning` / `≈-Reasoning` modules for equational-reasoning proofs.  Prefer this style over manual `trans` / `sym` / `cong` chains, especially when the proof involves more than two steps; e.g.,

```agda
-- Preferred for multi-step equational reasoning.
open ≈-Reasoning (Domain 𝑩)

proof : f (g x) ≈ h x
proof = begin
  f (g x)   ≈⟨ f-respects (g-eq x) ⟩
  f (g' x)  ≈⟨ composite-eq x ⟩
  h x       ∎
```

### Avoid opaque tactics

`tactic` macros and reflection-based automation can make proofs shorter but obscure the proof term.  For training-corpus purposes, an explicit proof term is worth more than a shorter-but-opaque one.  Use tactics sparingly and only when the explicit form would be substantially longer *and* less informative.

`RingSolver` and similar domain-specific solvers are fine — they produce legible proof terms.  General-purpose tactics that produce `solve`-typed proof terms are not.

---

## Comments and documentation

### Every public definition has a prose comment block

This is non-negotiable for public API.  A public definition — anything re-exported from a barrel module, anything documented in the user-facing literate-Agda files — has a comment block immediately above it; e.g.,

```agda
-- | `Hom 𝑨 𝑩` is the type of homomorphisms from `𝑨` to `𝑩`.  A
-- | homomorphism is a setoid function on carriers that respects every
-- | operation of the signature: for every operation symbol `𝑓`, the
-- | map commutes with `𝑓 ̂ 𝑨` and `𝑓 ̂ 𝑩`.
-- |
-- | See also: `IsHom` for the predicate form, `∘-hom` for composition,
-- | and `Setoid.Homomorphisms.Isomorphisms` for the isomorphism variant.
Hom : (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) → Type _
Hom 𝑨 𝑩 = Σ (Domain 𝑨 ⟶ Domain 𝑩) (IsHom 𝑨 𝑩)
```

### What a good comment block contains

1.  **What the definition is**, stated in the language a mathematician would use; e.g., "a homomorphism from `𝑨` to `𝑩`"; **not** "a Σ-type whose first projection is ...".
2.  **When a reader would reach for it**.  The mathematical motivation; what problem the definition solves.
3.  **Cross-references**.  The closest mathematical neighbors; e.g., a related definition, the predicate form, the canonical theorem about it.  Don't list everything possibly related; list the two or three most useful jumps.
4.  **Citation** if the concept comes from a specific source; textbook and page, or paper and theorem number; this is especially valuable for the training corpus.

### What a good comment block is not

+  **Not a restatement of the type signature**.  "`Hom 𝑨 𝑩 : Type _` is a type parametrized by two algebras that returns a type" adds nothing.
+  **Not marketing copy**.  "An elegant formulation of the homomorphism concept using cutting-edge type theory" is noise.

### Module-level comment blocks

See [Module structure and organization](#module-structure-and-organization) above.  A module header gets a comment block describing what the module is about, what's in it, and its closest-neighbor modules.

### Literate-Agda files

Files in `docs/lagda/` are user-facing exposition built around formal content.  The rules above for in-source comments apply to the `\begin{code}` ... `\end{code}` blocks; the surrounding prose can be more expansive.  The literate files are currently the primary vehicle for tutorial-style documentation.

---

## Deprecation policy

### The public API stability contract

Breaking changes to names or signatures in *publicly-exported* definitions go through at least one minor-version deprecation cycle.  "Publicly exported" means: re-exported from a barrel module, or documented in user-facing literate-Agda files.

Internal helpers (not re-exported from barrel modules, not documented publicly) can change without notice.

### The deprecation procedure

Deprecate a public definition as follows:

1.  **Add the new form**.  The new definition lives alongside the old one.
2.  **Mark the old form**.  Add a `{-# WARNING_ON_USAGE old-name "Use new-name instead." #-}` pragma.
3.  **Announce in CHANGELOG.md**.  Under `### Deprecated` for the in-progress `[Unreleased]` section.
4.  **Remove after at least one minor version**.  If the deprecation landed in 3.1, the removal can happen no earlier than 3.2.

### What counts as "breaking"

+  Renaming a public definition.
+  Changing the type of a public definition (including reordering its arguments).
+  Changing the semantics of a public definition (e.g., what elements satisfy a predicate).
+  Removing a public definition.

### What is "non-breaking"

+  Strengthening a type (if old callers still type-check against the new type).
+  Adding a new definition.
+  Internal refactorings that don't change the public type signature or semantics.

---

## Checklists

### Before opening a PR

+  [ ] `make check` passes locally under `nix develop`.
+  [ ] Every new public definition has a prose comment block.
+  [ ] Every new module has a module-header comment block.
+  [ ] No new synonyms for concepts already named elsewhere.
+  [ ] New notation is added to the [Notation and symbol table](#notation-and-symbol-table) section of this document.
+  [ ] Commit messages are coherent and explain the "why," not just the "what."
+  [ ] If the PR touches `src/`, the target is `Setoid/` or `Classical/` or the shared `Overture/` — not `Legacy/Base/`.

### When reviewing a PR

+  [ ] Every public definition has a comment block that passes the "would a mathematician know why to reach for this?" test.
+  [ ] Names consistent with the surrounding code.
+  [ ] Imports are tight, grouped, and ordered alphabetically within a group.
+  [ ] The PR does not introduce notation that collides with existing notation.
+  [ ] Large proofs are broken into named helper lemmas.

### When auditing a module during the M4-1 sweep

+  [ ] Module has a header comment block.
+  [ ] Every public definition has a prose comment block.
+  [ ] Names match the canonical convention (`IsX` / `x`, not `is-x` / `x`).
+  [ ] Notation matches the canonical table.
+  [ ] Imports use `using (...)` clauses.
+  [ ] No commented-out code.
+  [ ] No synonym pairs in the module's exports.

---

## References

+  Project roadmap: [`docs/GITHUB_PROJECT.md`][].
+  Architecture Decision Records: [`docs/adr/`](adr/) (scaffolding in M1-6).
+  Contributing guide: [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
+  Related Agda-ecosystem style references:
  +  [Agda standard library style guide](https://github.com/agda/agda-stdlib/blob/master/notes/style-guide.md).
  +  [Martin Escardó's TypeTopology](https://github.com/martinescardo/TypeTopology).
  +  [1Lab contribution guide](https://1lab.dev/1Lab.Contributing.html) — similar philosophy on prose-paired formal content.

---

*This document will evolve.  Specific decisions flagged as "tracked in M4-*" will be resolved as those issues close.  When you encounter an undocumented convention while working on the library, please open a PR or Issue to document it — style guides die when maintenance becomes someone-else's-problem.*

[`docs/GITHUB_PROJECT.md`]: https://github.com/ualib/agda-algebras/blob/master/docs/GITHUB_PROJECT.md
