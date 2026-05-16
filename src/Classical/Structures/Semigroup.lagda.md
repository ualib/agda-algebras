---
layout: default
file: "src/Classical/Structures/Semigroup.lagda.md"
title: "Classical.Structures.Semigroup module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-structures-semigroup">Semigroups</a>

This is the [Classical.Structures.Semigroup][] module of the [Agda Universal Algebra Library][].

A semigroup is an algebra equipped with a binary operation satisfying associativity.  Following [ADR-002][ADR-002], a semigroup in this library is **Σ-typed at the core**: a pair consisting of a `𝑆ₛₘ`-algebra and a proof that the algebra models the semigroup theory.  This mirrors the mathematical reading "a semigroup is an algebra equipped with a proof it satisfies the semigroup axioms"; record-typed *bundle views* compatible with the `Algebra.Bundles.Semigroup` idiom of the standard library are provided separately in [`Classical.Bundles.Semigroup`][Classical.Bundles.Semigroup].

Semigroup is the first concrete structure to land under [`Classical/`][Classical], and so the file-layout and helper-shape conventions established here are normative for every subsequent structure (Monoid in M3-4, Group also in M3-4, Lattice in M3-5, Ring in M3-6).  The conventions are:

+  **Signature representation**.  The signature lives in `Classical/Signatures/X.lagda.md` and uses a one-constructor data type per operation symbol with the suffix `op`, reserving the bare symbol for use-site infix sugar over `node`.  Arities are encoded as `Fin n`.  The signature module exports the symbols, the arity function, and the assembled `Signature` value `𝑆ₓ`.
+  **Equational theory representation**.  The theory lives in `Classical/Theories/X.lagda.md` and uses two named-constructor enums: one for the variables appearing in the equations (`XVar`, with constructors `x`, `y`, `z`, …) and one for the equation indices (`Eq-X`, with one constructor per equation in the theory).  The theory itself is a function `Th-X : Eq-X → Term XVar × Term XVar`.  The format is indexed rather than predicate-style so the model relation lands in the `Modᵗ` form of `Setoid.Varieties.EquationalLogic`.
+  **Σ-typed core**.  This file (`Classical/Structures/X.lagda.md`) defines `X α ρ = Σ[ 𝑨 ∈ Algebra 𝑆ₓ α ρ ] 𝑨 ⊨ Th-X`, where `_⊨_` is a local alias for `Modᵗ Th-X`.  Three named accessors (`Domain`, `Signature`, `equations`) are defined alongside the core to offset the use-site ergonomic cost of Σ-projection; these get pulled up to a shared location (probably `Classical.Structures` itself, or a thin `Classical.Accessors` module) once a second consumer exists, but landing them locally for the first structure is deliberate — premature shared abstraction is the failure mode the #326 scaffold non-goals were drawn to avoid.
+  **`fromPropEq` helper**.  A per-structure constructor that builds the Σ-typed core from a propositional-equality formulation of the equations: signature `fromPropEq : (A : Type α) (_·_ : A → A → A) (assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)) → X α α`.  This is the bridge by which users build classical structures from ordinary definitions without an explicit Setoid wrapping; the underlying setoid in the result is `(A, _≡_)`.  Same pull-up policy as the accessors.
+  **Bundle view**.  Parallel record-typed bundle matching `Algebra.Bundles.X` from the standard library, plus bidirectional conversion functions `⟨_⟩ₓ`, `⟪_⟫ₓ` and a round-trip lemma.  Lives in `Classical/Bundles/X.lagda.md`.
+  **Level-fixed veneer**.  `Classical/Small/Structures/X.lagda.md` fixes both levels to `lzero` and re-exports the `lzero`-specialized `fromPropEq`.  This is the import path for downstream consumers (M7 finite-template CSP, M6 FLRP finite cases, tutorial Examples/) that do not need universe polymorphism.
+  **Morphisms**.  No per-structure invariant is required: any `Setoid.Homomorphisms` morphism between the underlying algebras already preserves operations, and the target's models-the-theory predicate is automatically inherited from the source's.  Concretely, a "semigroup morphism" is definitionally an algebra homomorphism of underlying algebras; there is nothing structure-specific to define here.
+  **Cubical portability discipline**.  Equations are stated purely in terms of the `Algebra.Domain` setoid equivalence, never reaching for setoid-specific machinery without a cubical analog.  When `Cubical/` becomes canonical for 4.0 ([ADR-003][ADR-003]), the port from `Setoid/`-based equivalence to path-type equivalence is intended to be a substitutional rewrite rather than a re-derivation.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Semigroup where

-- Imports from Agda and the Agda Standard Library ----------------------
open import Agda.Primitive   using ()             renaming ( Set to Type )
open import Data.Fin.Base    using ( Fin )
open import Data.Fin.Patterns                     using ( 0F ; 1F )
open import Data.Product     using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ ; _×_)
open import Function         using ( Func )
open import Level            using ( 0ℓ ; Level ; _⊔_ )
open import Relation.Binary  using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡
  using ( _≡_ ; refl ; cong₂ )

-- Imports from agda-algebras -------------------------------------------
open import Classical.Signatures.Semigroup
  using ( 𝑆ₛₘ ; Op-Semigroup ; ∙op )
open import Classical.Theories.Semigroup
  using ( SemigroupVar ; Eq-Semigroup ; assoc ; Th-Semigroup ; x ; y ; z )
open import Setoid.Algebras                       {𝑆 = 𝑆ₛₘ}
  using ( Algebra ; ⟨_⟩ ; _̂_ )
open import Setoid.Varieties.EquationalLogic      {𝑆 = 𝑆ₛₘ}
  using ( Modᵗ )

open Algebra using ( Interp ) renaming ( Domain to AlgDomain )
open Func    using ( cong )            renaming ( to to _⟨$⟩_ )

open import Overture.Terms      {𝑆 = 𝑆ₛₘ}  using ( Term ; ℊ ; node )
private variable α ρ : Level
```

The local `_⊨_` alias for `Modᵗ`-on-`Th-Semigroup`.  Kept private to this module per the M3-2 design decision; pull-up to a shared location is deferred until at least one additional structure (Monoid, M3-4) confirms the shape generalizes.

```agda
private
  _⊨_ : Algebra α ρ → (Eq-Semigroup → (Term SemigroupVar × Term SemigroupVar)) → Type _
  𝑨 ⊨ E = Modᵗ E 𝑨
```

The Σ-typed core.  A `Semigroup α ρ` is a `𝑆ₛₘ`-algebra together with a proof that the algebra satisfies the semigroup theory.

```agda
Semigroup : (α ρ : Level) → Type _
Semigroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Semigroup
```

#### <a id="named-accessors">Named accessors</a>

Three convenience projections offset the Σ-projection cost at use sites.

```agda
module _ (𝑺 : Semigroup α ρ) where

  Domain : Setoid α ρ
  Domain = AlgDomain (proj₁ 𝑺)

  Signature : Algebra α ρ
  Signature = proj₁ 𝑺

  equations : proj₁ 𝑺 ⊨ Th-Semigroup
  equations = proj₂ 𝑺
```

#### <a id="from-propositional-equality">Building a semigroup from propositional equality</a>

The `fromPropEq` helper builds a `Semigroup α α` from a carrier type, a binary operation, and an associativity proof phrased in terms of the *propositional* equality `_≡_`.  Under the resulting setoid the equivalence is exactly `_≡_`; the interpretation of `∙op` reduces definitionally to the supplied operation, so concrete computations downstream do not encounter opacity introduced by the Σ-encoding.

```agda
-- Wrapping `fromPropEq` in an explicit-`α` module is deliberate: inside
-- a `private variable α` regime, every signature — including those in
-- `where` clauses — is independently subject to generalization, which
-- would force the inner `Setoid α α`, `Algebra α α`, and `𝑨 ⊨ Th-Semigroup`
-- to live at fresh, unrelated levels.  Binding `α` as a module parameter
-- pins it once for the whole construction.
module _ {α : Level} where

  fromPropEq :  (A : Type α)
                (_·_ : A → A → A)
                (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
                → Semigroup α α
  fromPropEq A _·_ ·-assoc = 𝑨 , thm
    where
      A-setoid : Setoid α α
      A-setoid = record  { Carrier        = A
                         ; _≈_            = _≡_
                         ; isEquivalence  = ≡.isEquivalence
                         }

      interp : Func (⟨ 𝑆ₛₘ ⟩ A-setoid) A-setoid
      interp ⟨$⟩ (∙op , args)            = args 0F · args 1F
      cong   interp {∙op , u} {.∙op , v} (refl , u≈v)
                                         = cong₂ _·_ (u≈v 0F) (u≈v 1F)

      𝑨 : Algebra α α
      𝑨 = record { Domain = A-setoid ; Interp = interp }

      -- The single equation of the semigroup theory is associativity.
      -- For variable assignment ρ : SemigroupVar → A, the interpretation
      -- of the LHS and RHS reduces by computation:
      --
      --   ⟦ (ℊ x ∙ ℊ y) ∙ ℊ z ⟧ ⟨$⟩ ρ  ≡  (ρ x · ρ y) · ρ z
      --   ⟦ ℊ x ∙ (ℊ y ∙ ℊ z) ⟧ ⟨$⟩ ρ  ≡  ρ x · (ρ y · ρ z)
      --
      -- so the supplied propositional associativity proof
      -- discharges the obligation directly.
      thm : 𝑨 ⊨ Th-Semigroup
      thm assoc ρ = ·-assoc (ρ x) (ρ y) (ρ z)
```

--------------------------------------

<span style="float:left;">[← Classical.Structures](Classical.Structures.html)</span>
<span style="float:right;">[Classical.Bundles.Semigroup →](Classical.Bundles.Semigroup.html)</span>

{% include UALib.Links.md %}
