---
layout: default
file: "src/Overture/Signatures/Morphisms.lagda.md"
title: "Overture.Signatures.Morphisms module"
date: "2026-06-07"
author: "the agda-algebras development team"
---

### Signature morphisms and the category of signatures

This is the [Overture.Signatures.Morphisms][] module of the [Agda Universal Algebra Library][].

A *signature morphism* `𝑆₁ → 𝑆₂` is the Abbott–Altenkirch–Ghani[^1] *container morphism*,
specialized to the container `Signature = (OperationSymbolsOf ▷ ArityOf)`.  It is a pair
`(ι , κ)`: a map `ι` sending each operation symbol of `𝑆₁` to one of `𝑆₂` (covariant on
symbols), together with a family `κ` sending the arity of `ι o` back to the arity of `o`
(contravariant on positions).  These are exactly the two arguments that
[`reduct`][Setoid.Algebras.Reduct] consumes today; this module packages them as a
first-class record and assembles signatures and their morphisms into a category.

Morphism equality here is *propositional* (`_≡_`), not a hom-setoid.  Because `ι` and `κ`
are plain functions, the identity morphism is `id` on both components and composition is
ordinary function composition, so the three category laws hold *definitionally* and are
proved by `refl`: function η reduces `f ∘ id`, `id ∘ f`, and `(f ∘ g) ∘ h` to `f`, `f`,
and `f ∘ (g ∘ h)`, and record η lifts those field equalities to the morphism record.  The
`Fin n` η-gap that forces pointwise reasoning at the stdlib bundle bridges (ADR-002 §6)
does **not** arise here, because the laws compose abstract position maps rather than
normalizing `Fin`-pattern lambdas.  See ADR-006 for the decision and its rationale.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Signatures.Morphisms where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Function                               using ( id ; _∘_ )
open import Level                                  using ( _⊔_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
-- 𝓞 / 𝓥 are the canonical operation-symbol / arity level variables (ADR-005);
-- imported here, never re-declared.
open import Overture.Signatures
  using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )

private variable
  𝑆 𝑆₁ 𝑆₂ 𝑆₃ 𝑆₄ : Signature 𝓞 𝓥
```
-->

#### Signature morphisms

A `SigMorphism 𝑆₁ 𝑆₂` is a container morphism between the signatures-as-containers: the
operation-symbol map `ι` runs forwards, while for each symbol `o` the position map `κ o`
runs backwards, from the arity of `ι o` in `𝑆₂` to the arity of `o` in `𝑆₁`.  The two
signatures are fixed at a common pair of levels `(𝓞 , 𝓥)`.

```agda
record SigMorphism (𝑆₁ 𝑆₂ : Signature 𝓞 𝓥) : Type (𝓞 ⊔ 𝓥) where
  constructor mkSigMorphism
  field
    -- covariant on symbols
    ι : OperationSymbolsOf 𝑆₁ → OperationSymbolsOf 𝑆₂

    -- contravariant on positions
    κ : (o : OperationSymbolsOf 𝑆₁) → ArityOf 𝑆₂ (ι o) → ArityOf 𝑆₁ o

open SigMorphism public
```

#### Identity and composition

The identity morphism is the identity on symbols and, for each symbol, the identity on
positions.  Composition runs `ι` forwards (covariantly) and `κ` backwards (contravariantly):
to reindex a position of the composite at `o`, first pull it back through `ψ` at `ι φ o`,
then through `φ` at `o`.

```agda
id-morphism : SigMorphism 𝑆 𝑆
id-morphism = record { ι = id ; κ = λ _ → id }

infixr 9 _∘ₛ_

_∘ₛ_ : SigMorphism 𝑆₂ 𝑆₃ → SigMorphism 𝑆₁ 𝑆₂ → SigMorphism 𝑆₁ 𝑆₃
ψ ∘ₛ φ = record { ι = ι ψ ∘ ι φ ; κ = λ o → κ φ o ∘ κ ψ (ι φ o) }
```

#### The category laws

The left and right identity laws and associativity each hold by `refl`: the relevant
function compositions reduce away by η, and record η lifts the componentwise equalities to
the morphism record.  No hom-setoid and no funext are needed.[^2]

```agda
∘ₛ-identityˡ : (φ : SigMorphism 𝑆₁ 𝑆₂) → id-morphism ∘ₛ φ ≡ φ
∘ₛ-identityˡ _ = refl

∘ₛ-identityʳ : (φ : SigMorphism 𝑆₁ 𝑆₂) → φ ∘ₛ id-morphism ≡ φ
∘ₛ-identityʳ _ = refl

∘ₛ-assoc : (χ : SigMorphism 𝑆₃ 𝑆₄) (ψ : SigMorphism 𝑆₂ 𝑆₃) (φ : SigMorphism 𝑆₁ 𝑆₂)
  → (χ ∘ₛ ψ) ∘ₛ φ ≡ χ ∘ₛ (ψ ∘ₛ φ)
∘ₛ-assoc _ _ _ = refl
```

These four pieces — `SigMorphism`, `id-morphism`, `_∘ₛ_`, and the three laws — are exactly
the data of a category `Sig 𝓞 𝓥` whose objects are signatures at levels `(𝓞 , 𝓥)`,
and whose realization is self-contained (no `agda-categories` dependency for now; see ADR-006).
Bundling them into a reusable `Category` record — shared with the category of algebras — is
postponed for follow-up work.

--------------------------------------

[^1]: M. Abbott, T. Altenkirch, N. Ghani, *Containers: constructing strictly positive types*, Theoret. Comput. Sci. **342** (2005) 3–27.

[^2]: This is the result that ADR-006 records.
