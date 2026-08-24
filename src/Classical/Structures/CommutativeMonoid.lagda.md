---
layout: default
file: "src/Classical/Structures/CommutativeMonoid.lagda.md"
title: "Classical.Structures.CommutativeMonoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Commutative Monoids

This is the [Classical.Structures.CommutativeMonoid][] module of the [Agda Universal Algebra Library][].

`Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-CommutativeMonoid` over `Sig-Monoid`.  An equation-only
extension of Monoid: `commutativeMonoid→monoid` is a pure theory-reindex, and
`CommutativeMonoid-Op` inherits `_∙_`, `ε`, and all three monoid laws through it,
adding `comm-law`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.CommutativeMonoid where

open import Agda.Primitive                          using () renaming ( Set to Type )

open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

open import Classical.Signatures.Monoid            using ( Sig-Monoid )
open import Classical.Structures.Monoid            using ( Monoid ; module Monoid-Op ; opsToBareMonoid )
open import Classical.Theories.Monoid              using ( assoc ; idˡ ; idʳ )
open import Classical.Theories.CommutativeMonoid   using ( Eq-CommutativeMonoid ; Th-CommutativeMonoid ; comm )
                                                   renaming ( assoc to assocᶜ ; idˡ to idˡᶜ ; idʳ to idʳᶜ )
open import Overture.Terms {𝑆 = Sig-Monoid}        using (Term ; ℊ )
open import Setoid.Algebras.Basic using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Varieties.EquationalLogic using ( _⊧_≈_ )

private variable α ρ : Level
```
-->

#### Satisfaction predicate and the `CommutativeMonoid` type

```agda
infix 4 _⊨ᶜᵐᵒ_
_⊨ᶜᵐᵒ_ : (𝑨 : Algebra {𝑆 = Sig-Monoid} α ρ) (ℰ : Eq-CommutativeMonoid → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᶜᵐᵒ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

CommutativeMonoid : (α ρ : Level) → Type (suc α ⊔ suc ρ)
CommutativeMonoid α ρ = Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Monoid} α ρ ] 𝑨 ⊨ᶜᵐᵒ Th-CommutativeMonoid
```

#### The forgetful projection to monoids

`commutativeMonoid→monoid`{.AgdaFunction} keeps the algebra and discards
commutativity.  Because a commutative monoid is a monoid with an extra *equation*
rather than an extra operation, the signature does not change and no reduct is
needed; what the function does is re-index the satisfaction witness, mapping each
constructor of `Eq-Monoid`{.AgdaDatatype} to its counterpart in
`Eq-CommutativeMonoid`{.AgdaDatatype}.  The `λ { assoc → mod assocᶜ ; … }` clause is
exactly that renaming, and it is the cheap case of the pattern: contrast
`monoid→semigroup`{.AgdaFunction} of [Classical.Structures.Monoid][], which must
reduct and re-prove.

```agda
commutativeMonoid→monoid : CommutativeMonoid α ρ → Monoid α ρ
commutativeMonoid→monoid (𝑨 , mod) = 𝑨 , λ { assoc → mod assocᶜ
                                           ; idˡ   → mod idˡᶜ
                                           ; idʳ   → mod idʳᶜ }
```

#### The `CommutativeMonoid-Op` module

`CommutativeMonoid-Op 𝑪`{.AgdaModule} inherits the whole monoid interface through the
forgetful — `_∙_`{.AgdaFunction}, `ε`{.AgdaFunction}, the congruence, both
containment lemmas and all three laws — and adds exactly one accessor of its own.
`equations`{.AgdaFunction} is the new satisfaction witness, and
`comm-law`{.AgdaFunction} is commutativity in curried form.

That single addition is the point of the idiom: the inherited names are re-exported
rather than restated, so opening this module gives the full monoid vocabulary plus
commutativity, and the only proof written here is the one genuinely new law.  Its
proof also shows why the containment lemmas were worth naming: `comm-law` is
`equations comm` with `interp-node-∙`{.AgdaFunction} applied on each side.

```agda
module CommutativeMonoid-Op {α ρ : Level} (𝑪 : CommutativeMonoid α ρ) where
  private 𝑨 = proj₁ 𝑪
  open Setoid 𝔻[ 𝑨 ]

  open Monoid-Op (commutativeMonoid→monoid 𝑪) public
    using ( _∙_ ; ε ; ∙-cong ; interp-node-∙ ; interp-node-ε
          ; assoc-law ; idˡ-law ; idʳ-law )

  equations : 𝑨 ⊨ᶜᵐᵒ Th-CommutativeMonoid
  equations = proj₂ 𝑪

  comm-law : ∀ x y → x ∙ y ≈ y ∙ x
  comm-law x y = trans (sym (interp-node-∙ (ℊ 0F) (ℊ 1F) {η}))
                       (trans (equations comm η) (interp-node-∙ (ℊ 1F) (ℊ 0F) {η}))
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → y ; 2F → x }
```

#### `eqsToCommutativeMonoid`

`eqsToCommutativeMonoid`{.AgdaFunction} is the constructor a downstream user calls.
It takes the raw data — a carrier, a binary operation, an identity element — and the
four laws as *propositional* equations, and returns a `CommutativeMonoid α α`.

The four proof obligations discharge by direct evaluation rather than by reasoning.
Under `≡.setoid A` the setoid equality is propositional equality, and the
interpretation of each term in `opsToBareMonoid`{.AgdaFunction} reduces
definitionally to the corresponding application of `_·_`, so each clause is just the
supplied law applied to the right environment components.  Factoring through
`opsToBareMonoid`{.AgdaFunction} is also what makes the forgetful-agreement criterion
of ADR-002 discharge by `refl`.

```agda
eqsToCommutativeMonoid : (A : Type α) (_·_ : A → A → A) (e : A)
  → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  → (·-idˡ : ∀ a → e · a ≡ a) (·-idʳ : ∀ a → a · e ≡ a)
  → (·-comm : ∀ a b → a · b ≡ b · a)
  → CommutativeMonoid α α
eqsToCommutativeMonoid A _·_ e ·-assoc ·-idˡ ·-idʳ ·-comm = opsToBareMonoid _·_ e , proof
  where
  proof : opsToBareMonoid _·_ e ⊨ᶜᵐᵒ Th-CommutativeMonoid
  proof assocᶜ ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof idˡᶜ   ρ = ·-idˡ   (ρ 0F)
  proof idʳᶜ   ρ = ·-idʳ   (ρ 0F)
  proof comm   ρ = ·-comm  (ρ 0F) (ρ 1F)
```
