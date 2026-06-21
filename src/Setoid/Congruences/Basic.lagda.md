---
layout: default
title : "Setoid.Congruences.Basic module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

#### Congruences of Setoid Algebras

This is the [Setoid.Congruences.Basic][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Congruences.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda Standard Library ---------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Function         using ( id ; Func )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
                             renaming ( Rel to BinRel )

open import Relation.Binary.PropositionalEquality using ( refl )

-- Imports from the Agda Universal Algebras Library ------------------------------
open import Overture          using ( proj₁  ; proj₂ ; 0[_] ; _|:_ ; Equivalence ; 0[_]IsEquivalence )
open import Setoid.Relations  using ( ⟪_⟫ ; _/_ ; ⟪_∼_⟫-elim )
open import Setoid.Algebras.Basic {𝑆 = 𝑆} using ( ov ; Algebra ; 𝔻[_] ; 𝕌[_] ; _^_ )

private variable α ρ ℓ : Level
```

We now define the predicate `_∣≈_` so that, if `𝑨` denotes an algebra and `R` a
binary relation, then `𝑨 ∣≈ R` will represent the assertion that `R` is
*compatible* with all basic operations of `𝑨`. The formal definition is immediate
since all the work is done by the relation `|:`, which we defined above (see
[Setoid.Relations.Discrete][]).

```agda
-- Algebra compatibility with binary relation
_∣≈_ : (𝑨 : Algebra α ρ) → BinRel 𝕌[ 𝑨 ] ℓ → Type _
𝑨 ∣≈ R = ∀ 𝑓 → (𝑓 ^ 𝑨) |: R
```

A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation
that is compatible with the basic operations of `𝑨`.  This concept can be
represented in a number of alternative but equivalent ways. Formally, we define a
record type (`IsCongruence`) to represent the property of being a congruence, and
we define a Sigma type (`Con`) to represent the type of congruences of a given
algebra.

Congruences should obviously contain the equality relation on the underlying
setoid. That is, they must be reflexive. Unfortunately this doesn't come for free
(e.g., as part of the definition of `IsEquivalence` on Setoid), so we must add the
field `reflexive` to the definition of `IsCongruence`. (In fact, we should
probably redefine equivalence relation on setoids to be reflexive with respect to
the underlying setoid equality (and not just with respect to _≡_).)

```agda
module _ (𝑨 : Algebra α ρ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
  record IsCongruence (θ : BinRel 𝕌[ 𝑨 ] ℓ) : Type (𝓞 ⊔ 𝓥 ⊔ ρ ⊔ ℓ ⊔ α)  where
    constructor mkcon
    field
      reflexive : ∀ {a₀ a₁} → a₀ ≈ a₁ → θ a₀ a₁
      is-equivalence : IsEquivalence θ
      is-compatible  : 𝑨 ∣≈ θ

    Eqv : Equivalence 𝕌[ 𝑨 ] {ℓ}
    Eqv = θ , is-equivalence

  open IsCongruence public

  Con : (ℓ : Level) → Type (α ⊔ ρ ⊔ ov ℓ)
  Con ℓ = Σ[ θ ∈ BinRel 𝕌[ 𝑨 ] ℓ ] IsCongruence θ
```

Each of these types captures what it means to be a congruence and they are
equivalent in the sense that each implies the other. One implication is the
"uncurry" operation and the other is the second projection.

```agda
IsCongruence→Con : {𝑨 : Algebra α ρ}(θ : BinRel 𝕌[ 𝑨 ] ℓ) → IsCongruence 𝑨 θ → Con 𝑨 ℓ
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α ρ}((θ , _) : Con 𝑨 ℓ) → IsCongruence 𝑨 θ
Con→IsCongruence (_ , p) = p
```

#### Greatest and least congruences

The greatest congruence is the total relation `1ᴬ` (which relates every pair of elements), and the least congruence is the diagonal `0ᴬ` (which relates only pairs of equal elements).  Both are congruences: they are equivalence relations, and they are compatible with every operation (trivially, since they relate all pairs or only equal pairs, respectively).

```agda
1[_] : (𝑨 : Algebra α ρ) → BinRel 𝕌[ 𝑨 ] ℓ
1[ 𝑨 ] = {!!}

𝟘[_]' : (𝑨 : Algebra α ρ) → BinRel 𝕌[ 𝑨 ] (α ⊔ ρ)
𝟘[ 𝑨 ]' = 0[ 𝕌[ 𝑨 ] ] _≈_
  where open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

𝟘[_] : (𝑨 : Algebra α ρ) → Con 𝑨 _
𝟘[ 𝑨 ] = 0[ 𝕌[ 𝑨 ] ] _≈_ , Goal
  where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; isEquivalence )
  Goal : IsCongruence 𝑨 (0[ 𝕌[ 𝑨 ] ] _≈_)
  Goal .reflexive = λ z → Level.lift z
  Goal .is-equivalence = 0[ 𝕌[ 𝑨 ] ]IsEquivalence isEquivalence
  Goal .is-compatible 𝑓 x = Level.lift {!!}
```

#### Quotient algebras

In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with
respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient
is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients
using this standard notation.

```agda
open Algebra  using ( Domain ; Interp )
open Setoid   using ( Carrier )
open Func     using ( cong ) renaming ( to to _⟨$⟩_ )

_╱_ : (𝑨 : Algebra α ρ) → Con 𝑨 ℓ → Algebra α ℓ
Domain (𝑨 ╱ θ) = 𝕌[ 𝑨 ] / (Eqv (proj₂ θ))
Interp (𝑨 ╱ θ) ⟨$⟩ (f , a) = (f ^ 𝑨) a
Interp (𝑨 ╱ θ) .cong {f , u} {.f , v} (refl , a) = is-compatible (proj₂ θ) f a

module _ (𝑨 : Algebra α ρ) where
  open Setoid 𝔻[ 𝑨 ]   using ( _≈_ )

  _/∙_ : 𝕌[ 𝑨 ] → (θ : Con 𝑨 ℓ) → 𝕌[ 𝑨 ╱ θ ]
  a /∙ θ = a

  /-≡ : (θ : Con 𝑨 ℓ){u v : 𝕌[ 𝑨 ]}
    → ⟪ u ⟫{Eqv (proj₂ θ)} ≈ ⟪ v ⟫{Eqv (proj₂ θ)} → (proj₁ θ) u v

  /-≡ θ uv = reflexive (Con→IsCongruence θ) uv
```

--------------------------------------

<span style="float:left;">[← Setoid.Algebras.Products](Setoid.Algebras.Products.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
