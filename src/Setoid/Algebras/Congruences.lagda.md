---
layout: default
title : "Setoid.Algebras.Congruences module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

#### <a id="congruences-of-setoidalgebras">Congruences of Setoid Algebras</a>

This is the [Setoid.Algebras.Congruences][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda Standard Library ---------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Function         using ( id ; Func )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
                             renaming ( Rel to BinRel )

open import Relation.Binary.PropositionalEquality using ( refl )

-- Imports from the Agda Universal Algebras Library ------------------------------
open import Overture          using ( ∣_∣  ; ∥_∥  )
open import Legacy.Base.Relations    using ( 0[_] ; _|:_ ; Equivalence )
open import Setoid.Relations  using ( ⟪_⟫ ; _/_ ; ⟪_∼_⟫-elim )
open import Setoid.Algebras.Basic {𝑆 = 𝑆} using ( ov ; Algebra ; 𝕌[_] ; _̂_ )

private variable α ρ ℓ : Level
```


We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is *compatible* with all basic operations of `𝑨`. The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Setoid.Relations.Discrete][]).


```agda


-- Algebra compatibility with binary relation
_∣≈_ : (𝑨 : Algebra α ρ) → BinRel 𝕌[ 𝑨 ] ℓ → Type _
𝑨 ∣≈ R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R
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
probably redefine equivalence relation on setiods to be reflexive with respect to
the underying setoid equality (and not just with respect to _≡_).)


```agda


module _ (𝑨 : Algebra α ρ) where
 open Algebra 𝑨  using ()  renaming (Domain to A )
 open Setoid A   using ( _≈_ )

 record IsCongruence (θ : BinRel 𝕌[ 𝑨 ] ℓ) : Type (𝓞 ⊔ 𝓥 ⊔ ρ ⊔ ℓ ⊔ α)  where
  constructor mkcon
  field
   reflexive : ∀ {a₀ a₁} → a₀ ≈ a₁ → θ a₀ a₁
   is-equivalence : IsEquivalence θ
   is-compatible  : 𝑨 ∣≈ θ

  Eqv : Equivalence 𝕌[ 𝑨 ] {ℓ}
  Eqv = θ , is-equivalence

 open IsCongruence public

 Con : {ℓ : Level} → Type (α ⊔ ρ ⊔ ov ℓ)
 Con {ℓ} = Σ[ θ ∈ ( BinRel 𝕌[ 𝑨 ] ℓ ) ] IsCongruence θ
```


Each of these types captures what it means to be a congruence and they are
equivalent in the sense that each implies the other. One implication is the
"uncurry" operation and the other is the second projection.


```agda


IsCongruence→Con : {𝑨 : Algebra α ρ}(θ : BinRel 𝕌[ 𝑨 ] ℓ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α ρ}((θ , _) : Con 𝑨 {ℓ}) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥
```



#### <a id="quotient-algebras">Quotient algebras</a>

In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with
respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient
is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients
using this standard notation.


```agda


open Algebra  using ( Domain ; Interp )
open Setoid   using ( Carrier )
open Func     using ( cong ) renaming ( to to _⟨$⟩_ )

_╱_ : (𝑨 : Algebra α ρ) → Con 𝑨 {ℓ} → Algebra α ℓ
Domain (𝑨 ╱ θ) = 𝕌[ 𝑨 ] / (Eqv ∥ θ ∥)
(Interp (𝑨 ╱ θ)) ⟨$⟩ (f , a) = (f ̂ 𝑨) a
cong (Interp (𝑨 ╱ θ)) {f , u} {.f , v} (refl , a) = is-compatible ∥ θ ∥ f a

module _ (𝑨 : Algebra α ρ) where
 open Algebra 𝑨  using ( )      renaming (Domain to A )
 open Setoid A   using ( _≈_ )  renaming (refl to refl₁)

 _/∙_ : 𝕌[ 𝑨 ] → (θ : Con 𝑨{ℓ}) → Carrier (Domain (𝑨 ╱ θ))
 a /∙ θ = a

 /-≡ :  (θ : Con 𝑨{ℓ}){u v : 𝕌[ 𝑨 ]}
  →     ⟪ u ⟫{Eqv ∥ θ ∥} ≈ ⟪ v ⟫{Eqv ∥ θ ∥} → ∣ θ ∣ u v

 /-≡ θ {u}{v} uv = reflexive ∥ θ ∥ uv
```


--------------------------------------

<span style="float:left;">[← Setoid.Algebras.Products](Setoid.Algebras.Products.html)</span>
<span style="float:right;">[Setoid.Homomorphisms →](Setoid.Homomorphisms.html)</span>

{% include UALib.Links.md %}
