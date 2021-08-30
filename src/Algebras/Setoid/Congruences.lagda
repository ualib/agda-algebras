---
layout: default
title : "Algebras.Setoid.Congruences module (The Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

#### <a id="congruences-of-setoidalgebras">Congruences of Setoid Algebras</a>

This is the [Algebras.Setoid.Congruences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature)

module Algebras.Setoid.Congruences {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda Standard Library ---------------------------------------
open import Function.Bundles      using ( Func )
open import Agda.Primitive        using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product          using ( _,_ ; Σ-syntax )
open import Relation.Binary       using ( Setoid ; IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Binary.PropositionalEquality
                                  using ( refl )

-- Imports from the Agda Universal Algebras Library ------------------------------
open import Overture.Preliminaries        using ( ∣_∣  ; ∥_∥  )
open import Relations.Discrete            using ( 0[_] ; _|:_ )
open import Algebras.Setoid.Basic {𝑆 = 𝑆} using ( ov ; SetoidAlgebra ; 𝕌[_]
                                                ; _̂_ ; Algebroid ; _∙_ )
private variable α ρ ℓ : Level

\end{code}

We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is *compatible* with all basic operations of `𝑨`. The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Relations.Discrete][]).

\begin{code}

open Setoid
open SetoidAlgebra

-- SetoidAlgebra compatibility with binary relation
_∣≈_ : (𝑨 : SetoidAlgebra α ρ) → BinRel 𝕌[ 𝑨 ] ℓ → Type _
𝑨 ∣≈ R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

-- Algebroid compatibility with binary relation
_∣≋_ : (𝑨 : Algebroid α ρ) → BinRel (Carrier ∣ 𝑨 ∣) ℓ → Type _
𝑨 ∣≋ R = ∀ 𝑓 → (𝑓 ∙ 𝑨) |: R

\end{code}


A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of being a congruence, and we define a Sigma type (`Con`) to represent the type of congruences of a given algebra.

\begin{code}

record IsCongruence (𝑨 : SetoidAlgebra α ρ)(θ : BinRel 𝕌[ 𝑨 ] ℓ) : Type (ov ℓ ⊔ α)  where
 constructor mkcon
 field       is-equivalence : IsEquivalence θ
             is-compatible  : 𝑨 ∣≈ θ

open IsCongruence public

Con : (𝑨 : SetoidAlgebra α ρ) → {ℓ : Level} → Type _
Con 𝑨 {ℓ} = Σ[ θ ∈ ( BinRel 𝕌[ 𝑨 ] ℓ ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

IsCongruence→Con : {𝑨 : SetoidAlgebra α ρ}(θ : BinRel 𝕌[ 𝑨 ] ℓ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : SetoidAlgebra α ρ}((θ , _) : Con 𝑨 {ℓ}) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

\end{code}


#### <a id="quotient-algebras">Quotient algebras</a>

In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.

\begin{code}


open Func using ( cong ) renaming ( f to _<$>_  )

_╱_ : (𝑨 : SetoidAlgebra α ρ) → Con {α}{ρ} 𝑨 {ℓ} → SetoidAlgebra _ _

Domain (𝑨 ╱ θ) = record { Carrier = 𝕌[ 𝑨 ]
                        ; _≈_ = ∣ θ ∣
                        ; isEquivalence = is-equivalence ∥ θ ∥
                        }
(Interp (𝑨 ╱ θ)) <$> (f , a) = (f ̂ 𝑨) a
cong (Interp (𝑨 ╱ θ)) {f , u} {.f , v} (refl , a) = is-compatible  ∥ θ ∥ f a

\end{code}

--------------------------------------

<span style="float:left;">[← Algebras.Setoid.Products](Algebras.Setoid.Products.html)</span>
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}
