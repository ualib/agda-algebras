---
layout: default
title : Algebras.SetoidCongruences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: [the agda-algebras development team][]
---

### <a id="congruence-relations">Congruence Relations</a>
This section presents the [Algebras.Congruences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature)

module Algebras.SetoidCongruences {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Function.Bundles       using    ( Func                    )
open import Agda.Builtin.Equality  using    ( _≡_    ;  refl          )
open import Agda.Primitive         using    ( _⊔_    ;  Level         )
                                   renaming ( Set    to Type          )
open import Data.Product           using    ( _,_    ;  Σ-syntax      )
open import Relation.Binary        using    ( Setoid ;  IsEquivalence )
                                   renaming ( Rel    to BinRel        )

-- -- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries    using ( ∣_∣  ; ∥_∥  )
open import Relations.Discrete        using ( 0[_] ; _|:_ )
open import Algebras.Products {𝑆 = 𝑆} using ( ov )
open import Algebras.Setoid   {𝑆 = 𝑆} using ( Algebroid ; _̂_ ; ⟦_⟧s)

private variable α ρ ℓ : Level

\end{code}

#### Compatibility of binary relations

We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is *compatible* with all basic operations of `𝑨`. The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Relations.Discrete][]).

\begin{code}
open Setoid

_∣≈_ : (𝑨 : Algebroid α ρ) → BinRel (Carrier ∣ 𝑨 ∣) ℓ → Type _
𝑨 ∣≈ R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

\end{code}


A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of being a congruence, and we define a Sigma type (`Con`) to represent the type of congruences of a given algebra.

\begin{code}

record IsCongruence (𝑨 : Algebroid α ρ)(θ : BinRel (Carrier ∣ 𝑨 ∣) ℓ) : Type (ov ℓ ⊔ α)  where
 constructor mkcon
 field       is-equivalence : IsEquivalence θ
             is-compatible  : 𝑨 ∣≈ θ

Con : {α ρ : Level}(𝑨 : Algebroid α ρ) → {ℓ : Level} → Type _
Con 𝑨 {ℓ} = Σ[ θ ∈ ( BinRel (Carrier ∣ 𝑨 ∣) ℓ ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

IsCongruence→Con : {𝑨 : Algebroid α ρ}(θ : BinRel (Carrier ∣ 𝑨 ∣) ℓ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {ℓ : Level}{𝑨 : Algebroid α ρ}((θ , _) : Con 𝑨 {ℓ}) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

\end{code}

#### <a id="quotient-algebras">Quotient algebras</a>
In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.<sup>[1](Algebras.Congruences.html#fn1)</sup>

\begin{code}

open IsCongruence

module _ {α ρ ℓ : Level} where

 _╱_ : (𝑨 : Algebroid α ρ) → Con 𝑨 {ℓ} → Algebroid _ _

 𝑨 ╱ θ = domain            -- the domain of the quotient algebra
       , interp            -- the basic operations of the quotient algebra
  where
  open Func using ( cong ) renaming ( f to apply  )

  -- the domain of the quotient algebra
  domain : Setoid α ℓ
  domain = record { Carrier = Carrier ∣ 𝑨 ∣
              ; _≈_ = λ x y → ∣ θ ∣ x y
              ; isEquivalence = is-equivalence ∥ θ ∥
              }

  -- the basic operations of the quotient algebra
  interp : Func (⟦ 𝑆 ⟧s domain) domain
  apply interp (f , a) = (f ̂ 𝑨) a
  cong interp {f , u} {.f , v} (refl , a) = Goal
   where
   Goal : ∣ θ ∣ ((f ̂ 𝑨) u) ((f ̂ 𝑨) v)
   Goal = is-compatible ∥ θ ∥ f a


\end{code}

--------------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team






