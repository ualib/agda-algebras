---
layout: default
title : Terms.Setoid module (The Agda Universal Algebra Library)
date : 2021-06-28
author: [the agda-algebras development team][]
---

### Interpretation of Terms in Setoid Algebras

The approach to terms and their interpretation in this module was inspired by
Andreas Abel's proof of Birkhoff's completeness theorem.
(See http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic

module Terms.Setoid {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive         using    ( Level  ;  _⊔_  ;  lsuc  )
                                   renaming ( Set    to Type          )
open import Agda.Builtin.Equality  using    ( _≡_    ;  refl  )
open import Data.Product           using    ( _,_    ; _×_   ; Σ-syntax         )
open import Function.Bundles       using    ( Func                    )
open import Relation.Binary        using    ( Setoid ;  IsEquivalence )
open import Data.Empty.Polymorphic using    ( ⊥      ;  ⊥-elim        )
open import Data.Sum.Base          using    ( _⊎_                     )
                                   renaming ( inj₁   to inl
                                            ; inj₂   to inr           )
open import Level                 using    (  Level ; Lift   )
import Relation.Binary.PropositionalEquality as P

-- -- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries           using ( ∣_∣ ; ∥_∥ )
open import Algebras.Setoid          {𝑆 = 𝑆} using ( SetoidAlgebra )
open import Terms.Basic              {𝑆 = 𝑆} using ( Term )
open Term


private variable
 χ α ℓ : Level
 Γ Δ : Type χ

\end{code}

To obtain terms with free variables, we add nullary operations, each representing a variable.
These are covered in the std lib FreeMonad module, albeit with the restriction that the sets of
operation symbols and variable symbols have the same size.

\begin{code}

Ops : Type χ → Signature (𝓞 ⊔ χ) 𝓥
Ops X = ((∣ 𝑆 ∣ ⊎ X) , ar)
 where
 ar : ∣ 𝑆 ∣ ⊎ X → Type _
 ar (inl f) = ∥ 𝑆 ∥ f
 ar (inr x) = ⊥             -- Add a nullary operation symbol for each variable symbol.


-- Parallel substitutions. A substitution from Δ to Γ holds a term in Γ for each variable in Δ.
Sub : (Γ Δ : Type χ) → Type _
Sub Γ Δ = (x : Δ) → Term Γ


-- Application of a substitution.
_[_] : (t : Term Δ) (σ : Sub Γ Δ) → Term Γ
(ℊ x) [ σ ] = σ x
(node f ts) [ σ ] = node f (λ i → ts i [ σ ])


-- Interpretation of terms in a model.
module Environment (M : SetoidAlgebra α ℓ) where

 open SetoidAlgebra M

 open Setoid        renaming ( refl  to  reflS
                             ; sym   to  symS
                             ; trans to  transS)

 -- Equality in M's interpretation of its sort.
 _≃_ : Carrier Domain → Carrier Domain → Type ℓ
 _≃_ = Domain ._≈_
 infix -1 _≃_

 -- An environment for Γ maps each variable `x : Γ` to an element of M.
 -- Equality of environments is defined pointwise.
 Env : Type χ → Setoid _ _
 Env Γ = record { Carrier = (x : Γ) → Carrier Domain

                ; _≈_ = λ ρ ρ' → (x : Γ) → ρ x ≃ ρ' x

                ; isEquivalence =
                   record { refl = λ _ → reflS Domain
                          ; sym = λ h x → symS Domain (h x)
                          ; trans = λ g h x → transS Domain (g x) (h x)
                          }
                }



 -- Interpretation of terms is iteration on the W-type.
 -- The standard library offers `iter' (on sets), but we need this to be a Func (on setoids).
 open Func renaming ( f to _<$>_ )

 ⦅_⦆ : (t : Term Γ) → Func (Env Γ) Domain
 ⦅ ℊ x ⦆         <$> ρ =  ρ x
 ⦅ node f args ⦆  <$> ρ = Interp <$> (f , λ i → ⦅ args i ⦆ <$> ρ)
 cong  ⦅ ℊ x ⦆ ρ₁≡ρ₂ = ρ₁≡ρ₂ x
 cong  ⦅ node f args ⦆  ρ₁=ρ₂  =  cong Interp (refl , λ i → cong ⦅ args i ⦆ ρ₁=ρ₂)


 -- An equality between two terms holds in a model
 -- if the two terms are equal under all valuations of their free variables.
 Equal : ∀ {Γ : Type χ} (p q : Term Γ) → Type _
 Equal p q = ∀ (ρ : Env _ .Carrier) →  ⦅ p ⦆ <$> ρ ≃ ⦅ q ⦆ <$> ρ


 -- Equal is an equivalence relation.
 isEquiv : IsEquivalence (Equal {Γ = Γ})

 isEquiv = record { refl  =         λ ρ → reflS  Domain
                  ; sym   =     λ x=y ρ → symS   Domain (x=y ρ)
                  ; trans = λ i=j j=k ρ → transS Domain (i=j ρ) (j=k ρ)
                  }

 -- Evaluation of a substitution gives an environment.
 ⦅_⦆s : Sub Γ Δ → Carrier (Env Γ) → Carrier (Env Δ)
 ⦅ σ ⦆s ρ x = ⦅ σ x ⦆ <$> ρ


 -- Substitution lemma: ⦅t[σ]⦆ρ ≃ ⦅t⦆⦅σ⦆ρ
 substitution : (t : Term Δ) (σ : Sub Γ Δ) (ρ : Env Γ .Carrier)
  →             ⦅ t [ σ ] ⦆ <$> ρ  ≃  ⦅ t ⦆ <$> (⦅ σ ⦆s ρ)

 substitution (ℊ x) σ ρ = reflS Domain
 substitution (node f ts) σ ρ = cong Interp (refl , λ i → substitution (ts i) σ ρ)

\end{code}




-- -- The Absolutely Free Algebra (haven't gotten this to work yet)
--
-- open SetoidAlgebra
-- open Func renaming (f to apply)
-- open Setoid
-- open Level
-- 𝑻 : (X : Type χ ) → SetoidAlgebra (𝓞 ⊔ 𝓥 ⊔ lsuc χ) _
-- Carrier (Domain (𝑻 X)) = Term X
-- _≈_ (Domain (𝑻 X)) (ℊ x) (ℊ y) = Lift (𝓞 ⊔ 𝓥) (x ≡ y)
-- _≈_ (Domain (𝑻 X)) (ℊ x) (node f t) = ⊥
-- _≈_ (Domain (𝑻 X)) (node f s) (ℊ y) = ⊥
-- _≈_ (Domain (𝑻 X)) (node f s) (node g t) = Σ[ eqv ∈ f ≡ g ] (EqArgs eqv s t)
--  where
--  EqArgs : f ≡ g → (∥ 𝑆 ∥ f → Term X) → (∥ 𝑆 ∥ g → Term X) → Type _
--  EqArgs P.refl u v = ∀ i → (_≈_ (Domain (𝑻 X))) (u i) (v i)

-- isEquivalence (Domain (𝑻 X)) = {!!}
-- --  record { refl = P.refl ; sym = P.sym ; trans = P.trans }
-- apply (Interp (𝑻 X)) (f , ts) = node f ts
-- cong (Interp (𝑻 X)) {f , xs} {.f , ys} (refl , xs=ys) = {!!} -- P.cong (node f) (cong (Interp {!𝑻 X!}) {!!})


--------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
