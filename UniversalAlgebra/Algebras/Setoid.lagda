---
layout: default
title : Algebras.Basic module (Agda Universal Algebra Library)
date : 2021-04-23
author: [the ualib/agda-algebras development team][]
---

### <a id="algebras">Basic Definitions</a>

This is the [Algebras.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic

module Algebras.Setoid {𝑆 : Signature 𝓞 𝓥} where

-- -- Imports from the Agda (Builtin) and the Agda Standard Library
open import Function.Base          using    ( _on_    ; flip           )
open import Function.Bundles       using    ( Func                     )
open import Agda.Builtin.Equality  using    ( _≡_     ;   refl         )
open import Agda.Primitive         using    ( _⊔_                      )
                                   renaming ( Set     to Type          )
open import Data.Product           using    ( _,_     ;  _×_
                                            ; Σ       ;  Σ-syntax      )
                                   renaming ( proj₁   to fst
                                             ; proj₂  to snd           )
open import Level                  renaming ( suc     to lsuc          )
open import Relation.Binary.Core   using    ( _=[_]⇒_ )
open import Relation.Binary        using    ( Setoid  ;  IsEquivalence )
                                   renaming ( Rel     to BinRel        )

-- -- -- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries using ( ∥_∥ )

\end{code}

#### Models (again)

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

(This approach is inspired by the one taken, e.g., by Andreas Abel in his formalization Birkhoff's completeness theorem; see http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf.)

First we define an operator that translates an ordinary signature into a signature over a setoid domain.

\begin{code}

⟦_⟧s : {α ρ : Level} → Signature 𝓞 𝓥 → Setoid α ρ → Setoid _ _

open Setoid using    ( _≈_      ;   isEquivalence )
            renaming ( Carrier  to  ∣_∣           )

⟦ 𝑆 ⟧s ξ .∣_∣ = Σ[ f ∈ (fst 𝑆) ] ((∥ 𝑆 ∥ f) → ∣ ξ ∣)
⟦ 𝑆 ⟧s ξ ._≈_ (f , args) (f' , args') = Σ[ eq ∈ f ≡ f' ] EqArgs eq args args'
 where
 EqArgs : (eq : f ≡ f') → (∥ 𝑆 ∥ f → ∣ ξ ∣) → (∥ 𝑆 ∥ f' → ∣ ξ ∣) → Type _
 EqArgs refl args args' = (i : ∥ 𝑆 ∥ f) → ξ ._≈_ (args i) (args' i)

IsEquivalence.refl  (⟦ 𝑆 ⟧s ξ .isEquivalence)                       = refl , λ _ → Setoid.refl  ξ
IsEquivalence.sym   (⟦ 𝑆 ⟧s ξ .isEquivalence) (refl , g)            = refl , λ i → Setoid.sym   ξ (g i)
IsEquivalence.trans (⟦ 𝑆 ⟧s ξ .isEquivalence) (refl , g) (refl , h) = refl , λ i → Setoid.trans ξ (g i) (h i)

\end{code}


##### Setoid Algebra

A setoid algebra is just like an algebra but we require that all basic operations of the algebra respect the underlying setoid equality.
The `Func` record packs a function (apply) with a proof (cong) that the function respects equality.

\begin{code}

Algebroid : (α ρ : Level)(𝑆 : Signature 𝓞 𝓥) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ))
Algebroid α ρ 𝑆 = Σ[ A ∈ Setoid α ρ ]      -- the domain (a setoid)
                   Func (⟦ 𝑆 ⟧s A) A       -- the basic operations, along with proofs that each respects setoid equality

record SetoidAlgebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
  field
    Den  :  Setoid α ρ
    den  :  Func (⟦ 𝑆 ⟧s Den) Den
     --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
     --       1. a function  f : (⟦ 𝑆 ⟧s Den) .Carrier  → Den . Carrier
     --       2. a proof cong : f Preserves _≈₁_ ⟶ _≈₂_ (that f preserves the setoid equalities)


\end{code}

#### Products of SetoidAlgebras

\begin{code}

module _ {α ρ ι : Level} where

 open SetoidAlgebra
 open Func           using    ( cong                     )
                     renaming ( f             to  apply  )
 open Setoid         using    ( Carrier       ;   _≈_    )
                     renaming ( isEquivalence to  isEqv  )
 open IsEquivalence  renaming ( refl          to  reflE
                              ; sym           to  symE
                              ; trans         to  transE )

 ⨅ : {I : Type ι }(𝒜 : I → SetoidAlgebra α ρ) → SetoidAlgebra (α ⊔ ι) (ρ ⊔ ι)

 Den (⨅ {I} 𝒜) =

  record { Carrier = ∀ i → Carrier (Den (𝒜 i))

         ; _≈_ = λ a b → ∀ i → Den (𝒜 i) ._≈_ (a i) (b i)

         ; isEquivalence =
            record { refl  =     λ i → reflE  (isEqv (Den (𝒜 i)))
                   ; sym   =   λ x i → symE   (isEqv (Den (𝒜 i)))(x i)
                   ; trans = λ x y i → transE (isEqv (Den (𝒜 i)))(x i)(y i)
                   }
         }

 (den (⨅ {I} 𝒜)) .apply (f    , a    ) i = apply (den (𝒜 i)) (f    , flip a i    )
 (den (⨅ {I} 𝒜)) .cong  (refl , u'≈v') i = cong  (den (𝒜 i)) (refl , flip u'≈v' i)

\end{code}

