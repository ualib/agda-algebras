---
layout: default
title : Algebras.Basic module (Agda Universal Algebra Library)
date : 2021-04-23
author: [the agda-algebras development team][]
---

### <a id="algebras">Basic Definitions</a>

This is the [Algebras.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

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
open import Overture.Preliminaries using ( ∥_∥ ; ∣_∣ )
open import Relations.Discrete using ( _|:_)

\end{code}

#### Models (again)

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

(This approach is inspired by the one taken, e.g., by Andreas Abel in his formalization Birkhoff's completeness theorem; see http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf.)

First we define an operator that translates an ordinary signature into a signature over a setoid domain.

\begin{code}

open Setoid using    (_≈_ ; Carrier )
            renaming ( refl  to reflS
                     ; sym   to symS
                     ; trans to transS
                     ; isEquivalence to isEqv )
open Func renaming   ( f to apply )

⟦_⟧s : {α ρ : Level} → Signature 𝓞 𝓥 → Setoid α ρ → Setoid _ _

Carrier (⟦ 𝑆 ⟧s ξ) = Σ[ f ∈ ∣ 𝑆 ∣ ] ((∥ 𝑆 ∥ f) → ξ .Carrier)
_≈_ (⟦ 𝑆 ⟧s ξ) (f , u) (g , v) = Σ[ eqv ∈ f ≡ g ] EqArgs eqv u v
 where
 EqArgs : f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type _
 EqArgs refl u v = ∀ i → (_≈_ ξ) (u i) (v i)

IsEquivalence.refl  (isEqv (⟦ 𝑆 ⟧s ξ))                     = refl , λ _ → reflS  ξ
IsEquivalence.sym   (isEqv (⟦ 𝑆 ⟧s ξ))(refl , g)           = refl , λ i → symS   ξ (g i)
IsEquivalence.trans (isEqv (⟦ 𝑆 ⟧s ξ))(refl , g)(refl , h) = refl , λ i → transS ξ (g i) (h i)

\end{code}


##### Setoid Algebras

A setoid algebra is just like an algebra but we require that all basic operations of the algebra respect the underlying setoid equality.
The `Func` record packs a function (apply) with a proof (cong) that the function respects equality.

\begin{code}

Algebroid : (α ρ : Level) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ))
Algebroid α ρ = Σ[ A ∈ Setoid α ρ ]      -- the domain (a setoid)
                 Func (⟦ 𝑆 ⟧s A) A       -- the basic operations,
                                           -- along with congruence proofs that
                                           -- each operation espects setoid equality

record SetoidAlgebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
  field
    Domain : Setoid α ρ
    Interp : Func (⟦ 𝑆 ⟧s Domain) Domain
     --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
     --       1. a function  f : (⟦ 𝑆 ⟧s Den) .Carrier  → Den . Carrier
     --       2. a proof cong : f Preserves _≈₁_ ⟶ _≈₂_ (that f preserves the setoid equalities)

\end{code}

Easier notation for application of an (interpreted) operation symbol.

\begin{code}

_̂_ : {α ρ : Level} (f : ∣ 𝑆 ∣)(𝑨 : Algebroid α ρ) → (∥ 𝑆 ∥ f  →  Carrier ∣ 𝑨 ∣) → Carrier ∣ 𝑨 ∣

f ̂ 𝑨 = λ a → apply ∥ 𝑨 ∥ (f , a)

\end{code}

\end{code}

#### Products of Algebroids

\begin{code}

open Func           using    ( cong                     )
                    renaming ( f             to  apply  )
open Setoid         using    ( Carrier       ;   _≈_    )
                    renaming ( isEquivalence to  isEqv  )
open IsEquivalence  renaming ( refl          to  reflE
                             ; sym           to  symE
                             ; trans         to  transE )

module _ {α ρ ι : Level} where

 ⨅ : {I : Type ι }(𝒜 : I → Algebroid α ρ) → Algebroid (α ⊔ ι) (ρ ⊔ ι)

 ⨅ {I} 𝒜 = domain , interp-ops
  where
  domain : Setoid _ _
  domain = record { Carrier = ∀ i → Carrier ∣ 𝒜 i ∣
                  ; _≈_ = λ u v  → ∀ i → (_≈_ ∣ 𝒜 i ∣) (u i) (v i)
                  ; isEquivalence =
                     record { refl  =     λ i → reflE  (isEqv ∣ 𝒜 i ∣)
                            ; sym   =   λ x i → symE   (isEqv ∣ 𝒜 i ∣)(x i)
                            ; trans = λ u v i → transE (isEqv ∣ 𝒜 i ∣)(u i)(v i)
                            }
                  }

  interp-ops : Func (⟦ 𝑆 ⟧s domain) domain
  apply interp-ops ( f   , as ) i = apply ∥ 𝒜 i ∥ ( f   , (flip as i ))
  cong  interp-ops (refl , f=g) i = cong  ∥ 𝒜 i ∥ (refl , (flip f=g i))

\end{code}

#### Products of SetoidAlgebras

\begin{code}

module _ {α ρ ι : Level} where

 open SetoidAlgebra

 ⨅' : {I : Type ι }(𝒜 : I → SetoidAlgebra α ρ) → SetoidAlgebra (α ⊔ ι) (ρ ⊔ ι)

 Domain (⨅' {I} 𝒜) =

  record { Carrier = ∀ i → Carrier (Domain (𝒜 i))

         ; _≈_ = λ a b → ∀ i → Domain (𝒜 i) ._≈_ (a i) (b i)

         ; isEquivalence =
            record { refl  =     λ i → reflE  (isEqv (Domain (𝒜 i)))
                   ; sym   =   λ x i → symE   (isEqv (Domain (𝒜 i)))(x i)
                   ; trans = λ x y i → transE (isEqv (Domain (𝒜 i)))(x i)(y i)
                   }
         }

 (Interp (⨅' {I} 𝒜)) .apply (f    , a   ) i = apply (Interp (𝒜 i)) (f    , flip a i   )
 (Interp (⨅' {I} 𝒜)) .cong  (refl , f=g ) i = cong  (Interp (𝒜 i)) (refl , flip f=g i )

\end{code}


--------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
