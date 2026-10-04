{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Compose where

open import Function.Bundles            using ( Func )
open import Level                       using ( Level )
open import Relation.Binary             using ( Setoid )

open import Overture                    using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )
open import Setoid.Algebras             using ( Algebra ; _^_ ; 𝔻[_] )
open import Setoid.Functions            using ( _⊙_ )
open import Setoid.Homomorphisms.Basic  using ( IsHom )

open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  α β γ ρᵃ ρᵇ ρᶜ : Level
  𝑆 : Signature 𝓞 𝓥

module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where
  open Setoid 𝔻[ 𝑪 ] using ( _≈_ ; trans )
  open IsHom

  -- The composite of two homomorphisms is a homomorphism.
  ⊙-is-hom : {g : Func 𝔻[ 𝑨 ] 𝔻[ 𝑩 ]} {h : Func 𝔻[ 𝑩 ] 𝔻[ 𝑪 ]}
    → IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⊙ g)
  ⊙-is-hom {g} {h} ghom hhom .compatible {f} {a} = trans (cong h (compatible ghom)) (compatible hhom)
