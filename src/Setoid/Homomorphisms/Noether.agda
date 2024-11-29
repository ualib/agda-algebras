
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

open import Data.Product     using (Σ-syntax ; _,_ )  renaming ( _×_ to _∧_ ; proj₁ to fst)
open import Function         using ( id )             renaming ( Func to _⟶_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Overture          using ( ∣_∣ ; ∥_∥ )
open import Setoid.Functions  using ( IsInjective )

open import Setoid.Algebras {𝑆 = 𝑆}               using ( Algebra ; _̂_)
open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}    using ( hom ; IsHom )
open import Setoid.Homomorphisms.Kernels {𝑆 = 𝑆}  using ( kerquo ; πker )

private variable α ρᵃ β ρᵇ γ ρᶜ ι : Level

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )
open Algebra using ( Domain )

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Algebra 𝑩 using ( Interp ) renaming ( Domain to B )
 open Setoid B using ( _≈_ ; refl ; sym ; trans ) -- renaming ( _≈_ to _≈₂_ )
 open Algebra (kerquo hh) using () renaming ( Domain to A/hKer )

 open IsHom
 private
  hfunc = ∣ hh ∣
  h = _⟨$⟩_ hfunc

 FirstHomTheorem :  Σ[ φ ∈ hom (kerquo hh) 𝑩  ]
                    ( ∀ a → h a ≈ ∣ φ ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a) )
                     ∧ IsInjective ∣ φ ∣

 FirstHomTheorem = (φ , φhom) , (λ _ → refl) , φmon
  where
  φ : A/hKer ⟶ B
  _⟨$⟩_ φ = h
  cong φ = id

  φhom : IsHom (kerquo hh) 𝑩 φ
  compatible φhom = trans (compatible ∥ hh ∥) (cong Interp (≡.refl , (λ _ → refl)))

  φmon : IsInjective φ
  φmon = id

 FirstHomUnique :  (f g : hom (kerquo hh) 𝑩)
  →                ( ∀ a →  h a ≈ ∣ f ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a) )
  →                ( ∀ a →  h a ≈ ∣ g ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a) )
  →                ∀ [a]  →  ∣ f ∣ ⟨$⟩ [a] ≈ ∣ g ∣ ⟨$⟩ [a]

 FirstHomUnique fh gh hfk hgk a = trans (sym (hfk a)) (hgk a)

