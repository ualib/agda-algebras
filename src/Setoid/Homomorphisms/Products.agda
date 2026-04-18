
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Products {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Function         using () renaming ( Func to _⟶_ )
open import Data.Product     using ( _,_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

open import Overture         using ( ∣_∣ ; ∥_∥)
open import Setoid.Algebras {𝑆 = 𝑆}
                             using ( Algebra ; _̂_ ; ⨅ )
open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}
                             using ( hom ; IsHom ; epi )

private variable a α b β 𝓘 : Level

module _ {I : Type 𝓘}{𝑨 : Algebra a α }(ℬ : I → Algebra b β)  where
 open Algebra 𝑨      using ()        renaming ( Domain to A )
 open Algebra (⨅ ℬ)  using ()        renaming ( Domain to ⨅B )
 open _⟶_            using ( cong )  renaming ( to to _⟨$⟩_ )
 open IsHom

 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom
  where
  h : A ⟶ ⨅B
  (h ⟨$⟩ a) i = ∣ 𝒽 i ∣ ⟨$⟩ a
  cong h xy i = cong ∣ 𝒽 i ∣ xy

  hhom : IsHom 𝑨 (⨅ ℬ) h
  compatible hhom = λ i → compatible ∥ 𝒽 i ∥

 ⨅-hom : (𝒜 : I → Algebra a α) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom 𝒜 𝒽 = F , isHom
  where
  open Algebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )

  F : ⨅A ⟶ ⨅B
  (F ⟨$⟩ x) i = ∣ 𝒽 i ∣ ⟨$⟩ x i
  cong F xy i = cong ∣ 𝒽 i ∣ (xy i)

  isHom : IsHom (⨅ 𝒜) (⨅ ℬ) F
  compatible isHom i = compatible ∥ 𝒽 i ∥

 ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom i = F , isHom
  where
  open Algebra (ℬ i)  using () renaming ( Domain to Bi )
  open Setoid Bi      using () renaming ( refl to reflᵢ )

  F : ⨅B ⟶ Bi
  F ⟨$⟩ x = x i
  cong F xy = xy i

  isHom : IsHom (⨅ ℬ) (ℬ i) F
  compatible isHom {f} {a} = reflᵢ

