
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} where

open  import Data.Product      using ( _,_ )
open  import Function          using ( _∘_ ; id ) renaming ( Func to _⟶_ )
open  import Level             using ( Level )
open  import Relation.Binary   using ( Setoid )
open  import Relation.Binary.PropositionalEquality as ≡ using ()

open  import Overture          using  ( ∣_∣ ; ∥_∥ )
open  import Base.Relations    using  ( kerRel ; kerRelOfEquiv )
open  import Setoid.Functions  using  ( Image_∋_ )

open  import Setoid.Algebras {𝑆 = 𝑆}
      using ( Algebra ; _̂_ ; ov ; _∣≈_ ; Con ; mkcon ; _╱_ ; IsCongruence )

open  import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}
      using ( hom ; IsHom ; epi ; IsEpi ; epi→hom )

open  import Setoid.Homomorphisms.Properties {𝑆 = 𝑆} using ( 𝒾𝒹 )

private variable  α β ρᵃ ρᵇ ℓ : Level

open Algebra  using ( Domain )
open _⟶_      using ( cong ) renaming ( to to _⟨$⟩_ )

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} (hh : hom 𝑨 𝑩) where

 open Setoid (Domain 𝑨)  renaming ( _≈_ to _≈₁_ )  using ( reflexive )
 open Algebra 𝑩          renaming (Domain to B )   using ( Interp )
 open Setoid B           renaming ( _≈_ to _≈₂_ )
                         using ( sym ; trans ; isEquivalence )
 private h = _⟨$⟩_ ∣ hh ∣

 HomKerComp : 𝑨 ∣≈ kerRel _≈₂_ h
 HomKerComp f {u}{v} kuv = Goal
  where
  fhuv : (f ̂ 𝑩)(h ∘ u) ≈₂ (f ̂ 𝑩)(h ∘ v)
  fhuv = cong Interp (≡.refl , kuv)

  lem1 : h ((f ̂ 𝑨) u) ≈₂ (f ̂ 𝑩)(h ∘ u)
  lem1 = IsHom.compatible ∥ hh ∥

  lem2 : (f ̂ 𝑩) (h ∘ v) ≈₂ h ((f ̂ 𝑨) v)
  lem2 = sym (IsHom.compatible ∥ hh ∥)

  Goal : h ((f ̂ 𝑨) u) ≈₂ h ((f ̂ 𝑨) v)
  Goal = trans lem1 (trans fhuv lem2)

 kercon : Con 𝑨
 kercon =  kerRel _≈₂_ h ,
           mkcon (λ x → cong ∣ hh ∣ x)(kerRelOfEquiv isEquivalence h)(HomKerComp)

 kerquo : Algebra α ρᵇ
 kerquo = 𝑨 ╱ kercon

ker[_⇒_]_ :  (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) → hom 𝑨 𝑩 → Algebra _ _
ker[ 𝑨 ⇒ 𝑩 ] h = kerquo h

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} (h : hom 𝑨 𝑩) where
 open IsCongruence

 πepi : (θ : Con 𝑨 {ℓ}) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = p , pepi
  where

  open Algebra (𝑨 ╱ θ)      using () renaming ( Domain to A/θ )
  open Setoid A/θ           using ( sym ; refl )
  open IsHom {𝑨 = (𝑨 ╱ θ)}  using ( compatible )

  p : (Domain 𝑨) ⟶ A/θ
  p = record { to = id ; cong = reflexive ∥ θ ∥ }

  pepi : IsEpi 𝑨 (𝑨 ╱ θ) p
  pepi = record  { isHom = record { compatible = sym (compatible ∥ 𝒾𝒹 ∥) }
                 ; isSurjective = λ {y} → Image_∋_.eq y refl
                 }

 πhom : (θ : Con 𝑨 {ℓ}) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi→hom 𝑨 (𝑨 ╱ θ) (πepi θ)

 πker : epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h)
 πker = πepi (kercon h)

 open IsCongruence

 ker-in-con : {θ : Con 𝑨 {ℓ}} → ∀ {x}{y} → ∣ kercon (πhom θ) ∣ x y →  ∣ θ ∣ x y
 ker-in-con = id

