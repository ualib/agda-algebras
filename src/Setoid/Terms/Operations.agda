
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms.Operations {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive    using ()  renaming ( Set to Type )
open import Data.Product      using ( _,_ )
open import Function.Base     using ( _∘_ )
open import Function.Bundles  using ()         renaming ( Func to _⟶_ )
open import Level             using ( Level )
open import Relation.Binary   using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open  import Overture                         using ( ∣_∣ ; ∥_∥ )
open  import Base.Terms               {𝑆 = 𝑆} using ( Term )
open  import Setoid.Algebras          {𝑆 = 𝑆} using ( Algebra ; _̂_ ; ov ; ⨅ )
open  import Setoid.Homomorphisms     {𝑆 = 𝑆} using ( hom ; IsHom )
open  import Setoid.Terms.Properties  {𝑆 = 𝑆} using ( free-lift )
open  import Setoid.Terms.Basic       {𝑆 = 𝑆}
      using ( module Environment ; 𝑻 ; _≐_ ; ≐-isRefl )

open Term
open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
 α ρᵃ β ρᵇ ρ χ ι : Level
 X : Type χ

module _ {𝑨 : Algebra α ρᵃ} where
 open Algebra 𝑨      using ( Interp )      renaming (Domain to A )
 open Setoid A       using ( _≈_ ; refl )  renaming ( Carrier to ∣A∣ )
 open Environment 𝑨  using ( ⟦_⟧ )

 free-lift-interp :  (η : X → ∣A∣)(p : Term X)
  →                  ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p

 free-lift-interp η (ℊ x) = refl
 free-lift-interp η (node f t) = cong Interp (≡.refl , (free-lift-interp η) ∘ t)

module _ {X : Type χ} where
 open Algebra (𝑻 X)      using ( Interp )      renaming (Domain to TX )
 open Setoid TX          using ( _≈_ ; refl )  renaming ( Carrier to ∣TX∣ )
 open Environment (𝑻 X)  using ( ⟦_⟧ ; ≐→Equal )
 open SetoidReasoning TX

 term-interp :  (f : ∣ 𝑆 ∣){s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → s i ≐ t i)
  →             ∀ η → ⟦ node f s ⟧ ⟨$⟩ η ≈ ⟦ node f t ⟧ ⟨$⟩ η -- (f ̂ 𝑻 X) t

 term-interp f {s}{t} st η = cong Interp (≡.refl , λ i → ≐→Equal (s i) (t i) (st i) η )

 term-agreement : (p : Term X) → p ≈ ⟦ p ⟧ ⟨$⟩ ℊ
 term-agreement (ℊ x) = refl
 term-agreement (node f t) = cong Interp (≡.refl , (λ i → term-agreement (t i)))

module _ {X : Type χ }{I : Type ι}(𝒜 : I → Algebra α ρᵃ) where
 open Algebra (⨅ 𝒜)      using (Interp)  renaming ( Domain to ⨅A )
 open Setoid ⨅A          using ( _≈_ ; refl )
 open Environment (⨅ 𝒜)  using ()        renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment        using ( ⟦_⟧ ; ≐→Equal )

 interp-prod :  (p : Term X)
  →             ∀ ρ → ⟦ p ⟧₁ ⟨$⟩ ρ ≈ (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (ρ x) i))

 interp-prod (ℊ x) = λ ρ i → ≐→Equal (𝒜 i) (ℊ x) (ℊ x) ≐-isRefl λ x' → (ρ x) i
 interp-prod (node f t) = λ ρ i → cong Interp (≡.refl , (λ j k → interp-prod (t j) ρ k)) i

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Algebra 𝑨      using () renaming (Domain to A ; Interp to Interp₁ )
 open Setoid A       using () renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣ )
 open Algebra 𝑩      using () renaming (Domain to B ; Interp to Interp₂ )
 open Setoid B       using ( _≈_ ; sym ; refl )
 open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment 𝑩  using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
 open SetoidReasoning B
 open IsHom

 private
  hfunc = ∣ hh ∣
  h = _⟨$⟩_ hfunc

 comm-hom-term :  (t : Term X) (a : X → ∣A∣)
  →               h (⟦ t ⟧₁ ⟨$⟩ a) ≈ ⟦ t ⟧₂ ⟨$⟩ (h ∘ a)

 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a = goal
  where
  goal : h (⟦ node f t ⟧₁ ⟨$⟩ a) ≈ (⟦ node f t ⟧₂ ⟨$⟩ (h ∘ a))
  goal = begin
   h (⟦ node f t ⟧₁ ⟨$⟩ a)             ≈⟨ (compatible ∥ hh ∥) ⟩
   (f ̂ 𝑩)(λ i → h (⟦ t i ⟧₁ ⟨$⟩ a))    ≈⟨ cong Interp₂ (≡.refl , λ i → comm-hom-term (t i) a) ⟩
   (f ̂ 𝑩)(λ i → ⟦ t i ⟧₂ ⟨$⟩ (h ∘ a))  ≈⟨ refl ⟩
   (⟦ node f t ⟧₂ ⟨$⟩ (h ∘ a))         ∎

_[_]s : {χ : Level}{X Y : Type χ} → Term Y → (Y → X) → Term X
(ℊ y) [ σ ]s = ℊ (σ y)
(node f t)  [ σ ]s = node f λ i → t i [ σ ]s

Substerm : (X Y : Type χ) → Type (ov χ)
Substerm X Y = (y : Y) → Term X

_[_]t : {X Y : Type χ } → Term Y → Substerm X Y → Term X
(ℊ y) [ σ ]t = σ y
(node f t) [ σ ]t = node f (λ z → (t z) [ σ ]t )

