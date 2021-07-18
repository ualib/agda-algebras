---
layout: default
title : Subalgebras.Properties module (The Agda Universal Algebra Library)
date : 2021-07-18
author: [agda-algebras development team][]
---

### Properties of the Subalgebra inclusion relation

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Subalgebras.Properties {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Builtin.Equality using ( _≡_ ; refl )
open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product          using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base         using ( _∘_ ; id )
open import Function.Bundles      using ( Injection )
open import Relation.Unary        using ( Pred ; _⊆_ )
import Relation.Binary.PropositionalEquality as PE

-- -- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Overture.Inverses                  using (  id-is-injective ; ∘-injective ; IsInjective )
open import Algebras.Basic                     using ( Algebra ; Lift-Alg )
open import Algebras.Products          {𝑆 = 𝑆} using ( ov )
open import Homomorphisms.Basic        {𝑆 = 𝑆} using ( ∘-hom ; is-homomorphism ; ∘-is-hom )
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅toInjective ; ≅fromInjective ; ≅-refl
                                                     ; ≅-sym ; ≅-trans ; Lift-≅ ; mkiso )
open import Subalgebras.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; _≥_ ; _IsSubalgebraOfClass_ )

private variable α β γ 𝓧 : Level


-- The subalgebra relation is a *preorder*, i.e., a reflexive transitive binary relation.

open _≅_
≅→≤ : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≅→≤ φ = (to φ) , ≅toInjective φ

≅→≥ : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≅→≥ φ = (from φ) , ≅fromInjective φ


≤-reflexive : (𝑨 : Algebra α 𝑆) → 𝑨 ≤ 𝑨
≤-reflexive 𝑨 = (id , λ 𝑓 𝑎 → refl) , Injection.injective id-is-injective

≤-refl : {𝑨 : Algebra α 𝑆} {𝑩 : Algebra β 𝑆} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≤-refl A≅B = ≅→≤ A≅B

≥-refl : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≥-refl A≅B = ≅→≤ (≅-sym A≅B)

≤-trans : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
 →        𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪

≤-trans 𝑨 {𝑩} 𝑪 A≤B B≤C = (∘-hom 𝑨 𝑪 ∣ A≤B ∣ ∣ B≤C ∣) , ∘-injective ∥ A≤B ∥ ∥ B≤C ∥


≥-trans : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
 →        𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪

≥-trans 𝑨 {𝑩} 𝑪 A≥B B≥C = ≤-trans 𝑪 {𝑩} 𝑨 B≥C A≥B


module _ {α β ρ : Level} where

 open import Relation.Binary.Structures {a = (ov α)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α)} (_≅_ {α}{α})

 open IsPreorder
 ≤-preorder : IsPreorder _≤_
 isEquivalence ≤-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≤-preorder = ≤-refl
 trans ≤-preorder {𝑨}{𝑩}{𝑪} A≤B B≤C = ≤-trans 𝑨 {𝑩} 𝑪 A≤B B≤C

open _≅_

module _ {α β γ : Level}{𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆} where

-- If two algebras are isomorphic and one of them is a subalgebra of `𝑨`, then so is the other.

 A≥B×B≅C→A≥C : 𝑨 ≥ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥ 𝑪
 A≥B×B≅C→A≥C A≥B B≅C  = ≥-trans 𝑨 {𝑩} 𝑪 A≥B (≅→≥ B≅C)

 A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 A≤B×B≅C→A≤C A≤B B≅C = ≤-trans 𝑨{𝑩} 𝑪 A≤B (≅→≤ B≅C)

 A≅B×B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪

 A≅B×B≥C→A≥C A≅B B≥C = ≥-trans 𝑨{𝑩}𝑪 (≅→≥ A≅B) B≥C

 A≅B×B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 A≅B×B≤C→A≤C A≅B B≤C = ≤-trans 𝑨{𝑩}𝑪 (≅→≤ A≅B) B≤C


open PE.≡-Reasoning
iso→injective : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
 →              (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣
iso→injective {𝑨 = 𝑨} (mkiso f g f∼g g∼f) {x} {y} fxfy =
 x                  ≡⟨ (g∼f x)⁻¹ ⟩
 (∣ g ∣ ∘ ∣ f ∣) x  ≡⟨ PE.cong ∣ g ∣ fxfy ⟩
 (∣ g ∣ ∘ ∣ f ∣) y  ≡⟨ g∼f y ⟩
 y                  ∎

≤-iso : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆}
 →      𝑪 ≅ 𝑩 → 𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑨

≤-iso 𝑨 {𝑩} {𝑪} CB BA = (g ∘ f , gfhom) , gfinj
 where
  f : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  f = ∣ to CB ∣
  g : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  g = fst ∣ BA ∣

  gfinj : IsInjective (g ∘ f)
  gfinj = ∘-injective (iso→injective CB)(∥ BA ∥)

  gfhom : is-homomorphism 𝑪 𝑨 (g ∘ f)
  gfhom = ∘-is-hom 𝑪 𝑨 {f}{g} ∥ to CB ∥ (snd ∣ BA ∣)


≤-trans-≅ : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
 →          𝑨 ≤ 𝑩 → 𝑨 ≅ 𝑪 → 𝑪 ≤ 𝑩

≤-trans-≅ 𝑨 {𝑩} 𝑪 A≤B B≅C = ≤-iso 𝑩 (≅-sym B≅C) A≤B


≤-TRANS-≅ : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
 →          𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
≤-TRANS-≅ 𝑨 𝑪 A≤B B≅C = (∘-hom 𝑨 𝑪 ∣ A≤B ∣ (to B≅C)) , Goal
 where
 Goal : IsInjective ∣ (∘-hom 𝑨 𝑪 ∣ A≤B ∣ (to B≅C)) ∣
 Goal = ∘-injective (∥ A≤B ∥)(iso→injective B≅C)


≤-mono : (𝑩 : Algebra β 𝑆){𝒦 𝒦' : Pred (Algebra α 𝑆) γ}
 →       𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

≤-mono 𝑩 KK' KB = ∣ KB ∣ , fst ∥ KB ∥ , KK' (∣ snd ∥ KB ∥ ∣) , ∥ (snd ∥ KB ∥) ∥



-- --------------------
-- Lifts of subalgebras
-- --------------------

module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)}{𝑩 : Algebra α 𝑆} where

 Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-Alg 𝑩 α) IsSubalgebraOfClass 𝒦
 Lift-is-sub (𝑨 , (sa , (KA , B≅sa))) = 𝑨 , sa , KA , ≅-trans (≅-sym Lift-≅) B≅sa


≤-Lift : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{ℓ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Alg 𝑩 ℓ
≤-Lift 𝑨 {𝑩} {ℓ} A≤B = A≤B×B≅C→A≤C {𝑩 = 𝑩} A≤B Lift-≅

≥-Lift : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{ℓ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Alg 𝑩 ℓ
≥-Lift 𝑨 {𝑩}{ℓ} A≥B = A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩 = 𝑩} A≥B Lift-≅

Lift-≤-Lift : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level) → 𝑨 ≤ 𝑩 → Lift-Alg 𝑨 ℓᵃ ≤ Lift-Alg 𝑩 ℓᵇ
Lift-≤-Lift {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ A≤B = ≥-Lift (Lift-Alg 𝑩 ℓᵇ) {𝑨} (≤-Lift 𝑨 {𝑩} A≤B)

\end{code}


---------------------------------

{% include UALib.Links.md %}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

