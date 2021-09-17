---
layout: default
title : "Homomorphisms.Setoid.Isomoprhisms module (The Agda Universal Algebra Library)"
date : "2021-07-11"
author: "agda-algebras development team"
---

#### <a id="isomorphisms-of-setoid-algebras">Isomorphisms of setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.Isomorphisms {𝑆 : Signature 𝓞 𝓥}  where

-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional using () renaming (Extensionality to funext )
open import Agda.Primitive              using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product                using ( _,_ ; Σ-syntax ; _×_ )
open import Function.Base               using ( _∘_ )
open import Function.Equality           using ( Π ; _⟶_ )
open import Level                       using ( Level )
open import Relation.Binary             using ( Setoid ; REL)
open import Relation.Binary.Definitions using ( Reflexive ; Sym ; Trans ; Transitive )
open import Relation.Binary.PropositionalEquality as PE using ( module ≡-Reasoning ; _≡_ )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------------
open import Overture.Preliminaries
 using ( ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; lower∼lift ; lift∼lower ) renaming ( _≈_ to _≋_ )
open import Overture.Setoid.Injective          using ( IsInjective )
open import Algebras.Setoid.Products   {𝑆 = 𝑆} using ( ⨅ )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; _̂_ ; Lift-Alg)
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; IsHom )
open import Homomorphisms.Setoid.Properties {𝑆 = 𝑆} using ( ∘-hom ; ∘-is-hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇
                                                          ;  𝓁𝒾𝒻𝓉∼𝓁ℴ𝓌ℯ𝓇 ; 𝓁ℴ𝓌ℯ𝓇∼𝓁𝒾𝒻𝓉 )

\end{code}

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of *isomorphism*.

We could define this using Sigma types, like this.

```agda
_≅_ : {α β : Level}(𝑨 : Algebra α 𝑆)(𝑩 : SetoidAlgebra β ρᵇ) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
𝑨 ≅ 𝑩 =  Σ[ f ∈ (hom 𝑨 𝑩)] Σ[ g ∈ hom 𝑩 𝑨 ] ((∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣))
```

However, with four components, an equivalent record type is easier to work with.

\begin{code}

private variable
 α ρᵃ β ρᵇ γ ρᶜ ι : Level

open SetoidAlgebra
open Setoid
open Π
record _≅_ (𝑨 : SetoidAlgebra α ρᵃ)(𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ) where
 constructor mkiso
 field
  to : hom 𝑨 𝑩
  from : hom 𝑩 𝑨
  to∼from : ∀ b → (_≈_ (Domain 𝑩)) (∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ b)) b
  from∼to : ∀ a → (_≈_ (Domain 𝑨)) (∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ a)) a

open _≅_ public

\end{code}

That is, two structures are *isomorphic* provided there are homomorphisms going back and forth between them which compose to the identity map.


#### <a id="properties-of-isomorphisms-of-setoid-algebras">Properties of isomorphism of setoid algebras</a>

\begin{code}

open Setoid

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl (Domain 𝑨)) λ a → refl (Domain 𝑨)

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ})(_≅_{β}{ρᵇ})(_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
  where
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑩 𝑪 (to ab) (to bc)
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑩 𝑨 (from bc) (from ab)

  τ : ∀ b → (_≈_ (Domain 𝑪)) (∣ f ∣ ⟨$⟩ (∣ g ∣ ⟨$⟩ b)) b
  τ b = trans (Domain 𝑪) (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)

  ν : ∀ a → (_≈_ (Domain 𝑨)) (∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a)) a
  ν a = trans (Domain 𝑨) (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} where
 open SetoidAlgebra
 open Setoid
 open Π

 private
  A = Domain 𝑨
  B = Domain 𝑩
  _≈A≈_ = _≈_ A
  _≈B≈_ = _≈_ B

 -- The "to" map of an isomorphism is injective.
 ≅toInjective : (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣
 ≅toInjective (mkiso (f , _) (g , _) _ g∼f){a₀}{a₁} fafb = Goal
  where
  lem1 : a₀ ≈A≈ (g ⟨$⟩ (f ⟨$⟩ a₀))
  lem1 = sym A (g∼f a₀)
  lem2 : (g ⟨$⟩ (f ⟨$⟩ a₀)) ≈A≈ (g ⟨$⟩ (f ⟨$⟩ a₁))
  lem2 = cong g fafb
  lem3 : (g ⟨$⟩ (f ⟨$⟩ a₁)) ≈A≈ a₁
  lem3 = g∼f a₁
  Goal : a₀ ≈A≈ a₁
  Goal = trans A lem1 (trans A lem2 lem3)


-- The "from" map of an isomorphism is injective.
≅fromInjective : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}
                 (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ from φ ∣

≅fromInjective φ = ≅toInjective (≅-sym φ)

\end{code}

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of Agda's universe hierarchy.

\begin{code}

open Level

Lift-≅ : {ℓ : Level}{𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ)
Lift-≅ {ℓ = ℓ} {𝑨} = mkiso 𝓁𝒾𝒻𝓉 𝓁ℴ𝓌ℯ𝓇 (𝓁𝒾𝒻𝓉∼𝓁ℴ𝓌ℯ𝓇{𝑨 = 𝑨}) (𝓁ℴ𝓌ℯ𝓇∼𝓁𝒾𝒻𝓉{𝑨 = 𝑨}{ℓ = ℓ})

Lift-Alg-iso : {ℓᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}
               {ℓᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}
               -----------------------------------------
 →             𝑨 ≅ 𝑩 →  Lift-Alg 𝑨 ℓᵃ ≅ Lift-Alg 𝑩 ℓᵇ

Lift-Alg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ ) A≅B) Lift-≅

\end{code}

The lift is also associative, up to isomorphism at least.

\begin{code}

Lift-Alg-assoc : (ℓ₁ ℓ₂ : Level){𝑨 : SetoidAlgebra α ρᵃ}
 →                     Lift-Alg 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Alg (Lift-Alg 𝑨 ℓ₁) ℓ₂

Lift-Alg-assoc _ _ = ≅-trans (≅-trans (≅-sym Lift-≅) Lift-≅) Lift-≅

\end{code}

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}
         {𝒜 : I → SetoidAlgebra α ρᵃ}
         {ℬ : I → SetoidAlgebra β ρᵇ} where

 open SetoidAlgebra
 open IsHom

 private
  ⨅A = Domain (⨅ 𝒜)
  ⨅B = Domain (⨅ ℬ)
  _≈⨅A≈_ = _≈_ ⨅A
  _≈⨅B≈_ = _≈_ ⨅B

 ⨅≅ : (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

 ⨅≅ AB = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ
  where
   ϕ : ⨅A ⟶ ⨅B
   ϕ = record { _⟨$⟩_ = λ a i → ∣ to (AB i) ∣ ⟨$⟩ (a i)
              ; cong = λ a i → cong ∣ to (AB i) ∣ (a i) }

   ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom = record { compatible = λ f a i → compatible ∥ to (AB i) ∥ f (λ x → a x i)
                 ; preserves≈ = λ xy i → preserves≈ ∥ to (AB i) ∥ (xy i) }

   ψ : ⨅B ⟶ ⨅A
   ψ = record { _⟨$⟩_ = λ b i → ∣ from (AB i) ∣ ⟨$⟩ (b i)
              ; cong = λ b i → cong ∣ from (AB i) ∣ (b i) }

   ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom = record { compatible = λ f b i → compatible ∥ from (AB i) ∥ f λ x → b x i
                 ; preserves≈ = λ xy i → preserves≈ ∥ from (AB i) ∥ (xy i) }

   ϕ∼ψ : ∀ b → (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) ≈⨅B≈ b
   ϕ∼ψ b = λ i → to∼from (AB i) (b i)

   ψ∼ϕ : ∀ a → (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) ≈⨅A≈ a
   ψ∼ϕ a = λ i → from∼to (AB i)(a i)

\end{code}

A nearly identical proof goes through for isomorphisms of lifted products.

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}
         {𝒜 : I → SetoidAlgebra α ρᵃ}
         {ℬ : (Lift γ I) → SetoidAlgebra β ρᵇ} where

 open SetoidAlgebra
 open IsHom

 private
  ⨅A = Domain (⨅ 𝒜)
  ⨅B = Domain (⨅ ℬ)
  _≈⨅A≈_ = _≈_ ⨅A
  _≈⨅B≈_ = _≈_ ⨅B

 open Level
 Lift-Alg-⨅≅ : (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

 Lift-Alg-⨅≅ AB = Goal
  where
   ϕ : ⨅A ⟶ ⨅B
   ϕ = record { _⟨$⟩_ = λ a i → ∣ to (AB (lower i)) ∣ ⟨$⟩ (a (lower i))
              ; cong = λ a i → cong ∣ to (AB (lower i)) ∣ (a (lower i)) }


   ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom = record { compatible = λ f a i → compatible ∥ to (AB (lower i)) ∥ f (λ x → a x (lower i))
                 ; preserves≈ = λ xy i → preserves≈ ∥ to (AB (lower i)) ∥ (xy (lower i)) }

   ψ : ⨅B ⟶ ⨅A
   ψ = record { _⟨$⟩_ = λ b i → ∣ from (AB i) ∣ ⟨$⟩ (b (lift i))
              ; cong = λ b i → cong ∣ from (AB i) ∣ (b (lift i)) }

   ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom = record { compatible = λ f b i → compatible ∥ from (AB i) ∥ f λ x → b x (lift i)
                 ; preserves≈ = λ xy i → preserves≈ ∥ from (AB i) ∥ (xy (lift i)) }

   ϕ∼ψ : ∀ b → (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) ≈⨅B≈ b
   ϕ∼ψ b = λ i → to∼from (AB (lower i)) (b i)

   ψ∼ϕ : ∀ a → (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) ≈⨅A≈ a
   ψ∼ϕ a = λ i → from∼to (AB i)(a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ

   Goal : Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}

------------------------------

<span style="float:left;">[← Homomorphisms.Setoid.Noether](Homomorphisms.Setoid.Noether.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.HomomorphicImages →](Homomorphisms.Setoid.HomomorphicImages.html)</span>

{% include UALib.Links.md %}
