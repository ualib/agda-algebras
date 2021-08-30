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
open import Level                       using ( Level ; Lift )
open import Relation.Binary             using ( Setoid ; REL)
open import Relation.Binary.Definitions using ( Reflexive ; Sym ; Trans ; Transitive )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong ; module ≡-Reasoning ; cong-app )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------------
open import Overture.Preliminaries
 using ( ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; lower∼lift ; lift∼lower ) renaming ( _≈_ to _≋_ )
open import Overture.Inverses                  using ( IsInjective )
open import Algebras.Setoid.Products   {𝑆 = 𝑆} using ( ⨅ )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; _̂_ ; Lift-Alg)
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆}
 using ( hom ; kercon ; ker[_⇒_]_↾_ ; ∘-hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-homomorphism ; ∘-is-hom )

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

record _≅_ (𝑨 : SetoidAlgebra α ρᵃ)(𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β) where
 constructor mkiso
 field
  to : hom 𝑨 𝑩
  from : hom 𝑩 𝑨
  to∼from : ∣ to ∣ ∘ ∣ from ∣ ≋ ∣ 𝒾𝒹 𝑩 ∣
  from∼to : ∣ from ∣ ∘ ∣ to ∣ ≋ ∣ 𝒾𝒹 𝑨 ∣

open _≅_ public

\end{code}

That is, two structures are *isomorphic* provided there are homomorphisms going back and forth between them which compose to the identity map.


#### <a id="properties-of-isomorphisms-of-setoid-algebras">Properties of isomorphism of setoid algebras</a>

\begin{code}

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso (𝒾𝒹 𝑨) (𝒾𝒹 𝑨) (λ _ → refl) λ _ → refl

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ})(_≅_{β}{ρᵇ})(_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
  where
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑩 𝑪 (to ab) (to bc)
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑩 𝑨 (from bc) (from ab)

  τ : ∣ f ∣ ∘ ∣ g ∣ ≋ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ to bc ∣(to∼from ab (∣ from bc ∣ x)))∙(to∼from bc) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≋ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ from ab ∣(from∼to bc (∣ to ab ∣ x)))∙(from∼to ab) x


-- The "to" map of an isomorphism is injective.
≅toInjective : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}
               (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣

≅toInjective (mkiso (f , _) (g , _) _ g∼f){a}{b} fafb =
 a       ≡⟨ (g∼f a)⁻¹ ⟩
 g (f a) ≡⟨ cong g fafb ⟩
 g (f b) ≡⟨ g∼f b ⟩
 b       ∎ where open ≡-Reasoning


-- The "from" map of an isomorphism is injective.
≅fromInjective : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}
                 (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ from φ ∣

≅fromInjective φ = ≅toInjective (≅-sym φ)

\end{code}

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of Agda's universe hierarchy.

\begin{code}

open Level

Lift-≅ : {ℓ : Level}{𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ)
Lift-≅ {ℓ = ℓ} {𝑨} = record { to = 𝓁𝒾𝒻𝓉 {𝑨 = 𝑨}
                              ; from = 𝓁ℴ𝓌ℯ𝓇  {𝑨 = 𝑨}
                              ; to∼from = cong-app lift∼lower
                              ; from∼to = cong-app (lower∼lift {β = ℓ})
                              }

Lift-Alg-iso : {ℓᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}
                     {ℓᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}
               -------------------------------------------------------------
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

module _ {𝓘 : Level}{I : Type 𝓘}{fiu : funext 𝓘 α}{fiw : funext 𝓘 β} where

  open SetoidAlgebra

  ⨅≅ : {𝒜 : I → SetoidAlgebra α ρᵃ}{ℬ : I → SetoidAlgebra β ρᵇ} → (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

  ⨅≅ {𝒜 = 𝒜}{ℬ} AB = record { to = ϕ , ϕhom ; from = ψ , ψhom ; to∼from = ϕ∼ψ ; from∼to = ψ∼ϕ }
   where
   ϕ : 𝕌[ ⨅ 𝒜 ]  → 𝕌[ ⨅ ℬ ]
   ϕ a i = ∣ to (AB i) ∣ (a i)

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fiw (λ i → ∥ to (AB i) ∥ 𝑓 (λ x → a x i))

   ψ : 𝕌[ ⨅ ℬ ] → 𝕌[ ⨅ 𝒜 ]
   ψ b i = ∣ from (AB i) ∣ (b i)

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → ∥ from (AB i) ∥ 𝑓 (λ x → 𝒃 x i))

   ϕ∼ψ : ϕ ∘ ψ ≋ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ∼ψ 𝒃 = fiw λ i → to∼from (AB i) (𝒃 i)

   ψ∼ϕ : ψ ∘ ϕ ≋ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ∼ϕ a = fiu λ i → from∼to (AB i)(a i)

\end{code}


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}{fizw : funext (𝓘 ⊔ γ) β}{fiu : funext 𝓘 α} where

  Lift-Alg-⨅≅ : {𝒜 : I → SetoidAlgebra α ρᵃ}{ℬ : (Lift γ I) → SetoidAlgebra β ρᵇ}
   →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

  Lift-Alg-⨅≅ {𝒜 = 𝒜}{ℬ} AB = Goal
   where
   ϕ : 𝕌[ ⨅ 𝒜 ] → 𝕌[ ⨅ ℬ ]
   ϕ a i = ∣ to (AB  (lower i)) ∣ (a (lower i))

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fizw (λ i → (∥ to (AB (lower i)) ∥) 𝑓 (λ x → a x (lower i)))

   ψ : 𝕌[ ⨅ ℬ ] → 𝕌[ ⨅ 𝒜 ]
   ψ b i = ∣ from (AB i) ∣ (b (lift i))

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → ∥ from (AB i) ∥ 𝑓 (λ x → 𝒃 x (lift i)))

   ϕ∼ψ : ϕ ∘ ψ ≋ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ∼ψ 𝒃 = fizw λ i → to∼from (AB (lower i)) (𝒃 i)

   ψ∼ϕ : ψ ∘ ϕ ≋ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ∼ϕ a = fiu λ i → from∼to (AB i) (a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = record { to = ϕ , ϕhom ; from = ψ , ψhom ; to∼from = ϕ∼ψ ; from∼to = ψ∼ϕ }

   Goal : Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}

------------------------------

<span style="float:left;">[← Homomorphisms.Setoid.Noether](Homomorphisms.Setoid.Noether.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.HomomorphicImages →](Homomorphisms.Setoid.HomomorphicImages.html)</span>

{% include UALib.Links.md %}
