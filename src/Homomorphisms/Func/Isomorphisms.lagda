---
layout: default
title : "Homomorphisms.Func.Isomoprhisms module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

#### <a id="isomorphisms-of-setoid-algebras">Isomorphisms of setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.Isomorphisms {𝑆 : Signature 𝓞 𝓥}  where

-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Agda.Primitive              using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product                using ( _,_ )
open import Function                    using ( Func )
open import Level                       using ( Level ; Lift ; lift ; lower )
open import Relation.Binary             using ( Setoid )
open import Relation.Binary.Definitions using ( Reflexive ; Sym ; Trans )

-- Imports from the Agda Universal Algebra Library -----------------------------------------
open import Overture.Preliminaries                using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries           using ( _⟶_ ; _∘_ )
open import Overture.Func.Injective               using ( IsInjective )
open import Algebras.Func.Basic           {𝑆 = 𝑆} using ( SetoidAlgebra ; Lift-Alg ; Lift-Algˡ ; Lift-Algʳ )
open import Algebras.Func.Products        {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic      {𝑆 = 𝑆} using ( hom ; IsHom )
open import Homomorphisms.Func.Properties {𝑆 = 𝑆} using ( 𝒾𝒹 ; ∘-hom ; ToLiftˡ ; FromLiftˡ
                                                        ; ToFromLiftˡ ; FromToLiftˡ ; ToLiftʳ
                                                        ; FromLiftʳ ; ToFromLiftʳ ; FromToLiftʳ )

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


open Func using ( cong ) renaming ( f to _⟨$⟩_ )
open SetoidAlgebra using ( Domain )

module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where
 open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₁_ )
 open Setoid (Domain 𝑩) using () renaming ( _≈_ to _≈₂_ )

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ) where
  constructor mkiso
  field
   to : hom 𝑨 𝑩
   from : hom 𝑩 𝑨
   to∼from : ∀ b → (∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ b)) ≈₂ b
   from∼to : ∀ a → (∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ a)) ≈₁ a

\end{code}

That is, two structures are *isomorphic* provided there are homomorphisms going back and forth between them which compose to the identity map.


#### <a id="properties-of-isomorphisms-of-setoid-algebras">Properties of isomorphism of setoid algebras</a>

\begin{code}

open _≅_

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl
 where open Setoid (Domain 𝑨) using ( refl )

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ})(_≅_{β}{ρᵇ})(_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
  where
  open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₁_ ; trans to trans₁ )
  open Setoid (Domain 𝑪) using () renaming ( _≈_ to _≈₃_ ; trans to trans₃ )

  f : hom 𝑨 𝑪
  f = ∘-hom (to ab) (to bc)
  g : hom 𝑪 𝑨
  g = ∘-hom (from bc) (from ab)

  τ : ∀ b → (∣ f ∣ ⟨$⟩ (∣ g ∣ ⟨$⟩ b)) ≈₃ b
  τ b = trans₃ (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)

  ν : ∀ a → (∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a)) ≈₁ a
  ν a = trans₁ (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)



module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} where
 open Setoid (Domain 𝑨) using ( _≈_ ; sym ; trans )

 -- The "to" map of an isomorphism is injective.
 ≅toInjective : (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣
 ≅toInjective (mkiso (f , _) (g , _) _ g∼f){a₀}{a₁} fafb = Goal
  where
  lem1 : a₀ ≈ (g ⟨$⟩ (f ⟨$⟩ a₀))
  lem1 = sym (g∼f a₀)
  lem2 : (g ⟨$⟩ (f ⟨$⟩ a₀)) ≈ (g ⟨$⟩ (f ⟨$⟩ a₁))
  lem2 = cong g fafb
  lem3 : (g ⟨$⟩ (f ⟨$⟩ a₁)) ≈ a₁
  lem3 = g∼f a₁
  Goal : a₀ ≈ a₁
  Goal = trans lem1 (trans lem2 lem3)


 -- The "from" map of an isomorphism is injective.

≅fromInjective : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}
                 (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ from φ ∣

≅fromInjective φ = ≅toInjective (≅-sym φ)

\end{code}

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of Agda's universe hierarchy.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})

 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : SetoidAlgebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ


module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}{ℓᵃ ℓᵇ : Level} where

 Lift-Alg-isoˡ : 𝑨 ≅ 𝑩 → Lift-Algˡ 𝑨 ℓᵃ ≅ Lift-Algˡ 𝑩 ℓᵇ
 Lift-Alg-isoˡ A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ˡ ) A≅B) Lift-≅ˡ

 Lift-Alg-isoʳ : 𝑨 ≅ 𝑩 →  Lift-Algʳ 𝑨 ℓᵃ ≅ Lift-Algʳ 𝑩 ℓᵇ
 Lift-Alg-isoʳ A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ʳ ) A≅B) Lift-≅ʳ


Lift-Alg-iso : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}{ℓᵃ rᵃ ℓᵇ rᵇ : Level}
 →             𝑨 ≅ 𝑩 → Lift-Alg 𝑨 ℓᵃ rᵃ ≅ Lift-Alg 𝑩 ℓᵇ rᵇ
Lift-Alg-iso {ℓᵇ = ℓᵇ} A≅B =
  ≅-trans (Lift-Alg-isoʳ{ℓᵇ = ℓᵇ}(≅-trans (Lift-Alg-isoˡ{ℓᵇ = ℓᵇ} A≅B) (≅-sym Lift-≅ˡ)))
          (Lift-Alg-isoʳ Lift-≅ˡ)

\end{code}

The lift is also associative, up to isomorphism at least.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}{ℓ₁ ℓ₂ : Level} where

 Lift-assocˡ : Lift-Algˡ 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Algˡ (Lift-Algˡ 𝑨 ℓ₁) ℓ₂
 Lift-assocˡ = ≅-trans (≅-trans (≅-sym Lift-≅ˡ) Lift-≅ˡ) Lift-≅ˡ

 Lift-assocʳ : Lift-Algʳ 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Algʳ (Lift-Algʳ 𝑨 ℓ₁) ℓ₂
 Lift-assocʳ = ≅-trans (≅-trans (≅-sym Lift-≅ʳ) Lift-≅ʳ) Lift-≅ʳ


Lift-assoc : {𝑨 : SetoidAlgebra α ρᵃ}{ℓ ρ : Level}
 →           Lift-Alg 𝑨 ℓ ρ ≅  Lift-Algʳ (Lift-Algˡ 𝑨 ℓ) ρ
Lift-assoc {𝑨 = 𝑨}{ℓ}{ρ} = ≅-trans (≅-sym Lift-≅) (≅-trans Lift-≅ˡ Lift-≅ʳ)

\end{code}

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}
         {𝒜 : I → SetoidAlgebra α ρᵃ}
         {ℬ : I → SetoidAlgebra β ρᵇ} where


 open SetoidAlgebra (⨅ 𝒜) using () renaming (Domain to ⨅A )
 open Setoid ⨅A using () renaming ( _≈_ to _≈₁_ )

 open SetoidAlgebra (⨅ ℬ) using () renaming (Domain to ⨅B )
 open Setoid ⨅B using () renaming ( _≈_ to _≈₂_ )

 open IsHom

 ⨅≅ : (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

 ⨅≅ AB = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ
  where
   ϕ : ⨅A ⟶ ⨅B
   ϕ = record { f = λ a i → ∣ to (AB i) ∣ ⟨$⟩ (a i)
              ; cong = λ a i → cong ∣ to (AB i) ∣ (a i) }

   ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom = record { compatible = λ i → compatible ∥ to (AB i) ∥
                 ; preserves≈ = λ xy i → preserves≈ ∥ to (AB i) ∥ (xy i) }

   ψ : ⨅B ⟶ ⨅A
   ψ = record { f = λ b i → ∣ from (AB i) ∣ ⟨$⟩ (b i)
              ; cong = λ b i → cong ∣ from (AB i) ∣ (b i) }

   ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom = record { compatible = λ i → compatible ∥ from (AB i) ∥
                 ; preserves≈ = λ xy i → preserves≈ ∥ from (AB i) ∥ (xy i) }

   ϕ∼ψ : ∀ b → (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) ≈₂ b
   ϕ∼ψ b = λ i → to∼from (AB i) (b i)

   ψ∼ϕ : ∀ a → (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) ≈₁ a
   ψ∼ϕ a = λ i → from∼to (AB i)(a i)

\end{code}

A nearly identical proof goes through for isomorphisms of lifted products.

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}
         {𝒜 : I → SetoidAlgebra α ρᵃ}
         {ℬ : (Lift γ I) → SetoidAlgebra β ρᵇ} where

 open SetoidAlgebra (⨅ 𝒜) using () renaming (Domain to ⨅A )
 open Setoid ⨅A using () renaming ( _≈_ to _≈₁_ )

 open SetoidAlgebra (⨅ ℬ) using () renaming (Domain to ⨅B )
 open Setoid ⨅B using () renaming ( _≈_ to _≈₂_ )
 open IsHom


 Lift-Alg-⨅≅ˡ : (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Algˡ (⨅ 𝒜) γ ≅ ⨅ ℬ

 Lift-Alg-⨅≅ˡ AB = Goal
  where
   ϕ : ⨅A ⟶ ⨅B
   ϕ = record { f = λ a i → ∣ to (AB (lower i)) ∣ ⟨$⟩ (a (lower i))
              ; cong = λ a i → cong ∣ to (AB (lower i)) ∣ (a (lower i)) }


   ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom = record { compatible = λ i → compatible ∥ to (AB (lower i)) ∥
                 ; preserves≈ = λ xy i → preserves≈ ∥ to (AB (lower i)) ∥ (xy (lower i)) }

   ψ : ⨅B ⟶ ⨅A
   ψ = record { f = λ b i → ∣ from (AB i) ∣ ⟨$⟩ (b (lift i))
              ; cong = λ b i → cong ∣ from (AB i) ∣ (b (lift i)) }

   ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom = record { compatible = λ i → compatible ∥ from (AB i) ∥
                 ; preserves≈ = λ xy i → preserves≈ ∥ from (AB i) ∥ (xy (lift i)) }

   ϕ∼ψ : ∀ b → (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) ≈₂ b
   ϕ∼ψ b = λ i → to∼from (AB (lower i)) (b i)

   ψ∼ϕ : ∀ a → (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) ≈₁ a
   ψ∼ϕ a = λ i → from∼to (AB i)(a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ

   Goal : Lift-Algˡ (⨅ 𝒜) γ ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅ˡ) A≅B

\end{code}

------------------------------

<span style="float:left;">[← Homomorphisms.Func.Factor](Homomorphisms.Func.Factor.html)</span>
<span style="float:right;">[Homomorphisms.Func.HomomorphicImages →](Homomorphisms.Func.HomomorphicImages.html)</span>

{% include UALib.Links.md %}
