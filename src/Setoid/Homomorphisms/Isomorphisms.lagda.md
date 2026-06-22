---
layout: default
title : "Setoid.Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

#### Isomorphisms of setoid algebras

This is the [Setoid.Homomorphisms.Factor][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥}  where

-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Agda.Primitive              using ()      renaming ( Set to Type )
open import Data.Product                using ( _,_ )
open import Data.Unit.Polymorphic.Base  using ()      renaming ( ⊤ to 𝟙 ; tt to ∗ )
open import Data.Unit.Base              using ( ⊤ ; tt )
open import Function                    using ( id )  renaming ( Func to _⟶_ )
open import Level                       using ( Level ; Lift ; lift ; lower ; _⊔_ )
open import Relation.Binary             using ( Setoid ; Reflexive ; Sym ; Trans )

open import Relation.Binary.PropositionalEquality as ≡ using ()

-- Imports from the Agda Universal Algebra Library -----------------------------------------
open import Overture          using ( proj₁ ; proj₂ )
open import Setoid.Functions  using ( _⊙_ ; eq ; IsInjective ; IsSurjective ; SurjInv ; SurjInvIsInverseʳ )

open import Setoid.Algebras {𝑆 = 𝑆}  using ( Algebra ; Lift-Alg ; _^_ )
                                     using ( Lift-Algˡ ; Lift-Algʳ ; ⨅ )

open import Setoid.Homomorphisms.Basic       {𝑆 = 𝑆} using  ( hom ; IsHom )
open import Setoid.Homomorphisms.Properties  {𝑆 = 𝑆} using
 ( 𝒾𝒹 ; ⊙-hom ; ToLiftˡ ; FromLiftˡ ; ToFromLiftˡ ; FromToLiftˡ
 ; ToLiftʳ ; FromLiftʳ ; ToFromLiftʳ ; FromToLiftʳ )

open _⟶_      using ( cong ) renaming ( to to _⟨$⟩_ )
open Algebra  using ( Domain ; Interp )

private variable  α ρᵃ β ρᵇ γ ρᶜ ι : Level
```


Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of *isomorphism*.

We could define this using Sigma types, like this.

    _≅_ : {α β : Level}(𝑨 : Algebra α 𝑆)(𝑩 : Algebra β ρᵇ) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
    𝑨 ≅ 𝑩 =  Σ[ f ∈ (hom 𝑨 𝑩)] Σ[ g ∈ hom 𝑩 𝑨 ] (((proj₁ f) ∘ (proj₁ g) ≈ (proj₁ (𝒾𝒹 𝑩))) × ((proj₁ g) ∘ (proj₁ f) ≈ (proj₁ (𝒾𝒹 𝑨))))

However, with four components, an equivalent record type is easier to work with.


```agda
module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid (Domain 𝑨) using ( sym ; trans ) renaming ( _≈_ to _≈₁_ )
 open Setoid (Domain 𝑩) using () renaming ( _≈_ to _≈₂_ ; sym to sym₂ ; trans to trans₂)

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ) where
  constructor mkiso
  field
   to : hom 𝑨 𝑩
   from : hom 𝑩 𝑨
   to∼from : ∀ b → ((proj₁ to) ⟨$⟩ ((proj₁ from) ⟨$⟩ b)) ≈₂ b
   from∼to : ∀ a → ((proj₁ from) ⟨$⟩ ((proj₁ to) ⟨$⟩ a)) ≈₁ a

  toIsSurjective : IsSurjective (proj₁ to)
  toIsSurjective {y} = eq ((proj₁ from) ⟨$⟩ y) (sym₂ (to∼from y))

  toIsInjective : IsInjective (proj₁ to)
  toIsInjective {x} {y} xy = Goal
   where
   ξ : (proj₁ from) ⟨$⟩ ((proj₁ to) ⟨$⟩ x) ≈₁ (proj₁ from) ⟨$⟩ ((proj₁ to) ⟨$⟩ y)
   ξ = cong (proj₁ from) xy
   Goal : x ≈₁ y
   Goal = trans (sym (from∼to x)) (trans ξ (from∼to y))


  fromIsSurjective : IsSurjective (proj₁ from)
  fromIsSurjective {y} = eq ((proj₁ to) ⟨$⟩ y) (sym (from∼to y))

  fromIsInjective : IsInjective (proj₁ from)
  fromIsInjective {x} {y} xy = Goal
   where
   ξ : (proj₁ to) ⟨$⟩ ((proj₁ from) ⟨$⟩ x) ≈₂ (proj₁ to) ⟨$⟩ ((proj₁ from) ⟨$⟩ y)
   ξ = cong (proj₁ to) xy
   Goal : x ≈₂ y
   Goal = trans₂ (sym₂ (to∼from x)) (trans₂ ξ (to∼from y))
```


That is, two structures are *isomorphic* provided there are homomorphisms going back and forth between them which compose to the identity map.


#### Properties of isomorphism of setoid algebras


```agda
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
  f = ⊙-hom (to ab) (to bc)

  g : hom 𝑪 𝑨
  g = ⊙-hom (from bc) (from ab)

  τ : ∀ b → ((proj₁ f) ⟨$⟩ ((proj₁ g) ⟨$⟩ b)) ≈₃ b
  τ b = trans₃ (cong (proj₁ (to bc)) (to∼from ab ((proj₁ (from bc)) ⟨$⟩ b))) (to∼from bc b)

  ν : ∀ a → ((proj₁ g) ⟨$⟩ ((proj₁ f) ⟨$⟩ a)) ≈₁ a
  ν a = trans₁ (cong (proj₁ (from ab)) (from∼to bc ((proj₁ (to ab)) ⟨$⟩ a))) (from∼to ab a)

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open Setoid (Domain 𝑨) using ( _≈_ ; sym ; trans )

 -- The "to" map of an isomorphism is injective.
 ≅toInjective : (φ : 𝑨 ≅ 𝑩) → IsInjective (proj₁ (to φ))
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
≅fromInjective :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}
                  (φ : 𝑨 ≅ 𝑩) → IsInjective (proj₁ (from φ))

≅fromInjective φ = ≅toInjective (≅-sym φ)
```


#### A bijective homomorphism is an isomorphism

A homomorphism that is both injective and surjective is an isomorphism.  The witness
is the surjective right inverse `g = SurjInv h`, which is a *two-sided* inverse because
`h` is injective; and `g` is again a homomorphism — to see `g (f b) ≈ f (g ∘ b)` it
suffices, by injectivity of `h`, to compare the `h`-images, where `h ∘ g` cancels.
This is the converse of `≅toInjective`/`toIsSurjective` and lets one promote a
bijective `hom` to an `_≅_` without exhibiting the inverse homomorphism by hand.


```agda
module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open Setoid (Domain 𝑨)  using ()              renaming ( Carrier to A ; _≈_ to _≈₁_ )
 open Setoid (Domain 𝑩)  using ( sym ; trans ) renaming ( Carrier to B ; _≈_ to _≈₂_ )
 open IsHom

 Bijective→≅ :  (h : hom 𝑨 𝑩) → IsInjective (proj₁ h) → IsSurjective (proj₁ h) → 𝑨 ≅ 𝑩
 Bijective→≅ h hM hE = mkiso h (g , gHom) (λ _ → invʳ) (λ _ → hM invʳ)
  where
  hf : Domain 𝑨 ⟶ Domain 𝑩
  hf = proj₁ h

  -- the surjective right inverse of h, made two-sided by injectivity
  ginv : B → A
  ginv = SurjInv hf hE

  invʳ : ∀ {b} → hf ⟨$⟩ (ginv b) ≈₂ b
  invʳ = SurjInvIsInverseʳ hf hE

  -- ginv preserves setoid equality: pull b₀ ≈ b₁ back through h and cancel h ∘ ginv
  gcong : ∀ {b₀ b₁} → b₀ ≈₂ b₁ → ginv b₀ ≈₁ ginv b₁
  gcong b₀≈b₁ = hM (trans invʳ (trans b₀≈b₁ (sym invʳ)))

  g : Domain 𝑩 ⟶ Domain 𝑨
  g = record { to = ginv ; cong = gcong }

  -- ginv is a homomorphism: compare h-images (h injective) and cancel h ∘ ginv
  gHom : IsHom 𝑩 𝑨 g
  compatible gHom {f}{b} =
   hM (trans invʳ (sym (trans (compatible (proj₂ h))
                              (cong (Interp 𝑩) (≡.refl , λ _ → invʳ)))))
```


Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic
invariant*). As our focus is universal algebra, this is important and is what
makes the lift operation a workable solution to the technical problems that arise
from the noncumulativity of Agda's universe hierarchy.


```agda
module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})

 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ


module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{ℓᵃ ℓᵇ : Level} where

 Lift-Alg-isoˡ : 𝑨 ≅ 𝑩 → Lift-Algˡ 𝑨 ℓᵃ ≅ Lift-Algˡ 𝑩 ℓᵇ
 Lift-Alg-isoˡ A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ˡ ) A≅B) Lift-≅ˡ

 Lift-Alg-isoʳ : 𝑨 ≅ 𝑩 →  Lift-Algʳ 𝑨 ℓᵃ ≅ Lift-Algʳ 𝑩 ℓᵇ
 Lift-Alg-isoʳ A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ʳ ) A≅B) Lift-≅ʳ


Lift-Alg-iso :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{ℓᵃ rᵃ ℓᵇ rᵇ : Level}
 →              𝑨 ≅ 𝑩 → Lift-Alg 𝑨 ℓᵃ rᵃ ≅ Lift-Alg 𝑩 ℓᵇ rᵇ
Lift-Alg-iso {ℓᵇ = ℓᵇ} A≅B =
  ≅-trans  (Lift-Alg-isoʳ{ℓᵇ = ℓᵇ}(≅-trans (Lift-Alg-isoˡ{ℓᵇ = ℓᵇ} A≅B) (≅-sym Lift-≅ˡ)))
           (Lift-Alg-isoʳ Lift-≅ˡ)
```


The lift is also associative, up to isomorphism at least.


```agda
module _ {𝑨 : Algebra α ρᵃ}{ℓ₁ ℓ₂ : Level} where

 Lift-assocˡ : Lift-Algˡ 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Algˡ (Lift-Algˡ 𝑨 ℓ₁) ℓ₂
 Lift-assocˡ = ≅-trans (≅-trans (≅-sym Lift-≅ˡ) Lift-≅ˡ) Lift-≅ˡ

 Lift-assocʳ : Lift-Algʳ 𝑨 (ℓ₁ ⊔ ℓ₂) ≅  Lift-Algʳ (Lift-Algʳ 𝑨 ℓ₁) ℓ₂
 Lift-assocʳ = ≅-trans (≅-trans (≅-sym Lift-≅ʳ) Lift-≅ʳ) Lift-≅ʳ

Lift-assoc :  {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level}
 →            Lift-Alg 𝑨 ℓ ρ ≅  Lift-Algʳ (Lift-Algˡ 𝑨 ℓ) ρ
Lift-assoc {𝑨 = 𝑨}{ℓ}{ρ} = ≅-trans (≅-sym Lift-≅) (≅-trans Lift-≅ˡ Lift-≅ʳ)

Lift-assoc' :  {𝑨 : Algebra α α}{β γ : Level}
 →             Lift-Alg 𝑨 (β ⊔ γ) (β ⊔ γ) ≅ Lift-Alg (Lift-Alg 𝑨 β β) γ γ
Lift-assoc'{𝑨 = 𝑨}{β}{γ} = ≅-trans (≅-sym Lift-≅) (≅-trans Lift-≅ Lift-≅)
```


Products of isomorphic families of algebras are themselves isomorphic. The proof
looks a bit technical, but it is as straightforward as it ought to be.


```agda
module _ {𝓘 : Level}{I : Type 𝓘} {𝒜 : I → Algebra α ρᵃ} {ℬ : I → Algebra β ρᵇ} where
 open Algebra (⨅ 𝒜)  using () renaming (Domain to ⨅A )
 open Setoid ⨅A      using () renaming ( _≈_ to _≈₁_ )
 open Algebra (⨅ ℬ)  using () renaming (Domain to ⨅B )
 open Setoid ⨅B      using () renaming ( _≈_ to _≈₂_ )
 open IsHom

 ⨅≅ : (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ
 ⨅≅ AB = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ
  where
   ϕ : ⨅A ⟶ ⨅B
   ϕ = record  { to = λ a i → (proj₁ (to (AB i))) ⟨$⟩ (a i)
               ; cong = λ a i → cong (proj₁ (to (AB i))) (a i)
               }

   ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom = record { compatible = λ i → compatible (proj₂ (to (AB i))) }

   ψ : ⨅B ⟶ ⨅A
   ψ = record  { to = λ b i → (proj₁ (from (AB i))) ⟨$⟩ (b i)
               ; cong = λ b i → cong (proj₁ (from (AB i))) (b i)
               }

   ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom = record { compatible = λ i → compatible (proj₂ (from (AB i))) }

   ϕ∼ψ : ∀ b → (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) ≈₂ b
   ϕ∼ψ b = λ i → to∼from (AB i) (b i)

   ψ∼ϕ : ∀ a → (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) ≈₁ a
   ψ∼ϕ a = λ i → from∼to (AB i)(a i)
```


A nearly identical proof goes through for isomorphisms of lifted products.


```agda
module _  {𝓘 : Level}{I : Type 𝓘}
          {𝒜 : I → Algebra α ρᵃ}
          {ℬ : (Lift γ I) → Algebra β ρᵇ} where

 open Algebra (⨅ 𝒜)  using () renaming (Domain to ⨅A )
 open Setoid ⨅A      using () renaming ( _≈_ to _≈₁_ )
 open Algebra (⨅ ℬ)  using () renaming (Domain to ⨅B )
 open Setoid ⨅B      using () renaming ( _≈_ to _≈₂_ )
 open IsHom

 Lift-Alg-⨅≅ˡ : (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Algˡ (⨅ 𝒜) γ ≅ ⨅ ℬ
 Lift-Alg-⨅≅ˡ AB = ≅-trans (≅-sym Lift-≅ˡ) A≅B
  where
   ϕ : ⨅A ⟶ ⨅B
   ϕ = record  { to = λ a i → (proj₁ (to (AB (lower i)))) ⟨$⟩ (a (lower i))
               ; cong = λ a i → cong (proj₁ (to (AB (lower i)))) (a (lower i))
               }

   ϕhom : IsHom (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom = record { compatible = λ i → compatible (proj₂ (to (AB (lower i)))) }

   ψ : ⨅B ⟶ ⨅A
   ψ = record  { to = λ b i → (proj₁ (from (AB i))) ⟨$⟩ (b (lift i))
               ; cong = λ b i → cong (proj₁ (from (AB i))) (b (lift i))
               }

   ψhom : IsHom (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom = record { compatible = λ i → compatible (proj₂ (from (AB i))) }

   ϕ∼ψ : ∀ b → (ϕ ⟨$⟩ (ψ ⟨$⟩ b)) ≈₂ b
   ϕ∼ψ b = λ i → to∼from (AB (lower i)) (b i)

   ψ∼ϕ : ∀ a → (ψ ⟨$⟩ (ϕ ⟨$⟩ a)) ≈₁ a
   ψ∼ϕ a = λ i → from∼to (AB i)(a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = mkiso (ϕ , ϕhom) (ψ , ψhom) ϕ∼ψ ψ∼ϕ

module _ {𝓘 : Level}{I : Type 𝓘} {𝒜 : I → Algebra α ρᵃ} where
 open IsHom
 open Algebra  using (Domain)
 open Setoid   using (_≈_ )

 ⨅≅⨅ℓ : ∀ {ℓ} → ⨅ 𝒜 ≅ ⨅ (λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ)
 ⨅≅⨅ℓ {ℓ} = mkiso (φ , φhom) (ψ , ψhom) φ∼ψ ψ∼φ
  where
  open Algebra (⨅ 𝒜)  using () renaming (Domain to ⨅A )
  open Setoid ⨅A      using () renaming ( _≈_ to _≈₁_ )

  ⨅ℓ𝒜 : Algebra _ _
  ⨅ℓ𝒜 = ⨅ (λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ)

  open Algebra ⨅ℓ𝒜 using () renaming (Domain to ⨅ℓA)

  φ : ⨅A ⟶ ⨅ℓA
  (φ ⟨$⟩ x) i = lift (x (lower i))
  cong φ x i = lift (x (lower i))
  φhom : IsHom (⨅ 𝒜) ⨅ℓ𝒜  φ
  compatible φhom i = lift refl
   where open Setoid (Domain (𝒜 (lower i))) using ( refl )

  ψ : ⨅ℓA ⟶ ⨅A
  (ψ ⟨$⟩ x) i = lower (x (lift i))
  cong ψ x i = lower (x (lift i))
  ψhom : IsHom ⨅ℓ𝒜 (⨅ 𝒜) ψ
  compatible ψhom i = refl
   where open Setoid (Domain (𝒜 i)) using ( refl )

  φ∼ψ : ∀ b i → (Domain (Lift-Alg (𝒜 (lower i)) ℓ ℓ)) ._≈_ ((φ ⟨$⟩ (ψ ⟨$⟩ b)) i) (b i)
  φ∼ψ _ i = lift (reflexive ≡.refl)
   where open Setoid (Domain (𝒜 (lower i))) using ( reflexive )

  ψ∼φ : ∀ a i → (Domain (𝒜 i)) ._≈_ ((ψ ⟨$⟩ (φ ⟨$⟩ a)) i) (a i)
  ψ∼φ _ i = (reflexive ≡.refl)
   where open Setoid (Domain (𝒜  i)) using ( reflexive )

module _ {ι : Level}{I : Type ι}{𝒜 : I → Algebra α ρᵃ} where
 open IsHom
 open Algebra  using (Domain)
 open Setoid   using (_≈_ )

 ⨅≅⨅ℓρ : ∀ {ℓ ρ} → ⨅ 𝒜 ≅ ⨅ (λ i → Lift-Alg (𝒜 i) ℓ ρ)
 ⨅≅⨅ℓρ {ℓ}{ρ} = mkiso φ ψ φ∼ψ ψ∼φ
  where
  open Algebra (⨅ 𝒜)                         using () renaming ( Domain to ⨅A )
  open Setoid ⨅A                             using () renaming ( _≈_ to _≈⨅A≈_ )
  open Algebra (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ)  using () renaming ( Domain to ⨅lA )
  open Setoid ⨅lA                            using () renaming ( _≈_ to _≈⨅lA≈_ )

  φfunc : ⨅A ⟶ ⨅lA
  (φfunc ⟨$⟩ x) i = lift (x i)
  cong φfunc x i = lift (x i)

  φhom : IsHom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ) φfunc
  compatible φhom i = refl
   where open Setoid (Domain (Lift-Alg (𝒜 i) ℓ ρ)) using ( refl )

  φ : hom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ)
  φ = φfunc , φhom

  ψfunc : ⨅lA ⟶ ⨅A
  (ψfunc ⟨$⟩ x) i = lower (x i)
  cong ψfunc x i = lower (x i)

  ψhom : IsHom (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ) (⨅ 𝒜) ψfunc
  compatible ψhom i = refl
   where open Setoid (Domain (𝒜 i)) using (refl)

  ψ : hom (⨅ λ i → Lift-Alg (𝒜 i) ℓ ρ) (⨅ 𝒜)
  ψ = ψfunc , ψhom

  φ∼ψ : ∀ b → (proj₁ φ) ⟨$⟩ ((proj₁ ψ) ⟨$⟩ b) ≈⨅lA≈ b
  φ∼ψ _ i = reflexive ≡.refl
   where open Setoid (Domain (Lift-Alg (𝒜 i) ℓ ρ)) using ( reflexive )

  ψ∼φ : ∀ a → (proj₁ ψ) ⟨$⟩ ((proj₁ φ) ⟨$⟩ a) ≈⨅A≈ a
  ψ∼φ _ = reflexive ≡.refl
   where open Setoid (Domain (⨅ 𝒜)) using ( reflexive )


module _ {ℓᵃ : Level}{I : Type ℓᵃ}{𝒜 : I → Algebra α ρᵃ}where
 open IsHom
 open Algebra  using (Domain)
 open Setoid   using (_≈_ )

 ⨅≅⨅lowerℓρ : ∀ {ℓ ρ} → ⨅ 𝒜 ≅ ⨅ λ i → Lift-Alg (𝒜 (lower{ℓ = α ⊔ ρᵃ} i)) ℓ ρ
 ⨅≅⨅lowerℓρ {ℓ}{ρ} = mkiso φ ψ φ∼ψ ψ∼φ
  where
  open Algebra (⨅ 𝒜)                               using() renaming ( Domain to ⨅A )
  open Setoid ⨅A                                   using() renaming ( _≈_ to _≈⨅A≈_ )
  open Algebra(⨅ λ i → Lift-Alg(𝒜 (lower i)) ℓ ρ)  using() renaming ( Domain to ⨅lA )
  open Setoid ⨅lA                                  using() renaming ( _≈_ to _≈⨅lA≈_ )

  φfunc : ⨅A ⟶ ⨅lA
  (φfunc ⟨$⟩ x) i = lift (x (lower i))
  cong φfunc x i = lift (x (lower i))

  φhom : IsHom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ) φfunc
  compatible φhom i = refl
   where open Setoid (Domain (Lift-Alg (𝒜 (lower i)) ℓ ρ)) using ( refl )

  φ : hom (⨅ 𝒜) (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ)
  φ = φfunc , φhom

  ψfunc : ⨅lA ⟶ ⨅A
  (ψfunc ⟨$⟩ x) i = lower (x (lift i))
  cong ψfunc x i = lower (x (lift i))

  ψhom : IsHom (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ) (⨅ 𝒜) ψfunc
  compatible ψhom i = refl
   where open Setoid (Domain (𝒜 i)) using (refl)

  ψ : hom (⨅ λ i → Lift-Alg (𝒜 (lower i)) ℓ ρ) (⨅ 𝒜)
  ψ = ψfunc , ψhom

  φ∼ψ : ∀ b → (proj₁ φ) ⟨$⟩ ((proj₁ ψ) ⟨$⟩ b) ≈⨅lA≈ b
  φ∼ψ _ i = reflexive ≡.refl
   where open Setoid (Domain (Lift-Alg (𝒜 (lower i)) ℓ ρ)) using (reflexive)

  ψ∼φ : ∀ a → (proj₁ ψ) ⟨$⟩ ((proj₁ φ) ⟨$⟩ a) ≈⨅A≈ a
  ψ∼φ _ = reflexive ≡.refl
   where open Setoid (Domain (⨅ 𝒜)) using (reflexive)

 ℓ⨅≅⨅ℓ : ∀ {ℓ} → Lift-Alg (⨅ 𝒜) ℓ ℓ ≅ ⨅ λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ
 ℓ⨅≅⨅ℓ {ℓ} = mkiso (φ , φhom) (ψ , ψhom) φ∼ψ ψ∼φ -- φ∼ψ ψ∼φ
  where
  ℓ⨅𝒜 : Algebra _ _
  ℓ⨅𝒜 = Lift-Alg (⨅ 𝒜) ℓ ℓ
  ⨅ℓ𝒜 : Algebra _ _
  ⨅ℓ𝒜 = ⨅ (λ i → Lift-Alg (𝒜 (lower{ℓ = ℓ} i)) ℓ ℓ)

  open Algebra ℓ⨅𝒜  using() renaming (Domain to ℓ⨅A )
  open Setoid ℓ⨅A   using() renaming ( _≈_ to _≈₁_ )
  open Algebra ⨅ℓ𝒜  using() renaming (Domain to ⨅ℓA)
  open Setoid ⨅ℓA   using() renaming ( _≈_ to _≈₂_ )

  φ : ℓ⨅A ⟶ ⨅ℓA
  (φ ⟨$⟩ x) i = lift ((lower x)(lower i))
  cong φ x i = lift ((lower x)(lower i))
  φhom : IsHom ℓ⨅𝒜 ⨅ℓ𝒜  φ
  compatible φhom i = lift refl
   where open Setoid (Domain (𝒜 (lower i))) using ( refl )

  ψ : ⨅ℓA ⟶ ℓ⨅A
  (ψ ⟨$⟩ x) = lift λ i → lower (x (lift i))
  cong ψ x = lift λ i → lower (x (lift i))
  ψhom : IsHom ⨅ℓ𝒜 ℓ⨅𝒜 ψ
  lower (compatible ψhom) i = refl
   where open Setoid (Domain (𝒜 i)) using ( refl )

  φ∼ψ : ∀ b → (φ ⟨$⟩ (ψ ⟨$⟩ b)) ≈₂ b
  lower (φ∼ψ _ i) = reflexive ≡.refl
   where open Setoid (Domain (𝒜 (lower i))) using ( reflexive )

  ψ∼φ : ∀ a → (ψ ⟨$⟩ (φ ⟨$⟩ a)) ≈₁ a
  lower (ψ∼φ _) i = reflexive ≡.refl
   where open Setoid (Domain (𝒜  i)) using ( reflexive )

module _ {ι : Level}{𝑨 : Algebra α ρᵃ} where
 open Algebra 𝑨                     using() renaming ( Domain to A )
 open Algebra (⨅ λ (i : 𝟙{ι}) → 𝑨)  using() renaming ( Domain to ⨅A )
 open Setoid A                      using ( refl )
 open _≅_
 open IsHom

 private
  to𝟙 : A ⟶ ⨅A
  (to𝟙 ⟨$⟩ x) ∗ = x
  cong to𝟙 xy ∗ = xy
  from𝟙 : ⨅A ⟶ A
  from𝟙 ⟨$⟩ x = x ∗
  cong from𝟙 xy = xy ∗

  to𝟙IsHom : IsHom 𝑨 (⨅ (λ _ → 𝑨)) to𝟙
  compatible to𝟙IsHom = λ _ → refl
  from𝟙IsHom : IsHom (⨅ (λ _ → 𝑨)) 𝑨 from𝟙
  compatible from𝟙IsHom = refl

 ≅⨅⁺-refl : 𝑨 ≅ ⨅ (λ (i : 𝟙) → 𝑨)
 to ≅⨅⁺-refl = to𝟙 , to𝟙IsHom
 from ≅⨅⁺-refl = from𝟙 , from𝟙IsHom
 to∼from ≅⨅⁺-refl = λ _ _ → refl
 from∼to ≅⨅⁺-refl = λ _ → refl

module _ {𝑨 : Algebra α ρᵃ} where
 open Algebra 𝑨                  using () renaming ( Domain to A )
 open Algebra (⨅ λ (i : ⊤) → 𝑨)  using () renaming ( Domain to ⨅A )
 open Setoid A                   using ( refl )
 open _≅_
 open IsHom

 private
  to⊤ : A ⟶ ⨅A
  (to⊤ ⟨$⟩ x) = λ _ → x
  cong to⊤ xy = λ _ → xy
  from⊤ : ⨅A ⟶ A
  from⊤ ⟨$⟩ x = x tt
  cong from⊤ xy = xy tt

  to⊤IsHom : IsHom 𝑨 (⨅ λ _ → 𝑨) to⊤
  compatible to⊤IsHom = λ _ → refl
  from⊤IsHom : IsHom (⨅ λ _ → 𝑨) 𝑨 from⊤
  compatible from⊤IsHom = refl

 ≅⨅-refl : 𝑨 ≅ ⨅ (λ (i : ⊤) → 𝑨)
 to ≅⨅-refl = to⊤ , to⊤IsHom
 from ≅⨅-refl = from⊤ , from⊤IsHom
 to∼from ≅⨅-refl = λ _ _ → refl
 from∼to ≅⨅-refl = λ _ → refl
```


------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.Factor](Setoid.Homomorphisms.Factor.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.HomomorphicImages →](Setoid.Homomorphisms.HomomorphicImages.html)</span>

{% include UALib.Links.md %}
