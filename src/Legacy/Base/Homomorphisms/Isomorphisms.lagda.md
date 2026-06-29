---
layout: default
title : "Legacy.Base.Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)"
date : "2021-07-11"
author: "agda-algebras development team"
---

### <a id="isomorphisms">Isomorphisms</a>

This is the [Legacy.Base.Homomorphisms.Isomorphisms][] module of the [Agda Universal Algebra Library][].
Here we formalize the informal notion of isomorphism between algebraic structures.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( Signature ; 𝓞 ; 𝓥 )

module Legacy.Base.Homomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥}  where

-- Imports from Agda and the Agda Standard Library -----------------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
open import Function         using ( _∘_ )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Reflexive ; Sym ; Symmetric; Trans; Transitive )

open  import Relation.Binary.PropositionalEquality as ≡
      using ( _≡_ ; module ≡-Reasoning )

open  import Axiom.Extensionality.Propositional
      using () renaming (Extensionality to funext )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Overture using ( ∣_∣ ; ∥_∥ ; _≈_ ; _∙_ ; lower∼lift ; lift∼lower )
open import Legacy.Base.Functions using ( IsInjective )

open import Legacy.Base.Algebras {𝑆 = 𝑆} using ( Algebra ; Lift-Alg ; ⨅ )

open import Legacy.Base.Homomorphisms.Basic {𝑆 = 𝑆}
 using ( hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-homomorphism )

open import Legacy.Base.Homomorphisms.Properties  {𝑆 = 𝑆}  using ( ∘-hom )
```


#### <a id="definition-of-isomorphism">Definition of isomorphism</a>

Recall, we use ``f ≈ g`` to denote the assertion that ``f`` and ``g`` are
*extensionally* (or point-wise) equal; i.e., ``∀ x, f x ≡ g x``. This notion
of equality of functions is used in the following definition of *isomorphism*
between two algebras, say, `𝑨` and `𝑩`.


```agda


record _≅_ {α b : Level}(𝑨 : Algebra α)(𝑩 : Algebra b) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ b) where
 constructor mkiso
 field
  to : hom 𝑨 𝑩
  from : hom 𝑩 𝑨
  to∼from : ∣ to ∣ ∘ ∣ from ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣
  from∼to : ∣ from ∣ ∘ ∣ to ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣

open _≅_ public
```


That is, two structures are *isomorphic* provided there are homomorphisms going back and forth between them which compose to the identity map.

We could define this using Sigma types, like this.

    _≅_ : {α b : Level}(𝑨 : Algebra α)(𝑩 : Algebra b) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ b)
    𝑨 ≅ 𝑩 =  Σ[ f ∈ (hom 𝑨 𝑩)] Σ[ g ∈ hom 𝑩 𝑨 ] ((∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣))

However, with four components, an equivalent record type is easier to work with.

#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>


```agda


private variable a b c ℓ : Level

≅-refl : Reflexive (_≅_ {a})
≅-refl {α}{𝑨} = mkiso (𝒾𝒹 𝑨) (𝒾𝒹 𝑨) (λ _ → ≡.refl) λ _ → ≡.refl

≅-sym : Sym (_≅_ {a}) (_≅_ {b})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {a})(_≅_ {b})(_≅_ {a}{ℓ})
≅-trans {ℓ = ℓ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
 where
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑪 (to ab) (to bc)
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑨 (from bc) (from ab)

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (≡.cong ∣ to bc ∣(to∼from ab (∣ from bc ∣ x)))∙(to∼from bc) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (≡.cong ∣ from ab ∣(from∼to bc (∣ to ab ∣ x)))∙(from∼to ab) x


-- The "to" map of an isomorphism is injective.
≅toInjective :  {a b : Level}{𝑨 : Algebra a}{𝑩 : Algebra b}
                (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣

≅toInjective (mkiso (f , _) (g , _) _ g∼f){a}{b} fafb =
 a        ≡⟨ ≡.sym (g∼f a) ⟩
 g (f a)  ≡⟨ ≡.cong g fafb ⟩
 g (f b)  ≡⟨ g∼f b ⟩
 b        ∎ where open ≡-Reasoning


-- The "from" map of an isomorphism is injective.
≅fromInjective :  {a b : Level}{𝑨 : Algebra a}{𝑩 : Algebra b}
                  (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ from φ ∣

≅fromInjective φ = ≅toInjective (≅-sym φ)
```



#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of Agda's universe hierarchy.


```agda


open Level

Lift-≅ : {a b : Level}{𝑨 : Algebra a} → 𝑨 ≅ (Lift-Alg 𝑨 b)
Lift-≅{b = b}{𝑨 = 𝑨} = record  { to = 𝓁𝒾𝒻𝓉 𝑨
                               ; from = 𝓁ℴ𝓌ℯ𝓇 𝑨
                               ; to∼from = ≡.cong-app lift∼lower
                               ; from∼to = ≡.cong-app (lower∼lift {b = b})
                               }

Lift-Alg-iso :  {a b : Level}{𝑨 : Algebra a}{𝓧 : Level}
                {𝑩 : Algebra b}{𝓨 : Level}
 →              𝑨 ≅ 𝑩 → (Lift-Alg 𝑨 𝓧) ≅ (Lift-Alg 𝑩 𝓨)

Lift-Alg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅) A≅B) Lift-≅
```



#### <a id="lift-associativity">Lift associativity</a>

The lift is also associative, up to isomorphism at least.


```agda


Lift-Alg-assoc :  (ℓ₁ ℓ₂ : Level) {𝑨 : Algebra a}
 →                Lift-Alg 𝑨 (ℓ₁ ⊔ ℓ₂) ≅ (Lift-Alg (Lift-Alg 𝑨 ℓ₁) ℓ₂)

Lift-Alg-assoc ℓ₁ ℓ₂ {𝑨} = ≅-trans (≅-trans Goal Lift-≅) Lift-≅
 where
 Goal : Lift-Alg 𝑨 (ℓ₁ ⊔ ℓ₂) ≅ 𝑨
 Goal = ≅-sym Lift-≅
```



#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.


```agda


module _ {a b ι : Level}{I : Type ι}{fiu : funext ι a}{fiw : funext ι b} where

  ⨅≅ :  {𝒜 : I → Algebra a}{ℬ : I → Algebra b}
   →     (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

  ⨅≅ {𝒜}{ℬ} AB = record  { to = ϕ , ϕhom ; from = ψ , ψhom
                         ; to∼from = ϕ∼ψ ; from∼to = ψ∼ϕ
                         }
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ to (AB i) ∣ (a i)

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fiw (λ i → ∥ to (AB i) ∥ 𝑓 (λ x → a x i))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ from (AB i) ∣ (b i)

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → ∥ from (AB i) ∥ 𝑓 (λ x → 𝒃 x i))

   ϕ∼ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ∼ψ 𝒃 = fiw λ i → to∼from (AB i) (𝒃 i)

   ψ∼ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ∼ϕ a = fiu λ i → from∼to (AB i)(a i)
```


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)


```agda


module _ {a b γ ι  : Level}{I : Type ι}{fizw : funext (ι ⊔ γ) b}{fiu : funext ι a} where

  Lift-Alg-⨅≅ :  {𝒜 : I → Algebra a}{ℬ : (Lift γ I) → Algebra b}
   →             (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

  Lift-Alg-⨅≅ {𝒜}{ℬ} AB = Goal
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ to (AB  (lower i)) ∣ (a (lower i))

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fizw (λ i → (∥ to (AB (lower i)) ∥) 𝑓 (λ x → a x (lower i)))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ from (AB i) ∣ (b (lift i))

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → ∥ from (AB i) ∥ 𝑓 (λ x → 𝒃 x (lift i)))

   ϕ∼ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ∼ψ 𝒃 = fizw λ i → to∼from (AB (lower i)) (𝒃 i)

   ψ∼ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ∼ϕ a = fiu λ i → from∼to (AB i) (a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = record { to = ϕ , ϕhom ; from = ψ , ψhom ; to∼from = ϕ∼ψ ; from∼to = ψ∼ϕ }

   Goal : Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅) A≅B
```
