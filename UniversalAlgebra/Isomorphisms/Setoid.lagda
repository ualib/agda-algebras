---
layout: default
title : Isomoprhisms.Setoid module (The Agda Universal Algebra Library)
date : 2021-07-11
author: [agda-algebras development team][]
---

### Isomorphisms between Setoid Algebras

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Isomorphisms.Setoid {𝑆 : Signature 𝓞 𝓥}  where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional    renaming (Extensionality to funext )
open import Agda.Primitive                        using    ( _⊔_    ;   lsuc   )
                                                  renaming ( Set    to  Type      )
open import Agda.Builtin.Equality                 using    ( _≡_    ;   refl      )
open import Data.Product                          using    ( _,_    ;   Σ-syntax
                                                           ;  Σ     ;   _×_       )
                                                  renaming ( proj₁  to  fst
                                                           ; proj₂  to  snd       )
open import Level using ( Level ; Lift )
open import Function.Base                         using    ( _∘_                  )
open import Relation.Binary        using    ( Setoid ; REL)
open import Relation.Binary.PropositionalEquality as PE using    ( cong   ;   cong-app  )


-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ ; _⁻¹ ; transport ; _∙_
                                               ; lower∼lift ; lift∼lower )
                                          renaming (_≈_ to _≋_ )
open import Overture.Inverses            using (IsInjective)
open import Products.Basic       {𝑆 = 𝑆} using ( ov )
open import Products.Setoid       {𝑆 = 𝑆} using ( ⨅ )
open import Algebras.Setoid      {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; _̂_ ; Lift-SetoidAlg)
open import Homomorphisms.Setoid {𝑆 = 𝑆} using ( hom ; kercon ; ker[_⇒_]_↾_ ; ∘-hom ; 𝒾𝒹 
                                               ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-homomorphism ; ∘-is-hom ) -- ; Lift-hom)

-- private variable α ρᵃ β ρᵇ γ ρᶜ : Level

\end{code}

#### <a id="isomorphism-toolbox">Definition of isomorphism</a>

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

We could define this using Sigma types, like this.

```agda
_≅_ : {α β : Level}(𝑨 : Algebra α 𝑆)(𝑩 : SetoidAlgebra β ρᵇ) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
𝑨 ≅ 𝑩 =  Σ[ f ∈ (hom 𝑨 𝑩)] Σ[ g ∈ hom 𝑩 𝑨 ] ((∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣))
```

However, with four components, an equivalent record type is easier to work with.

\begin{code}

private variable
 α ρᵃ β ρᵇ ρ : Level

record _≅_ (𝑨 : SetoidAlgebra α ρᵃ)(𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β) where
 constructor mkiso
 field
  to : hom 𝑨 𝑩
  from : hom 𝑩 𝑨
  to∼from : ∣ to ∣ ∘ ∣ from ∣ ≋ ∣ 𝒾𝒹 𝑩 ∣
  from∼to : ∣ from ∣ ∘ ∣ to ∣ ≋ ∣ 𝒾𝒹 𝑨 ∣

open _≅_ public


IsIsomorphismREL : {α ρᵃ β ρᵇ ρ : Level}
 →                 REL (SetoidAlgebra α ρᵃ)(SetoidAlgebra β ρᵇ) ρ → Type (ov (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ))
IsIsomorphismREL {α} {ρᵃ} {β}{ρᵇ} _ = ∀{𝑨}{𝑩} → _≅_ {α} {ρᵃ} {β}{ρᵇ} 𝑨 𝑩


\end{code}

That is, two structures are **isomorphic** provided there are homomorphisms going back and forth between them which compose to the identity map.



#### Isomorphism is an equivalence relation

\begin{code}

≅-refl : {α ρᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑨
≅-refl {𝑨 = 𝑨} = record { to = 𝒾𝒹 𝑨 ; from = 𝒾𝒹 𝑨 ; to∼from = λ _ → refl ; from∼to = λ _ → refl }

≅-sym : {α ρᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}
        {β ρᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
≅-sym φ = record { to = from φ ; from = to φ ; to∼from = from∼to φ ; from∼to = to∼from φ }

≅-trans : {α ρᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}
          {β ρᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}
          {γ ρᶜ : Level}{𝑪 : SetoidAlgebra γ ρᶜ}
 →        𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

≅-trans {𝑨 = 𝑨}{ρᵇ = ρᵇ}{𝑩} {𝑪 = 𝑪} ab bc = record { to = f ; from = g ; to∼from = τ ; from∼to = ν }
 where
  f1 : hom 𝑨 𝑩
  f1 = to ab
  f2 : hom 𝑩 𝑪
  f2 = to bc
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑩 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = from bc
  g2 : hom 𝑩 𝑨
  g2 = from ab
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑩 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≋ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(to∼from ab (∣ g1 ∣ x)))∙(to∼from bc) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≋ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(from∼to bc (∣ f1 ∣ x)))∙(from∼to ab) x




-- The "to" map of an isomorphism is injective.
≅toInjective : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}
               (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣

≅toInjective (mkiso (f , _) (g , _) _ g∼f){a}{b} fafb =
 a       ≡⟨ (g∼f a)⁻¹ ⟩
 g (f a) ≡⟨ cong g fafb ⟩
 g (f b) ≡⟨ g∼f b ⟩
 b       ∎ where open PE.≡-Reasoning


-- The "from" map of an isomorphism is injective.
≅fromInjective : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}
                 (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ from φ ∣

≅fromInjective φ = ≅toInjective (≅-sym φ)




\end{code}






#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in [Overture.Lifts][].

\begin{code}

open Level

Lift-≅ : {α ρᵃ : Level}{β : Level}{𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ (Lift-SetoidAlg 𝑨 β)
Lift-≅ {β = β} {𝑨} = record { to = 𝓁𝒾𝒻𝓉 {𝑨 = 𝑨}
                              ; from = 𝓁ℴ𝓌ℯ𝓇  {𝑨 = 𝑨}
                              ; to∼from = cong-app lift∼lower
                              ; from∼to = cong-app (lower∼lift {β = β})
                              }

Lift-SetoidAlg-iso : {α ρᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}{𝓧 : Level}
               {β ρᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ}{𝓨 : Level}
               -----------------------------------------
 →             𝑨 ≅ 𝑩 → (Lift-SetoidAlg 𝑨 𝓧) ≅ (Lift-SetoidAlg 𝑩 𝓨)

Lift-SetoidAlg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅ ) A≅B) Lift-≅

\end{code}



#### Lift associativity

The lift is also associative, up to isomorphism at least.

\begin{code}

module _ {𝓘 : Level} where

  Lift-SetoidAlg-assoc : {α ρᵃ : Level}(β : Level){𝑨 : SetoidAlgebra α ρᵃ} → Lift-SetoidAlg 𝑨 (β ⊔ 𝓘) ≅ (Lift-SetoidAlg (Lift-SetoidAlg 𝑨 β) 𝓘)
  Lift-SetoidAlg-assoc β {𝑨} = ≅-trans (≅-trans Goal Lift-≅) Lift-≅
   where
   Goal : Lift-SetoidAlg 𝑨 (β ⊔ 𝓘)  ≅ 𝑨
   Goal = ≅-sym Lift-≅

  Lift-SetoidAlg-associative : {α ρᵃ : Level}(β : Level)(𝑨 : SetoidAlgebra α ρᵃ) → Lift-SetoidAlg 𝑨 (β ⊔ 𝓘) ≅ (Lift-SetoidAlg (Lift-SetoidAlg 𝑨 β) 𝓘)
  Lift-SetoidAlg-associative β 𝑨 = Lift-SetoidAlg-assoc β {𝑨}

\end{code}




#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

begin{code}

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

   -- Goal : ⨅ 𝒜 ≅ ⨅ ℬ
   -- Goal = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

\end{code}


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}{fizw : funext (𝓘 ⊔ γ) β}{fiu : funext 𝓘 α} where

  Lift-SetoidAlg-⨅≅ : {𝒜 : I → SetoidAlgebra α ρᵃ}{ℬ : (Lift γ I) → SetoidAlgebra β ρᵇ}
   →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-SetoidAlg (⨅ 𝒜) γ ≅ ⨅ ℬ

  Lift-SetoidAlg-⨅≅ {𝒜 = 𝒜}{ℬ} AB = Goal
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

   Goal : Lift-SetoidAlg (⨅ 𝒜) γ ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team














