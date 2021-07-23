---
layout: default
title : Structures.Isos module (The Agda Universal Algebra Library)
date : 2021-07-23
author: [agda-algebras development team][]
---

### <a id="isomorphisms">Isomorphisms</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Isos where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional using () renaming (Extensionality to funext)
open import Agda.Primitive                        using    ( _⊔_    ;   lsuc     )
                                                  renaming ( Set    to  Type     )
open import Agda.Builtin.Equality                 using    ( _≡_    ;   refl     )
open import Data.Product                          using    ( _,_    ;   Σ-syntax
                                                           ;  Σ     ;   _×_      )
                                                  renaming ( proj₁  to  fst
                                                           ; proj₂  to  snd      )
open import Level                                 using    ( Level  ;  Lift
                                                           ; lift   ;  lower     )
open import Function.Base                         using    ( _∘_                 )
open import Relation.Binary.PropositionalEquality using    ( cong   ; cong-app   )


-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries    using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower )
open import Structures.Basic    using ( signature ; structure ; Lift-Strucˡ ; Lift-Struc ; sigl ; siglˡ ; siglʳ )
open import Structures.Homs     using ( hom ; 𝒾𝒹 ; ∘-hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-hom )
open import Structures.Products using ( ⨅ ; ℓp ; ℑ ; class-product )

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ α ρᵃ β ρᵇ γ ρᶜ ι : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁

\end{code}

#### Definition of isomorphism

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

\begin{code}

record _≅_ (𝑨 : structure  𝐹 𝑅 {α}{ρᵃ})(𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}) : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
 constructor mkiso
 field
  to : hom 𝑨 𝑩
  from : hom 𝑩 𝑨
  to∼from : ∣ to ∣ ∘ ∣ from ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑩} ∣
  from∼to : ∣ from ∣ ∘ ∣ to ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑨} ∣

open _≅_ public

\end{code}

That is, two structures are isomorphic provided there are homomorphisms going back and forth between them which compose to the identity map.


#### Isomorphism is an equivalence relation

\begin{code}

≅-refl : {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} → 𝑨 ≅ 𝑨
≅-refl {𝑨 = 𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ _ → refl) (λ _ → refl)


≅-sym : {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}}{𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
≅-sym A≅B = mkiso (from A≅B) (to A≅B) (from∼to A≅B) (to∼from A≅B)

module _ (𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}){𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}}
         (𝑪 : structure 𝐹 𝑅 {γ}{ρᶜ}) where

 ≅-trans : 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

 ≅-trans ab bc = record { to = f ; from = g ; to∼from = τ ; from∼to = ν }
  where
  f1 : hom 𝑨 𝑩
  f1 = to ab
  f2 : hom 𝑩 𝑪
  f2 = to bc
  f : hom 𝑨 𝑪
  f = ∘-hom {𝑨 = 𝑨}{𝑩}{𝑪} f1 f2

  g1 : hom 𝑪 𝑩
  g1 = from bc
  g2 : hom 𝑩 𝑨
  g2 = from ab
  g : hom 𝑪 𝑨
  g = ∘-hom {𝑨 = 𝑪}{𝑩}{𝑨}g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑪} ∣
  τ x = (cong ∣ f2 ∣(to∼from ab (∣ g1 ∣ x)))∙(to∼from bc) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 {𝑨 = 𝑨} ∣
  ν x = (cong ∣ g2 ∣(from∼to bc (∣ f1 ∣ x)))∙(from∼to ab) x

\end{code}

#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in [Overture.Lifts][].

\begin{code}

open Level

Lift-≅ˡ : (ℓ : Level) → {𝑨 : structure 𝐹 𝑅{α}{ρᵃ}} → 𝑨 ≅ (Lift-Strucˡ ℓ 𝑨)
Lift-≅ˡ {α = α}{ρᵃ} ℓ {𝑨} = record { to = 𝓁𝒾𝒻𝓉
                                   ; from = 𝓁ℴ𝓌ℯ𝓇 {𝑨 = 𝑨}
                                   ; to∼from = cong-app lift∼lower
                                   ; from∼to = cong-app (lower∼lift{α}{ρᵃ})
                                   }

 -- (todo: a more general version)
 -- Lift-≅ : (ℓ ρ : Level) → {𝑨 : structure 𝐹 𝑅{α}{ρᵃ}} → 𝑨 ≅ (Lift-Struc ℓ ρ 𝑨)
 -- Lift-≅ ℓ ρ {𝑨} = record { to = 𝓁𝒾𝒻𝓉   -- 𝓁𝒾𝒻𝓉 ℓ ρ 𝑨
 --                         ; from = 𝓁ℴ𝓌ℯ𝓇 -- ℓ ρ 𝑨
 --                         ; to∼from = cong-app lift∼lower
 --                         ; from∼to = cong-app (lower∼lift{α}{ρ})
 --                         }

module _ {𝑨 : structure 𝐹 𝑅{α}{ρᵃ}}{𝑩 : structure 𝐹 𝑅{β}{ρᵇ}} where

 Lift-Strucˡ-iso : (ℓ ℓ' : Level) → 𝑨 ≅ 𝑩 → Lift-Strucˡ ℓ 𝑨 ≅ Lift-Strucˡ ℓ' 𝑩

 Lift-Strucˡ-iso ℓ ℓ' A≅B = ≅-trans (Lift-Strucˡ ℓ 𝑨) (Lift-Strucˡ ℓ' 𝑩)
                                 ( ≅-trans (Lift-Strucˡ ℓ 𝑨) 𝑩 (≅-sym (Lift-≅ˡ ℓ)) A≅B )
                                  (Lift-≅ˡ ℓ')


 -- (todo: a more general version)
 -- Lift-Struc-iso : (ℓ ρ ℓ' ρ' : Level) → 𝑨 ≅ 𝑩 → Lift-Struc ℓ ρ 𝑨 ≅ Lift-Struc ℓ' ρ' 𝑩
 -- Lift-Struc-iso ℓ ρ ℓ' ρ' A≅B = ≅-trans (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
 --                                 ( ≅-trans (Lift-Struc ℓ ρ 𝑨) 𝑩 (≅-sym (Lift-≅ ℓ ρ)) A≅B )
 --                                  (Lift-≅ ℓ' ρ')

\end{code}



#### Lift associativity

The lift is also associative, up to isomorphism at least.

\begin{code}

-- module _ {α ρᵃ : Level}
--          {𝑨 : Structure {α} {ρᵃ} 𝑅 𝐹} where

--  Lift-Struc-assocˡ : {ℓ ℓ' : Level} → Lift-Strucˡ (ℓ ⊔ ℓ') 𝑨 ≅ (Lift-Strucˡ ℓ (Lift-Strucˡ ℓ' 𝑨))
--  Lift-Struc-assocˡ = {!!} -- ≅-trans (≅-trans Goal Lift-≅) Lift-≅
--   -- where
--   -- Goal : Lift-Alg 𝑨 (β ⊔ 𝓘) ≅ 𝑨
--   -- Goal = ≅-sym Lift-≅

--  Lift-Struc-assocʳ : {ρ ρ' : Level} → Lift-Strucʳ (ρ ⊔ ρ') 𝑨 ≅ (Lift-Strucʳ ρ (Lift-Strucʳ ρ' 𝑨))
--  Lift-Struc-assocʳ = {!!} -- ≅-trans (≅-trans Goal Lift-≅) Lift-≅

--  Lift-Struc-assoc : {ℓ ℓ' ρ ρ' : Level}
--   →                 Lift-Struc (ℓ ⊔ ℓ') (ρ ⊔ ρ') 𝑨 ≅ (Lift-Struc ℓ ρ (Lift-Struc ℓ' ρ' 𝑨))
--  Lift-Struc-assoc = {!!} -- ≅-trans (≅-trans Goal Lift-≅) Lift-≅

\end{code}




#### Products preserve isomorphisms

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

module _ {I : Type ι}
         {fe : funext ρᵇ ρᵇ}
         {fiu : funext ι α}{fiw : funext ι β} where

 open structure
 ⨅≅ : {𝒜 : I → structure 𝐹 𝑅{α}{ρᵃ}}{ℬ : I → structure 𝐹 𝑅{β}{ρᵇ}} → (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

 ⨅≅ {𝒜 = 𝒜}{ℬ} AB = record { to = ϕ , ϕhom ; from = ψ , ψhom ; to∼from = ϕ~ψ ; from∼to = ψ~ϕ }
  where
  ϕ : carrier (⨅ 𝒜) → carrier (⨅ ℬ)
  ϕ a i = ∣ to (AB i) ∣ (a i)

  ϕhom : is-hom (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom = (λ r a x 𝔦 → fst ∥ to (AB 𝔦) ∥ r (λ z → a z 𝔦) (x 𝔦)) ,
          λ f a → fiw (λ i → snd ∥ to (AB i) ∥ f (λ z → a z i))

  ψ : carrier (⨅ ℬ) → carrier (⨅ 𝒜)
  ψ b i = ∣ from (AB i) ∣ (b i)

  ψhom : is-hom (⨅ ℬ) (⨅ 𝒜) ψ
  ψhom = (λ r a x 𝔦 → fst ∥ from (AB 𝔦) ∥ r (λ z → a z 𝔦) (x 𝔦)) ,
          (λ f a → fiu (λ i → snd ∥ from (AB i) ∥ f (λ z → a z i)))

  ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 {𝑨 = ⨅ ℬ} ∣
  ϕ~ψ 𝒃 = fiw λ i → (to∼from (AB i)) (𝒃 i)

  ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 {𝑨 = ⨅ 𝒜} ∣
  ψ~ϕ a = fiu λ i → (from∼to (AB i)) (a i)


\end{code}


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

\begin{code}

-- module _ {𝓘 : Level}{I : Type 𝓘}{fizw : funext (𝓘 ⊔ γ) β}{fiu : funext 𝓘 α} where

--   Lift-Alg-⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : (Lift γ I) → Algebra β 𝑆}
--    →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

--   Lift-Alg-⨅≅ {𝒜}{ℬ} AB = Goal
--    where
--    ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
--    ϕ a i = ∣ fst (AB  (lower i)) ∣ (a (lower i))

--    ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
--    ϕhom 𝑓 a = fizw (λ i → (∥ fst (AB (lower i)) ∥) 𝑓 (λ x → a x (lower i)))

--    ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
--    ψ b i = ∣ fst ∥ AB i ∥ ∣ (b (lift i))

--    ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
--    ψhom 𝑓 𝒃 = fiu (λ i → (snd ∣ snd (AB i) ∣) 𝑓 (λ x → 𝒃 x (lift i)))

--    ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
--    ϕ~ψ 𝒃 = fizw λ i → fst ∥ snd (AB (lower i)) ∥ (𝒃 i)

--    ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
--    ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

--    A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
--    A≅B = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

--    Goal : Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ
--    Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


