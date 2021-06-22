---
layout: default
title : Structures.Iso module (The Agda Universal Algebra Library)
date : 2021-06-22
author: [the ualib/agda-algebras development team][]
---

### <a id="isomorphisms">Isomorphisms</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Iso where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
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
open import Overture.Preliminaries using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower )
open import Structures.Basic         using ( Signature ; Structure ; Lift-Struc )
open import Structures.Homs         using ( Hom ; 𝒾𝒹 ; ∘-Hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 )

private variable 𝑅 𝐹 : Signature

\end{code}

#### <a id="isomorphism-toolbox">Definition of isomorphism</a>

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

\begin{code}

module _ {α ρᵃ β ρᵇ : Level} where

 _≅_ : (𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹)(𝑩 : Structure {β}{ρᵇ} 𝑅 𝐹) → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 𝑨 ≅ 𝑩 =  Σ[ f ∈ (Hom 𝑨 𝑩)] Σ[ g ∈ Hom 𝑩 𝑨 ] ((∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣))

\end{code}

That is, two structures are **isomorphic** provided there are homomorphisms going back and forth between them which compose to the identity map.



#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}

module _ {α ρᵃ : Level} where

 ≅-refl : {𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹} → 𝑨 ≅ 𝑨
 ≅-refl {𝑨 = 𝑨} = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , ((λ _ → refl) , (λ _ → refl))

module _ {α ρᵃ β ρᵇ : Level} where

 ≅-sym : {𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹}{𝑩 : Structure {β}{ρᵇ} 𝑅 𝐹}
  →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
 ≅-sym h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

module _ {α ρᵃ β ρᵇ γ ρᶜ : Level}
         (𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹){𝑩 : Structure {β}{ρᵇ} 𝑅 𝐹}
         (𝑪 : Structure {γ}{ρᶜ} 𝑅 𝐹) where

 ≅-trans : 𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

 ≅-trans ab bc = f , (g , (τ , ν))
  where
  f1 : Hom 𝑨 𝑩
  f1 = ∣ ab ∣
  f2 : Hom 𝑩 𝑪
  f2 = ∣ bc ∣
  f : Hom 𝑨 𝑪
  f = ∘-Hom 𝑨 𝑪 f1 f2

  g1 : Hom 𝑪 𝑩
  g1 = fst ∥ bc ∥
  g2 : Hom 𝑩 𝑨
  g2 = fst ∥ ab ∥
  g : Hom 𝑪 𝑨
  g = ∘-Hom 𝑪 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(∣ snd ∥ ab ∥ ∣ (∣ g1 ∣ x)))∙(∣ snd ∥ bc ∥ ∣) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(∥ snd ∥ bc ∥ ∥ (∣ f1 ∣ x)))∙(∥ snd ∥ ab ∥ ∥) x

\end{code}

#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in [Overture.Lifts][].

\begin{code}

open Level

module _ {α ρᵃ : Level} where

 Lift-≅ : (ℓ ρ : Level) → {𝑨 : Structure {α}{ρᵃ} 𝑅 𝐹} → 𝑨 ≅ (Lift-Struc ℓ ρ 𝑨)
 Lift-≅ ℓ ρ {𝑨} = 𝓁𝒾𝒻𝓉 ℓ ρ 𝑨 , 𝓁ℴ𝓌ℯ𝓇 ℓ ρ 𝑨 , cong-app lift∼lower , cong-app (lower∼lift {α}{ρ})

module _ {α ρᵃ β ρᵇ : Level}
         {𝑨 : Structure {α} {ρᵃ} 𝑅 𝐹}{𝑩 : Structure {β}{ρᵇ} 𝑅 𝐹} where

 Lift-Struc-iso : (ℓ ρ ℓ' ρ' : Level) → 𝑨 ≅ 𝑩 → Lift-Struc ℓ ρ 𝑨 ≅ Lift-Struc ℓ' ρ' 𝑩

 Lift-Struc-iso ℓ ρ ℓ' ρ' A≅B = ≅-trans (Lift-Struc ℓ ρ 𝑨) (Lift-Struc ℓ' ρ' 𝑩)
                                 ( ≅-trans (Lift-Struc ℓ ρ 𝑨) 𝑩 (≅-sym (Lift-≅ ℓ ρ)) A≅B )
                                  (Lift-≅ ℓ' ρ')



\end{code}




#### <a id="lift-associativity">Lift associativity</a>

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




#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

-- module _ {𝓘 : Level}{I : Type 𝓘}{fiu : funext 𝓘 α}{fiw : funext 𝓘 β} where

--   ⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : I → Algebra β 𝑆} → (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

--   ⨅≅ {𝒜}{ℬ} AB = Goal
--    where
--    ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
--    ϕ a i = ∣ fst (AB i) ∣ (a i)

--    ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
--    ϕhom 𝑓 a = fiw (λ i → ∥ fst (AB i) ∥ 𝑓 (λ x → a x i))

--    ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
--    ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

--    ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
--    ψhom 𝑓 𝒃 = fiu (λ i → snd ∣ snd (AB i) ∣ 𝑓 (λ x → 𝒃 x i))

--    ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
--    ϕ~ψ 𝒃 = fiw λ i → fst ∥ snd (AB i) ∥ (𝒃 i)

--    ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
--    ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

--    Goal : ⨅ 𝒜 ≅ ⨅ ℬ
--    Goal = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

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

--------------------------------------

<br>

[← Homomorphisms.Noether](Homomorphisms.Noether.html)
<span style="float:right;">[Homomorphisms.HomomorphicImages →](Homomorphisms.HomomorphicImages.html)</span>

{% include UALib.Links.md %}


------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team














<!-- NO LONGER USED

#### <a id="embedding-tools">Embedding tools</a>

Finally, we prove some useful facts about embeddings that occasionally come in handy.

private variable 𝓘 : Level

 -- embedding-lift-nat : hfunext 𝓘 α → hfunext 𝓘 β
 --   →                   {I : Type 𝓘}{A : I → Type α}{B : I → Type β}
 --                       (h : Nat A B) → (∀ i → is-embedding (h i))
 --                       ------------------------------------------
 --   →                   is-embedding(NatΠ h)

 -- embedding-lift-nat hfiu hfiw h hem = NatΠ-is-embedding hfiu hfiw h hem


 -- embedding-lift-nat' : hfunext 𝓘 α → hfunext 𝓘 β
 --   →                    {I : Type 𝓘}{𝒜 : I → Algebra α 𝑆}{ℬ : I → Algebra β 𝑆}
 --                        (h : Nat(fst ∘ 𝒜)(fst ∘ ℬ)) → (∀ i → is-embedding (h i))
 --                        --------------------------------------------------------
 --   →                    is-embedding(NatΠ h)

 -- embedding-lift-nat' hfiu hfiw h hem = NatΠ-is-embedding hfiu hfiw h hem


 -- embedding-lift : hfunext 𝓘 α → hfunext 𝓘 β
 --   →               {I : Type 𝓘} → {𝒜 : I → Algebra α 𝑆}{ℬ : I → Algebra β 𝑆}
 --   →               (h : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣) → (∀ i → is-embedding (h i))
 --                   ----------------------------------------------------------
 --   →               is-embedding(λ (x : ∣ ⨅ 𝒜 ∣) (i : I) → (h i)(x i))

 -- embedding-lift hfiu hfiw {I}{𝒜}{ℬ} h hem = embedding-lift-nat' hfiu hfiw {I}{𝒜}{ℬ} h hem


 -- iso→embedding : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} → (ϕ : 𝑨 ≅ 𝑩) → is-embedding (fst ∣ ϕ ∣)
 -- iso→embedding ϕ = equiv-is-embedding (fst ∣ ϕ ∣) {!!} -- (invertible-is-equiv (fst ∣ ϕ ∣) finv)
 --  where
 --  finv : invertible (fst ∣ ϕ ∣)
 --  finv = ∣ fst ∥ ϕ ∥ ∣ , (snd ∥ snd ϕ ∥ , fst ∥ snd ϕ ∥)
