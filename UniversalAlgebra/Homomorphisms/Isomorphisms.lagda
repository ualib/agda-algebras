---
layout: default
title : Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

### <a id="isomorphisms">Isomorphisms</a>

This section describes the [Homomorphisms.Isomorphisms][] module of the [Agda Universal Algebra Library][].
Here we formalize the informal notion of isomorphism between algebraic structures.
̇
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level using ( Level ; Lift )
open import Algebras.Basic

module Homomorphisms.Isomorphisms {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥)  where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional    renaming (Extensionality to funext )
open import Agda.Primitive                        using    ( _⊔_    ;   lsuc      )
                                                  renaming ( Set    to  Type      )
open import Agda.Builtin.Equality                 using    ( _≡_    ;   refl      )
open import Data.Product                          using    ( _,_    ;   Σ-syntax
                                                           ;  Σ     ;   _×_       )
                                                  renaming ( proj₁  to  fst
                                                           ; proj₂  to  snd       )
open import Function.Base                         using    ( _∘_                  )
open import Relation.Binary.PropositionalEquality using    ( cong   ;   cong-app  )


-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ ; _⁻¹ ; _≈_ ; transport ; _∙_
                                         ; lower∼lift ; lift∼lower )
open import Algebras.Products    𝑆 using ( ⨅ )
open import Homomorphisms.Basic   using ( hom ; kercon ; ker[_⇒_]_↾_ ; πker ; 𝒾𝒹 ; ∘-hom
                                         ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-homomorphism ; ∘-is-hom )

private variable α β γ : Level

\end{code}

#### <a id="isomorphism-toolbox">Definition of isomorphism</a>

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

\begin{code}

_≅_ : {α β : Level}(𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
𝑨 ≅ 𝑩 =  Σ[ f ∈ (hom 𝑨 𝑩)] Σ[ g ∈ hom 𝑩 𝑨 ] ((∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣))

\end{code}

That is, two structures are **isomorphic** provided there are homomorphisms going back and forth between them which compose to the identity map.



#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}

≅-refl : {α : Level} {𝑨 : Algebra α 𝑆} → 𝑨 ≅ 𝑨
≅-refl {α}{𝑨} = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , (λ a → refl) , (λ a → refl)

≅-sym : {α β : Level}{𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
≅-sym h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

≅-trans : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆}
 →        𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

≅-trans {𝑨 = 𝑨} {𝑩}{𝑪} ab bc = f , g , τ , ν
 where
  f1 : hom 𝑨 𝑩
  f1 = ∣ ab ∣
  f2 : hom 𝑩 𝑪
  f2 = ∣ bc ∣
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = fst ∥ bc ∥
  g2 : hom 𝑩 𝑨
  g2 = fst ∥ ab ∥
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(∣ snd ∥ ab ∥ ∣ (∣ g1 ∣ x)))∙(∣ snd ∥ bc ∥ ∣) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(∥ snd ∥ bc ∥ ∥ (∣ f1 ∣ x)))∙(∥ snd ∥ ab ∥ ∥) x

\end{code}

#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in [Overture.Lifts][].

\begin{code}

open Level

Lift-≅ : {𝑨 : Algebra α 𝑆} → 𝑨 ≅ (Lift-Alg 𝑨 β)
Lift-≅{β = β}{𝑨 = 𝑨} = 𝓁𝒾𝒻𝓉 𝑨 , 𝓁ℴ𝓌ℯ𝓇 𝑨 , cong-app lift∼lower , cong-app (lower∼lift {β = β})

Lift-hom : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆} (ℓᵇ : Level)
 →         hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)

Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
 where
 lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
 lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → refl) fhom

 Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
 Goal = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ){f ∘ lower}{lift} lABh λ _ _ → refl


Lift-Alg-iso : {𝑨 : Algebra α 𝑆}{𝓧 : Level}
               {𝑩 : Algebra β 𝑆}{𝓨 : Level}
               -----------------------------------------
 →             𝑨 ≅ 𝑩 → (Lift-Alg 𝑨 𝓧) ≅ (Lift-Alg 𝑩 𝓨)

Lift-Alg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅) A≅B) Lift-≅

\end{code}




#### <a id="lift-associativity">Lift associativity</a>

The lift is also associative, up to isomorphism at least.

\begin{code}

module _ {𝓘 : Level} where

  Lift-Alg-assoc : {𝑨 : Algebra α 𝑆} → Lift-Alg 𝑨 (β ⊔ 𝓘) ≅ (Lift-Alg (Lift-Alg 𝑨 β) 𝓘)
  Lift-Alg-assoc {α}{β}{𝑨} = ≅-trans (≅-trans Goal Lift-≅) Lift-≅
   where
   Goal : Lift-Alg 𝑨 (β ⊔ 𝓘) ≅ 𝑨
   Goal = ≅-sym Lift-≅

  Lift-Alg-associative : (𝑨 : Algebra α 𝑆) → Lift-Alg 𝑨 (β ⊔ 𝓘) ≅ (Lift-Alg (Lift-Alg 𝑨 β) 𝓘)
  Lift-Alg-associative 𝑨 = Lift-Alg-assoc {𝑨 = 𝑨}

\end{code}




#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

Products of isomorphic families of algebras are themselves isomorphic. The proof looks a bit technical, but it is as straightforward as it ought to be.

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}{fiu : funext 𝓘 α}{fiw : funext 𝓘 β} where

  ⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : I → Algebra β 𝑆} → (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

  ⨅≅ {𝒜}{ℬ} AB = Goal
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ fst (AB i) ∣ (a i)

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fiw (λ i → ∥ fst (AB i) ∥ 𝑓 (λ x → a x i))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → snd ∣ snd (AB i) ∣ 𝑓 (λ x → 𝒃 x i))

   ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ~ψ 𝒃 = fiw λ i → fst ∥ snd (AB i) ∥ (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

   Goal : ⨅ 𝒜 ≅ ⨅ ℬ
   Goal = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

\end{code}


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}{fizw : funext (𝓘 ⊔ γ) β}{fiu : funext 𝓘 α} where

  Lift-Alg-⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : (Lift γ I) → Algebra β 𝑆}
   →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

  Lift-Alg-⨅≅ {𝒜}{ℬ} AB = Goal
   where
   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = ∣ fst (AB  (lower i)) ∣ (a (lower i))

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 a = fizw (λ i → (∥ fst (AB (lower i)) ∥) 𝑓 (λ x → a x (lower i)))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ fst ∥ AB i ∥ ∣ (b (lift i))

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = fiu (λ i → (snd ∣ snd (AB i) ∣) 𝑓 (λ x → 𝒃 x (lift i)))

   ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
   ϕ~ψ 𝒃 = fizw λ i → fst ∥ snd (AB (lower i)) ∥ (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
   ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

   Goal : Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ
   Goal = ≅-trans (≅-sym Lift-≅) A≅B

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
