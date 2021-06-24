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

module Homomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥}  where


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
open import Algebras.Products    {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Basic  {𝑆 = 𝑆} using ( hom ; kercon ; ker[_⇒_]_↾_ ; πker ; 𝒾𝒹 ; ∘-hom
                                         ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-homomorphism ; ∘-is-hom ; Lift-hom)

private variable α β γ : Level

\end{code}

#### <a id="isomorphism-toolbox">Definition of isomorphism</a>

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

We could define this using Sigma types, like this.

```agda
_≅_ : {α β : Level}(𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
𝑨 ≅ 𝑩 =  Σ[ f ∈ (hom 𝑨 𝑩)] Σ[ g ∈ hom 𝑩 𝑨 ] ((∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣))
```

However, with four components, an equivalent record type is easier to work with.

\begin{code}

record _≅_ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β) where
 constructor mkiso
 field
  to : hom 𝑨 𝑩
  from : hom 𝑩 𝑨
  to∼from : ∣ to ∣ ∘ ∣ from ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣
  from∼to : ∣ from ∣ ∘ ∣ to ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣

open _≅_ public


\end{code}

That is, two structures are **isomorphic** provided there are homomorphisms going back and forth between them which compose to the identity map.



#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}

≅-refl : {α : Level} {𝑨 : Algebra α 𝑆} → 𝑨 ≅ 𝑨
≅-refl {α}{𝑨} = record { to = 𝒾𝒹 𝑨 ; from = 𝒾𝒹 𝑨 ; to∼from = λ _ → refl ; from∼to = λ _ → refl }

≅-sym : {α β : Level}{𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
≅-sym φ = record { to = from φ ; from = to φ ; to∼from = from∼to φ ; from∼to = to∼from φ }

≅-trans : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆}
 →        𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

≅-trans {𝑨 = 𝑨} {𝑩}{𝑪} ab bc = record { to = f ; from = g ; to∼from = τ ; from∼to = ν }
 where
  f1 : hom 𝑨 𝑩
  f1 = to ab
  f2 : hom 𝑩 𝑪
  f2 = to bc
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = from bc
  g2 : hom 𝑩 𝑨
  g2 = from ab
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(to∼from ab (∣ g1 ∣ x)))∙(to∼from bc) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(from∼to bc (∣ f1 ∣ x)))∙(from∼to ab) x

\end{code}

#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of the universe hierarchy discussed in [Overture.Lifts][].

\begin{code}

open Level

Lift-≅ : {𝑨 : Algebra α 𝑆} → 𝑨 ≅ (Lift-Alg 𝑨 β)
Lift-≅{β = β}{𝑨 = 𝑨} = record { to = 𝓁𝒾𝒻𝓉 𝑨
                              ; from = 𝓁ℴ𝓌ℯ𝓇 𝑨
                              ; to∼from = cong-app lift∼lower
                              ; from∼to = cong-app (lower∼lift {β = β})
                              }

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

  ⨅≅ {𝒜}{ℬ} AB = record { to = ϕ , ϕhom ; from = ψ , ψhom ; to∼from = ϕ∼ψ ; from∼to = ψ∼ϕ }
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

   -- Goal : ⨅ 𝒜 ≅ ⨅ ℬ
   -- Goal = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

\end{code}


A nearly identical proof goes through for isomorphisms of lifted products (though, just for fun, we use the universal quantifier syntax here to express the dependent function type in the statement of the lemma, instead of the Pi notation we used in the statement of the previous lemma; that is, `∀ i → 𝒜 i ≅ ℬ (lift i)` instead of `Π i ꞉ I , 𝒜 i ≅ ℬ (lift i)`.)

\begin{code}

module _ {𝓘 : Level}{I : Type 𝓘}{fizw : funext (𝓘 ⊔ γ) β}{fiu : funext 𝓘 α} where

  Lift-Alg-⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : (Lift γ I) → Algebra β 𝑆}
   →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

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
