---
layout: default
title : "Varieties.Func.Properties module (The Agda Universal Algebra Library)"
date : "2021-09-24"
author: "agda-algebras development team"
---

### <a id="properties-of-the-models-relation">Properties of the models relation for setoid algebras</a>

We prove some closure and invariance properties of the relation `⊧`.  In particular, we prove the following facts (which are needed, for example, in the proof the Birkhoff HSP Theorem).

* [Algebraic invariance](#algebraic-invariance). `⊧` is an *algebraic invariant* (stable under isomorphism).

* [Subalgebraic invariance](#subalgebraic-invariance). Identities modeled by a class of algebras are also modeled by all subalgebras of algebras in the class.

* [Product invariance](#product-invariance). Identities modeled by a class of algebras are also modeled by all products of algebras in the class.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Func.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive   using ( Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function.Base    using ( _∘_ )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ )

open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; Lift-Algˡ ; ov )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( hom )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; mkiso ; Lift-≅ˡ ; ≅-sym )
open import Terms.Basic                     {𝑆 = 𝑆} using ( Term )
open import Terms.Func.Basic                {𝑆 = 𝑆} using ( 𝑻 ; _≐_ ; module Environment )
open import Terms.Func.Operations           {𝑆 = 𝑆} using ( comm-hom-term ; interp-prod ; term-agreement )
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; SubalgebrasOfClass )
open import Varieties.Func.EquationalLogic  {𝑆 = 𝑆}  using ( _⊧_≈_ ; _⊫_≈_ )

private variable
 α ρᵃ β ρᵇ χ ℓ : Level

open Func          renaming ( f to _⟨$⟩_ )
\end{code}


#### <a id="algebraic-invariance-of-models">Algebraic invariance of ⊧</a>

The binary relation ⊧ would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism).

\begin{code}

open Term
-- open ≡-Reasoning
open _≅_

open Func using ( cong ) renaming (f to _⟨$⟩_ )

module _ {X : Type χ}{𝑨 : SetoidAlgebra α ρᵃ}
         (𝑩 : SetoidAlgebra β ρᵇ)(p q : Term X) where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Setoid A using ( ) renaming ( _≈_ to _≈₁_ )


 open SetoidAlgebra 𝑩 using () renaming (Domain to B )
 open Environment 𝑩 using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
 open Setoid B using ( _≈_ ; sym )
 open SetoidReasoning B

 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ =
  begin
   ⟦ p ⟧₂ ⟨$⟩ ρ             ≈˘⟨ cong ⟦ p ⟧₂ (λ x → f∼g (ρ x)) ⟩
   ⟦ p ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ)) ≈˘⟨ comm-hom-term fh p (g ∘ ρ) ⟩
   f (⟦ p ⟧₁ ⟨$⟩ (g ∘ ρ))   ≈⟨ cong ∣ fh ∣ (Apq (g ∘ ρ)) ⟩
   f (⟦ q ⟧₁ ⟨$⟩ (g ∘ ρ))   ≈⟨ comm-hom-term fh q (g ∘ ρ) ⟩
   ⟦ q ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ)) ≈⟨ cong ⟦ q ⟧₂ (λ x → f∼g (ρ x)) ⟩
   ⟦ q ⟧₂ ⟨$⟩ ρ             ∎
  where private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣

\end{code}


 As the proof makes clear, we show 𝑩 ⊧ p ≈ q by showing that `𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧ holds *extensionally*, that is, `∀ x, 𝑩 ⟦ p ⟧ x ≡ 𝑩 ⟦q ⟧ x`.

#### <a id="lift-invariance">Lift-invariance of ⊧</a>
The ⊧ relation is also invariant under the algebraic lift and lower operations.

\begin{code}

-- module _ (wd : SwellDef){α β χ : Level}{X : Type χ}{𝑨 : SetoidAlgebra α ρᵃ} where
module _ {X : Type χ}{𝑨 : SetoidAlgebra α ρᵃ} where

 ⊧-Lift-invar : (p q : Term X) → 𝑨 ⊧ p ≈ q → Lift-Algˡ 𝑨 β ⊧ p ≈ q
 ⊧-Lift-invar p q Apq = ⊧-I-invar (Lift-Algˡ 𝑨 _) p q Apq Lift-≅ˡ

 ⊧-lower-invar : (p q : Term X) → Lift-Algˡ 𝑨 β ⊧ p ≈ q  →  𝑨 ⊧ p ≈ q
 ⊧-lower-invar p q lApq = ⊧-I-invar 𝑨 p q lApq (≅-sym Lift-≅ˡ)

\end{code}



#### <a id="subalgebraic-invariance">Subalgebraic invariance of ⊧</a>

Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`, which fact can be formalized as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : SetoidAlgebra α ρᵃ}
         (𝑩 : SetoidAlgebra β ρᵇ)(p q : Term X) where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Setoid A using ( ) renaming ( _≈_ to _≈₁_ )


 open SetoidAlgebra 𝑩 using () renaming (Domain to B )
 open Environment 𝑩 using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
 open Setoid B using ( _≈_ ; sym )
 open SetoidReasoning A


 ⊧-S-invar : 𝑨 ⊧ p ≈ q  →  𝑩 ≤ 𝑨  →  𝑩 ⊧ p ≈ q
 ⊧-S-invar Apq B≤A b = goal
  where
  hh : hom 𝑩 𝑨
  hh = ∣ B≤A ∣
  h = _⟨$⟩_ ∣ hh ∣
  ξ : ∀ b → h (⟦ p ⟧₂ ⟨$⟩ b) ≈₁ h (⟦ q ⟧₂ ⟨$⟩ b)
  ξ b = begin
         h (⟦ p ⟧₂ ⟨$⟩ b)   ≈⟨ comm-hom-term hh p b ⟩
         ⟦ p ⟧₁ ⟨$⟩ (h ∘ b) ≈⟨ Apq (h ∘ b) ⟩
         ⟦ q ⟧₁ ⟨$⟩ (h ∘ b) ≈˘⟨ comm-hom-term hh q b ⟩
         h (⟦ q ⟧₂ ⟨$⟩ b)   ∎
  goal : ⟦ p ⟧₂ ⟨$⟩ b ≈ ⟦ q ⟧₂ ⟨$⟩ b
  goal = ∥ B≤A ∥ (ξ b)


\end{code}

Next, identities modeled by a class of algebras is also modeled by all subalgebras of the class.  In other terms, every term equation `p ≈ q` that is satisfied by all `𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of 𝒦.

\begin{code}
module _ {X : Type χ}{𝑨 : SetoidAlgebra α ρᵃ}
         (p q : Term X) where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Setoid A using ( ) renaming ( _≈_ to _≈₁_ )

 open SetoidReasoning A

 ⊧-S-class-invar : {𝒦 : Pred (SetoidAlgebra α ρᵃ) ℓ}
  →                (𝒦 ⊫ p ≈ q) → (𝑩 : SubalgebrasOfClass 𝒦 {β}{ρᵇ})
  →                ∣ 𝑩 ∣ ⊧ p ≈ q
 ⊧-S-class-invar Kpq (𝑩 , 𝑨 , kA , B≤A) = ⊧-S-invar 𝑩 p q (Kpq kA) B≤A

\end{code}



#### <a id="product-invariance">Product invariance of ⊧</a>

An identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in that collection.

\begin{code}

module _ {I : Type ℓ}(𝒜 : I → SetoidAlgebra α ρᵃ){X : Type χ} where

 open SetoidAlgebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )
 open Setoid ⨅A using ( _≈_ )
 open Environment (⨅ 𝒜) using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment using ( ⟦_⟧ )
 open SetoidReasoning ⨅A
 ⊧-P-invar : (p q : Term X) → (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar p q 𝒜pq a = goal
  where
  ξ : (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (a x) i)) ≈ (λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ (λ x → (a x) i))
  ξ = λ i → 𝒜pq i (λ x → (a x) i)
  goal : ⟦ p ⟧₁ ⟨$⟩ a ≈ ⟦ q ⟧₁ ⟨$⟩ a
  goal = begin
          ⟦ p ⟧₁ ⟨$⟩ a ≈⟨ interp-prod 𝒜 p a ⟩
          (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (a x) i)) ≈⟨ ξ ⟩
          (λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ (λ x → (a x) i)) ≈˘⟨ interp-prod 𝒜 q a ⟩
          ⟦ q ⟧₁ ⟨$⟩ a ∎

\end{code}

An identity satisfied by all algebras in a class is also satisfied by the product of algebras in the class.

\begin{code}

 ⊧-P-class-invar : (𝒦 : Pred (SetoidAlgebra α ρᵃ)(ov α)){p q : Term X}
  →                𝒦 ⊫ p ≈ q → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ p ≈ q

 ⊧-P-class-invar 𝒦 {p}{q}σ K𝒜 = ⊧-P-invar p q (λ i ρ → σ (K𝒜 i) ρ)

\end{code}

Another fact that will turn out to be useful is that a product of a collection of algebras models p ≈ q if the lift of each algebra in the collection models p ≈ q.

\begin{code}

 ⊧-P-lift-invar : (p q : Term X) → (∀ i → Lift-Algˡ (𝒜 i) β ⊧ p ≈ q)  →  ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-lift-invar p q α = ⊧-P-invar p q Aipq
  where
  Aipq : ∀ i → (𝒜 i) ⊧ p ≈ q
  Aipq i = ⊧-lower-invar{𝑨 = (𝒜 i)} p q (α i)

\end{code}



#### <a id="homomorphisc-invariance">Homomorphic invariance of ⊧</a>

If an algebra 𝑨 models an identity p ≈ q, then the pair (p , q) belongs to the kernel of every homomorphism φ : hom (𝑻 X) 𝑨 from the term algebra to 𝑨; that is, every homomorphism from 𝑻 X to 𝑨 maps p and q to the same element of 𝑨.

 \begin{code}

module _ {X : Type χ}{𝑨 : SetoidAlgebra α ρᵃ}(φh : hom (𝑻 X) 𝑨) where
 open  SetoidAlgebra 𝑨 using () renaming ( Domain to A )
 open Setoid A using ( _≈_ )
 open SetoidReasoning A
 open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment using ( ⟦_⟧ )
 private φ = _⟨$⟩_ ∣ φh ∣

 ⊧-H-invar : {p q : Term X} → 𝑨 ⊧ p ≈ q → φ p ≈ φ q
 ⊧-H-invar {p}{q} β =
  begin
   φ p                   ≈⟨ cong ∣ φh ∣ (term-agreement p) ⟩
   φ ((⟦ 𝑻 X ⟧ p) ⟨$⟩ ℊ) ≈⟨ comm-hom-term φh p ℊ ⟩
   ⟦ p ⟧₁ ⟨$⟩ (φ ∘ ℊ)    ≈⟨ β (φ ∘ ℊ) ⟩
   ⟦ q ⟧₁ ⟨$⟩ (φ ∘ ℊ)    ≈˘⟨ comm-hom-term φh q ℊ ⟩
   φ ((⟦ 𝑻 X ⟧ q) ⟨$⟩ ℊ) ≈˘⟨ cong ∣ φh ∣ (term-agreement q) ⟩
   φ q                   ∎

\end{code}

---------------------------------

<span style="float:left;">[← Varieties.Func.Closure](Varieties.Func.Closure.html)</span>
<span style="float:right;">[Varieties.Func.Preservation →](Varieties.Func.Preservation.html)</span>

{% include UALib.Links.md %}
