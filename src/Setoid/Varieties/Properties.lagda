---
layout: default
title : "Setoid.Varieties.Properties module (The Agda Universal Algebra Library)"
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

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive    using ( Level ; _⊔_ ) renaming ( Set to Type )
open import Data.Product      using ( _,_ )
open import Function.Base     using ( _∘_ )
open import Function.Bundles  using ( Func )
open import Relation.Binary   using ( Setoid )
open import Relation.Unary    using ( Pred ; _∈_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Base.Overture.Preliminaries                     using ( ∣_∣ ; ∥_∥ )
open import Base.Terms.Basic                        {𝑆 = 𝑆} using ( Term ; ℊ )
open import Setoid.Overture.Inverses                        using ( InvIsInverseʳ )
open import Setoid.Overture.Surjective                      using ( SurjInv )
open import Setoid.Algebras.Basic                   {𝑆 = 𝑆} using ( Algebra ; Lift-Algˡ ; ov ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Products                {𝑆 = 𝑆} using ( ⨅ )
open import Setoid.Homomorphisms.Basic              {𝑆 = 𝑆} using ( hom )
open import Setoid.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} using ( _≅_ ; mkiso ; Lift-≅ˡ ; ≅-sym )
open import Setoid.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} using ( _IsHomImageOf_ )
open import Setoid.Terms.Basic                      {𝑆 = 𝑆} using ( 𝑻 ; module Environment )
open import Setoid.Terms.Operations                 {𝑆 = 𝑆} using ( comm-hom-term ; interp-prod )
                                                            using ( term-agreement )
open import Setoid.Subalgebras.Subalgebras          {𝑆 = 𝑆} using ( _≤_ ; SubalgebrasOfClass )
open import Setoid.Varieties.SoundAndComplete       {𝑆 = 𝑆} using ( _⊧_ ; _⊨_ ; _⊫_ ; Eq ; _≈̇_ )
                                                            using ( lhs ; rhs ; _⊢_▹_≈_ )

private variable
 α ρᵃ β ρᵇ χ ℓ : Level

open Func using ( cong ) renaming (f to _⟨$⟩_ )
open Algebra using ( Domain )

\end{code}


#### <a id="algebraic-invariance-of-models">Algebraic invariance of ⊧</a>

The binary relation ⊧ would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism).

\begin{code}


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}
         (𝑩 : Algebra β ρᵇ)(p q : Term X) where
 open Environment 𝑨     using () renaming ( ⟦_⟧   to ⟦_⟧₁ )
 open Environment 𝑩     using () renaming ( ⟦_⟧   to ⟦_⟧₂ )
 open Setoid (Domain 𝑨) using () renaming ( _≈_   to _≈₁_ )
 open Setoid (Domain 𝑩) using ( _≈_ ; sym )
 open SetoidReasoning (Domain 𝑩)

 ⊧-I-invar : 𝑨 ⊧ (p ≈̇ q)  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ (p ≈̇ q)
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

-- module _ (wd : SwellDef){α β χ : Level}{X : Type χ}{𝑨 : Algebra α ρᵃ} where
module _ {X : Type χ}{𝑨 : Algebra α ρᵃ} where

 ⊧-Lift-invar : (p q : Term X) → 𝑨 ⊧ (p ≈̇ q) → Lift-Algˡ 𝑨 β ⊧ (p ≈̇ q)
 ⊧-Lift-invar p q Apq = ⊧-I-invar (Lift-Algˡ 𝑨 _) p q Apq Lift-≅ˡ

 ⊧-lower-invar : (p q : Term X) → Lift-Algˡ 𝑨 β ⊧ (p ≈̇ q)  →  𝑨 ⊧ (p ≈̇ q)
 ⊧-lower-invar p q lApq = ⊧-I-invar 𝑨 p q lApq (≅-sym Lift-≅ˡ)

\end{code}



#### <a id="homomorphic-invariance">Homomorphic invariance of ⊧</a>
Identities modeled by an algebra `𝑨` are also modeled by every homomorphic image of `𝑨`, which fact can be formalized as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where

 ⊧-H-invar : 𝑨 ⊧ (p ≈̇ q) → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ (p ≈̇ q)
 ⊧-H-invar Apq (φh , φE) ρ =
  begin
       ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
   φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong ∣ φh ∣ (Apq (φ⁻¹ ∘ ρ))         ⟩
   φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
       ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ q ⟧   ⟨$⟩               ρ    ∎
  where
  φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
  φ⁻¹ = SurjInv ∣ φh ∣ φE
  private φ = (_⟨$⟩_ ∣ φh ∣)
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
  open Environment 𝑩  using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑩 ]
\end{code}


#### <a id="subalgebraic-invariance">Subalgebraic invariance of ⊧</a>
Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`, which fact can be formalized as follows.

\begin{code}

module _ {X : Type χ}{p q : Term X}{𝑨 : Algebra α ρᵃ}
         {𝑩 : Algebra β ρᵇ} where
 open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment 𝑩 using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
 open Setoid (Domain 𝑨) using ( _≈_ )
 open Setoid (Domain 𝑩) using () renaming ( _≈_ to _≈₂_ )
 open SetoidReasoning (Domain 𝑨)


 ⊧-S-invar : 𝑨 ⊧ (p ≈̇ q) →  𝑩 ≤ 𝑨  →  𝑩 ⊧ (p ≈̇ q)
 ⊧-S-invar Apq B≤A b = goal
  where
  hh : hom 𝑩 𝑨
  hh = ∣ B≤A ∣
  h = _⟨$⟩_ ∣ hh ∣
  ξ : ∀ b → h (⟦ p ⟧₂ ⟨$⟩ b) ≈ h (⟦ q ⟧₂ ⟨$⟩ b)
  ξ b = begin
         h (⟦ p ⟧₂ ⟨$⟩ b)   ≈⟨ comm-hom-term hh p b ⟩
         ⟦ p ⟧₁ ⟨$⟩ (h ∘ b) ≈⟨ Apq (h ∘ b) ⟩
         ⟦ q ⟧₁ ⟨$⟩ (h ∘ b) ≈˘⟨ comm-hom-term hh q b ⟩
         h (⟦ q ⟧₂ ⟨$⟩ b)   ∎
  goal : ⟦ p ⟧₂ ⟨$⟩ b ≈₂ ⟦ q ⟧₂ ⟨$⟩ b
  goal = ∥ B≤A ∥ (ξ b)


\end{code}

Next, identities modeled by a class of algebras is also modeled by all subalgebras of the class.  In other terms, every term equation `(p ≈̇ q)` that is satisfied by all `𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of 𝒦.

\begin{code}
module _ {X : Type χ}{p q : Term X} where

 ⊧-S-class-invar : {𝒦 : Pred (Algebra α ρᵃ) ℓ}
  →                (𝒦 ⊫ (p ≈̇ q)) → ((𝑩 , _) : SubalgebrasOfClass 𝒦 {β}{ρᵇ})
  →                𝑩 ⊧ (p ≈̇ q)
 ⊧-S-class-invar Kpq (𝑩 , 𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (Kpq 𝑨 kA) B≤A

\end{code}



#### <a id="product-invariance">Product invariance of ⊧</a>

An identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in that collection.

\begin{code}

module _ {X : Type χ}{p q : Term X}{I : Type ℓ}(𝒜 : I → Algebra α ρᵃ) where

 ⊧-P-invar : (∀ i → 𝒜 i ⊧ (p ≈̇ q)) → ⨅ 𝒜 ⊧ (p ≈̇ q)
 ⊧-P-invar 𝒜pq a = goal
  where
  open Algebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )
  open Environment   (⨅ 𝒜) using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment using ( ⟦_⟧ )
  open Setoid ⨅A   using ( _≈_ )
  open SetoidReasoning ⨅A

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

 ⊧-P-class-invar : (𝒦 : Pred (Algebra α ρᵃ)(ov α))
  →                𝒦 ⊫ (p ≈̇ q) → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ (p ≈̇ q)

 ⊧-P-class-invar 𝒦 σ K𝒜 = ⊧-P-invar (λ i ρ → σ (𝒜 i) (K𝒜 i) ρ)

\end{code}

Another fact that will turn out to be useful is that a product of a collection of algebras models (p ≈̇ q) if the lift of each algebra in the collection models (p ≈̇ q).

\begin{code}

 ⊧-P-lift-invar : (∀ i → Lift-Algˡ (𝒜 i) β ⊧ (p ≈̇ q))  →  ⨅ 𝒜 ⊧ (p ≈̇ q)
 ⊧-P-lift-invar α = ⊧-P-invar Aipq
  where
  Aipq : ∀ i → (𝒜 i) ⊧ (p ≈̇ q)
  Aipq i = ⊧-lower-invar{𝑨 = (𝒜 i)} p q (α i)

\end{code}



#### <a id="homomorphisc-invariance">Homomorphic invariance of ⊧</a>

If an algebra 𝑨 models an identity (p ≈̇ q), then the pair (p , q) belongs to the kernel of every homomorphism φ : hom (𝑻 X) 𝑨 from the term algebra to 𝑨; that is, every homomorphism from 𝑻 X to 𝑨 maps p and q to the same element of 𝑨.

 \begin{code}

module _ {X : Type χ}{p q : Term X}{𝑨 : Algebra α ρᵃ}(φh : hom (𝑻 X) 𝑨) where
 open Setoid (Domain 𝑨) using ( _≈_ )
 private φ = _⟨$⟩_ ∣ φh ∣

 ⊧-H-ker : 𝑨 ⊧ (p ≈̇ q) → φ p ≈ φ q
 ⊧-H-ker β =
  begin
   φ p                ≈⟨ cong ∣ φh ∣ (term-agreement p)⟩
   φ (⟦ p ⟧ ⟨$⟩ ℊ)    ≈⟨ comm-hom-term φh p ℊ ⟩
   ⟦ p ⟧₂ ⟨$⟩ (φ ∘ ℊ) ≈⟨ β (φ ∘ ℊ) ⟩
   ⟦ q ⟧₂ ⟨$⟩ (φ ∘ ℊ) ≈˘⟨ comm-hom-term φh q ℊ ⟩
   φ (⟦ q ⟧ ⟨$⟩ ℊ)    ≈˘⟨ cong ∣ φh ∣ (term-agreement q)⟩
   φ q                ∎

  where
  open SetoidReasoning (Domain 𝑨)
  open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
  open Environment (𝑻 X) using ( ⟦_⟧ )

\end{code}

---------------------------------

<span style="float:left;">[← Setoid.Varieties.Closure](Setoid.Varieties.Closure.html)</span>
<span style="float:right;">[Setoid.Varieties.Preservation →](Setoid.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}
