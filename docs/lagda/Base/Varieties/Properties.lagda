---
layout: default
title : "Base.Varieties.Properties module (The Agda Universal Algebra Library)"
date : "2021-06-24"
author: "agda-algebras development team"
---

### <a id="properties-of-the-models-relation">Properties of the models relation</a>

We prove some closure and invariance properties of the relation `⊧`.  In particular,
we prove the following facts (which we use later in our proof of Birkhoff's HSP Theorem).

*  [Algebraic invariance](#algebraic-invariance). `⊧` is an *algebraic invariant*
   (stable under isomorphism).

*  [Subalgebraic invariance](#subalgebraic-invariance). Identities modeled by a
   class of algebras are also modeled by all subalgebras of algebras in the class.

*  [Product invariance](#product-invariance). Identities modeled by a class of
   algebras are also modeled by all products of algebras in the class.

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Varieties.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( _∘_ )
open import Level           using ( Level ; _⊔_ )
open import Relation.Unary  using ( Pred ; _∈_ ; _⊆_ ; ⋂ )
open import Axiom.Extensionality.Propositional
                            using () renaming ( Extensionality to funext )
open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ; refl ; module ≡-Reasoning ; cong )

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Overture                     using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Functions               using ( IsInjective ; ∘-injective )
open import Base.Equality                using ( SwellDef ; DFunExt )
open import Base.Algebras       {𝑆 = 𝑆}  using ( Algebra ; Lift-Alg ; ov ; ⨅ )
open import Base.Homomorphisms  {𝑆 = 𝑆}  using ( hom ; ∘-hom ; _≅_ ; mkiso )
                                         using ( Lift-≅ ; ≅-sym ; ≅-trans )
open import Base.Terms          {𝑆 = 𝑆}  using ( Term ; 𝑻 ; lift-hom ; _⟦_⟧ )
                                         using ( comm-hom-term ; interp-prod )
                                         using ( term-agreement )
open import Base.Subalgebras    {𝑆 = 𝑆}  using ( _≤_ ; SubalgebraOfClass )
                                         using ( iso→injective )
open import Base.Varieties.EquationalLogic
                                {𝑆 = 𝑆}  using ( _⊧_≈_ ; _⊫_≈_ )
\end{code}


#### <a id="algebraic-invariance-of-models">Algebraic invariance of ⊧</a>

The binary relation ⊧ would be practically useless if it were not an *algebraic
invariant* (invariant under isomorphism).

\begin{code}

open Term
open ≡-Reasoning
open _≅_

module _  (wd : SwellDef){α β χ : Level}{X : Type χ}{𝑨 : Algebra α}
          (𝑩 : Algebra β)(p q : Term X) where

 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q

 ⊧-I-invar Apq (mkiso f g f∼g g∼f) x =
  (𝑩 ⟦ p ⟧) x                       ≡⟨ i p ⟩
  (𝑩 ⟦ p ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘ x)   ≡⟨ (ii p) ⁻¹ ⟩
  ∣ f ∣ ((𝑨 ⟦ p ⟧) (∣ g ∣ ∘ x))     ≡⟨ cong ∣ f ∣ (Apq (∣ g ∣ ∘ x))  ⟩
  ∣ f ∣ ((𝑨 ⟦ q ⟧) (∣ g ∣ ∘ x))     ≡⟨ ii q ⟩
  (𝑩 ⟦ q ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘  x)  ≡⟨ (i q)⁻¹ ⟩
  (𝑩 ⟦ q ⟧) x                       ∎
  where
  i : ∀ t → (𝑩 ⟦ t ⟧) x ≡ (𝑩 ⟦ t ⟧) λ x₁ → ∣ f ∣ (∣ g ∣ (x x₁))
  i t = wd χ β (𝑩 ⟦ t ⟧) x (∣ f ∣ ∘ ∣ g ∣ ∘ x) λ i → ( f∼g (x i))⁻¹

  ii :  ∀ t
   →    ∣ f ∣((𝑨 ⟦ t ⟧) λ x₁ → ∣ g ∣(x x₁)) ≡ (𝑩 ⟦ t ⟧) λ x₁ → ∣ f ∣(∣ g ∣(x x₁))
  ii t = comm-hom-term (wd 𝓥 β) 𝑩 f t (∣ g ∣ ∘ x)
\end{code}


In the above proof we showed `𝑩 ⊧ p ≈ q` by showing that `𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧` holds
*extensionally*, that is, `∀ x, 𝑩 ⟦ p ⟧ x ≡ 𝑩 ⟦q ⟧ x`.

#### <a id="lift-invariance-of-models">Lift-invariance of ⊧</a>
The `⊧` relation is also invariant under the algebraic lift and lower operations.

\begin{code}

module _ (wd : SwellDef){α β χ : Level}{X : Type χ}{𝑨 : Algebra α} where

 ⊧-Lift-invar : (p q : Term X) → 𝑨 ⊧ p ≈ q → Lift-Alg 𝑨 β ⊧ p ≈ q
 ⊧-Lift-invar p q Apq = ⊧-I-invar wd (Lift-Alg 𝑨 _) p q Apq Lift-≅

 ⊧-lower-invar : (p q : Term X) → Lift-Alg 𝑨 β ⊧ p ≈ q  →  𝑨 ⊧ p ≈ q
 ⊧-lower-invar p q lApq = ⊧-I-invar wd 𝑨 p q lApq (≅-sym Lift-≅)
\end{code}



#### <a id="subalgebraic-invariance">Subalgebraic invariance of ⊧</a>

Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`,
which fact can be formalized as follows.

\begin{code}

module _ (wd : SwellDef){χ : Level}{𝓤 𝓦 : Level}{X : Type χ} where

 ⊧-S-invar : {𝑨 : Algebra 𝓤}(𝑩 : Algebra 𝓦){p q : Term X}
  →          𝑨 ⊧ p ≈ q  →  𝑩 ≤ 𝑨  →  𝑩 ⊧ p ≈ q
 ⊧-S-invar {𝑨} 𝑩 {p}{q} Apq B≤A b = (∥ B≤A ∥) (ξ b)
  where
  h : hom 𝑩 𝑨
  h = ∣ B≤A ∣

  ξ : ∀ b → ∣ h ∣ ((𝑩 ⟦ p ⟧) b) ≡ ∣ h ∣ ((𝑩 ⟦ q ⟧) b)
  ξ b =  ∣ h ∣((𝑩 ⟦ p ⟧) b)    ≡⟨ comm-hom-term (wd 𝓥 𝓤) 𝑨 h p b ⟩
         (𝑨 ⟦ p ⟧)(∣ h ∣ ∘ b)  ≡⟨ Apq (∣ h ∣ ∘ b) ⟩
         (𝑨 ⟦ q ⟧)(∣ h ∣ ∘ b)  ≡⟨ (comm-hom-term (wd 𝓥 𝓤) 𝑨 h q b)⁻¹ ⟩
         ∣ h ∣((𝑩 ⟦ q ⟧) b)    ∎

\end{code}

Next, identities modeled by a class of algebras is also modeled by all subalgebras
of the class.  In other terms, every term equation `p ≈ q` that is satisfied by all
`𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of `𝒦`.

 \begin{code}

 ⊧-S-class-invar :  {𝒦 : Pred (Algebra 𝓤)(ov 𝓤)}(p q : Term X)
  →                 𝒦 ⊫ p ≈ q → (𝑩 : SubalgebraOfClass 𝒦) → ∣ 𝑩 ∣ ⊧ p ≈ q

 ⊧-S-class-invar p q Kpq (𝑩 , 𝑨 , SA , (ka , B≅SA)) =
  ⊧-S-invar 𝑩 {p}{q}((Kpq ka)) (h , hinj)
   where
   h : hom 𝑩 𝑨
   h = ∘-hom 𝑩 𝑨 (to B≅SA) ∣ snd SA ∣
   hinj : IsInjective ∣ h ∣
   hinj = ∘-injective (iso→injective B≅SA) ∥ snd SA ∥
\end{code}


#### <a id="product-invariance-of-models">Product invariance of ⊧</a>

An identity satisfied by all algebras in an indexed collection is also satisfied
by the product of algebras in that collection.

\begin{code}

module _  (fe : DFunExt)(wd : SwellDef)
          {α β χ : Level}{I : Type β}
          (𝒜 : I → Algebra α){X : Type χ} where

 ⊧-P-invar : (p q : Term X) → (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar p q 𝒜pq a = goal
  where
  -- This is where function extensionality is used.
  ξ : (λ i → (𝒜 i ⟦ p ⟧) (λ x → (a x) i)) ≡ (λ i → (𝒜 i ⟦ q ⟧)  (λ x → (a x) i))
  ξ = fe β α λ i → 𝒜pq i (λ x → (a x) i)

  goal : (⨅ 𝒜 ⟦ p ⟧) a  ≡  (⨅ 𝒜 ⟦ q ⟧) a
  goal =  (⨅ 𝒜 ⟦ p ⟧) a                      ≡⟨ interp-prod (wd 𝓥 (α ⊔ β)) p 𝒜 a ⟩
          (λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x)i))  ≡⟨ ξ ⟩
          (λ i → (𝒜 i ⟦ q ⟧)(λ x → (a x)i))  ≡⟨ (interp-prod (wd 𝓥 (α ⊔ β)) q 𝒜 a)⁻¹ ⟩
          (⨅ 𝒜 ⟦ q ⟧) a                      ∎

\end{code}

An identity satisfied by all algebras in a class is also satisfied by the product
of algebras in the class.

\begin{code}

 ⊧-P-class-invar :  (𝒦 : Pred (Algebra α)(ov α)){p q : Term X}
  →                 𝒦 ⊫ p ≈ q → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ p ≈ q

 ⊧-P-class-invar 𝒦 {p}{q}σ K𝒜 = ⊧-P-invar p q λ i → σ (K𝒜 i)

\end{code}

Another fact that will turn out to be useful is that a product of a collection of
algebras models ``p ≈ q`` if the lift of each algebra in the collection models ``p ≈ q``.

\begin{code}

 ⊧-P-lift-invar : (p q : Term X) → (∀ i → Lift-Alg (𝒜 i) β ⊧ p ≈ q)  →  ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-lift-invar p q α = ⊧-P-invar p q Aipq
  where
  Aipq : ∀ i → (𝒜 i) ⊧ p ≈ q
  Aipq i = ⊧-lower-invar wd p q (α i)
\end{code}

#### <a id="homomorphisc-invariance-of-models">Homomorphic invariance of ⊧</a>

If an algebra `𝑨` models an identity `p ≈ q`, then the pair `(p , q)`
belongs to the kernel of every homomorphism `φ : hom (𝑻 X) 𝑨` from the term
algebra to `𝑨`; that is, every homomorphism from `𝑻 X` to `𝑨` maps `p` and
`q` to the same element of `𝑨`.

 \begin{code}

module _ (wd : SwellDef){α χ : Level}{X : Type χ}{𝑨 : Algebra α} where

 ⊧-H-invar : {p q : Term X}(φ : hom (𝑻 X) 𝑨) → 𝑨 ⊧ p ≈ q  →  ∣ φ ∣ p ≡ ∣ φ ∣ q

 ⊧-H-invar {p}{q}φ β =  ∣ φ ∣ p                ≡⟨ i p ⟩
                        ∣ φ ∣((𝑻 X ⟦ p ⟧) ℊ)   ≡⟨ ii p ⟩
                        (𝑨 ⟦ p ⟧) (∣ φ ∣ ∘ ℊ)  ≡⟨ β (∣ φ ∣ ∘ ℊ ) ⟩
                        (𝑨 ⟦ q ⟧) (∣ φ ∣ ∘ ℊ)  ≡⟨ (ii q)⁻¹ ⟩
                        ∣ φ ∣ ((𝑻 X ⟦ q ⟧) ℊ)  ≡⟨ (i q)⁻¹ ⟩
                        ∣ φ ∣ q                ∎

  where
  i : ∀ t → ∣ φ ∣ t ≡ ∣ φ ∣ ((𝑻 X ⟦ t ⟧) ℊ)
  i t = cong ∣ φ ∣(term-agreement(wd 𝓥 (ov χ)) t)
  ii : ∀ t → ∣ φ ∣ ((𝑻 X ⟦ t ⟧) ℊ) ≡ (𝑨 ⟦ t ⟧) (λ x → ∣ φ ∣ (ℊ x))
  ii t = comm-hom-term (wd 𝓥 α) 𝑨 φ t ℊ
\end{code}

More generally, an identity is satisfied by all algebras in a class if and only if
that identity is invariant under all homomorphisms from the term algebra `𝑻 X`
into algebras of the class. More precisely, if `𝒦` is a class of `𝑆`-algebras and
`𝑝`, `𝑞` terms in the language of `𝑆`, then,
```
  𝒦 ⊧ p ≈ q  ⇔  ∀ 𝑨 ∈ 𝒦,  ∀ φ : hom (𝑻 X) 𝑨,  φ ∘ (𝑻 X)⟦ p ⟧ = φ ∘ (𝑻 X)⟦ q ⟧.
```
\begin{code}

module _ (wd : SwellDef){α χ : Level}{X : Type χ}{𝒦 : Pred (Algebra α)(ov α)}  where

 -- ⇒ (the "only if" direction)
 ⊧-H-class-invar :  {p q : Term X}
  →                 𝒦 ⊫ p ≈ q → ∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∀ a
  →                 ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)

 ⊧-H-class-invar {p = p}{q} σ 𝑨 φ ka a = ξ
  where
   ξ : ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)
   ξ =  ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a)  ≡⟨ comm-hom-term (wd 𝓥 α) 𝑨 φ p a ⟩
        (𝑨 ⟦ p ⟧)(∣ φ ∣ ∘ a)   ≡⟨ (σ ka) (∣ φ ∣ ∘ a) ⟩
        (𝑨 ⟦ q ⟧)(∣ φ ∣ ∘ a)   ≡⟨ (comm-hom-term (wd 𝓥 α) 𝑨 φ q a)⁻¹ ⟩
        ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)  ∎

 -- ⇐ (the "if" direction)
 ⊧-H-class-coinvar :  {p q : Term X}
  →                   (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∀ a → ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a))
  →                   𝒦 ⊫ p ≈ q

 ⊧-H-class-coinvar {p}{q} β {𝑨} ka = goal
  where
  φ : (a : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
  φ a = lift-hom 𝑨 a

  goal : 𝑨 ⊧ p ≈ q
  goal a =  (𝑨 ⟦ p ⟧)(∣ φ a ∣ ∘ ℊ)     ≡⟨(comm-hom-term (wd 𝓥 α) 𝑨 (φ a) p ℊ)⁻¹ ⟩
            (∣ φ a ∣ ∘ (𝑻 X ⟦ p ⟧)) ℊ  ≡⟨ β 𝑨 (φ a) ka ℊ ⟩
            (∣ φ a ∣ ∘ (𝑻 X ⟦ q ⟧)) ℊ  ≡⟨ (comm-hom-term (wd 𝓥 α) 𝑨 (φ a) q ℊ) ⟩
            (𝑨 ⟦ q ⟧)(∣ φ a ∣ ∘ ℊ)     ∎
\end{code}

---------------------------------

<span style="float:left;">[← Base.Varieties.Closure](Base.Varieties.Closure.html)</span>
<span style="float:right;">[Base.Varieties.Preservation →](Base.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}
