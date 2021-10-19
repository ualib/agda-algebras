---
layout: default
title : "Varieties.Func.Preservation (The Agda Universal Algebra Library)"
date : "2021-09-24"
author: "agda-algebras development team"
---

### <a id="Equation preservation">Equation preservation for setoid algebras</a>

This is the [Varieties.Func.Preservation][] module of the [Agda Universal Algebra Library][]. In this module we show that identities are preserved by closure operators H, S, and P.  This will establish the easy direction of Birkhoff's HSP Theorem.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Func.Preservation {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -----------------------------------------------
open import Agda.Primitive        using ( Level ; lsuc ) renaming ( Set to Type )
open import Data.Product          using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Function              using ( _∘_ )
open import Function.Bundles      using ( Func )
open import Relation.Binary       using ( Setoid )
open import Relation.Unary        using ( Pred ; _⊆_ ; _∈_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Surjective                using ( IsSurjective ; SurjInv ; SurjInvIsInverseʳ )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; 𝕌[_] ; Lift-Alg )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( hom )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( ≅⨅⁺-refl ; ≅-refl ; ≅-sym ; _≅_ ; ≅-trans ; Lift-≅ )
open import Homomorphisms.Func.HomomorphicImages {𝑆 = 𝑆} using ( IdHomImage )
open import Terms.Basic                     {𝑆 = 𝑆} using ( Term )
open import Terms.Func.Basic                {𝑆 = 𝑆} using ( module Environment)
open import Terms.Func.Operations           {𝑆 = 𝑆} using ( comm-hom-term )
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; _≤c_ )
open import Subalgebras.Func.Properties     {𝑆 = 𝑆} using ( ⨅-≤ ; ≅-trans-≤ ; ≤-reflexive )
open import Varieties.Func.Closure {𝑆 = 𝑆} using ( H ; S ; P ; V ; S-expa ; H-expa ; P-expa
                                                 ; V-expa ; Lift-class )
open import Varieties.Func.Properties {𝑆 = 𝑆} using ( ⊧-S-invar ; ⊧-P-invar ; ⊧-I-invar )
open import Varieties.Func.SoundAndComplete  {𝑆 = 𝑆} using ( _⊧_ ; _⊨_ ; _⊫_ ; Eq ; _≈̇_ ; lhs ; rhs ; _⊢_▹_≈_ ; ThPred)

private variable
 α ρᵃ β ρᵇ γ χ : Level

open SetoidAlgebra using ( Domain )

\end{code}



#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

module _ {𝒦 : Pred(SetoidAlgebra α α)(ov α)} where

 S⊆SP : S 𝒦 ⊆ S (P 𝒦)
 S⊆SP {𝑩} (𝑨 , (kA , B≤A )) = 𝑨 , (pA , B≤A)
  where
  pA : 𝑨 ∈ P 𝒦
  pA = ⊤ , (λ _ → 𝑨) , (λ _ → kA) , ≅⨅⁺-refl

\end{code}


#### <a id="PS-in-SP">PS(𝒦) ⊆ SP(𝒦)</a>

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

 PS⊆SP : P (S 𝒦) ⊆ S (P 𝒦)
 PS⊆SP {𝑩} (I , ( 𝒜 , sA , B≅⨅A )) = Goal
  where
  ℬ : I → SetoidAlgebra α α
  ℬ i = ∣ sA i ∣
  kB : (i : I) → ℬ i ∈ 𝒦
  kB i =  fst ∥ sA i ∥
  ⨅A≤⨅B : ⨅ 𝒜 ≤ ⨅ ℬ
  ⨅A≤⨅B = ⨅-≤ λ i → snd ∥ sA i ∥
  Goal : 𝑩 ∈ S (P 𝒦)
  Goal = ⨅ ℬ , ((I , (ℬ , (kB , ≅-refl))) , ≅-trans-≤ B≅⨅A ⨅A≤⨅B)

\end{code}



#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this subsection with three more inclusion relations that will have bit parts to play later (e.g., in the formal proof of Birkhoff's Theorem).

\begin{code}

 P⊆SP : P 𝒦 ⊆ S (P 𝒦)
 P⊆SP {𝑩} x = S-expa x

 P⊆HSP : P 𝒦 ⊆ H (S (P 𝒦))
 P⊆HSP {𝑩} x = H-expa (S-expa x)

 P⊆V : P 𝒦 ⊆ V 𝒦
 P⊆V = P⊆HSP

 SP⊆V : S (P 𝒦) ⊆ V 𝒦
 SP⊆V x = H-expa x

\end{code}

#### <a id="h-preserves-identities">H preserves identities</a>

First we prove that the closure operator H is compatible with identities that hold in the given class.

\begin{code}

open Func using ( cong ) renaming ( f to _⟨$⟩_ )

module _ {X : Type χ} {p q : Term X}{𝒦 : Pred (SetoidAlgebra α α)(ov α)} where

 H-id1 : 𝒦 ⊫ (p ≈̇ q) → H 𝒦 ⊫ (p ≈̇ q)
 H-id1 σ 𝑩 (𝑨 , kA , BimgOfA) ρ = B⊧pq
  where
  IH : 𝑨 ⊧ (p ≈̇ q)
  IH = σ 𝑨 kA
  open Setoid (Domain 𝑩) using ( _≈_ )
  open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁)
  open Environment 𝑩 using ( ⟦_⟧ )
  open SetoidReasoning (Domain 𝑩)

  φ : hom 𝑨 𝑩
  φ = ∣ BimgOfA ∣
  φE : IsSurjective ∣ φ ∣
  φE = ∥ BimgOfA ∥
  φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
  φ⁻¹ = SurjInv ∣ φ ∣ φE

  ζ : ∀ x → (∣ φ ∣ ⟨$⟩ (φ⁻¹ ∘ ρ) x ) ≈ ρ x
  ζ = λ _ → SurjInvIsInverseʳ ∣ φ ∣ φE

  B⊧pq : (⟦ p ⟧ ⟨$⟩ ρ) ≈ (⟦ q ⟧ ⟨$⟩ ρ)
  B⊧pq = begin
           ⟦ p ⟧ ⟨$⟩ ρ                               ≈˘⟨ cong ⟦ p ⟧ ζ ⟩
           ⟦ p ⟧ ⟨$⟩ (λ x → (∣ φ ∣ ⟨$⟩ (φ⁻¹ ∘ ρ) x)) ≈˘⟨ comm-hom-term φ p (φ⁻¹ ∘ ρ) ⟩
           ∣ φ ∣ ⟨$⟩  (⟦ p ⟧₁ ⟨$⟩ (φ⁻¹ ∘ ρ))         ≈⟨ cong ∣ φ ∣ (IH (φ⁻¹ ∘ ρ)) ⟩
           ∣ φ ∣ ⟨$⟩  (⟦ q ⟧₁ ⟨$⟩ (φ⁻¹ ∘ ρ))         ≈⟨ comm-hom-term φ q (φ⁻¹ ∘ ρ) ⟩
           ⟦ q ⟧ ⟨$⟩ (λ x → (∣ φ ∣ ⟨$⟩ (φ⁻¹ ∘ ρ) x)) ≈⟨ cong ⟦ q ⟧ ζ ⟩
           ⟦ q ⟧ ⟨$⟩ ρ                               ∎

\end{code}

The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we formalize it for completeness.

\begin{code}

 H-id2 : H 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
 H-id2 Hpq 𝑨 kA = Hpq 𝑨 (𝑨 , (kA , IdHomImage))

\end{code}


#### <a id="s-preserves-identities">S preserves identities</a>

\begin{code}

 S-id1 : 𝒦 ⊫ (p ≈̇ q) → S 𝒦 ⊫ (p ≈̇ q)
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

 S-id2 : S 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))


\end{code}



#### <a id="p-preserves-identities">P preserves identities</a>

\begin{code}


 P-id1 : 𝒦 ⊫ (p ≈̇ q) → P 𝒦 ⊫ (p ≈̇ q)
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
  where
  ih : ∀ i → 𝒜 i ⊧ (p ≈̇ q)
  ih i = σ (𝒜 i) (kA i)
  IH : ⨅ 𝒜 ⊧ (p ≈̇ q)
  IH = ⊧-P-invar {p = p}{q} 𝒜 ih

 P-id2 : P 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
 P-id2 PKpq 𝑨 kA = PKpq 𝑨 (P-expa kA)

\end{code}


#### <a id="v-preserves-identities">V preserves identities</a>

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

\begin{code}

module _ {X : Type χ}{p q : Term X} {𝒦 : Pred (SetoidAlgebra α α)(ov α)} where

 V-id1 : 𝒦 ⊫ (p ≈̇ q) → V 𝒦 ⊫ (p ≈̇ q)
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgOfA) = H-id1{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgOfA))
  where
  spA : 𝑨 ∈ S (P 𝒦)
  spA = ⨅A , (p⨅A , A≤⨅A)
  spK⊧pq : S (P 𝒦) ⊫ (p ≈̇ q)
  spK⊧pq = S-id1{p = p}{q} (P-id1{p = p}{q}{𝒦 = 𝒦} σ)

 V-id2 : V 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
 V-id2 Vpq 𝑨 kA = Vpq 𝑨 (V-expa kA)


-- Lift-class : {α β γ : Level} → Pred(SetoidAlgebra α α) (ov α) → Pred(SetoidAlgebra γ γ) (γ ⊔ ov (α ⊔ β))

 Lift-id1 : 𝒦 ⊫ (p ≈̇ q) → Lift-class{α}{β}{γ} 𝒦 ⊫ (p ≈̇ q)
 Lift-id1 {β} {γ} pKq 𝑨 (𝑩 , kB , lB≅A) ρ = Goal
  where
  open Environment 𝑨
  open Setoid (Domain 𝑨) using (_≈_)
  Goal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  Goal = ⊧-I-invar 𝑨 p q (pKq 𝑩 kB) (≅-trans Lift-≅ lB≅A) ρ


\end{code}


#### <a id="class-identities">Class identities</a>

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities modeled by `𝒦`.   We formalize this observation as follows.

\begin{code}

module _ {X : Type χ}{p q : Term X}{𝒦 : Pred (SetoidAlgebra α α)(ov α)} where

 classIds-⊆-VIds : 𝒦 ⊫ (p ≈̇ q)  → (p , q) ∈ ThPred (V 𝒦)
 classIds-⊆-VIds pKq 𝑨 = V-id1{p = p}{q} pKq 𝑨

 VIds-⊆-classIds : (p , q) ∈ ThPred (V 𝒦) → 𝒦 ⊫ (p ≈̇ q)
 VIds-⊆-classIds Thpq 𝑨 kA = V-id2{p = p}{q}{𝒦} Thpq 𝑨 kA

\end{code}


----------------------------

<span style="float:left;">[← Varieties.Func.Properties](Varieties.Func.Properties.html)</span>
<span style="float:right;">[Varieties.Func.FreeAlgebras →](Varieties.Func.FreeAlgebras.html)</span>

{% include UALib.Links.md %}



<!--

#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof of Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally) in the [agda-algebras](https://github.com/ualib/agda-algebras) library as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

 private
  I = ℑ{𝒦 = 𝒦}
  𝒜 = 𝔄{𝒦 = 𝒦}

 P⨅𝒜 : ⨅ 𝒜 ∈ Lift-class (P 𝒦)
 P⨅𝒜 = {!!}

-->
