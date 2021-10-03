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
open import Agda.Primitive  using ( _⊔_ ; lsuc ; Level ) renaming ( Set   to Type )
open import Data.Product    using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd ) 
open import Function.Base   using ( _∘_ )
open import Relation.Unary  using ( Pred ; _⊆_ ; _∈_ ) -- ; ｛_｝ ; _∪_ )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; Lift-Alg ; Lift-Algˡ )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ ; ℑ ; 𝔄 )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅-sym ; Lift-≅ ; ⨅≅ ; Lift-≅ˡ; ≅-refl
                                                          ; Lift-≅ʳ ; Lift-Alg-iso ; ≅-trans)
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; _≤c_ )
open import Subalgebras.Func.Properties     {𝑆 = 𝑆} using ( A≤B×B≅C→A≤C ; ⨅-≤ ; Lift-≤-Liftˡ )
open import Varieties.Func.Closure          {𝑆 = 𝑆} using ( H ; S ; P ; V ; subalgebra→S
                                                          ; S→subalgebra ; S-mono ; P-idemp )
open H
open S
open P
open V
open _≅_
private variable
 α ρᵃ β ρᵇ : Level

\end{code}



#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

S⊆SP' : {α β γ : Level}(𝒦 : Pred (SetoidAlgebra α α)(ov α))
 →     S{α}{α ⊔ β ⊔ γ} 𝒦 ⊆ S{α ⊔ β ⊔ γ}{α ⊔ β ⊔ γ} (P{α}{β}{γ} 𝒦)
S⊆SP' {α} {β} {γ} 𝒦 {𝑨} (sbase{𝑩} kB B≅A) = Goal
 where
 PB : 𝑩 ∈ P{α}{α}{α} 𝒦
 PB = pbase kB ≅-refl
 PlB : Lift-Alg 𝑩 β β ∈ P{α}{β}{β} 𝒦
 PlB = piso (pbase kB Lift-≅) ≅-refl

 PllB : Lift-Alg 𝑩 (β ⊔ γ) (β ⊔ γ) ∈ P{α}{β}{γ} 𝒦
 PllB = piso PlB (≅-trans (≅-sym Lift-≅) Lift-≅)


 Goal : 𝑨 ∈ S{α ⊔ β ⊔ γ}{α ⊔ β ⊔ γ} (P{α}{β}{γ} 𝒦)
 Goal = sbase PllB (≅-trans (≅-sym Lift-≅) B≅A)


S⊆SP' {α} {β} {γ} 𝒦 {𝑨} (ssub{𝑩} sB A≤B) = ssub (S⊆SP' 𝒦 sB) A≤B


S⊆SP : {α β γ : Level}(𝒦 : Pred (SetoidAlgebra α α)(ov α))
 →     S{α}{α ⊔ β ⊔ γ} 𝒦 ⊆ S{α}{α ⊔ β ⊔ γ} (P{α}{α}{α} 𝒦)

S⊆SP{α}{β}{γ} 𝒦 {𝑨} (sbase{𝑩} kB B≅A) = Goal
 where
 PB : 𝑩 ∈ P{α}{α}{α} 𝒦
 PB = pbase kB ≅-refl
 Goal : 𝑨 ∈ S{α}{α ⊔ β ⊔ γ} (P{α}{α}{α} 𝒦)
 Goal = sbase PB B≅A

S⊆SP{α}{β}{γ} 𝒦 {𝑨} (ssub{𝑩} x x₁) = Goal
 where
 SPB : 𝑩 ∈ S{α}{α ⊔ β ⊔ γ} (P{α}{α}{α} 𝒦)
 SPB = S⊆SP{β = β}{γ} 𝒦 x
 Goal : 𝑨 ∈ S{α}{α ⊔ β ⊔ γ} (P{α}{α}{α} 𝒦)
 Goal = ssub SPB x₁

\end{code}


We need to formalize one more lemma before arriving the main objective of this section, which is the proof of the inclusion PS⊆SP.

\begin{code}

module _ {α β γ : Level}{𝒦 : Pred(SetoidAlgebra α α)(ov α)} where

 lemPS⊆SP : {I : Type β}{ℬ : I → SetoidAlgebra α α}
  →         (∀ i → (ℬ i) ≤c 𝒦) → ⨅ ℬ ≤c (P{α}{β}{γ} 𝒦)

 lemPS⊆SP {I = I}{ℬ} B≤K = ⨅ lA , P⨅lA , ⨅B≤⨅lA
  where
  lA : I → SetoidAlgebra (α ⊔ β ⊔ γ)(α ⊔ β ⊔ γ)
  lA = λ i → Lift-Alg ∣ B≤K i ∣ (β ⊔ γ) (β ⊔ γ)

  P⨅lA : ⨅ lA ∈ P 𝒦
  P⨅lA = {!!} -- pprod (λ i → pbase (fst ∥ B≤K i ∥))

  B≤A : ∀ i → ℬ i ≤ ∣ B≤K i ∣
  B≤A = λ i → snd ∥ B≤K i ∥

  ⨅B≤⨅lA : ⨅ ℬ ≤ ⨅ lA
  ⨅B≤⨅lA = A≤B×B≅C→A≤C (⨅-≤ B≤A) (⨅≅ (λ _ → Lift-≅))

 lemPS⊆SP' : {I : Type β}{ℬ : I → SetoidAlgebra α α}
  →          (∀ i → (ℬ i) ∈ S{α}{α} 𝒦) → (⨅ ℬ) ∈ S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦)
 lemPS⊆SP'{I = I}{ℬ} sB = {!!} -- subalgebra→S (lemPS⊆SP (S→subalgebra ∘ sB))

\end{code}



#### <a id="PS-in-SP">PS(𝒦) ⊆ SP(𝒦)</a>

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

module _ {α β γ : Level} {𝒦 : Pred (SetoidAlgebra α α)(ov α)} where

 PS⊆SP : P{α ⊔ β}{β}{γ} (S{α}{β} 𝒦) ⊆ S{α ⊔ β ⊔ γ}{α ⊔ β ⊔ γ} (P{α}{β}{γ} 𝒦)

 PS⊆SP (pbase{𝑨}{𝑩} sA A≅B) = {!!}
 PS⊆SP (pprod x) = {!!}
 PS⊆SP (piso x x₁) = {!!}
\end{code}



#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this subsection with three more inclusion relations that will have bit parts to play later (e.g., in the formal proof of Birkhoff's Theorem).

\begin{code}

P⊆V : {α β : Level}{𝒦 : Pred (SetoidAlgebra α α)(ov α)} → P{α}{β} 𝒦 ⊆ V{α}{β} 𝒦

P⊆V x = {!!}

SP⊆V : {α β : Level}{𝒦 : Pred (SetoidAlgebra α α)(ov α)}
 →     S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦) ⊆ V 𝒦

SP⊆V x = {!!}
\end{code}


#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof of Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally) in the [agda-algebras](https://github.com/ualib/agda-algebras) library as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

Before doing so, we need to redefine the class product so that each factor comes with a map from the type `X` of variable symbols into that factor.  We will explain the reason for this below.

\begin{code}

module _ {α : Level}{𝒦 : Pred (SetoidAlgebra α α) (ov α)} where

 private
  I = ℑ{𝒦 = 𝒦}
  𝒜 = 𝔄{𝒦 = 𝒦}
 open P

 P⨅𝒜 : ⨅ 𝒜 ∈ P{α}{ov α} 𝒦
 P⨅𝒜 = piso (pprod PAi) (⨅≅ λ _ → ≅-sym Lift-≅)
  where
  PAi : (i : I) → Lift-Alg (𝒜 i) (ov α)(ov α) ∈ P{α}{ov α} 𝒦
  PAi i = {!!} -- pbase ∥ i ∥

\end{code}


----------------------------

<span style="float:left;">[← Varieties.Func.Properties](Varieties.Func.Properties.html)</span>
<span style="float:right;">[Varieties.Func.FreeAlgebras →](Varieties.Func.FreeAlgebras.html)</span>

{% include UALib.Links.md %}
