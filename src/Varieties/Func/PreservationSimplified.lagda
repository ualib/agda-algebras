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

module Varieties.Func.PreservationSimplified {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -----------------------------------------------
open import Agda.Primitive  using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base   using ( _∘_ )
open import Relation.Unary  using ( Pred ; _⊆_ ; _∈_ ) -- ; ｛_｝ ; _∪_ )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Preliminaries                       using ( 𝟙⁺ )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; Lift-Alg ; Lift-Algˡ )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ ; ℑ ; 𝔄 )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅-sym ; Lift-≅ ; ⨅≅ ; Lift-≅ˡ; ≅-refl
                                                          ; Lift-≅ʳ ; Lift-Alg-iso ; ≅-trans; ≅⨅⁺-refl)
open import Subalgebras.Func.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; _≤c_ )
open import Subalgebras.Func.Properties     {𝑆 = 𝑆} using ( A≤B×B≅C→A≤C ; ⨅-≤ ; Lift-≤-Liftˡ ; ≅-trans-≤ )
open import Varieties.Func.ClosureSimplified {𝑆 = 𝑆} using ( H ; S ; P ; V ; subalgebra→S ; Lift-class
                                                          ; S→subalgebra ; S-mono ; H-expa; S-expa) -- ; P-idemp )
-- open H
-- open S
-- open P
-- open V
open _≅_
private variable
 α ρᵃ β ρᵇ : Level

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
  pA = 𝟙⁺ , (λ _ → 𝑨) , (λ _ → kA) , ≅⨅⁺-refl

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


----------------------------

<span style="float:left;">[← Varieties.Func.Properties](Varieties.Func.Properties.html)</span>
<span style="float:right;">[Varieties.Func.FreeAlgebras →](Varieties.Func.FreeAlgebras.html)</span>

{% include UALib.Links.md %}





<!--

module _ {𝒦 : Pred(SetoidAlgebra α α)(ov α)} where

 lemPS⊆SP : {I : Type α}{ℬ : I → SetoidAlgebra α α}
  →         (∀ i → (ℬ i) ≤c 𝒦) → ⨅ ℬ ≤c (P 𝒦)

 lemPS⊆SP {I = I}{ℬ} B≤K = {!!}



#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof of Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally) in the [agda-algebras](https://github.com/ualib/agda-algebras) library as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

 private
  I = ℑ{𝒦 = 𝒦}
  𝒜 = 𝔄{𝒦 = 𝒦}

 P⨅𝒜 : ⨅ 𝒜 ∈ Lift-class (P 𝒦)
 P⨅𝒜 = {!!} 

-->
