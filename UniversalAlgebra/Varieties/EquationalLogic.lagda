---
layout: default
title : Varieties.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

This is the [Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level renaming ( suc to lsuc )
open import Algebras.Basic


module Varieties.EquationalLogic {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where



-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ )
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary          using    ( _∈_ ; Pred ; _⊆_ )



-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ )
open import Overture.Inverses            using (IsInjective)
open import Relations.Truncation         using ( hfunext )

open import Algebras.Products          𝑆 using ( ov ; ⨅ ; 𝔄 ; class-product)
open import Homomorphisms.Basic        𝑆 using (hom; 𝒾𝒹; ∘-hom; is-homomorphism)
open import Homomorphisms.Isomorphisms 𝑆 using (_≅_ ; ≅-sym ; Lift-≅ ; ≅-trans
                                               ; ≅-refl ; Lift-Alg-iso ; ⨅≅
                                               ; Lift-Alg-associative ; Lift-Alg-⨅≅ )

open import Subalgebras.Subalgebras    𝑆 using ( _≤_ ; _IsSubalgebraOfClass_ ; Lift-≤-Lift
                                               ; SubalgebraOfClass ; iso→injective
                                               ; ≤-Lift ; _IsSubalgebraOf_ )
private variable α β γ : Level

import Varieties.Closure.H 𝑆 as VC-H
import Varieties.Closure.S 𝑆 as VC-S
import Varieties.Closure.P 𝑆 as VC-P
import Varieties.Closure.V 𝑆 as VC-V

\end{code}


Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

A straight-forward verification confirms that H, S, and P are **closure operators** (expansive, monotone, and idempotent).  A class 𝒦 of 𝑆-algebras is said to be *closed under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, 𝒦 is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`). The operators H, S, and P can be composed with one another repeatedly, forming yet more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under isomorphism.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define an inductive type `V` which simultaneously represents closure under all three operators, `H`, `S`, and `P`.


We import some of these things from sub-modules.
\begin{code}
open VC-H using (H) public
open VC-S public
open VC-P public
open VC-V public
\end{code}


#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

S⊆SP : (𝒦 : Pred (Algebra α 𝑆)(ov α))
 →     S{α}{β} 𝒦 ⊆ S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦)

S⊆SP {α} {β} 𝒦 {.(Lift-Alg 𝑨 β)}(sbase{𝑨} x) = siso spllA(≅-sym Lift-≅)
 where
 llA : Algebra (α ⊔ β) 𝑆
 llA = Lift-Alg (Lift-Alg 𝑨 β) (α ⊔ β)

 spllA : llA ∈ S (P 𝒦)
 spllA = sbase{α ⊔ β}{α ⊔ β} (pbase x)

S⊆SP {α} {β} 𝒦 {.(Lift-Alg 𝑨 β)}(slift{𝑨} x) = subalgebra→S lAsc
 where
 splAu : 𝑨 ∈ S(P 𝒦)
 splAu = S⊆SP{α}{α} 𝒦 x

 Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
 Asc = S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} splAu

 lAsc : (Lift-Alg 𝑨 β) IsSubalgebraOfClass (P 𝒦)
 lAsc = Lift-Alg-subP' Asc
S⊆SP {α} {β} 𝒦 {𝑩}(ssub{𝑨} sA B≤A) = ssub (subalgebra→S lAsc)( ≤-Lift 𝑨 B≤A )
 where
  lA : Algebra (α ⊔ β) 𝑆
  lA = Lift-Alg 𝑨 β

  splAu : 𝑨 ∈ S (P 𝒦)
  splAu = S⊆SP{α}{α} 𝒦 sA

  Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
  Asc = S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P 𝒦)
  lAsc = Lift-Alg-subP' Asc

S⊆SP {α = α}{β} 𝒦 {𝑩}(siso{𝑨} sA A≅B) = siso{α ⊔ β}{α ⊔ β} lAsp lA≅B
 where
 lA : Algebra (α ⊔ β) 𝑆
 lA = Lift-Alg 𝑨 β

 lAsc : lA IsSubalgebraOfClass (P 𝒦)
 lAsc = Lift-Alg-subP' (S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} (S⊆SP 𝒦 sA))

 lAsp : lA ∈ S(P 𝒦)
 lAsp = subalgebra→S{α ⊔ β}{α ⊔ β}{P{α}{β} 𝒦}{lA} lAsc

 lA≅B : lA ≅ 𝑩
 lA≅B = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}



We need to formalize one more lemma before arriving the main objective of this section, which is the proof of the inclusion PS⊆SP.

\begin{code}

module _ {α β : Level} {𝒦 : Pred(Algebra α 𝑆)(ov α)} where

 lemPS⊆SP : hfunext β α → funext β α → {I : Type β}{ℬ : I → Algebra α 𝑆}
  →         (∀ i → (ℬ i) IsSubalgebraOfClass 𝒦)
  →         ⨅ ℬ IsSubalgebraOfClass (P{α}{β} 𝒦)

 lemPS⊆SP hwu fwu {I}{ℬ} B≤K = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜) , ξ , (⨅≅ {fiu = fwu}{fiw = fwu} B≅SA)
  where
  𝒜 : I → Algebra α 𝑆
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra α 𝑆
  SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

  B≅SA : ∀ i → ℬ i ≅ SA i
  B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → fst ∣ SA≤𝒜 i ∣

  hinj : ∀ i → IsInjective (h i)
  hinj = λ i → snd (snd ∣ ∥ B≤K i ∥ ∣)

  σ : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
  σ = λ x i → (h i) (x i)
  ν : is-homomorphism (⨅ SA) (⨅ 𝒜) σ
  ν = λ 𝑓 𝒂 → fwu λ i → (snd ∣ SA≤𝒜 i ∣) 𝑓 (λ x → 𝒂 x i)

  σinj : IsInjective σ
  σinj σxσy = fwu λ i → (hinj i)(cong-app σxσy i)

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = (σ , ν) , σinj

  ξ : ⨅ 𝒜 ∈ P 𝒦
  ξ = produ (λ i → P-expa (∣ snd ∥ B≤K i ∥ ∣))


\end{code}



#### <a id="PS-in-SP">PS(𝒦) ⊆ SP(𝒦)</a>

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

module _ {α : Level} {fovu : funext (ov α) (ov α)}{𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 PS⊆SP : -- extensionality assumptions:
            hfunext (ov α)(ov α)

  →      P{ov α}{ov α} (S{α}{ov α} 𝒦) ⊆ S{ov α}{ov α} (P{α}{ov α} 𝒦)

 PS⊆SP _ (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP _ (pbase (slift{𝑨} x)) = slift (S⊆SP{α}{ov α} 𝒦 (slift x))
 PS⊆SP _ (pbase{𝑩}(ssub{𝑨} sA B≤A)) = siso(ssub(S⊆SP 𝒦 (slift sA))(Lift-≤-Lift (ov(α)){𝑨}(ov(α))B≤A)) ≅-refl
 PS⊆SP _ (pbase (siso{𝑨}{𝑩} x A≅B)) = siso (S⊆SP 𝒦 (slift x)) ( Lift-Alg-iso A≅B )
 PS⊆SP hfe (pliftu x) = slift (PS⊆SP hfe x)
 PS⊆SP hfe (pliftw x) = slift (PS⊆SP hfe x)

 PS⊆SP hfe (produ{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{α}{ov α} 𝒦)
   ξ i = S→subalgebra (PS⊆SP hfe (x i))

   η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov α}{ov α} (P{α}{ov α} 𝒦))
   η = lemPS⊆SP hfe fovu {I} {𝒜} ξ

 PS⊆SP hfe (prodw{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{α}{ov α} 𝒦)
   ξ i = S→subalgebra (PS⊆SP hfe (x i))

   η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov α}{ov α} (P{α}{ov α} 𝒦))
   η = lemPS⊆SP hfe fovu  {I} {𝒜} ξ

 PS⊆SP hfe (pisow{𝑨}{𝑩} pA A≅B) = siso (PS⊆SP hfe pA) A≅B

\end{code}



#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this subsection with three more inclusion relations that will have bit parts to play later (e.g., in the formal proof of Birkhoff's Theorem).

\begin{code}

P⊆V : {α β : Level}{𝒦 : Pred (Algebra α 𝑆)(ov α)} → P{α}{β} 𝒦 ⊆ V{α}{β} 𝒦

P⊆V (pbase x) = vbase x
P⊆V{α} (pliftu x) = vlift (P⊆V{α}{α} x)
P⊆V{α}{β} (pliftw x) = vliftw (P⊆V{α}{β} x)
P⊆V (produ x) = vprodu (λ i → P⊆V (x i))
P⊆V (prodw x) = vprodw (λ i → P⊆V (x i))
P⊆V (pisow x x₁) = visow (P⊆V x) x₁


SP⊆V : {α β : Level}{𝒦 : Pred (Algebra α 𝑆)(ov α)}
 →     S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦) ⊆ V 𝒦

SP⊆V (sbase{𝑨} PCloA) = P⊆V (pisow PCloA Lift-≅)
SP⊆V (slift{𝑨} x) = vliftw (SP⊆V x)
SP⊆V (ssub{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (siso x x₁) = visow (SP⊆V x) x₁

\end{code}
#### <a id="V-is-closed-under-lift">V is closed under lift</a>

As mentioned earlier, a technical hurdle that must be overcome when formalizing proofs in Agda is the proper handling of universe levels. In particular, in the proof of the Birkhoff's theorem, for example, we will need to know that if an algebra 𝑨 belongs to the variety V 𝒦, then so does the lift of 𝑨.  Let us get the tedious proof of this technical lemma out of the way.

Above we proved that `SP(𝒦) ⊆ V(𝒦)`, and we did so under fairly general assumptions about the universe level parameters.  Unfortunately, this is sometimes not quite general enough, so we now prove the inclusion again for the specific universe parameters that align with subsequent applications of this result.


\begin{code}

module _ {α : Level}  {fe₀ : funext (ov α) α}
         {fe₁ : funext ((ov α) ⊔ (lsuc (ov α))) (lsuc (ov α))}
         {fe₂ : funext (ov α) (ov α)}
         {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 open Vlift {α}{fe₀}{fe₁}{fe₂}{𝒦}

 SP⊆V' : S{ov α}{lsuc (ov α)} (P{α}{ov α} 𝒦) ⊆ V 𝒦

 SP⊆V' (sbase{𝑨} x) = visow (VlA (SP⊆V (sbase x))) (≅-sym (Lift-Alg-associative 𝑨))
 SP⊆V' (slift x) = VlA (SP⊆V x)

 SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw (VlA (SP⊆V spA)) B≤lA
  where
   B≤lA : 𝑩 ≤ Lift-Alg 𝑨 (lsuc (ov α))
   B≤lA = ≤-Lift 𝑨 B≤A

 SP⊆V' (siso{𝑨}{𝑩} x A≅B) = visow (VlA (SP⊆V x)) Goal
  where
   Goal : Lift-Alg 𝑨 (lsuc (ov α)) ≅ 𝑩
   Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}


#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof of Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally) in the [UniversalAlgebra][] library as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

Before doing so, we need to redefine the class product so that each factor comes with a map from the type `X` of variable symbols into that factor.  We will explain the reason for this below.

\begin{code}

module class-products-with-maps {α : Level}
 {X : Type α}
 {fe𝓕α : funext (ov α) α}
 {fe₁ : funext ((ov α) ⊔ (lsuc (ov α))) (lsuc (ov α))}
 {fe₂ : funext (ov α) (ov α)}
 (𝒦 : Pred (Algebra α 𝑆)(ov α))
 where

 ℑ' : Type (ov α)
 ℑ' = Σ[ 𝑨 ∈ (Algebra α 𝑆) ] ((𝑨 ∈ S{α}{α} 𝒦) × (X → ∣ 𝑨 ∣))

\end{code}
Notice that the second component of this dependent pair type is  `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`. In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`, until we realized that adding the type `X → ∣ 𝑨 ∣` is quite useful. Later we will see exactly why, but for now suffice it to say that a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as an *ambient context*, or more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to *variable symbols* in `X`.  When computing with or reasoning about products, while we don't want to rigidly impose a context in advance, want do want to lay our hands on whatever context is ultimately assumed.  Including the "context map" inside the index type `ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra α 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

\begin{code}

 𝔄' : ℑ' → Algebra α 𝑆
 𝔄' = λ (i : ℑ') → ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

 class-product' : Algebra (ov α) 𝑆
 class-product' = ⨅ 𝔄'

\end{code}

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, we view the triple `(𝑨 , p , h) ∈ ℑ` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p, h)`-th component.

\begin{code}

 class-prod-s-∈-ps : class-product' ∈ P{ov α}{ov α}(S 𝒦)
 class-prod-s-∈-ps = pisow psPllA (⨅≅ {fiu = fe₂}{fiw = fe𝓕α} llA≅A)

  where
  lA llA : ℑ' → Algebra (ov α) 𝑆
  lA i =  Lift-Alg (𝔄 i) (ov α)
  llA i = Lift-Alg (lA i) (ov α)

  slA : ∀ i → (lA i) ∈ S 𝒦
  slA i = siso (fst ∥ i ∥) Lift-≅

  psllA : ∀ i → (llA i) ∈ P (S 𝒦)
  psllA i = pbase (slA i)

  psPllA : ⨅ llA ∈ P (S 𝒦)
  psPllA = produ psllA

  llA≅A : ∀ i → (llA i) ≅ (𝔄' i)
  llA≅A i = ≅-trans (≅-sym Lift-≅)(≅-sym Lift-≅)

\end{code}


So, since `PS⊆SP`, we see that that the product of all subalgebras of a class `𝒦` belongs to `SP(𝒦)`.

\begin{code}

 class-prod-s-∈-sp : hfunext (ov α) (ov α) → class-product ∈ S(P 𝒦)
 class-prod-s-∈-sp hfe = PS⊆SP {fovu = fe₂} hfe class-prod-s-∈-ps

\end{code}

----------------------------

[← Varieties.EquationalLogic](Varieties.EquationalLogic.html)
<span style="float:right;">[Varieties.Preservation →](Varieties.Preservation.html)</span>

{% include UALib.Links.md %}


--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
