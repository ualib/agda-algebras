---
layout: default
title : Varieties.Varieties module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="the-inductive-types-h-s-p-v">The Inductive Types H, S, P, V</a>

This section presents the [Varieties.Varieties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product using (_,_; Σ; _×_; Σ-syntax)
open import Function.Base  using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (cong; cong-app; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Unary using (⋂; _∈_; Pred; _⊆_)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Inverses using (IsInjective)
open import Overture.Preliminaries
 using (Type; _∙_;_⁻¹; ∣_∣; ∥_∥; snd; fst)
open import Relations.Truncation using (hfunext)

module Varieties.Varieties {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Algebras.Products{𝑆 = 𝑆} using (ov; ⨅; 𝔄; class-product)
open import Homomorphisms.Basic{𝑆 = 𝑆} using (hom; 𝒾𝒹; ∘-hom; is-homomorphism)
open import Homomorphisms.HomomorphicImages{𝑆 = 𝑆} using (HomImages; Lift-alg-hom-image)
open import Homomorphisms.Isomorphisms{𝑆 = 𝑆} using (_≅_; ≅-sym; Lift-≅; ≅-trans; ≅-refl; Lift-alg-iso; ⨅≅; Lift-alg-associative; Lift-alg-⨅≅)
open import Subalgebras.Subalgebras{𝑆 = 𝑆} using (_≤_; _IsSubalgebraOfClass_; ≤-iso; ≤-refl; Subalgebra; ≤-TRANS-≅; ≤-trans; Lift-≤-Lift; ≤-Lift; _IsSubalgebraOf_)

import Varieties.Algebras.H 𝑆 as VA-H
import Varieties.Algebras.S 𝑆 as VA-S
import Varieties.Algebras.P 𝑆 as VA-P

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
open VA-H using (H) public
open VA-S public
open VA-P public
\end{code}

#### <a id="varietal-closure">Varietal closure</a>

A class 𝒦 of 𝑆-algebras is called a **variety** if it is closed under each of the closure operators H, S, and P introduced above; the corresponding closure operator is often denoted 𝕍, but we will denote it by `V`.

We now define `V` as an inductive type.

\begin{code}

data V {𝓤 𝓦 : Level}(𝒦 : Pred(Algebra 𝓤 𝑆)(ov 𝓤)) : Pred(Algebra(𝓤 ⊔ 𝓦)𝑆)(ov(𝓤 ⊔ 𝓦))
 where
 vbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → Lift-alg 𝑨 𝓦 ∈ V 𝒦
 vlift  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → Lift-alg 𝑨 𝓦 ∈ V 𝒦
 vliftw : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → Lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ V 𝒦
 vhimg  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → ((𝑩 , _) : HomImages 𝑨) → 𝑩 ∈ V 𝒦
 vssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
 vssubw : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
 vprodu : {I : Type 𝓦}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
 vprodw : {I : Type 𝓦}{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
 visou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦
 visow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦

\end{code}

Thus, if 𝒦 is a class of 𝑆-algebras, then the **variety generated by** 𝒦 is denoted by `V 𝒦` and defined to be the smallest class that contains 𝒦 and is closed under `H`, `S`, and `P`.

With the closure operator V representing closure under HSP, we represent formally what it means to be a variety of algebras as follows.

\begin{code}

is-variety : {𝓤 : Level}(𝒱 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) → Type(ov 𝓤)
is-variety{𝓤} 𝒱 = V{𝓤}{𝓤} 𝒱 ⊆ 𝒱

variety : (𝓤 : Level) → Type(lsuc (𝓞 ⊔ 𝓥 ⊔ (lsuc 𝓤)))
variety 𝓤 = Σ[ 𝒱 ∈ (Pred (Algebra 𝓤 𝑆)(ov 𝓤)) ] is-variety 𝒱

\end{code}



#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

S⊆SP : {𝓤 𝓦 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)

S⊆SP {𝓤}{𝓦}{𝒦}{.(Lift-alg 𝑨 𝓦)}(sbase{𝑨} x) = siso spllA(≅-sym Lift-≅)
 where
 llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
 llA = Lift-alg (Lift-alg 𝑨 𝓦) (𝓤 ⊔ 𝓦)

 spllA : llA ∈ S (P 𝒦)
 spllA = sbase{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (pbase x)

S⊆SP {𝓤}{𝓦}{𝒦} {.(Lift-alg 𝑨 𝓦)} (slift{𝑨} x) = subalgebra→S lAsc
 where
 splAu : 𝑨 ∈ S(P 𝒦)
 splAu = S⊆SP{𝓤}{𝓤} x

 Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
 Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

 lAsc : (Lift-alg 𝑨 𝓦) IsSubalgebraOfClass (P 𝒦)
 lAsc = Lift-alg-subP Asc

S⊆SP {𝓤}{𝓦}{𝒦}{𝑩}(ssub{𝑨} sA B≤A) =
 ssub (subalgebra→S lAsc)( ≤-Lift 𝑨 B≤A )
  where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = Lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S (P 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} sA

  Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
  Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P 𝒦)
  lAsc = Lift-alg-subP Asc

S⊆SP (ssubw{𝑨} sA B≤A) = ssubw (S⊆SP sA) B≤A

S⊆SP {𝓤}{𝓦}{𝒦}{𝑩}(siso{𝑨} sA A≅B) = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B
 where
 lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
 lA = Lift-alg 𝑨 𝓦

 lAsc : lA IsSubalgebraOfClass (P 𝒦)
 lAsc = Lift-alg-subP (S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} (S⊆SP sA))

 lAsp : lA ∈ S(P 𝒦)
 lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

 lA≅B : lA ≅ 𝑩
 lA≅B = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}



We need to formalize one more lemma before arriving the main objective of this section, which is the proof of the inclusion PS⊆SP.

\begin{code}

module _ {𝓤 𝓦 : Level} {𝒦 : Pred(Algebra 𝓤 𝑆)(ov 𝓤)} where

 lemPS⊆SP : hfunext 𝓦 𝓤 → funext 𝓦 𝓤 → {I : Type 𝓦}{ℬ : I → Algebra 𝓤 𝑆}
  →         (∀ i → (ℬ i) IsSubalgebraOfClass 𝒦)
  →         ⨅ ℬ IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

 lemPS⊆SP hwu fwu {I}{ℬ} B≤K = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜) , ξ , (⨅≅ {fiu = fwu}{fiw = fwu} B≅SA)
  where
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra 𝓤 𝑆
  SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

  B≅SA : ∀ i → ℬ i ≅ SA i
  B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → fst ∣ SA≤𝒜 i ∣

  hinj : ∀ i → IsInjective (h i)
  hinj = λ i → snd (snd ∣ ∥ B≤K i ∥ ∣)

  α : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
  α = λ x i → (h i) (x i)
  β : is-homomorphism (⨅ SA) (⨅ 𝒜) α
  β = λ 𝑓 𝒂 → fwu λ i → (snd ∣ SA≤𝒜 i ∣) 𝑓 (λ x → 𝒂 x i)
  γ : IsInjective α
  γ αxαy = fwu λ i → (hinj i)(cong-app αxαy i)

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = (α , β) , γ

  ξ : ⨅ 𝒜 ∈ P 𝒦
  ξ = produ (λ i → P-expa (∣ snd ∥ B≤K i ∥ ∣))


\end{code}



#### <a id="PS-in-SP">PS(𝒦) ⊆ SP(𝒦)</a>

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

module _ {𝓤 : Level} {fovu : funext (ov 𝓤) (ov 𝓤)}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 PS⊆SP : -- extensionality assumptions:
            hfunext (ov 𝓤)(ov 𝓤)

  →      P{ov 𝓤}{ov 𝓤} (S{𝓤}{ov 𝓤} 𝒦) ⊆ S{ov 𝓤}{ov 𝓤} (P{𝓤}{ov 𝓤} 𝒦)

 PS⊆SP _ (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP _ (pbase (slift{𝑨} x)) = slift (S⊆SP{𝓤}{ov 𝓤}{𝒦} (slift x))
 PS⊆SP _ (pbase{𝑩}(ssub{𝑨} sA B≤A)) = siso(ssub(S⊆SP(slift sA))(Lift-≤-Lift 𝑨 B≤A)) ≅-refl
 PS⊆SP _ (pbase {𝑩}(ssubw{𝑨} sA B≤A)) = ssub(slift(S⊆SP sA))(Lift-≤-Lift 𝑨 B≤A)
 PS⊆SP _ (pbase (siso{𝑨}{𝑩} x A≅B)) = siso (S⊆SP (slift x)) ( Lift-alg-iso A≅B )
 PS⊆SP hfe (pliftu x) = slift (PS⊆SP hfe x)
 PS⊆SP hfe (pliftw x) = slift (PS⊆SP hfe x)

 PS⊆SP hfe (produ{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov 𝓤} 𝒦)
   ξ i = S→subalgebra (PS⊆SP hfe (x i))

   η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov 𝓤}{ov 𝓤} (P{𝓤}{ov 𝓤} 𝒦))
   η = lemPS⊆SP hfe fovu {I} {𝒜} ξ

 PS⊆SP hfe (prodw{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov 𝓤} 𝒦)
   ξ i = S→subalgebra (PS⊆SP hfe (x i))

   η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov 𝓤}{ov 𝓤} (P{𝓤}{ov 𝓤} 𝒦))
   η = lemPS⊆SP hfe fovu  {I} {𝒜} ξ

 PS⊆SP hfe (pisou{𝑨}{𝑩} pA A≅B) = siso (PS⊆SP hfe pA) A≅B
 PS⊆SP hfe (pisow{𝑨}{𝑩} pA A≅B) = siso (PS⊆SP hfe pA) A≅B

\end{code}



#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this subsection with three more inclusion relations that will have bit parts to play later (e.g., in the formal proof of Birkhoff's Theorem).

\begin{code}

P⊆V : {𝓤 𝓦 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → P{𝓤}{𝓦} 𝒦 ⊆ V{𝓤}{𝓦} 𝒦

P⊆V (pbase x) = vbase x
P⊆V{𝓤} (pliftu x) = vlift (P⊆V{𝓤}{𝓤} x)
P⊆V{𝓤}{𝓦} (pliftw x) = vliftw (P⊆V{𝓤}{𝓦} x)
P⊆V (produ x) = vprodu (λ i → P⊆V (x i))
P⊆V (prodw x) = vprodw (λ i → P⊆V (x i))
P⊆V (pisou x x₁) = visou (P⊆V x) x₁
P⊆V (pisow x x₁) = visow (P⊆V x) x₁


SP⊆V : {𝓤 𝓦 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →     S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦) ⊆ V 𝒦

SP⊆V (sbase{𝑨} PCloA) = P⊆V (pisow PCloA Lift-≅)
SP⊆V (slift{𝑨} x) = vliftw (SP⊆V x)
SP⊆V (ssub{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (ssubw{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (siso x x₁) = visow (SP⊆V x) x₁

\end{code}
#### <a id="V-is-closed-under-lift">V is closed under lift</a>

As mentioned earlier, a technical hurdle that must be overcome when formalizing proofs in Agda is the proper handling of universe levels. In particular, in the proof of the Birkhoff's theorem, for example, we will need to know that if an algebra 𝑨 belongs to the variety V 𝒦, then so does the lift of 𝑨.  Let us get the tedious proof of this technical lemma out of the way.

\begin{code}

open Lift

module Vlift {𝓤 : Level} {fe₀ : funext (ov 𝓤) 𝓤}
         {fe₁ : funext ((ov 𝓤) ⊔ (lsuc (ov 𝓤))) (lsuc (ov 𝓤))}
         {fe₂ : funext (ov 𝓤) (ov 𝓤)}
         {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 VlA : {𝑨 : Algebra (ov 𝓤) 𝑆} → 𝑨 ∈ V{𝓤}{ov 𝓤} 𝒦
  →    Lift-alg 𝑨 (lsuc (ov 𝓤)) ∈ V{𝓤}{lsuc (ov 𝓤)} 𝒦
 VlA (vbase{𝑨} x) = visow (vbase x) (Lift-alg-associative 𝑨)
 VlA (vlift{𝑨} x) = visow (vlift x) (Lift-alg-associative 𝑨)
 VlA (vliftw{𝑨} x) = visow (VlA x) (Lift-alg-associative 𝑨)

 VlA (vhimg{𝑨}{𝑩} x hB) =
  vhimg{𝑩 = Lift-alg 𝑩 (lsuc (ov 𝓤))}
   (VlA x) ((Lift-alg ∣ hB ∣ (lsuc (ov 𝓤))) , (Lift-alg-hom-image {𝑩 = ∣ hB ∣} ∥ hB ∥))

 VlA (vssub{𝑨}{𝑩} x B≤A) = vssubw (vlift{𝓦 = (lsuc (ov 𝓤))} x) (Lift-≤-Lift 𝑨 B≤A)
 VlA (vssubw{𝑨}{𝑩} x B≤A) = vssubw (VlA x) (Lift-≤-Lift 𝑨 B≤A)
 VlA (vprodu{I}{𝒜} x) = visow (vprodw vlA) (≅-sym B≅A)
  where
  𝑰 : Type (lsuc (ov 𝓤))
  𝑰 = Lift (lsuc (ov 𝓤)) I

  lA : 𝑰 → Algebra (lsuc (ov 𝓤)) 𝑆
  lA i = Lift-alg (𝒜 (lower i)) (lsuc (ov 𝓤))

  vlA : ∀ i → (lA i) ∈ V{𝓤}{lsuc (ov 𝓤)} 𝒦
  vlA i = vlift (x (lower i))

  iso-components : ∀ i → 𝒜 i ≅ lA (lift i)
  iso-components i = Lift-≅

  B≅A : Lift-alg (⨅ 𝒜) (lsuc (ov 𝓤)) ≅ ⨅ lA
  B≅A = Lift-alg-⨅≅  {fizw = fe₁}{fiu = fe₀} iso-components


 VlA (vprodw{I}{𝒜} x) = visow (vprodw vlA) (≅-sym B≅A)
  where
  𝑰 : Type (lsuc (ov 𝓤))
  𝑰 = Lift (lsuc (ov 𝓤)) I

  lA : 𝑰 → Algebra (lsuc (ov 𝓤)) 𝑆
  lA i = Lift-alg (𝒜 (lower i)) (lsuc (ov 𝓤))

  vlA : ∀ i → (lA i) ∈ V{𝓤}{lsuc (ov 𝓤)} 𝒦
  vlA i = VlA (x (lower i))

  iso-components : ∀ i → 𝒜 i ≅ lA (lift i)
  iso-components i = Lift-≅

  B≅A : Lift-alg (⨅ 𝒜) (lsuc (ov 𝓤)) ≅ ⨅ lA
  B≅A = Lift-alg-⨅≅ {fizw = fe₁}{fiu = fe₂} iso-components

 VlA (visou{𝑨}{𝑩} x A≅B) = visow (vlift x) (Lift-alg-iso A≅B)
 VlA (visow{𝑨}{𝑩} x A≅B) = visow (VlA x) (Lift-alg-iso A≅B)

\end{code}



Above we proved that `SP(𝒦) ⊆ V(𝒦)`, and we did so under fairly general assumptions about the universe level parameters.  Unfortunately, this is sometimes not quite general enough, so we now prove the inclusion again for the specific universe parameters that align with subsequent applications of this result.

\begin{code}

 SP⊆V' : S{ov 𝓤}{lsuc (ov 𝓤)} (P{𝓤}{ov 𝓤} 𝒦) ⊆ V 𝒦

 SP⊆V' (sbase{𝑨} x) = visow (VlA (SP⊆V (sbase x))) (≅-sym (Lift-alg-associative 𝑨))
 SP⊆V' (slift x) = VlA (SP⊆V x)

 SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw (VlA (SP⊆V spA)) B≤lA
  where
   B≤lA : 𝑩 ≤ Lift-alg 𝑨 (lsuc (ov 𝓤))
   B≤lA = ≤-Lift 𝑨 B≤A

 SP⊆V' (ssubw spA B≤A) = vssubw (SP⊆V' spA) B≤A

 SP⊆V' (siso{𝑨}{𝑩} x A≅B) = visow (VlA (SP⊆V x)) γ
  where
   γ : Lift-alg 𝑨 (lsuc (ov 𝓤)) ≅ 𝑩
   γ = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}


#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof of Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally) in the [UniversalAlgebra][] library as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

Before doing so, we need to redefine the class product so that each factor comes with a map from the type `X` of variable symbols into that factor.  We will explain the reason for this below.

\begin{code}

module class-products-with-maps {𝓤 : Level}
 {X : Type 𝓤}
 {fe𝓕𝓤 : funext (ov 𝓤) 𝓤}
 {fe₁ : funext ((ov 𝓤) ⊔ (lsuc (ov 𝓤))) (lsuc (ov 𝓤))}
 {fe₂ : funext (ov 𝓤) (ov 𝓤)}
 (𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤))
 where

 ℑ' : Type (ov 𝓤)
 ℑ' = Σ[ 𝑨 ∈ (Algebra 𝓤 𝑆) ] ((𝑨 ∈ S{𝓤}{𝓤} 𝒦) × (X → ∣ 𝑨 ∣))

\end{code}
Notice that the second component of this dependent pair type is  `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`. In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`, until we realized that adding the type `X → ∣ 𝑨 ∣` is quite useful. Later we will see exactly why, but for now suffice it to say that a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as an *ambient context*, or more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to *variable symbols* in `X`.  When computing with or reasoning about products, while we don't want to rigidly impose a context in advance, want do want to lay our hands on whatever context is ultimately assumed.  Including the "context map" inside the index type `ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

\begin{code}

 𝔄' : ℑ' → Algebra 𝓤 𝑆
 𝔄' = λ (i : ℑ') → ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

 class-product' : Algebra (ov 𝓤) 𝑆
 class-product' = ⨅ 𝔄'

\end{code}

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, we view the triple `(𝑨 , p , h) ∈ ℑ` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p, h)`-th component.

\begin{code}

 class-prod-s-∈-ps : class-product' ∈ P{ov 𝓤}{ov 𝓤}(S 𝒦)
 class-prod-s-∈-ps = pisou psPllA (⨅≅ {fiu = fe₂}{fiw = fe𝓕𝓤} llA≅A)

  where
  lA llA : ℑ' → Algebra (ov 𝓤) 𝑆
  lA i =  Lift-alg (𝔄 i) (ov 𝓤)
  llA i = Lift-alg (lA i) (ov 𝓤)

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

 class-prod-s-∈-sp : hfunext (ov 𝓤) (ov 𝓤) → class-product ∈ S(P 𝒦)
 class-prod-s-∈-sp hfe = PS⊆SP {fovu = fe₂} hfe class-prod-s-∈-ps

\end{code}

----------------------------

[← Varieties.EquationalLogic](Varieties.EquationalLogic.html)
<span style="float:right;">[Varieties.Preservation →](Varieties.Preservation.html)</span>

{% include UALib.Links.md %}
