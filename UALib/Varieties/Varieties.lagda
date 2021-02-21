---
layout: default
title : UALib.Varieties.Varieties module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="inductive-types-h-s-p-and-v">Inductive Types H, S, P, and V</a>

This section presents the [UALib.Varieties.Varieties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)

module UALib.Varieties.Varieties {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Varieties.EquationalLogic{𝑆 = 𝑆}{gfe} public

\end{code}


Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

A straight-forward verification confirms that H, S, and P are **closure operators** (expansive, monotone, and idempotent).  A class 𝒦 of 𝑆-algebras is said to be *closed under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, 𝒦 is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`). The operators H, S, and P can be composed with one another repeatedly, forming yet more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under isomorphism.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define an inductive type `V` which simultaneously represents closure under all three operators, `H`, `S`, and `P`.




#### <a id="homomorphic-closure">Homomorphic closure</a>

We define the inductive type `H` to represent classes of algebras that include all homomorphic images of algebras in the class; i.e., classes that are closed under the taking of homomorphic images.

\begin{code}

data H {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(ov(𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H 𝒦
  hlift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H 𝒦
  hhimg : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓦} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H 𝒦
  hiso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H 𝒦

\end{code}



#### <a id="subalgebraic-closure">Subalgebraic closure</a>

The most useful inductive type that we have found for representing the semantic notion of a class of algebras that is closed under the taking of subalgebras is the following.

\begin{code}

data S {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (ov(𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S 𝒦
  ssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
  ssubw : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓦} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S 𝒦

\end{code}



#### <a id="product-closure">Product closure</a>

The most useful inductive type that we have found for representing the semantic notion of an class of algebras closed under the taking of arbitrary products is the following.

\begin{code}

data P {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(ov(𝓤 ⊔ 𝓦)) where
  pbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P 𝒦
  pliftu : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P 𝒦
  pliftw : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P 𝒦
  produ  : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
  prodw  : {I : 𝓦 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
  pisou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦
  pisow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦

\end{code}



#### <a id="varietal-closure">Varietal closure</a>

A class 𝒦 of 𝑆-algebras is called a **variety** if it is closed under each of the closure operators H, S, and P introduced above; the corresponding closure operator is often denoted 𝕍, but we will denote it by `V`.

We now define `V` as an inductive type.

\begin{code}

data V {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(ov(𝓤 ⊔ 𝓦)) where
  vbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ V 𝒦
  vlift  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ V 𝒦
  vliftw : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ V 𝒦
  vhimg  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ V 𝒦
  vssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
  vssubw : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
  vprodu : {I : 𝓦 ̇}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
  vprodw : {I : 𝓦 ̇}{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
  visou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦
  visow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦

\end{code}

Thus, if 𝒦 is a class of 𝑆-algebras, then the **variety generated by** 𝒦 is denoted by `V 𝒦` and defined to be the smallest class that contains 𝒦 and is closed under `H`, `S`, and `P`.

With the closure operator V representing closure under HSP, we represent formally what it means to be a variety of algebras as follows.

\begin{code}

is-variety : {𝓤 : Universe}(𝒱 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) → ov 𝓤 ̇
is-variety{𝓤} 𝒱 = V{𝓤}{𝓤} 𝒱 ⊆ 𝒱

variety : (𝓤 : Universe) → (ov 𝓤)⁺ ̇
variety 𝓤 = Σ 𝒱 ꞉ (Pred (Algebra 𝓤 𝑆)(ov 𝓤)) , is-variety 𝒱

\end{code}


#### <a id="V-is-closed-under-lift">V is closed under lift</a>

As mentioned earlier, a technical hurdle that must be overcome when formalizing proofs in Agda is the proper handling of universe levels. In particular, in the proof of the Birkhoff's theorem, for example, we will need to know that if an algebra 𝑨 belongs to the variety V 𝒦, then so does the lift of 𝑨.  Let us get the tedious proof of this technical lemma out of the way.

\begin{code}

open Lift
VlA : {𝓤 : Universe} {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
      {𝑨 : Algebra (ov 𝓤) 𝑆}
 →    𝑨 ∈ V{𝓤}{ov 𝓤} 𝒦
      ---------------------------------
 →    lift-alg 𝑨 (ov 𝓤 ⁺) ∈ V{𝓤}{ov 𝓤 ⁺} 𝒦

VlA (vbase{𝑨} x) = visow (vbase x) (lift-alg-associative 𝑨)
VlA (vlift{𝑨} x) = visow (vlift x) (lift-alg-associative 𝑨)
VlA (vliftw{𝑨} x) = visow (VlA x) (lift-alg-associative 𝑨)
VlA (vhimg{𝑨}{𝑩} x hB) = vhimg (VlA x) (lift-alg-hom-image hB)
VlA {𝓤}(vssub{𝑨}{𝑩} x B≤A) = vssubw (vlift{𝓦 = (ov 𝓤 ⁺)} x) (lift-alg-≤ 𝑩{𝑨} B≤A)
VlA (vssubw{𝑨}{𝑩} x B≤A) = vssubw (VlA x) (lift-alg-≤ 𝑩{𝑨} B≤A)
VlA {𝓤}{𝒦}(vprodu{I}{𝒜} x) = visow (vprodw vlA) (sym-≅ B≅A)
 where
  𝑰 : (ov 𝓤 ⁺) ̇
  𝑰 = Lift{ov 𝓤}{ov 𝓤 ⁺} I

  lA+ : Algebra (ov 𝓤 ⁺) 𝑆
  lA+ = lift-alg (⨅ 𝒜) (ov 𝓤 ⁺)

  lA : 𝑰 → Algebra (ov 𝓤 ⁺) 𝑆
  lA i = lift-alg (𝒜 (lower i)) (ov 𝓤 ⁺)

  vlA : (i : 𝑰) → (lA i) ∈ V{𝓤}{ov 𝓤 ⁺} 𝒦
  vlA i = vlift (x (lower i))

  iso-components : (i : I) → 𝒜 i ≅ lA (lift i)
  iso-components i = lift-alg-≅

  B≅A : lA+ ≅ ⨅ lA
  B≅A = lift-alg-⨅≅ gfe iso-components

VlA {𝓤}{𝒦}(vprodw{I}{𝒜} x) = visow (vprodw vlA) (sym-≅ B≅A)
 where
  𝑰 : (ov 𝓤 ⁺) ̇
  𝑰 = Lift{ov 𝓤}{ov 𝓤 ⁺} I

  lA+ : Algebra (ov 𝓤 ⁺) 𝑆
  lA+ = lift-alg (⨅ 𝒜) (ov 𝓤 ⁺)

  lA : 𝑰 → Algebra (ov 𝓤 ⁺) 𝑆
  lA i = lift-alg (𝒜 (lower i)) (ov 𝓤 ⁺)

  vlA : (i : 𝑰) → (lA i) ∈ V{𝓤}{ov 𝓤 ⁺} 𝒦
  vlA i = VlA (x (lower i))

  iso-components : (i : I) → 𝒜 i ≅ lA (lift i)
  iso-components i = lift-alg-≅

  B≅A : lA+ ≅ ⨅ lA
  B≅A = lift-alg-⨅≅ gfe iso-components

VlA {𝓤}(visou{𝑨}{𝑩} x A≅B) = visow (vlift x) (lift-alg-iso 𝓤 (ov 𝓤 ⁺) 𝑨 A≅B)
VlA {𝓤}(visow{𝑨}{𝑩} x A≅B) = visow (VlA x) (lift-alg-iso (ov 𝓤) (ov 𝓤 ⁺) 𝑨 A≅B)

\end{code}



#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties that we need later.

First, `P` is a closure operator.  This is proved by checking that `P` is *monotone*, *expansive*, and *idempotent*. The meaning of these terms will be clear from the definitions of the types that follow.

\begin{code}

P-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred(Algebra 𝓤 𝑆)(ov 𝓤)} → 𝒦 ⊆ 𝒦' → P{𝓤}{𝓦} 𝒦 ⊆ P{𝓤}{𝓦} 𝒦'

P-mono kk' (pbase x)    = pbase (kk' x)
P-mono kk' (pliftu x)   = pliftu (P-mono kk' x)
P-mono kk' (pliftw x)   = pliftw (P-mono kk' x)
P-mono kk' (produ x)    = produ (λ i → P-mono kk' (x i))
P-mono kk' (prodw x)    = prodw (λ i → P-mono kk' (x i))
P-mono kk' (pisou x x₁) = pisou (P-mono kk' x) x₁
P-mono kk' (pisow x x₁) = pisow (P-mono kk' x) x₁


P-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → 𝒦 ⊆ P{𝓤}{𝓤} 𝒦

P-expa{𝓤}{𝒦} {𝑨} KA = pisou{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)


P-idemp : {𝓤 : Universe}{𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →        P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦

P-idemp (pbase x)             = pliftw x
P-idemp {𝓤}{𝓦} (pliftu x)   = pliftw (P-idemp{𝓤}{𝓦} x)
P-idemp {𝓤}{𝓦} (pliftw x)   = pliftw (P-idemp{𝓤}{𝓦} x)
P-idemp {𝓤}{𝓦} (produ x)    = prodw (λ i → P-idemp{𝓤}{𝓦} (x i))
P-idemp {𝓤}{𝓦} (prodw x)    = prodw (λ i → P-idemp{𝓤}{𝓦} (x i))
P-idemp {𝓤}{𝓦} (pisou x x₁) = pisow (P-idemp{𝓤}{𝓦} x) x₁
P-idemp {𝓤}{𝓦} (pisow x x₁) = pisow (P-idemp{𝓤}{𝓦} x) x₁

\end{code}

Similarly, S is a closure operator.  The facts that S is idempotent and expansive won't be needed below, so we omit these, but we will make use of monotonicity of S.  Here is the proof of the latter.

\begin{code}

S-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → 𝒦 ⊆ 𝒦' → S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'

S-mono kk' (sbase x)            = sbase (kk' x)
S-mono kk' (slift{𝑨} x)         = slift (S-mono kk' x)
S-mono kk' (ssub{𝑨}{𝑩} sA B≤A)  = ssub (S-mono kk' sA) B≤A
S-mono kk' (ssubw{𝑨}{𝑩} sA B≤A) = ssubw (S-mono kk' sA) B≤A
S-mono kk' (siso x x₁)          = siso (S-mono kk' x) x₁

\end{code}

We sometimes want to go back and forth between our two representations of subalgebras of algebras in a class. The tools `subalgebra→S` and `S→subalgebra` are made for that purpose.

\begin{code}

module _ {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 subalgebra→S : {𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦

 subalgebra→S {𝑩} (𝑨 , ((𝑪 , C≤A) , KA , B≅C)) = ssub sA B≤A
  where
   B≤A : 𝑩 ≤ 𝑨
   B≤A = Iso-≤ 𝑨 𝑩 C≤A B≅C

   slAu : lift-alg 𝑨 𝓤 ∈ S{𝓤}{𝓤} 𝒦
   slAu = sbase KA

   sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦
   sA = siso slAu (sym-≅ lift-alg-≅)


module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 S→subalgebra : {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S{𝓤}{𝓤} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦

 S→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , (sym-≅ lift-alg-≅)
 S→subalgebra (slift{𝑩} x) = ∣ BS ∣ , SA , ∣ snd ∥ BS ∥ ∣ , TRANS-≅ (sym-≅ lift-alg-≅) B≅SA
  where
   BS : 𝑩 IsSubalgebraOfClass 𝒦
   BS = S→subalgebra x
   SA : Subalgebra ∣ BS ∣
   SA = fst ∥ BS ∥
   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BS ∥ ∥

 S→subalgebra {𝑩} (ssub{𝑨} sA B≤A) = ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , refl-≅
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = transitivity-≤ 𝑩{∣ SA ∣}{∣ AS ∣} B≤SA ∥ SA ∥

 S→subalgebra {𝑩} (ssubw{𝑨} sA B≤A) = ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , refl-≅
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = transitivity-≤ 𝑩{∣ SA ∣}{∣ AS ∣} B≤SA ∥ SA ∥

 S→subalgebra {𝑩} (siso{𝑨} sA A≅B) = ∣ AS ∣ , SA ,  ∣ snd ∥ AS ∥ ∣ , (TRANS-≅ (sym-≅ A≅B) A≅SA)
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd AS ∥

\end{code}

Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.

\begin{code}

lift-alg-subP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}{𝑩 : Algebra 𝓤 𝑆}
 →              𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
                -------------------------------------------------
 →              (lift-alg 𝑩 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lift-alg-subP {𝓤}{𝓦}{𝒦}{𝑩}(𝑨 , (𝑪 , C≤A) , pA , B≅C ) = lA , (lC , lC≤lA) , plA , (lift-alg-iso 𝓤 𝓦 𝑩 B≅C)
 where
  lA lC : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  lC = lift-alg 𝑪 𝓦

  lC≤lA : lC ≤ lA
  lC≤lA = lift-alg-≤ 𝑪 {𝑨} C≤A
  plA : lA ∈ P{𝓤}{𝓦} 𝒦
  plA = pliftu pA

\end{code}

The next lemma would be too obvoius to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

S⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)

S⊆SP {𝓤}{𝓦}{𝒦}{.(lift-alg 𝑨 𝓦)}(sbase{𝑨} x) = siso spllA (sym-≅ lift-alg-≅)
  where
   llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   llA = lift-alg (lift-alg 𝑨 𝓦) (𝓤 ⊔ 𝓦)

   spllA : llA ∈ S (P 𝒦)
   spllA = sbase{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (pbase x)

S⊆SP {𝓤}{𝓦}{𝒦} {.(lift-alg 𝑨 𝓦)} (slift{𝑨} x) = subalgebra→S lAsc
  where
   splAu : 𝑨 ∈ S(P 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} x

   Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : (lift-alg 𝑨 𝓦) IsSubalgebraOfClass (P 𝒦)
   lAsc = lift-alg-subP Asc

S⊆SP {𝓤}{𝓦}{𝒦}{𝑩}(ssub{𝑨} sA B≤A) = ssub (subalgebra→S lAsc) (lift-alg-sub-lift 𝑨 B≤A)
  where
   lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   lA = lift-alg 𝑨 𝓦

   splAu : 𝑨 ∈ S (P 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} sA

   Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : lA IsSubalgebraOfClass (P 𝒦)
   lAsc = lift-alg-subP Asc

S⊆SP (ssubw{𝑨} sA B≤A) = ssubw (S⊆SP sA) B≤A

S⊆SP {𝓤}{𝓦}{𝒦}{𝑩}(siso{𝑨} sA A≅B) = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  lAsc : lA IsSubalgebraOfClass (P 𝒦)
  lAsc = lift-alg-subP (S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} (S⊆SP sA))

  lAsp : lA ∈ S(P 𝒦)
  lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B

\end{code}



We need to formalize one more lemma before arriving the main objective of this section, which is the proof of the inclusion PS⊆SP.

\begin{code}

lemPS⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →         {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →         (∀ i → (ℬ i) IsSubalgebraOfClass 𝒦)
           -------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lemPS⊆SP {𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , ξ , (⨅≅ gfe B≅SA)
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

  α : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
  α = λ x i → (h i) (x i)
  β : is-homomorphism (⨅ SA) (⨅ 𝒜) α
  β = λ 𝑓 𝒂 → gfe λ i → (snd ∣ SA≤𝒜 i ∣) 𝑓 (λ x → 𝒂 x i)
  γ : is-embedding α
  γ = embedding-lift hfe hfe {I}{SA}{𝒜}h(λ i → ∥ SA≤𝒜 i ∥)

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = (α , β) , γ

  ξ : ⨅ 𝒜 ∈ P 𝒦
  ξ = produ (λ i → P-expa (∣ snd ∥ B≤K i ∥ ∣))


\end{code}



#### <a id="PS-in-SP">PS(𝒦) ⊆ SP(𝒦)</a>

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} {hfe : hfunext (ov 𝓤)(ov 𝓤)} where

 ov𝓾 : Universe
 ov𝓾 = ov 𝓤

 PS⊆SP : (P{ov𝓾}{ov𝓾} (S{𝓤}{ov𝓾} 𝒦)) ⊆ (S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))

 PS⊆SP (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP (pbase (slift{𝑨} x)) = slift (S⊆SP{𝓤}{ov𝓾}{𝒦} (slift x))
 PS⊆SP (pbase {𝑩} (ssub{𝑨} sA B≤A)) = siso(ssub(S⊆SP(slift sA)) (lift-alg-≤ 𝑩{𝑨} B≤A)) refl-≅
 PS⊆SP (pbase {𝑩}(ssubw{𝑨} sA B≤A)) = ssub(slift(S⊆SP sA)) (lift-alg-≤ 𝑩{𝑨} B≤A)
 PS⊆SP (pbase (siso{𝑨}{𝑩} x A≅B)) = siso (S⊆SP (slift x)) (lift-alg-iso 𝓤 ov𝓾 𝑨 A≅B)
 PS⊆SP (pliftu x) = slift (PS⊆SP x)
 PS⊆SP (pliftw x) = slift (PS⊆SP x)

 PS⊆SP (produ{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov𝓾} 𝒦)
   ξ i = S→subalgebra (PS⊆SP (x i))

   η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
   η = lemPS⊆SP{𝓤 = ov𝓾}{ov𝓾}{𝒦 = (P 𝒦)}{hfe}{I = I}{ℬ = 𝒜} ξ

 PS⊆SP (prodw{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov𝓾} 𝒦)
   ξ i = S→subalgebra (PS⊆SP (x i))

   η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
   η = lemPS⊆SP{𝓤 = ov𝓾}{ov𝓾}{𝒦 = (P 𝒦)}{hfe}{I = I}{ℬ = 𝒜} ξ

 PS⊆SP (pisou{𝑨}{𝑩} pA A≅B) = siso (PS⊆SP pA) A≅B
 PS⊆SP (pisow{𝑨}{𝑩} pA A≅B) = siso (PS⊆SP pA) A≅B

\end{code}



#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this module with three more inclusion relations that will have bit parts to play later (e.g., in the formal proof of Birkhoff's Theorem).

\begin{code}

P⊆V : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → P{𝓤}{𝓦} 𝒦 ⊆ V{𝓤}{𝓦} 𝒦

P⊆V (pbase x) = vbase x
P⊆V{𝓤} (pliftu x) = vlift (P⊆V{𝓤}{𝓤} x)
P⊆V{𝓤}{𝓦} (pliftw x) = vliftw (P⊆V{𝓤}{𝓦} x)
P⊆V (produ x) = vprodu (λ i → P⊆V (x i))
P⊆V (prodw x) = vprodw (λ i → P⊆V (x i))
P⊆V (pisou x x₁) = visou (P⊆V x) x₁
P⊆V (pisow x x₁) = visow (P⊆V x) x₁


SP⊆V : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →     S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦) ⊆ V{𝓤}{𝓦} 𝒦

SP⊆V (sbase{𝑨} PCloA) = P⊆V (pisow PCloA lift-alg-≅)
SP⊆V (slift{𝑨} x) = vliftw (SP⊆V x)
SP⊆V (ssub{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (ssubw{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (siso x x₁) = visow (SP⊆V x) x₁

\end{code}

We just prove that `SP(𝒦) ⊆ V(𝒦)`, and we did so under fairly general assumptions about the universe level parameters.  Unfortunately, this is sometimes not quite general enough, so we now prove the inclusion again for the specific universe parameters that align with subsequent applications of this result.

\begin{code}

SP⊆V' : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)}
 →      S{ov 𝓤}{ov 𝓤 ⁺} (P{𝓤}{ov 𝓤} 𝒦) ⊆ V{𝓤}{ov 𝓤 ⁺} 𝒦

SP⊆V' (sbase{𝑨} x) = visow (VlA (SP⊆V (sbase x))) (sym-≅ (lift-alg-associative 𝑨))
SP⊆V' (slift x) = VlA (SP⊆V x)

SP⊆V' {𝓤}(ssub{𝑨}{𝑩} spA B≤A) = vssubw (VlA (SP⊆V spA)) B≤lA
 where
  B≤lA : 𝑩 ≤ lift-alg 𝑨 (ov 𝓤 ⁺)
  B≤lA = (lift-alg-lower-≤-lift 𝑩 {𝑨}) B≤A

SP⊆V' (ssubw spA B≤A) = vssubw (SP⊆V' spA) B≤A

SP⊆V' {𝓤}{𝒦}(siso{𝑨}{𝑩} x A≅B) = visow (VlA vA) (Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B)
 where
  lA : Algebra (ov 𝓤 ⁺) 𝑆
  lA = lift-alg 𝑨 (ov 𝓤 ⁺)

  vA : 𝑨 ∈ V 𝒦
  vA = SP⊆V x

\end{code}





#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof of Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally) in the [UALib][] as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

\begin{code}

class-prod-s-∈-ps : {𝓤 : Universe}{X : 𝓤 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →                  class-product {𝓤}{𝓤}{X} (S 𝒦) ∈ (P{ov 𝓤}{ov 𝓤} (S 𝒦))

class-prod-s-∈-ps {𝓤}{X}{𝒦}  = pisou psPllA (⨅≅ gfe llA≅A)
 where
  lA llA : ℑ (S 𝒦) → Algebra (ov 𝓤) 𝑆
  lA i =  lift-alg (𝔄 (S 𝒦) i) (ov 𝓤)
  llA i = lift-alg (lA i) (ov 𝓤)

  slA : ∀ i → (lA i) ∈ S 𝒦
  slA i = siso (fst ∥ i ∥) lift-alg-≅

  psllA : ∀ i → (llA i) ∈ P (S 𝒦)
  psllA i = pbase (slA i)

  psPllA : ⨅ llA ∈ P (S 𝒦)
  psPllA = produ psllA

  llA≅A : ∀ i → (llA i) ≅ (𝔄 (S 𝒦) i)
  llA≅A i = Trans-≅ (llA i) (𝔄 (S 𝒦) i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

-- So, since PS⊆SP, we see that that the product of all subalgebras of a class 𝒦 belongs to SP(𝒦).
class-prod-s-∈-sp : {𝓤 : Universe}{X : 𝓤 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → hfunext (ov 𝓤) (ov 𝓤)
 →                  class-product{𝓤}{𝓤}{X} (S 𝒦) ∈ S(P 𝒦)
class-prod-s-∈-sp hfe = PS⊆SP{hfe = hfe} class-prod-s-∈-ps

\end{code}

----------------------------

[← UALib.Varieties.EquationalLogic](UALib.Varieties.EquationalLogic.html)
<span style="float:right;">[UALib.Varieties.Preservation →](UALib.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}


