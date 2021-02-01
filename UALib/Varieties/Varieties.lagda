---
layout: default
title : UALib.Varieties.Varieties module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="inductive-types-h-s-p-and-v">Inductive Types H, S, P, and V</a>

This section presents the [UALib.Varieties.Varieties][] module of the [Agda Universal Algebra Library][].

Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

A straight-forward verification confirms that H, S, and P are **closure operators** (expansive, monotone, and idempotent).  A class 𝒦 of 𝑆-algebras is said to be *closed under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, 𝒦 is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`).

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under isomorphism.

The operators H, S, and P can be composed with one another repeatedly, forming yet more closure operators.

<!-- If C₁ and C₂ are closure operators on classes of structures, let us say that C₁ ≤ C₂ if for every class 𝒦 we have C₁(𝒦) ⊆ C₂(𝒦). -->

A **variety** is a class 𝒦 of algebras in a fixed signature that is closed under the taking of homomorphic images (H), subalgebras (S), and arbitrary products (P).  That is, 𝒦 is a variety if and only if `H S P 𝒦 ⊆ 𝒦`.

This module defines what we have found to be the most useful inductive types representing the closure operators H, S, and P. Separately, we define the inductive type `V` for simultaneously representing closure under `H`, `S`, and `P`.

<!-- ; consequently, we expect `V 𝒦 ≡ H (S (P 𝒦))` to hold for each class 𝒦 of algebras of a fixed signature. classes of algebras that are closed under H, S, P, and V ≡ HSP. -->

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Varieties.Varieties
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Varieties.EquationalLogic{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

-----------------------------------

#### <a id="homomorphic-closure">Homomorphism closure</a>

We define the inductive type `H` to represent classes of algebras that include all homomorphic images of algebras in the class; i.e., classes that are closed under the taking of homomorphic images.

\begin{code}

--Closure wrt H
data H {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H 𝒦
  hlift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H 𝒦
  hhimg : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓦} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H 𝒦
  hiso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H 𝒦

\end{code}

<!-- We say that a class 𝒦 is **closed under** `H` (or `H`-**closed**) provided `H 𝒦 ⊆ 𝒦`. -->

--------------------------------

#### <a id="subalgebra-closure">Subalgebra closure</a>

The most useful inductive type that we have found for representing classes of algebras that are closed under the taking of subalgebras as an inductive type.

\begin{code}

--Closure wrt S
data S {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S 𝒦
  ssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
  ssubw : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓦} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S 𝒦

\end{code}

<!-- A class 𝒦 is **closed under** `S` (or `S`-**closed**) provided `S 𝒦 ⊆ 𝒦` -->

-----------------------------------------

#### <a id="product-closure">Product closure</a>

The most useful inductive type that we have found for representing classes of algebras closed under arbitrary products is the following. 

\begin{code}

data P {𝓤 𝓦 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (OV (𝓤 ⊔ 𝓦)) where
  pbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P 𝒦
  pliftu : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P 𝒦
  pliftw : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P 𝒦
  produ  : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
  prodw  : {I : 𝓦 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
  pisou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦
  pisow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦

\end{code}

<!-- A class 𝒦 is **closed under** `P` (or `P`-**closed**) provided `P 𝒦 ⊆ 𝒦`. -->

-----------------------------------------------

#### <a id="variety-closure">Varietal closure</a>

A class 𝒦 of 𝑆-algebras is called a **variety** if it is closed under each of the closure operators H, S, and P introduced above; the corresponding closure operator is often denoted 𝕍, but we will typically denote it by `V`.

Thus, if 𝒦 is a class of 𝑆-algebras, then the **variety generated by** 𝒦 is denoted by `V 𝒦` and defined to be the smallest class that contains 𝒦 and is closed under `H`, `S`, and `P`.

We now define `V` as an inductive type.

\begin{code}

data V {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) where
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

-------------------------------

#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties since we will need them later.

\begin{code}

-- P is a closure operator; in particular, it's expansive.
P-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ P{𝓤}{𝓤} 𝒦

P-expa{𝓤}{𝒦} {𝑨} KA = pisou{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

-- P is a closure operator; in particular, it's idempotent.
P-idemp : {𝓤 : Universe}{𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →         P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦

P-idemp (pbase x) = pliftw x
P-idemp {𝓤}{𝓦} (pliftu x) = pliftw (P-idemp{𝓤}{𝓦} x)
P-idemp {𝓤}{𝓦} (pliftw x) = pliftw (P-idemp{𝓤}{𝓦} x)
P-idemp {𝓤}{𝓦} (produ x) = prodw (λ i → P-idemp{𝓤}{𝓦} (x i))
P-idemp {𝓤}{𝓦} (prodw x) = prodw (λ i → P-idemp{𝓤}{𝓦} (x i))
P-idemp {𝓤}{𝓦} (pisou x x₁) = pisow (P-idemp{𝓤}{𝓦} x) x₁
P-idemp {𝓤}{𝓦} (pisow x x₁) = pisow (P-idemp{𝓤}{𝓦} x) x₁

-- S is a closure operator; in particular, it's monotone.
S-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →       𝒦 ⊆ 𝒦'  →  S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'
S-mono ante (sbase x) = sbase (ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (slift{𝑨} x) = slift{𝓤}{𝓦}{𝒦'} (S-mono{𝓤}{𝓤} ante x)
S-mono ante (ssub{𝑨}{𝑩} sA B≤A) = ssub (S-mono ante sA) B≤A
S-mono ante (ssubw{𝑨}{𝑩} sA B≤A) = ssubw (S-mono ante sA) B≤A
S-mono ante (siso x x₁) = siso (S-mono ante x) x₁

\end{code}

We sometimes want to go back and forth between our two representations of subalgebras of algebras in a class. The tools `subalgebra→S` and `S→subalgebra` are made for that purpose.

\begin{code}

subalgebra→S : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
               {𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑪 IsSubalgebraOfClass 𝒦
             ----------------------------------------------------------
 →                  𝑪 ∈ S{𝓤}{𝓦} 𝒦

subalgebra→S {𝓤}{𝓦}{𝒦}{𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = ssub sA C≤A
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  slAu : lift-alg 𝑨 𝓤 ∈ S{𝓤}{𝓤} 𝒦
  slAu = sbase KA

  sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦
  sA = siso slAu (sym-≅ lift-alg-≅)


module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} where

 S→subalgebra : {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S{𝓤}{𝓤} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦
 S→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , (sym-≅ lift-alg-≅)
 S→subalgebra (slift{𝑩} x) = ∣ BS ∣ , SA , KA , TRANS-≅ (sym-≅ lift-alg-≅) B≅SA
  where
   BS : 𝑩 IsSubalgebraOfClass 𝒦
   BS = S→subalgebra x

   SA : SUBALGEBRA ∣ BS ∣
   SA = fst ∥ BS ∥

   KA : ∣ BS ∣ ∈ 𝒦
   KA = ∣ snd ∥ BS ∥ ∣

   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BS ∥ ∥

 S→subalgebra {𝑩} (ssub{𝑨} sA B≤A) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : SUBALGEBRA ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = transitivity-≤ 𝑩{∣ SA ∣}{∣ AS ∣} B≤SA ∥ SA ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ =  ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , refl-≅

 S→subalgebra {𝑩} (ssubw{𝑨} sA B≤A) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : SUBALGEBRA ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = transitivity-≤ 𝑩{∣ SA ∣}{∣ AS ∣} B≤SA ∥ SA ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ =  ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , refl-≅

 S→subalgebra {𝑩} (siso{𝑨} sA A≅B) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : SUBALGEBRA ∣ AS ∣
   SA = fst ∥ AS ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd AS ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ = ∣ AS ∣ , SA ,  ∣ snd ∥ AS ∥ ∣ , (TRANS-≅ (sym-≅ A≅B) A≅SA)

\end{code}

Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.

\begin{code}

lift-alg-subP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{𝑩 : Algebra 𝓤 𝑆}

 →                𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
            ---------------------------------------------------
 →           (lift-alg 𝑩 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lift-alg-subP {𝓤} {𝓦} {𝒦} {𝑩} (𝑨 , (𝑪 , C≤A) , pA , B≅C ) = γ
 where
  lA lB lC : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  lB = lift-alg 𝑩 𝓦
  lC = lift-alg 𝑪 𝓦

  lC≤lA : lC ≤ lA
  lC≤lA = lift-alg-lift-≤-lift 𝑪 {𝑨} C≤A
  plA : lA ∈ P{𝓤}{𝓦} 𝒦
  plA = pliftu pA

  γ : lB IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  γ = lA , (lC , lC≤lA) , plA , (lift-alg-iso 𝓤 𝓦 𝑩 𝑪 B≅C)

\end{code}

The next lemma would be too obvoius to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

S⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)

S⊆SP {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (sbase{𝑨} x) =
 siso spllA (sym-≅ lift-alg-≅)
  where
   llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   llA = lift-alg (lift-alg 𝑨 𝓦) (𝓤 ⊔ 𝓦)

   spllA : llA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
   spllA = sbase{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦 = (𝓤 ⊔ 𝓦)} (pbase x)

S⊆SP {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (slift{𝑨} x) =
 subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lift-alg 𝑨 𝓦} lAsc
  where
   splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} x

   Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : (lift-alg 𝑨 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
   lAsc = lift-alg-subP Asc

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (ssub{𝑨} sA B≤A) =
 ssub{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp (lift-alg-sub-lift 𝑨 B≤A)
  where
   lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   lA = lift-alg 𝑨 𝓦

   splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} sA

   Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
   lAsc = lift-alg-subP Asc

   lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
   lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (ssubw{𝑨} sA B≤A) = γ
 where
  spA : 𝑨 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  spA = S⊆SP sA
  γ : 𝑩 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  γ = ssubw{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} spA B≤A

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (siso{𝑨} sA A≅B) = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} sA

  lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP (S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu)

  lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B

\end{code}

We need to formalize one more lemma before arriving the short term objective of this section, which is the proof of the inclusion PS⊆SP.

\begin{code}

lemPS⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →        {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →        ((i : I) → (ℬ i) IsSubalgebraOfClass 𝒦)
          ----------------------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lemPS⊆SP {𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K =
 ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , (produ{𝓤}{𝓦}{I = I}{𝒜 = 𝒜} (λ i → P-expa (KA i)) ) , γ
 where
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra 𝓤 𝑆
  SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

  KA : ∀ i → 𝒜 i ∈ 𝒦
  KA = λ i → ∣ snd ∥ B≤K i ∥ ∣

  B≅SA : ∀ i → ℬ i ≅ SA i
  B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥
  pA : ∀ i → lift-alg (𝒜 i) 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  pA = λ i → pbase (KA i)

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → ∣ SA≤𝒜 i ∣

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = i , ii , iii
   where
    i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
    i = λ x i → (h i) (x i)
    ii : is-embedding i
    ii = embedding-lift{𝓠 = 𝓤}{𝓤 = 𝓤}{𝓘 = 𝓦} hfe hfe {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)
  γ : ⨅ ℬ ≅ ⨅ SA
  γ = ⨅≅ gfe B≅SA

\end{code}

#### PS(𝒦) ⊆ SP(𝒦)

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

module _ {𝓤 : Universe}{𝒦u : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} {hfe : hfunext (OV 𝓤)(OV 𝓤)} where

 ov𝓾 : Universe
 ov𝓾 = OV 𝓤

 PS⊆SP : (P{ov𝓾}{ov𝓾} (S{𝓤}{ov𝓾} 𝒦u)) ⊆ (S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))
 PS⊆SP (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP (pbase (slift{𝑨} x)) = slift splA
  where
   splA : (lift-alg 𝑨 ov𝓾) ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   splA = S⊆SP{𝓤}{ov𝓾}{𝒦u} (slift x)

 PS⊆SP (pbase {𝑩} (ssub{𝑨} sA B≤A)) = siso γ refl-≅
  where
   lA lB : Algebra ov𝓾 𝑆
   lA = lift-alg 𝑨 ov𝓾
   lB = lift-alg 𝑩 ov𝓾

   ζ : lB ≤ lA
   ζ = lift-alg-lift-≤-lift 𝑩{𝑨} B≤A

   spA : lA ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   spA = S⊆SP{𝓤}{ov𝓾}{𝒦u} (slift sA)

   γ : (lift-alg 𝑩 ov𝓾) ∈ (S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))
   γ = ssub{𝓤 = ov𝓾} spA ζ

 PS⊆SP (pbase {𝑩} (ssubw{𝑨} sA B≤A)) = ssub{𝓤 = ov𝓾} splA (lift-alg-≤ 𝑩{𝑨} B≤A)
  where
   lA lB : Algebra ov𝓾 𝑆
   lA = lift-alg 𝑨 ov𝓾
   lB = lift-alg 𝑩 ov𝓾

   splA : lA ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   splA = slift{ov𝓾}{ov𝓾} (S⊆SP sA)


 PS⊆SP (pbase (siso{𝑨}{𝑩} x A≅B)) = siso splA ζ
  where
   lA lB : Algebra ov𝓾 𝑆
   lA = lift-alg 𝑨 ov𝓾
   lB = lift-alg 𝑩 ov𝓾

   ζ : lA ≅ lB
   ζ = lift-alg-iso 𝓤 ov𝓾 𝑨 𝑩 A≅B

   splA : lA ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   splA = S⊆SP (slift x)

 PS⊆SP (pliftu x) = slift (PS⊆SP x)
 PS⊆SP (pliftw x) = slift (PS⊆SP x)

 PS⊆SP (produ{I}{𝒜} x) = γ
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov𝓾} 𝒦u)
   ξ i = S→subalgebra{𝒦 = (P{𝓤}{ov𝓾} 𝒦u)} (PS⊆SP (x i))

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))
   η' = lemPS⊆SP{𝓤 = (ov𝓾)}{ov𝓾}{𝒦 = (P{𝓤}{ov𝓾} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))
   η = subalgebra→S{𝓤 = (ov𝓾)}{𝓦 = ov𝓾}{𝒦 = (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   γ = (S-mono{𝓤 = (ov𝓾)}{𝒦 = (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))}{𝒦' = (P{𝓤}{ov𝓾} 𝒦u)} (P-idemp)) η

 PS⊆SP (prodw{I}{𝒜} x) = γ
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov𝓾} 𝒦u)
   ξ i = S→subalgebra{𝒦 = (P{𝓤}{ov𝓾} 𝒦u)} (PS⊆SP (x i))

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))
   η' = lemPS⊆SP{𝓤 = (ov𝓾)}{ov𝓾}{𝒦 = (P{𝓤}{ov𝓾} 𝒦u)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))
   η = subalgebra→S{𝓤 = (ov𝓾)}{𝓦 = ov𝓾}{𝒦 = (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   γ = (S-mono{𝓤 = (ov𝓾)}{𝒦 = (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u))}{𝒦' = (P{𝓤}{ov𝓾} 𝒦u)} (P-idemp)) η

 PS⊆SP (pisou{𝑨}{𝑩} pA A≅B) = siso{ov𝓾}{ov𝓾}{P{𝓤}{ov𝓾} 𝒦u}{𝑨}{𝑩} spA A≅B
  where
   spA : 𝑨 ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   spA = PS⊆SP pA

 PS⊆SP (pisow{𝑨}{𝑩} pA A≅B) = siso{ov𝓾}{ov𝓾}{P{𝓤}{ov𝓾} 𝒦u}{𝑨}{𝑩} spA A≅B
  where
   spA : 𝑨 ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦u)
   spA = PS⊆SP pA

\end{code}

#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this module with three more inclusion relations that will have bit parts to play in our formal proof of Birkhoff's Theorem.

\begin{code}

P⊆V : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →    P{𝓤}{𝓦} 𝒦 ⊆ V{𝓤}{𝓦} 𝒦
P⊆V (pbase x) = vbase x
P⊆V{𝓤} (pliftu x) = vlift (P⊆V{𝓤}{𝓤} x)
P⊆V{𝓤}{𝓦} (pliftw x) = vliftw (P⊆V{𝓤}{𝓦} x)
P⊆V (produ x) = vprodu (λ i → P⊆V (x i))
P⊆V (prodw x) = vprodw (λ i → P⊆V (x i))
P⊆V (pisou x x₁) = visou (P⊆V x) x₁
P⊆V (pisow x x₁) = visow (P⊆V x) x₁

SP⊆V : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)}
 →    S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦) ⊆ V{𝓤}{𝓦} 𝒦
SP⊆V (sbase{𝑨} PCloA) = P⊆V (pisow PCloA lift-alg-≅)
SP⊆V (slift{𝑨} x) = vliftw (SP⊆V x)
SP⊆V{𝓤}{𝓦} {𝒦} (ssub{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V{𝓤}{𝓦} {𝒦} (ssubw{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (siso x x₁) = visow (SP⊆V x) x₁

\end{code}


#### <a id="products-of-classes">Products of classes</a>

Above we proved PS(𝒦) ⊆ SP(𝒦).  It is slightly more painful to prove that the product of *all* algebras in the class S(𝒦) is a member of SP(𝒦). That is,

```agda
⨅ S(𝒦) ∈ SP(𝒦)
```

This is mainly due to the fact that it's not obvious (at least not to this author-coder) what should be the type of the product of all members of a class of algebras.  After a few false starts, eventually the right type revealed itself.  Of course, now that we have it in our hands, it seems rather obvious.

We now describe the this type of product of all algebras in an arbitrary class 𝒦 of algebras of the same signature.

\begin{code}

module class-product {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} where

 -- ℑ serves as the index of the product
 ℑ : {𝓤 : Universe} →  Pred (Algebra 𝓤 𝑆)(OV 𝓤) → (OV 𝓤) ̇
 ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

  -- 𝔄 produces an algebra for each index (i : ℑ).
 𝔄 : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} → ℑ 𝒦 → Algebra 𝓤 𝑆
 𝔄{𝓤}{𝒦} = λ (i : (ℑ 𝒦)) → ∣ i ∣

 -- The product of all members of 𝒦 can be written simply as follows:
 class-product : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
 class-product {𝓤} 𝒦 = ⨅ ( 𝔄{𝓤}{𝒦} )

 -- ...or, more explicitly, here is the expansion of this indexed product.
 class-product' : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(OV 𝓤) → Algebra (OV 𝓤) 𝑆
 class-product'{𝓤} 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦)) → ∣ i ∣

\end{code}

Notice that, if `p : 𝑨 ∈ 𝒦`, then we can think of the pair `(𝑨 , p) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p)` (which is obviously `𝑨`) as the projection of the product `⨅ ( 𝔄{𝓤}{𝒦} )` onto the `(𝑨 , p)`-th component.

#### ⨅ S(𝒦) ∈ SP(𝒦)
Finally, we prove the result that plays a leading role in the formal proof of Birkhoff's Theorem---namely, that our newly defined class product ⨅ ( 𝔄{𝓤}{𝒦} ) belongs to SP(𝒦).

\begin{code}

-- The product of all subalgebras of a class 𝒦 belongs to SP(𝒦).
module class-product-inclusions {𝓤 : Universe} {𝒦 : Pred (Algebra 𝓤 𝑆)(OV 𝓤)} where

 open class-product {𝓤 = 𝓤}{𝒦 = 𝒦}

 class-prod-s-∈-ps : class-product (S{𝓤}{𝓤} 𝒦) ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦))

 class-prod-s-∈-ps = pisou{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} ps⨅llA ⨅llA≅cpK
  where
   I : (OV 𝓤) ̇
   I = ℑ (S{𝓤}{𝓤} 𝒦)

   sA : (i : I) → (𝔄 i) ∈ (S{𝓤}{𝓤} 𝒦)
   sA i = ∥ i ∥

   lA llA : I → Algebra (OV 𝓤) 𝑆
   lA i =  lift-alg (𝔄 i) (OV 𝓤)
   llA i = lift-alg (lA i) (OV 𝓤)

   slA : (i : I) → (lA i) ∈ (S{𝓤}{(OV 𝓤)} 𝒦)
   slA i = siso (sA i) lift-alg-≅

   psllA : (i : I) → (llA i) ∈ (P{OV 𝓤}{OV 𝓤} (S{𝓤}{(OV 𝓤)} 𝒦))
   psllA i = pbase{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} (slA i)

   ps⨅llA : ⨅ llA ∈ P{OV 𝓤}{OV 𝓤} (S{𝓤}{OV 𝓤} 𝒦)
   ps⨅llA = produ{𝓤 = (OV 𝓤)}{𝓦 = (OV 𝓤)} psllA

   llA≅A : (i : I) → (llA i) ≅ (𝔄 i)
   llA≅A i = Trans-≅ (llA i) (𝔄 i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

   ⨅llA≅cpK : ⨅ llA ≅ class-product (S{𝓤}{𝓤} 𝒦)
   ⨅llA≅cpK = ⨅≅ gfe llA≅A

 -- So, since PS⊆SP, we see that that the product of all subalgebras of a class 𝒦 belongs to SP(𝒦).
 class-prod-s-∈-sp : hfunext (OV 𝓤) (OV 𝓤)
  →                  class-product (S{𝓤}{𝓤} 𝒦) ∈ (S{OV 𝓤}{OV 𝓤} (P{𝓤}{OV 𝓤} 𝒦))

 class-prod-s-∈-sp hfe = PS⊆SP{hfe = hfe} (class-prod-s-∈-ps)

\end{code}

----------------------------

[← UALib.Varieties.EquationalLogic](UALib.Varieties.EquationalLogic.html)
<span style="float:right;">[UALib.Varieties.Preservation →](UALib.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}

