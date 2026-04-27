---
layout: default
title : "Base.Varieties.Closure  module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

### <a id="closure-operators">Closure Operators</a>

Fix a signature `𝑆`, let `𝒦` be a class of `𝑆`-algebras, and define

* `H 𝒦` = algebras isomorphic to a homomorphic image of a member of `𝒦`;
* `S 𝒦` = algebras isomorphic to a subalgebra of a member of `𝒦`;
* `P 𝒦` = algebras isomorphic to a product of members of `𝒦`.

A straight-forward verification confirms that `H`, `S`, and `P` are *closure operators* (expansive, monotone, and idempotent).  A class `𝒦` of `𝑆`-algebras is said to be *closed under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, `𝒦` is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`). The operators `H`, `S`, and `P` can be composed with one another repeatedly, forming yet more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under isomorphism.

A *variety* is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define an inductive type `V` which simultaneously represents closure under all three operators, `H`, `S`, and `P`.



```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Varieties.Closure {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level ;  Lift ; _⊔_ ; suc )
open import Relation.Unary  using ( Pred ; _∈_ ; _⊆_ )
open import Data.Product    using ( _,_ ; Σ-syntax )
                            renaming ( proj₁ to fst ; proj₂ to snd )

open  import Axiom.Extensionality.Propositional
      using () renaming ( Extensionality to funext )

-- Imports from the Agda Universal Algebra Library ---------------------------------------
open import Overture               using ( ∣_∣ ; ∥_∥ )
open import Base.Algebras {𝑆 = 𝑆}  using ( Algebra ; Lift-Alg ; ov ; ⨅ )

open  import Base.Homomorphisms {𝑆 = 𝑆}
      using ( _≅_ ; ≅-sym ; Lift-≅ ; ≅-trans ; ≅-refl ; Lift-Alg-iso ; Lift-Alg-⨅≅ )
      using ( Lift-Alg-assoc ; HomImages ; _IsHomImageOf_ ; Lift-Alg-hom-image )

open  import Base.Subalgebras {𝑆 = 𝑆}
      using ( _≤_ ; _IsSubalgebraOfClass_ ; Subalgebra ; ≤-refl ; ≅-RESP-≤ )
      using ( ≤-RESP-≅ ; ≤-trans ; Lift-≤-Lift )
```


#### <a id="the-inductive-type-h">The Inductive Type H</a>

We define the inductive type `H` to represent classes of algebras that include
all homomorphic images of algebras in the class; i.e., classes that are closed
under the taking of homomorphic images.


```agda


data H{α β : Level}(𝒦 : Pred(Algebra α)(ov α)) : Pred(Algebra (α ⊔ β))(ov(α ⊔ β))
 where
 hbase : {𝑨 : Algebra α} → 𝑨 ∈ 𝒦 → Lift-Alg 𝑨 β ∈ H 𝒦
 hhimg : {𝑨 𝑩 : Algebra (α ⊔ β)} → 𝑨 ∈ H {α} {β} 𝒦 → ((𝑩 , _) : HomImages 𝑨) → 𝑩 ∈ H 𝒦
```


#### <a id="the-inductive-type-s">The Inductive Type S</a>

Here we define the inductive type `S` to represent classes of algebras closed under the taking of subalgebras.


```agda


data S {α β : Level}(𝒦 : Pred(Algebra α)(ov α)) : Pred(Algebra(α ⊔ β))(ov(α ⊔ β))
 where
 sbase : {𝑨 : Algebra α} → 𝑨 ∈ 𝒦 → Lift-Alg 𝑨 β ∈ S 𝒦
 slift : {𝑨 : Algebra α} → 𝑨 ∈ S{α}{α} 𝒦 → Lift-Alg 𝑨 β ∈ S 𝒦
 ssub  : {𝑨 : Algebra α}{𝑩 : Algebra _} → 𝑨 ∈ S{α}{α} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
 siso  : {𝑨 : Algebra α}{𝑩 : Algebra _} → 𝑨 ∈ S{α}{α} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S 𝒦
```


#### <a id="the-inductive-types-p">The Inductive Type P </a>

Here we define the inductive type `P` to represent classes of algebras closed under the taking of arbitrary products.


```agda


data P {α β : Level}(𝒦 : Pred(Algebra α)(ov α)) : Pred(Algebra(α ⊔ β))(ov(α ⊔ β))
 where
 pbase  : {𝑨 : Algebra α} → 𝑨 ∈ 𝒦 → Lift-Alg 𝑨 β ∈ P 𝒦
 pliftu : {𝑨 : Algebra α} → 𝑨 ∈ P{α}{α} 𝒦 → Lift-Alg 𝑨 β ∈ P 𝒦
 pliftw : {𝑨 : Algebra (α ⊔ β)} → 𝑨 ∈ P{α}{β} 𝒦 → Lift-Alg 𝑨 (α ⊔ β) ∈ P 𝒦
 produ  : {I : Type β }{𝒜 : I → Algebra α} → (∀ i → (𝒜 i) ∈ P{α}{α} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
 prodw  : {I : Type β }{𝒜 : I → Algebra _} → (∀ i → (𝒜 i) ∈ P{α}{β} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
 pisow  : {𝑨 𝑩 : Algebra _} → 𝑨 ∈ P{α}{β} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦
```



#### <a id="the-inductive-types-v">The Inductive Types V</a>

A class `𝒦` of `𝑆`-algebras is called a *variety* if it is closed under each of
the closure operators `H`, `S`, and `P` introduced elsewhere; the corresponding
closure operator is often denoted `𝕍`, but we will denote it by `V`.

We now define `V` as an inductive type which is crafted to contain all the parts
of `H`, `S` and `P`, under different names.


```agda


data V {α β : Level}(𝒦 : Pred(Algebra α)(ov α)) : Pred(Algebra(α ⊔ β))(ov(α ⊔ β))
 where
 vbase   : {𝑨 : Algebra α} → 𝑨 ∈ 𝒦 → Lift-Alg 𝑨 β ∈ V 𝒦
 vlift   : {𝑨 : Algebra α} → 𝑨 ∈ V{α}{α} 𝒦 → Lift-Alg 𝑨 β ∈ V 𝒦
 vliftw  : {𝑨 : Algebra _} → 𝑨 ∈ V{α}{β} 𝒦 → Lift-Alg 𝑨 (α ⊔ β) ∈ V 𝒦
 vhimg   : {𝑨 𝑩 : Algebra _} → 𝑨 ∈ V{α}{β} 𝒦 → ((𝑩 , _) : HomImages 𝑨) → 𝑩 ∈ V 𝒦
 vssubw  : {𝑨 𝑩 : Algebra _} → 𝑨 ∈ V{α}{β} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
 vprodu  : {I : Type β}{𝒜 : I → Algebra α} → (∀ i → (𝒜 i) ∈ V{α}{α} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
 vprodw  : {I : Type β}{𝒜 : I → Algebra _} → (∀ i → (𝒜 i) ∈ V{α}{β} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
 visou   : {𝑨 : Algebra α}{𝑩 : Algebra _} → 𝑨 ∈ V{α}{α} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦
 visow   : {𝑨 𝑩 : Algebra _} → 𝑨 ∈ V{α}{β} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦
```


Thus, if 𝒦 is a class of 𝑆-algebras, then the *variety generated by* 𝒦 is denoted
by `V 𝒦` and defined to be the smallest class that contains 𝒦 and is closed under
`H`, `S`, and `P`.

With the closure operator V representing closure under HSP, we represent formally
what it means to be a variety of algebras as follows.


```agda


is-variety : {α : Level}(𝒱 : Pred (Algebra α)(ov α)) → Type(ov α)
is-variety{α} 𝒱 = V{α}{α} 𝒱 ⊆ 𝒱

variety : (α : Level) → Type(suc (𝓞 ⊔ 𝓥 ⊔ (suc α)))
variety α = Σ[ 𝒱 ∈ (Pred (Algebra α)(ov α)) ] is-variety 𝒱
```



#### <a id="closure-properties-of-S">Closure properties of S</a>

`S` is a closure operator.  The facts that S is idempotent and expansive won't be
needed, so we omit these, but we will make use of monotonicity of S.  Here is the
proof of the latter.


```agda


S-mono :  {α β : Level}{𝒦 𝒦' : Pred (Algebra α)(ov α)}
 →        𝒦 ⊆ 𝒦' → S{α}{β} 𝒦 ⊆ S{α}{β} 𝒦'

S-mono kk (sbase x)            = sbase (kk x)
S-mono kk (slift{𝑨} x)         = slift (S-mono kk x)
S-mono kk (ssub{𝑨}{𝑩} sA B≤A)  = ssub (S-mono kk sA) B≤A
S-mono kk (siso x x₁)          = siso (S-mono kk x) x₁
```


We sometimes want to go back and forth between our two representations of subalgebras
of algebras in a class. The tools `subalgebra→S` and `S→subalgebra` are made for
that purpose.


```agda


module _ {α β : Level}{𝒦 : Pred (Algebra α)(ov α)} where

 subalgebra→S : {𝑩 : Algebra (α ⊔ β)} → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 ∈ S{α}{β} 𝒦
 subalgebra→S {𝑩} (𝑨 , ((𝑪 , C≤A) , KA , B≅C)) = ssub sA B≤A
  where
   B≤A : 𝑩 ≤ 𝑨
   B≤A = ≅-RESP-≤ {𝑪 = 𝑨} B≅C C≤A

   slAu : Lift-Alg 𝑨 α ∈ S{α}{α} 𝒦
   slAu = sbase KA

   sA : 𝑨 ∈ S{α}{α} 𝒦
   sA = siso slAu (≅-sym Lift-≅)


module _ {α : Level}{𝒦 : Pred (Algebra α)(ov α)} where

 S→subalgebra : {𝑩 : Algebra α} → 𝑩 ∈ S{α}{α} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦
 S→subalgebra (sbase{𝑩} x) =  𝑩 , ((𝑩 , (≤-refl ≅-refl)) , x , ≅-sym Lift-≅)
 S→subalgebra (slift{𝑩} x) =  ∣ BS ∣ ,
                              SA , ∣ snd ∥ BS ∥ ∣ , ≅-trans (≅-sym Lift-≅) B≅SA
  where
   BS : 𝑩 IsSubalgebraOfClass 𝒦
   BS = S→subalgebra x
   SA : Subalgebra ∣ BS ∣
   SA = fst ∥ BS ∥
   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BS ∥ ∥

 S→subalgebra {𝑩} (ssub{𝑨} sA B≤A) = ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , ≅-refl
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = ≤-RESP-≅ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = ≤-trans 𝑩 ∣ AS ∣ B≤SA ∥ SA ∥

 S→subalgebra {𝑩} (siso{𝑨} sA A≅B) =  ∣ AS ∣ ,
                                      SA ,
                                      ∣ snd ∥ AS ∥ ∣ , (≅-trans (≅-sym A≅B) A≅SA)
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd AS ∥
```



#### <a id="closure-properties-of-P">Closure properties of P</a>

`P` is a closure operator.  This is proved by checking that `P` is *monotone*,
*expansive*, and *idempotent*. The meaning of these terms will be clear from
the definitions of the types that follow.


```agda


P-mono :  {α β : Level}{𝒦 𝒦' : Pred(Algebra α)(ov α)}
 →        𝒦 ⊆ 𝒦' → P{α}{β} 𝒦 ⊆ P{α}{β} 𝒦'

P-mono kk' (pbase x)     = pbase (kk' x)
P-mono kk' (pliftu x)    = pliftu (P-mono kk' x)
P-mono kk' (pliftw x)    = pliftw (P-mono kk' x)
P-mono kk' (produ x)     = produ (λ i → P-mono kk' (x i))
P-mono kk' (prodw x)     = prodw (λ i → P-mono kk' (x i))
P-mono kk' (pisow x x₁)  = pisow (P-mono kk' x) x₁


P-expa : {α : Level}{𝒦 : Pred (Algebra α)(ov α)} → 𝒦 ⊆ P{α}{α} 𝒦
P-expa{α}{𝒦} {𝑨} KA = pisow {𝑩 = 𝑨} (pbase KA) (≅-sym Lift-≅)

module _ {α β : Level} where

 P-idemp :  {𝒦 : Pred (Algebra α)(ov α)}
  →         P{α ⊔ β}{α ⊔ β} (P{α}{α ⊔ β} 𝒦) ⊆ P{α}{α ⊔ β} 𝒦

 P-idemp (pbase x)     = pliftw x
 P-idemp (pliftu x)    = pliftw (P-idemp x)
 P-idemp (pliftw x)    = pliftw (P-idemp x)
 P-idemp (produ x)     = prodw (λ i → P-idemp (x i))
 P-idemp (prodw x)     = prodw (λ i → P-idemp (x i))
 P-idemp (pisow x x₁)  = pisow (P-idemp x) x₁
```


Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.


```agda


module _ {α β : Level}{𝒦 : Pred (Algebra α)(ov α)} where

 Lift-Alg-subP :  {𝑩 : Algebra β}
  →               𝑩 IsSubalgebraOfClass (P{α}{β} 𝒦)
  →               (Lift-Alg 𝑩 α) IsSubalgebraOfClass (P{α}{β} 𝒦)

 Lift-Alg-subP (𝑨 , (𝑪 , C≤A) , pA , B≅C ) =  lA ,
                                              (lC , lC≤lA) ,
                                              plA , (Lift-Alg-iso B≅C)
   where
   lA lC : Algebra (α ⊔ β)
   lA = Lift-Alg 𝑨 (α ⊔ β)
   lC = Lift-Alg 𝑪 α

   lC≤lA : lC ≤ lA
   lC≤lA = Lift-≤-Lift α {𝑨} (α ⊔ β) C≤A
   plA : lA ∈ P{α}{β} 𝒦
   plA = pliftw pA

 Lift-Alg-subP' :  {𝑨 : Algebra α}
  →                𝑨 IsSubalgebraOfClass (P{α}{α} 𝒦)
  →                (Lift-Alg 𝑨 β) IsSubalgebraOfClass (P{α}{β} 𝒦)

 Lift-Alg-subP' (𝑩 , (𝑪 , C≤B) , pB , A≅C ) = lB , (lC , lC≤lB) , plB , (Lift-Alg-iso A≅C)
   where
   lB lC : Algebra (α ⊔ β)
   lB = Lift-Alg 𝑩 β
   lC = Lift-Alg 𝑪 β

   lC≤lB : lC ≤ lB
   lC≤lB = Lift-≤-Lift β {𝑩} β C≤B
   plB : lB ∈ P{α}{β} 𝒦
   plB = pliftu pB
```


#### <a id="V-is-closed-under-lift">V is closed under lift</a>

As mentioned earlier, a technical hurdle that must be overcome when formalizing proofs in Agda is the proper handling of universe levels. In particular, in the proof of the Birkhoff's theorem, for example, we will need to know that if an algebra 𝑨 belongs to the variety V 𝒦, then so does the lift of 𝑨.  Let us get the tedious proof of this technical lemma out of the way.


```agda


open Level

module Vlift  {α : Level} {fe₀ : funext (ov α) α}
              {fe₁ : funext ((ov α) ⊔ (suc (ov α))) (suc (ov α))}
              {fe₂ : funext (ov α) (ov α)}
              {𝒦 : Pred (Algebra α)(ov α)} where

 VlA :  {𝑨 : Algebra (ov α)} → 𝑨 ∈ V{α}{ov α} 𝒦
  →     Lift-Alg 𝑨 (suc (ov α)) ∈ V{α}{suc (ov α)} 𝒦
 VlA (vbase{𝑨} x) = visow (vbase x) (Lift-Alg-assoc _ _ {𝑨})
 VlA (vlift{𝑨} x) = visow (vlift x) (Lift-Alg-assoc _ _ {𝑨})
 VlA (vliftw{𝑨} x) = visow (VlA x) (Lift-Alg-assoc _ _ {𝑨})

 VlA (vhimg{𝑨}{𝑩} x hB) = vhimg {𝑩 = Lift-Alg 𝑩 (suc (ov α))} (VlA x) (lC , lChi)
  where
  lC : Algebra (suc (ov α))
  lC = Lift-Alg ∣ hB ∣ (suc (ov α))
  lChi : lC IsHomImageOf _
  lChi = (Lift-Alg-hom-image (suc (ov(α))) {∣ hB ∣} (suc (ov(α))) ∥ hB ∥)

 VlA (vssubw{𝑨}{𝑩} x B≤A) =
  vssubw (VlA x) (Lift-≤-Lift (suc (ov(α))) {𝑨} (suc (ov(α))) B≤A)

 VlA (vprodu{I}{𝒜} x) = visow (vprodw vlA) (≅-sym B≅A)
  where
  𝑰 : Type (suc (ov α))
  𝑰 = Lift (suc (ov α)) I

  lA : 𝑰 → Algebra (suc (ov α))
  lA i = Lift-Alg (𝒜 (lower i)) (suc (ov α))

  vlA : ∀ i → (lA i) ∈ V{α}{suc (ov α)} 𝒦
  vlA i = vlift (x (lower i))

  iso-components : ∀ i → 𝒜 i ≅ lA (lift i)
  iso-components i = Lift-≅

  B≅A : Lift-Alg (⨅ 𝒜) (suc (ov α)) ≅ ⨅ lA
  B≅A = Lift-Alg-⨅≅  {fizw = fe₁}{fiu = fe₀} iso-components

 VlA (vprodw{I}{𝒜} x) = visow (vprodw vlA) (≅-sym B≅A)
  where
  𝑰 : Type (suc (ov α))
  𝑰 = Lift (suc (ov α)) I

  lA : 𝑰 → Algebra (suc (ov α))
  lA i = Lift-Alg (𝒜 (lower i)) (suc (ov α))

  vlA : ∀ i → (lA i) ∈ V{α}{suc (ov α)} 𝒦
  vlA i = VlA (x (lower i))

  iso-components : ∀ i → 𝒜 i ≅ lA (lift i)
  iso-components i = Lift-≅

  B≅A : Lift-Alg (⨅ 𝒜) (suc (ov α)) ≅ ⨅ lA
  B≅A = Lift-Alg-⨅≅ {fizw = fe₁}{fiu = fe₂} iso-components

 VlA (visou{𝑨}{𝑩} x A≅B) = visow (vlift x) (Lift-Alg-iso A≅B)
 VlA (visow{𝑨}{𝑩} x A≅B) = visow (VlA x) (Lift-Alg-iso A≅B)
```


---------------------------------

<span style="float:left;">[← Base.Varieties.EquationalLogic](Base.Varieties.EquationalLogic.html)</span>
<span style="float:right;">[Base.Varieties.Properties →](Base.Varieties.Properties.html)</span>

{% include UALib.Links.md %}
