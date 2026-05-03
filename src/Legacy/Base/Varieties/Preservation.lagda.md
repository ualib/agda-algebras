---
layout: default
title : "Base.Varieties.Preservation (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

### <a id="Equation preservation">Equation preservation</a>

This is the [Base.Varieties.Preservation][] module of the [Agda Universal Algebra Library][]. In this module we show that identities are preserved by closure operators H, S, and P.  This will establish the easy direction of Birkhoff's HSP Theorem.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Varieties.Preservation {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------
open  import Agda.Primitive
      using () renaming  ( Set to Type )
open  import Data.Product
      using ( _,_ ; Σ-syntax ; _×_ ) renaming  ( proj₁ to fst ; proj₂ to snd )
open  import Data.Sum
      using ( _⊎_ ) renaming  ( inj₁  to inl ; inj₂  to inr )
open  import Function
      using ( _∘_ )
open  import Level
      using ( Level ; _⊔_ ; suc )
open  import Relation.Unary
      using ( Pred ; _⊆_ ; _∈_ ; ｛_｝ ; _∪_ )
open  import Axiom.Extensionality.Propositional
      using () renaming (Extensionality to funext)
open  import Relation.Binary.PropositionalEquality as ≡
      using ( _≡_ ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture        using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Legacy.Base.Functions  using ( Inv ; InvIsInverseʳ ; IsInjective )
open import Legacy.Base.Equality   using ( SwellDef ; hfunext ; DFunExt )

open  import Legacy.Base.Algebras {𝑆 = 𝑆}
      using ( Algebra ; Lift-Alg ; ov ; ⨅ ; 𝔄 ; class-product )
open  import Legacy.Base.Homomorphisms {𝑆 = 𝑆}
      using ( is-homomorphism ; _≅_ ; ≅-sym ; Lift-≅ ; ≅-trans ; ⨅≅ ; ≅-refl )
      using ( Lift-Alg-iso ; Lift-Alg-assoc )
open  import Legacy.Base.Terms {𝑆 = 𝑆}
      using ( Term ; 𝑻 ; _⟦_⟧; comm-hom-term )
open  import Legacy.Base.Subalgebras {𝑆 = 𝑆}
      using ( _IsSubalgebraOfClass_ ; ≤-Lift ; _IsSubalgebraOf_ ; _≤_ )
      using ( Lift-≤-Lift ; SubalgebraOfClass )
open  import Legacy.Base.Varieties.EquationalLogic {𝑆 = 𝑆}
      using ( _⊫_≈_ ; _⊧_≈_ ; Th )
open  import Legacy.Base.Varieties.Properties {𝑆 = 𝑆}
      using ( ⊧-Lift-invar ; ⊧-lower-invar ; ⊧-I-invar ; ⊧-S-invar ; ⊧-P-invar )
      using ( ⊧-S-class-invar ; ⊧-P-lift-invar )
open  import Legacy.Base.Varieties.Closure {𝑆 = 𝑆}
      using ( H ; S ; P ; V ; P-expa ; S-mono ; S→subalgebra ; Lift-Alg-subP' )
      using ( subalgebra→S ; P-idemp ; module Vlift )

open H ; open S ; open P ; open V
private variable α β : Level
```



#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that we'll need it later, so it too must be formalized.


```agda


S⊆SP :  (𝒦 : Pred (Algebra α)(ov α))
 →      S{α}{β} 𝒦 ⊆ S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦)

S⊆SP {α} {β} 𝒦 {.(Lift-Alg 𝑨 β)}(sbase{𝑨} x) = siso spllA(≅-sym Lift-≅)
 where
 llA : Algebra (α ⊔ β)
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

S⊆SP {α} {β} 𝒦 {𝑩}(ssub{𝑨} sA B≤A) = ssub (subalgebra→S lAsc) (≤-Lift 𝑨 B≤A )
 where
  lA : Algebra (α ⊔ β)
  lA = Lift-Alg 𝑨 β

  splAu : 𝑨 ∈ S (P 𝒦)
  splAu = S⊆SP{α}{α} 𝒦 sA

  Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
  Asc = S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} splAu

  lAsc : lA IsSubalgebraOfClass (P 𝒦)
  lAsc = Lift-Alg-subP' Asc

S⊆SP {α = α}{β} 𝒦 {𝑩}(siso{𝑨} sA A≅B) = siso{α ⊔ β}{α ⊔ β} lAsp lA≅B
 where
 lA : Algebra (α ⊔ β)
 lA = Lift-Alg 𝑨 β

 lAsc : lA IsSubalgebraOfClass (P 𝒦)
 lAsc = Lift-Alg-subP' (S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} (S⊆SP 𝒦 sA))

 lAsp : lA ∈ S(P 𝒦)
 lAsp = subalgebra→S{α ⊔ β}{α ⊔ β}{P{α}{β} 𝒦}{lA} lAsc

 lA≅B : lA ≅ 𝑩
 lA≅B = ≅-trans (≅-sym Lift-≅) A≅B
```


We need to formalize one more lemma before arriving the main objective of this section, which is the proof of the inclusion PS⊆SP.


```agda


module _ {α β : Level} {𝒦 : Pred(Algebra α)(ov α)} where

 lemPS⊆SP :  hfunext β α → funext β α → {I : Type β}{ℬ : I → Algebra α}
  →          (∀ i → (ℬ i) IsSubalgebraOfClass 𝒦)
  →          ⨅ ℬ IsSubalgebraOfClass (P{α}{β} 𝒦)

 lemPS⊆SP hwu fwu {I}{ℬ} B≤K =  ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜) ,
                                 ξ , (⨅≅ {fiu = fwu}{fiw = fwu} B≅SA)
  where
  𝒜 : I → Algebra α
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra α
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
  σinj σxσy = fwu λ i → (hinj i)(≡.cong-app σxσy i)

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = (σ , ν) , σinj

  ξ : ⨅ 𝒜 ∈ P 𝒦
  ξ = produ (λ i → P-expa (∣ snd ∥ B≤K i ∥ ∣))
```



#### <a id="PS-in-SP">PS(𝒦) ⊆ SP(𝒦)</a>

Finally, we are in a position to prove that a product of subalgebras of algebras
in a class `𝒦` is a subalgebra of a product of algebras in `𝒦`.


```agda


module _  {α : Level} {fovu : funext (ov α) (ov α)}
          {𝒦 : Pred (Algebra α)(ov α)} where

 PS⊆SP :  -- extensionality assumptions:
          hfunext (ov α)(ov α)

  →       P{ov α}{ov α} (S{α}{ov α} 𝒦) ⊆ S{ov α}{ov α} (P{α}{ov α} 𝒦)

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
```


#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this subsection with three more inclusion relations that will have
bit parts to play later (e.g., in the formal proof of Birkhoff's Theorem).


```agda


P⊆V : {α β : Level}{𝒦 : Pred (Algebra α)(ov α)} → P{α}{β} 𝒦 ⊆ V{α}{β} 𝒦

P⊆V (pbase x) = vbase x
P⊆V{α} (pliftu x) = vlift (P⊆V{α}{α} x)
P⊆V{α}{β} (pliftw x) = vliftw (P⊆V{α}{β} x)
P⊆V (produ x) = vprodu (λ i → P⊆V (x i))
P⊆V (prodw x) = vprodw (λ i → P⊆V (x i))
P⊆V (pisow x x₁) = visow (P⊆V x) x₁

SP⊆V :  {α β : Level}{𝒦 : Pred (Algebra α)(ov α)}
 →      S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦) ⊆ V 𝒦

SP⊆V (sbase{𝑨} PCloA) = P⊆V (pisow PCloA Lift-≅)
SP⊆V (slift{𝑨} x) = vliftw (SP⊆V x)
SP⊆V (ssub{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (siso x x₁) = visow (SP⊆V x) x₁
```



#### <a id="V-is-closed-under-lift">V is closed under lift</a>

As mentioned earlier, a technical hurdle that must be overcome when formalizing
proofs in Agda is the proper handling of universe levels. In particular, in the
proof of the Birkhoff's theorem, for example, we will need to know that if an
algebra `𝑨` belongs to the variety `V 𝒦`, then so does the lift of `𝑨`.  Let
us get the tedious proof of this technical lemma out of the way.

Above we proved that `SP(𝒦) ⊆ V(𝒦)`, and we did so under fairly general
assumptions about the universe level parameters.  Unfortunately, this is sometimes
not quite general enough, so we now prove the inclusion again for the specific
universe parameters that align with subsequent applications of this result.


```agda


module _  {α : Level}  {fe₀ : funext (ov α) α}
          {fe₁ : funext ((ov α) ⊔ (suc (ov α))) (suc (ov α))}
          {fe₂ : funext (ov α) (ov α)}
          {𝒦 : Pred (Algebra α)(ov α)} where
 open Vlift {α}{fe₀}{fe₁}{fe₂}{𝒦}

 SP⊆V' : S{ov α}{suc (ov α)} (P{α}{ov α} 𝒦) ⊆ V 𝒦
 SP⊆V' (sbase{𝑨} x) = visow (VlA (SP⊆V (sbase x))) (≅-sym (Lift-Alg-assoc _ _{𝑨}))
 SP⊆V' (slift x) = VlA (SP⊆V x)

 SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw (VlA (SP⊆V spA)) B≤lA
  where
   B≤lA : 𝑩 ≤ Lift-Alg 𝑨 (suc (ov α))
   B≤lA = ≤-Lift 𝑨 B≤A

 SP⊆V' (siso{𝑨}{𝑩} x A≅B) = visow (VlA (SP⊆V x)) Goal
  where
   Goal : Lift-Alg 𝑨 (suc (ov α)) ≅ 𝑩
   Goal = ≅-trans (≅-sym Lift-≅) A≅B
```



#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove a result that plays an important role, e.g., in the formal proof
of Birkhoff's Theorem. As we saw in [Base.Algebras.Products][], the (informal)
product `⨅ S(𝒦)` of all subalgebras of algebras in 𝒦 is implemented (formally)
in the [agda-algebras](https://github.com/ualib/agda-algebras) library as
`⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so by
first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

Before doing so, we need to redefine the class product so that each factor comes
with a map from the type `X` of variable symbols into that factor.  We will
explain the reason for this below.


```agda


module class-products-with-maps {α : Level}
 {X : Type α}
 {fe𝓕α : funext (ov α) α}
 {fe₁ : funext ((ov α) ⊔ (suc (ov α))) (suc (ov α))}
 {fe₂ : funext (ov α) (ov α)}
 (𝒦 : Pred (Algebra α)(ov α))
 where

 ℑ' : Type (ov α)
 ℑ' = Σ[ 𝑨 ∈ (Algebra α) ] ((𝑨 ∈ S{α}{α} 𝒦) × (X → ∣ 𝑨 ∣))
```


Notice that the second component of this dependent pair type is
`(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`. In previous versions of the [UALib][] this second
component was simply `𝑨 ∈ 𝒦`, until we realized that adding the type `X → ∣ 𝑨 ∣`
is quite useful. Later we will see exactly why, but for now suffice it to say that
a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as an *ambient context*, or
more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to *variable symbols* in
`X`.  When computing with or reasoning about products, while we don't want to
rigidly impose a context in advance, want do want to lay our hands on whatever
context is ultimately assumed.  Including the "context map" inside the index type
`ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type `ℑ` requires a function that maps an index
`i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a triple, say,
`(𝑨 , p , h)`, where `𝑨 : Algebra α`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the
function mapping an index to the corresponding algebra is simply the first projection.


```agda


 𝔄' : ℑ' → Algebra α
 𝔄' = λ (i : ℑ') → ∣ i ∣
```


Finally, we define `class-product` which represents the product of all members of
`𝒦`.


```agda


 class-product' : Algebra (ov α)
 class-product' = ⨅ 𝔄'
```


If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, we view the triple `(𝑨 , p , h) ∈ ℑ` as an
index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`)
as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p, h)`-th component.


```agda


 class-prod-s-∈-ps : class-product' ∈ P{ov α}{ov α}(S 𝒦)
 class-prod-s-∈-ps = pisow psPllA (⨅≅ {fiu = fe₂}{fiw = fe𝓕α} llA≅A)
  where
  lA llA : ℑ' → Algebra (ov α)
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
```



So, since `PS⊆SP`, we see that that the product of all subalgebras of a class `𝒦`
belongs to `SP(𝒦)`.


```agda


 class-prod-s-∈-sp : hfunext (ov α) (ov α) → class-product ∈ S(P 𝒦)
 class-prod-s-∈-sp hfe = PS⊆SP {fovu = fe₂} hfe class-prod-s-∈-ps
```



#### <a id="h-preserves-identities">H preserves identities</a>

First we prove that the closure operator `H` is compatible with identities that
hold in the given class.


```agda


open ≡-Reasoning

private variable 𝓧 : Level
open Term

module _ (wd : SwellDef){X : Type 𝓧} {𝒦 : Pred (Algebra α)(ov α)} where

 H-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → H{β = α} 𝒦 ⊫ p ≈ q
 H-id1 p q σ (hbase x) = ⊧-Lift-invar wd p q (σ x)
 H-id1 p q σ (hhimg{𝑨}{𝑪} HA (𝑩 , ((φ , φh) , φE))) b = goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = (H-id1 p q σ) HA

  preim : X → ∣ 𝑨 ∣
  preim x = Inv φ (φE (b x))

  ζ : ∀ x → φ (preim x) ≡ b x
  ζ x = InvIsInverseʳ (φE (b x))

  goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
  goal =  (𝑩 ⟦ p ⟧) b           ≡⟨ wd 𝓧 α (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
          (𝑩 ⟦ p ⟧)(φ ∘ preim)  ≡⟨(comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) p preim)⁻¹ ⟩
          φ((𝑨 ⟦ p ⟧) preim)    ≡⟨ ≡.cong φ (IH preim) ⟩
          φ((𝑨 ⟦ q ⟧) preim)    ≡⟨ comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) q preim ⟩
          (𝑩 ⟦ q ⟧)(φ ∘ preim)  ≡⟨ wd 𝓧 α (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
          (𝑩 ⟦ q ⟧) b           ∎
```


The converse of the foregoing result is almost too obvious to bother with.
Nonetheless, we formalize it for completeness.


```agda


 H-id2 : ∀ {β} → (p q : Term X) → H{β = β} 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 H-id2 p q Hpq KA = ⊧-lower-invar wd p q (Hpq (hbase KA))
```



#### <a id="s-preserves-identities">S preserves identities</a>


```agda


 S-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → S{β = α} 𝒦 ⊫ p ≈ q
 S-id1 p q σ (sbase x) = ⊧-Lift-invar wd p q (σ x)
 S-id1 p q σ (slift x) = ⊧-Lift-invar wd p q ((S-id1 p q σ) x)
 S-id1 p q σ (ssub{𝑨}{𝑩} sA B≤A) = ⊧-S-class-invar wd p q goal ν
  where --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
  τ : 𝑨 ⊧ p ≈ q
  τ = S-id1 p q σ sA

  Apq : ｛ 𝑨 ｝ ⊫ p ≈ q
  Apq ≡.refl = τ

  goal : (𝒦 ∪ ｛ 𝑨 ｝) ⊫ p ≈ q
  goal {𝑩} (inl x) = σ x
  goal {𝑩} (inr y) = Apq y

  ν : SubalgebraOfClass  (λ z → (𝒦 ∪ ｛ 𝑨 ｝)
                         (Data.Product.proj₁ z , Data.Product.proj₂ z))

  ν = (𝑩 , 𝑨 , (𝑩 , B≤A) , _⊎_.inj₂ ≡.refl , ≅-refl)

 S-id1 p q σ (siso{𝑨}{𝑩} x x₁) = ⊧-I-invar wd 𝑩 p q (S-id1 p q σ x) x₁
```


Again, the obvious converse is barely worth the bits needed to formalize it.


```agda


 S-id2 : ∀{β}(p q : Term X) → S{β = β}𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 S-id2 p q Spq {𝑨} KA = ⊧-lower-invar wd p q (Spq (sbase KA))
```



#### <a id="p-preserves-identities">P preserves identities</a>


```agda


module _  (fe : DFunExt)(wd : SwellDef){X : Type 𝓧}
          {𝒦 : Pred (Algebra α)(ov α)} where

 P-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → P{β = α} 𝒦 ⊫ p ≈ q

 P-id1 p q σ (pbase x) = ⊧-Lift-invar wd p q (σ x)
 P-id1 p q σ (pliftu x) = ⊧-Lift-invar wd p q ((P-id1 p q σ) x)
 P-id1 p q σ (pliftw x) = ⊧-Lift-invar wd p q ((P-id1 p q σ) x)

 P-id1 p q σ (produ{I}{𝒜} x) = ⊧-P-lift-invar fe wd 𝒜  p q IH
  where
  IH : ∀ i → (Lift-Alg (𝒜 i) α) ⊧ p ≈ q
  IH i = ⊧-Lift-invar wd  p q ((P-id1 p q σ) (x i))

 P-id1 p q σ (prodw{I}{𝒜} x) = ⊧-P-lift-invar fe wd 𝒜  p q IH
  where
  IH : ∀ i → (Lift-Alg (𝒜 i) α) ⊧ p ≈ q
  IH i = ⊧-Lift-invar wd  p q ((P-id1 p q σ) (x i))

 P-id1 p q σ (pisow{𝑨}{𝑩} x y) = ⊧-I-invar wd 𝑩 p q (P-id1 p q σ x) y
```


and conversely,


```agda


module _  (wd : SwellDef){X : Type 𝓧} {𝒦 : Pred (Algebra α)(ov α)} where

 P-id2 : ∀ {β}(p q : Term X) → P{β = β} 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 P-id2 p q PKpq KA = ⊧-lower-invar wd p q (PKpq (pbase KA))
```


#### <a id="v-preserves-identities">V preserves identities</a>

Finally, we prove the analogous preservation lemmas for the closure operator `V`.


```agda


module Vid  (fe : DFunExt)(wd : SwellDef)
            {𝓧 : Level} {X : Type 𝓧}{𝒦 : Pred (Algebra α)(ov α)} where

 V-id1 : (p q : Term X) → 𝒦 ⊫ p ≈ q → V{β = α} 𝒦 ⊫ p ≈ q
 V-id1 p q σ (vbase x) = ⊧-Lift-invar wd p q (σ x)
 V-id1 p q σ (vlift{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
 V-id1 p q σ (vliftw{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
 V-id1 p q σ (vhimg{𝑨}{𝑪}VA (𝑩 , ((φ , φh) , φE))) b = goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1 p q σ VA

  preim : X → ∣ 𝑨 ∣
  preim x = Inv φ (φE (b x))

  ζ : ∀ x → φ (preim x) ≡ b x
  ζ x = InvIsInverseʳ (φE (b x))

  goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
  goal =  (𝑩 ⟦ p ⟧) b           ≡⟨ wd 𝓧 α (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
          (𝑩 ⟦ p ⟧)(φ ∘ preim)  ≡⟨(comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) p preim)⁻¹ ⟩
          φ((𝑨 ⟦ p ⟧) preim)    ≡⟨ ≡.cong φ (IH preim) ⟩
          φ((𝑨 ⟦ q ⟧) preim)    ≡⟨ comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) q preim ⟩
          (𝑩 ⟦ q ⟧)(φ ∘ preim)  ≡⟨ wd 𝓧 α (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
          (𝑩 ⟦ q ⟧) b           ∎

 V-id1 p q σ ( vssubw {𝑨}{𝑩} VA B≤A ) =
  ⊧-S-class-invar wd p q goal (𝑩 , 𝑨 , (𝑩 , B≤A) , inr ≡.refl , ≅-refl)
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q σ VA

   Asinglepq : ｛ 𝑨 ｝ ⊫ p ≈ q
   Asinglepq ≡.refl = IH

   goal : (𝒦 ∪ ｛ 𝑨 ｝) ⊫ p ≈ q
   goal {𝑩} (inl x) = σ x
   goal {𝑩} (inr y) = Asinglepq y

 V-id1 p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
 V-id1 p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
 V-id1 p q σ (visou{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B
 V-id1 p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B

module Vid'  (fe : DFunExt)(wd : SwellDef)
             {𝓧 : Level}{X : Type 𝓧}{𝒦 : Pred (Algebra α)(ov α)} where
 open Vid fe wd {𝓧}{X}{𝒦} public
 V-id1' : (p q : Term X) → 𝒦 ⊫ p ≈ q → V{β = β} 𝒦 ⊫ p ≈ q
 V-id1' p q σ (vbase x) = ⊧-Lift-invar wd p q (σ x)
 V-id1' p q σ (vlift{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
 V-id1' p q σ (vliftw{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1' p q σ) x)
 V-id1' p q σ (vhimg{𝑨}{𝑪} VA (𝑩 , ((φ , φh) , φE))) b = goal
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1' p q σ VA

  preim : X → ∣ 𝑨 ∣
  preim x = Inv φ (φE (b x))

  ζ : ∀ x → φ (preim x) ≡ b x
  ζ x = InvIsInverseʳ (φE (b x))

  goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
  goal =  (𝑩 ⟦ p ⟧) b           ≡⟨ wd 𝓧 _ (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
          (𝑩 ⟦ p ⟧)(φ ∘ preim)  ≡⟨(comm-hom-term (wd 𝓥 _) 𝑩 (φ , φh) p preim)⁻¹ ⟩
          φ((𝑨 ⟦ p ⟧) preim)    ≡⟨ ≡.cong φ (IH preim) ⟩
          φ((𝑨 ⟦ q ⟧) preim)    ≡⟨ comm-hom-term (wd 𝓥 _) 𝑩 (φ , φh) q preim ⟩
          (𝑩 ⟦ q ⟧)(φ ∘ preim)  ≡⟨ wd 𝓧 _ (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
          (𝑩 ⟦ q ⟧) b           ∎

 V-id1' p q σ (vssubw {𝑨}{𝑩} VA B≤A) = ⊧-S-invar wd 𝑩 {p}{q}(V-id1' p q σ VA) B≤A
 V-id1' p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
 V-id1' p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1' p q σ (V𝒜 i)
 V-id1' p q σ (visou {𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B
 V-id1' p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1' p q σ VA)A≅B
```



#### <a id="class-identities">Class identities</a>

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of
identities modeled by all structures in `𝒦` is equivalent to the set of identities
modeled by all structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the
set of identities modeled by `𝒦`.   We formalize this observation as follows.


```agda


module _  (fe : DFunExt)(wd : SwellDef)
          {𝓧 : Level}{X : Type 𝓧} {𝒦 : Pred (Algebra α)(ov α)} where
 ovu lovu : Level
 ovu = ov α
 lovu = suc (ov α)
 𝕍 : Pred (Algebra lovu) (suc lovu)
 𝕍 = V{α}{lovu} 𝒦
 𝒱 : Pred (Algebra ovu) lovu
 𝒱 = V{β = ovu} 𝒦

 open Vid' fe wd {𝓧}{X}{𝒦} public
 class-ids-⇒ : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊫ p ≈ q  →  (p , q) ∈ Th 𝒱
 class-ids-⇒ p q pKq VCloA = V-id1' p q pKq VCloA

 class-ids : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊫ p ≈ q  →  (p , q) ∈ Th 𝕍
 class-ids p q pKq VCloA = V-id1' p q pKq VCloA

 class-ids-⇐ : (p q : ∣ 𝑻 X ∣) → (p , q) ∈ Th 𝒱 →  𝒦 ⊫ p ≈ q
 class-ids-⇐ p q Thpq {𝑨} KA = ⊧-lower-invar wd p q (Thpq (vbase KA))
```


Once again, and for the last time, completeness dictates that we formalize the
coverse of `V-id1`, however obvious it may be.


```agda


module _ (wd : SwellDef){X : Type 𝓧}{𝒦 : Pred (Algebra α)(ov α)} where

 V-id2 : (p q : Term X) → (V{β = β} 𝒦 ⊫ p ≈ q) → (𝒦 ⊫ p ≈ q)
 V-id2 p q Vpq {𝑨} KA = ⊧-lower-invar wd p q (Vpq (vbase KA))
```


----------------------------

<span style="float:left;">[← Base.Varieties.Properties](Base.Varieties.Properties.html)</span>
<span style="float:right;">[Base.Varieties.FreeAlgebras →](Base.Varieties.FreeAlgebras.html)</span>

{% include UALib.Links.md %}
