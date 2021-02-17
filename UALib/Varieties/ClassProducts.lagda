---
layout: default
title : UALib.Varieties.ClassProducts module (The Agda Universal Algebra Library)
date : 2021-02-17
author: William DeMeo
---

### <a id="class-products">Class Products</a>

This section presents the [UALib.Varieties.ClassProducts][] module of the [Agda Universal Algebra Library][].
Here we formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all algebras in the class S(𝒦) belongs to SP(𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (to this author) how one expresses the product of an entire class of algebras as a dependent type. After a number of failed attempts, however, the right type revealed itself and now it seems almost obvious.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Varieties.ClassProducts
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Varieties.Varieties{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

First, we define the type that will serve to index the class (as well as the product of its members), as follows.

\begin{code}

ℑ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} →  Pred (Algebra 𝓤 𝑆)(ov 𝓤) → (𝓧 ⊔ ov 𝓤) ̇
ℑ {𝓤}{𝓧}{X} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)

\end{code}

Notice that the second component of the dependent pair is `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.  In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`.  However, we realized that adding a mapping of type `X → ∣ 𝑨 ∣` is quite useful.  The reason for this will become clear later; for now, suffice it to say that a map X → ∣ 𝑨 ∣ may be viewed as a context, and we would like to keep the context completely general.  Adding the map to the index set defined above accomplishes this.

Taking the product over this index type ℑ requires a function like the following, which takes an index (i : ℑ) and returns the corresponding algebra.

\begin{code}

𝔄 : {𝓤 : Universe}{𝓧 : Universe}{X : 𝓧 ̇}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) → ℑ{𝓤}{𝓧}{X} 𝒦 → Algebra 𝓤 𝑆
𝔄 𝒦 = λ (i : (ℑ 𝒦)) → ∣ i ∣
\end{code}

Finally, the product of all members of 𝒦 is represented as follows.

\begin{code}

class-product : {𝓤 : Universe}{𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆
class-product {𝓤}{𝓧}{X} 𝒦 = ⨅ ( 𝔄{𝓤}{𝓧}{X} 𝒦 )

\end{code}

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

\begin{code}

 -- class-product' : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (ov 𝓤) 𝑆
 -- class-product'{𝓤}{𝓧}{X} 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣))) → ∣ i ∣

\end{code}

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the pair `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is obviously `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.


#### <a id="S-in-SP">⨅ S(𝒦) ∈ SP(𝒦)</a>

Finally, we prove the result that plays an important role in the formal proof of Birkhoff's Theorem---namely, that our newly defined class product ⨅ ( 𝔄 𝒦 ) belongs to SP(𝒦).

As we just saw, the (informal) product ⨅ S(𝒦) of all subalgebras of algebras in 𝒦 is implemented (formally) in the [UALib][] as ⨅ ( 𝔄 S(𝒦) ), and our goal is to prove that this product belongs to SP(𝒦). We can do this by first proving that the product belongs to PS(𝒦) (in `class-prod-s-∈-ps`) and then applying the PS⊆SP lemma above.

\begin{code}

module class-product-inclusions {𝓤 : Universe}{X : 𝓤 ̇} {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where
 𝓸𝓿𝓾 : Universe
 𝓸𝓿𝓾 = ov 𝓤

 class-prod-s-∈-ps : class-product {𝓤}{𝓤}{X} (S{𝓤}{𝓤} 𝒦) ∈ (P{𝓸𝓿𝓾}{𝓸𝓿𝓾} (S{𝓤}{𝓸𝓿𝓾} 𝒦))
 class-prod-s-∈-ps = pisou{𝓤 = (𝓸𝓿𝓾)}{𝓦 = (𝓸𝓿𝓾)} psPllA (⨅≅ gfe llA≅A)
  where
   lA llA : ℑ (S{𝓤}{𝓤} 𝒦) → Algebra (𝓸𝓿𝓾) 𝑆
   lA i =  lift-alg (𝔄 (S{𝓤}{𝓤} 𝒦) i) (𝓸𝓿𝓾)
   llA i = lift-alg (lA i) (𝓸𝓿𝓾)

   slA : ∀ i → (lA i) ∈ S 𝒦
   slA i = siso (fst ∥ i ∥) lift-alg-≅

   psllA : ∀ i → (llA i) ∈ P (S 𝒦)
   psllA i = pbase{𝓤 = (𝓸𝓿𝓾)}{𝓦 = (𝓸𝓿𝓾)} (slA i)

   psPllA : ⨅ llA ∈ P (S 𝒦)
   psPllA = produ{𝓤 = (𝓸𝓿𝓾)}{𝓦 = (𝓸𝓿𝓾)} psllA

   llA≅A : ∀ i → (llA i) ≅ (𝔄 (S{𝓤}{𝓤} 𝒦) i)
   llA≅A i = Trans-≅ (llA i) (𝔄 (S{𝓤}{𝓤} 𝒦) i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

 -- So, since PS⊆SP, we see that that the product of all subalgebras of a class 𝒦 belongs to SP(𝒦).
 class-prod-s-∈-sp : hfunext(ov 𝓤)(ov 𝓤) → class-product (S 𝒦) ∈ S(P 𝒦)
 class-prod-s-∈-sp hfe = PS⊆SP{hfe = hfe} class-prod-s-∈-ps

\end{code}

----------------------------

[← UALib.Varieties.Varieties](UALib.Varieties.Varieties.html)
<span style="float:right;">[UALib.Varieties.Preservation →](UALib.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}


