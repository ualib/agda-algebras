---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="product-algebra-types">Product Algebra Types</a>

This section presents the [UALib.Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)

module UALib.Algebras.Products {𝑆 : Signature 𝓞 𝓥} where

open import UALib.Algebras.Algebras hiding (𝓞; 𝓥) public

\end{code}

We define products of algebras for both the Sigma type representation (the one we use most often) and the record type representation.

\begin{code}

-- product for algebras of sigma type
⨅ : {𝓤 𝓘 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆
⨅ {𝓤}{𝓘}{I} 𝒜 =
 ((i : I) → ∣ 𝒜 i ∣) , λ(f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)(i : I) → (f ̂ 𝒜 i) λ{x → 𝒂 x i}

open algebra

-- product for algebras of record type
⨅' : {𝓤 𝓘 : Universe}{I : 𝓘 ̇ }(𝒜 : I → algebra 𝓤 𝑆) → algebra (𝓘 ⊔ 𝓤) 𝑆
⨅' {𝓤}{𝓘}{I} 𝒜 = record
                   { univ = (i : I) → univ (𝒜 i)
                   ; op = λ(f : ∣ 𝑆 ∣)
                           (𝒂 : ∥ 𝑆 ∥ f → (j : I) → univ(𝒜 j))
                           (i : I) → ((op (𝒜 i)) f)
                           λ{x → 𝒂 x i}
                   }

\end{code}


#### <a id="notation">Notation</a>

Before we define the type of congruences, we define some syntactic sugar that will be used from now on throughout the [UALib][]. The type `Algebra 𝓤 𝑆` itself has a type; it is `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`. This type appears so often in the UALib that we will define the following shorthand for its universe level. 

\begin{code}

ov : Universe → Universe
ov 𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺

\end{code}

We can now write, e.g., `Algebra 𝓤 𝑆 : ov 𝓤 ̇` in place of the laborious `Algebra 𝓤 𝑆 : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`.

\end{code}


#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself. We present this "class product" type here.

First, we need a type that will serve to index the class, as well as the product of its members.

\begin{code}

ℑ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} →  Pred (Algebra 𝓤 𝑆)(ov 𝓤) → (𝓧 ⊔ ov 𝓤) ̇

ℑ {𝓤}{𝓧}{X} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)

\end{code}

Notice that the second component of this dependent pair type is `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.  In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`.  However, we realized that adding a mapping of type `X → ∣ 𝑨 ∣` is quite useful.  The reason for this will become clear later; for now, suffice it to say that a map X → ∣ 𝑨 ∣ may be viewed as a context and we want to keep the context completely general.  Adding the map to the index set ℑ accomplishes this.

Taking the product over the index type ℑ requires a function that takes an index (i : ℑ) and returns the corresponding algebra.

\begin{code}

𝔄 : {𝓤 : Universe}{𝓧 : Universe}{X : 𝓧 ̇}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) → ℑ{𝓤}{𝓧}{X} 𝒦 → Algebra 𝓤 𝑆

𝔄 𝒦 = λ (i : (ℑ 𝒦)) → ∣ i ∣
\end{code}

Finally, we represent the product of all members of 𝒦 as follows.

\begin{code}

class-product : {𝓤 : Universe}{𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆

class-product {𝓤}{𝓧}{X} 𝒦 = ⨅ ( 𝔄{𝓤}{𝓧}{X} 𝒦 )

\end{code}

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

\begin{code}

class-product' : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆
class-product'{𝓤}{𝓧}{X} 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣))) → ∣ i ∣

\end{code}

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the pair `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is obviously `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← UALib.Algebras.Algebras](UALib.Algebras.Algebras.html)
<span style="float:right;">[UALib.Algebras.Lifts →](UALib.Algebras.Lifts.html)</span>

{% include UALib.Links.md %}
