---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This section presents the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)

module Algebras.Products {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Algebras hiding (𝓞; 𝓥) public

\end{code}

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a \defn{product of} \ab 𝑆-\defn{algebras} is represented by the following type.

\begin{code}

module _ {𝓤 𝓘 : Universe}{I : 𝓘 ̇ } where

 ⨅ : (𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆

 ⨅ 𝒜 = (Π i ꞉ I , ∣ 𝒜 i ∣) ,            -- domain of the product algebra
       λ 𝑓 𝑎 i → (𝑓 ̂ 𝒜 i) λ x → 𝑎 x i   -- basic operations of the product algebra

\end{code}

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UALib][] whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

\begin{code}

 open algebra

 ⨅' : (𝒜 : I → algebra 𝓤 𝑆) → algebra (𝓘 ⊔ 𝓤) 𝑆

 ⨅' 𝒜 = record { univ = ∀ i → univ (𝒜 i) ;                 -- domain
                 op = λ 𝑓 𝑎 i → (op (𝒜 i)) 𝑓 λ x → 𝑎 x i } -- basic operations

\end{code}



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

\begin{code}

ov : Universe → Universe
ov 𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺

\end{code}



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) \_`.<sup>[1](Algebras.Products.html#fn1)</sup>

Later we will formally state and prove that, given an arbitrary class `𝒦` of algebras, the product of all subalgebras of algebras in the class belongs to the class  `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise. In fact, it is not immediately clear (to this author, at least) how to even express the product of an entire class of algebras as a dependent type. However, after some concerted thought and an honest reckoning with earlier failed attempts, the right type reveals itself.<sup>[2](Algebras.Products.html#fn2)</sup>

The solution is the \af{class-product} type whose construction is the main goal of this section. To begin, we need a type that will serve to index the class, as well as the product of its members.

\begin{code}

module class-products {𝓤 : Universe} (𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) where

 ℑ : ov 𝓤 ̇
 ℑ = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦)

\end{code}

Taking the product over the index type ℑ requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

\begin{code}

 𝔄 : ℑ → Algebra 𝓤 𝑆
 𝔄 = λ (i : ℑ) → ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

 class-product : Algebra (ov 𝓤) 𝑆
 class-product = ⨅ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> The underscore is merely a placeholder for the universe of the predicate type and needn't concern us here.</span>

<sup>2</sup><span class="footnote" id="fn2"> This was our own experience, but readers are encouraged to try to derive for themselves a type that represents the product of all algebras satisfying a given predicate. It is a good exercise. (*Hint*. The answer is not `Π 𝒦`. Although the latter is a valid type, it represnts not the product of algebras in `𝒦`, but rather the assertion that every algebra of type `Algebra 𝓤 𝑆` belongs to `𝒦`.)</span>

<br>
<br>

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

<!--

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

 class-product' : Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆
 class-product' 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣))) → ∣ i ∣

-->

