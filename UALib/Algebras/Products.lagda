---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="product-algebra-types">Product Algebra Types</a>

This section presents the [UALib.Algebras.Products][] module of the [Agda Universal Algebra Library][].

We define products of algebras for both the Sigma type representation (the one we use most often) and the record type representation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Algebras.Products where


open import UALib.Algebras.Algebras public


module _ {𝓤 : Universe}{𝑆 : Signature 𝓞 𝓥}  where

 -- product for algebras of sigma type
 ⨅ : {𝓘 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆
 ⨅ {𝓘}{I} 𝒜 =
  ((i : I) → ∣ 𝒜 i ∣) , λ(f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)(i : I) → (f ̂ 𝒜 i) λ{x → 𝒂 x i}

 ⊓ : {I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra 𝓤 𝑆
 ⊓ = ⨅ {𝓤}

 open algebra

 -- product for algebras of record type
 ⨅' : {𝓘 : Universe}{I : 𝓘 ̇ }(𝒜 : I → algebra 𝓤 𝑆) → algebra (𝓘 ⊔ 𝓤) 𝑆
 ⨅' {𝓘}{I} 𝒜 = record
                  { univ = (i : I) → univ (𝒜 i)
                  ; op = λ(f : ∣ 𝑆 ∣)
                          (𝒂 : ∥ 𝑆 ∥ f → (j : I) → univ(𝒜 j))
                          (i : I) → ((op (𝒜 i)) f)
                          λ{x → 𝒂 x i}
                  }


\end{code}

-----------------------

{% include UALib.Links.md %}
