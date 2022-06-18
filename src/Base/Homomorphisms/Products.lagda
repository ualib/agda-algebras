---
layout: default
title : "Base.Homomorphisms.Products module (The Agda Universal Algebra Library)"
date : "2021-09-08"
author: "agda-algebras development team"
---

### <a id="products-of-homomorphisms">Products of Homomorphisms</a>

This is the [Base.Homomorphisms.Products] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Homomorphisms.Products {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -----------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ )
open import Level           using ( Level ;  _⊔_ ; suc )

open import Relation.Binary.PropositionalEquality using ( refl )

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
  using ()

-- Imports from the Agda Universal Algebras Library ----------------------
open import Overture using ( ∣_∣ ; ∥_∥)

open import Base.Algebras             {𝑆 = 𝑆}  using ( Algebra ; ⨅ )
open import Base.Homomorphisms.Basic  {𝑆 = 𝑆}  using ( hom ; epi )

private variable 𝓘 β : Level

\end{code}

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

\begin{code}

module _ {I : Type 𝓘}(ℬ : I → Algebra β 𝑆) where

 ⨅-hom-co :  funext 𝓘 β → {α : Level}(𝑨 : Algebra α 𝑆)
  →           (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)

 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶

\end{code}

The foregoing generalizes easily to the case in which the domain is also a product
of a family of algebras. That is, if we are given `𝒜 : I → Algebra α 𝑆` and
`ℬ : I → Algebra β 𝑆` (two families of `𝑆`-algebras), and
`𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can
construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

\begin{code}

 ⨅-hom :  funext 𝓘 β → {α : Level}(𝒜 : I → Algebra α 𝑆)
  →        (∀(i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)

 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 λ x → 𝒶 x i
\end{code}


#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra
onto one of its factors is a homomorphism.

\begin{code}

 ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors,
but so far the single-factor result has sufficed.

---------------------------------

<span style="float:left;">[← Base.Homomorphisms.Kernels](Base.Homomorphisms.Kernels.html)</span>
<span style="float:right;">[Base.Homomorphisms.Noether →](Base.Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}
