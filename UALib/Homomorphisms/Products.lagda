---
layout: default
title : UALib.Homomorphisms.Products module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="homomorphisms-and-products">Homomorphisms and Products</a>

This section describes the [UALib.Homomorphisms.Products][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext; dfunext)

module UALib.Homomorphisms.Products {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Homomorphisms.Noether{𝑆 = 𝑆}{gfe} public

\end{code}

#### <a id="product-homomorphisms">Product homomorphisms</a>

\begin{code}

⨅-hom-co : {𝓠 𝓤 𝓘 : Universe} → dfunext 𝓘 𝓤
 →          (𝑨 : Algebra 𝓠 𝑆){I : 𝓘 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →          (∀ i → hom 𝑨 (ℬ i))
            -------------------
 →          hom 𝑨 (⨅ ℬ)

⨅-hom-co dfe 𝑨 {I}{ℬ} homs = ϕ , ϕhom
 where
  ϕ : ∣ 𝑨 ∣ → ∣ ⨅ ℬ ∣
  ϕ a = λ i → ∣ homs i ∣ a

  ϕhom : is-homomorphism 𝑨 (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒂 = dfe λ i → ∥ homs i ∥ 𝑓 (λ x → 𝒂 x)


⨅-hom : {𝓠 𝓤 𝓘 : Universe} → dfunext 𝓘 𝓤
 →       {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
 →       ((i : I) → hom (𝒜 i)(ℬ i))
         ---------------------------
 →       hom (⨅ 𝒜) (⨅ ℬ)

⨅-hom dfe {I}{𝒜}{ℬ} homs = ϕ , ϕhom
 where
  ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
  ϕ = λ x i → ∣ homs i ∣ (x i)

  ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒂 = dfe λ i → ∥ homs i ∥ 𝑓 (λ x → 𝒂 x i)

\end{code}



#### <a id="projection-homomorphisms">Projection homomorphisms</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

\begin{code}

⨅-projection-hom : {𝓤 𝓘 : Universe}
                   {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓤 𝑆}
                   --------------------------------
 →                  (i : I) → hom (⨅ 𝒜) (𝒜 i)

⨅-projection-hom {𝓤}{𝓘}{I}{𝒜} i = ϕi , ϕihom
 where
  ϕi : ∣ ⨅ 𝒜 ∣ → ∣ 𝒜 i ∣
  ϕi = λ x → x i

  ϕihom : is-homomorphism (⨅ 𝒜) (𝒜 i) ϕi
  ϕihom 𝑓 𝒂 = ϕi ((𝑓 ̂ ⨅ 𝒜) 𝒂) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             ((𝑓 ̂ ⨅ 𝒜) 𝒂) i ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             (𝑓 ̂ 𝒜 i) (λ x → 𝒂 x i) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             (𝑓 ̂ 𝒜 i) (λ x → ϕi (𝒂 x)) ∎

\end{code}

(Of course, we could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.)

--------------------------------------

[← UALib.homomorphisms.Noether](UALib.Homomorphisms.Noether.html)
<span style="float:right;">[UALib.Homomorphisms.Isomorphisms →](UALib.Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
