---
layout: default
title : UALib.Homomorphisms.Kernels module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="kernels-of-homomorphisms">Kernels of Homomorphisms</a>

This section presents the [UALib.Homomorphisms.Kernels][] module of the [Agda Universal Algebra Library][].

The kernel of a homomorphism is a congruence and conversely for every congruence θ, there exists a homomorphism with kernel θ.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)

module UALib.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} {gfe : global-dfunext} where

open import UALib.Homomorphisms.Basic{𝑆 = 𝑆} public

module _ {𝓤 𝓦 : Universe} where

 open Congruence

 hom-kernel-is-compatible : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
  →                         compatible 𝑨 (KER-rel ∣ h ∣)

 hom-kernel-is-compatible 𝑨 {𝑩} h f {𝒂}{𝒂'} Kerhab = γ
  where
   γ : ∣ h ∣ ((f ̂ 𝑨) 𝒂)     ≡ ∣ h ∣ ((f ̂ 𝑨) 𝒂')
   γ = ∣ h ∣ ((f ̂ 𝑨) 𝒂)     ≡⟨ ∥ h ∥ f 𝒂 ⟩
       (f ̂ 𝑩) (∣ h ∣ ∘ 𝒂)   ≡⟨ ap (λ - → (f ̂ 𝑩) -) (gfe λ x → Kerhab x) ⟩
       (f ̂ 𝑩) (∣ h ∣ ∘ 𝒂')  ≡⟨ (∥ h ∥ f 𝒂')⁻¹ ⟩
       ∣ h ∣ ((f ̂ 𝑨) 𝒂')    ∎

 hom-kernel-is-equivalence : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
  →                          IsEquivalence (KER-rel ∣ h ∣)

 hom-kernel-is-equivalence 𝑨 h = map-kernel-IsEquivalence ∣ h ∣

\end{code}

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `hom-kernel-congruence`, but since we will use it often we also give it a short alias---`kercon`.

\begin{code}

 kercon -- (alias)
  hom-kernel-congruence : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
  →                      Congruence 𝑨

 hom-kernel-congruence 𝑨 {𝑩} h = mkcon (KER-rel ∣ h ∣)
                                        (hom-kernel-is-compatible 𝑨 {𝑩} h)
                                         (hom-kernel-is-equivalence 𝑨 {𝑩} h)
 kercon = hom-kernel-congruence -- (alias)

 quotient-by-hom-kernel : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}
                          (h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆

 quotient-by-hom-kernel 𝑨{𝑩} h = 𝑨 ╱ (hom-kernel-congruence 𝑨{𝑩} h)

 -- NOTATION.
 _[_]/ker_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
 𝑨 [ 𝑩 ]/ker h = quotient-by-hom-kernel 𝑨 {𝑩} h


epi : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
epi 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g × Epic g

epi-to-hom : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}
 →           epi 𝑨 𝑩 → hom 𝑨 𝑩
epi-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

module _ {𝓤 𝓦 : Universe} where

 open Congruence

 canonical-projection : (𝑨 : Algebra 𝓤 𝑆) (θ : Congruence{𝓤}{𝓦} 𝑨)
                     -----------------------------------------------
   →                     epi 𝑨 (𝑨 ╱ θ)

 canonical-projection 𝑨 θ = cπ , cπ-is-hom , cπ-is-epic
   where
    cπ : ∣ 𝑨 ∣ → ∣ 𝑨 ╱ θ ∣
    cπ a = ⟦ a ⟧  -- ([ a ] (KER-rel ∣ h ∣)) , ?

    cπ-is-hom : is-homomorphism 𝑨 (𝑨 ╱ θ) cπ
    cπ-is-hom 𝑓 𝒂 = γ
     where
      γ : cπ ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ (𝑨 ╱ θ)) (λ x → cπ (𝒂 x))
      γ = cπ ((𝑓 ̂ 𝑨) 𝒂) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ⟦ (𝑓 ̂ 𝑨) 𝒂 ⟧ ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          (𝑓 ̂ (𝑨 ╱ θ)) (λ x → ⟦ 𝒂 x ⟧) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          (𝑓 ̂ (𝑨 ╱ θ)) (λ x → cπ (𝒂 x)) ∎

    cπ-is-epic : Epic cπ
    cπ-is-epic (.(⟨ θ ⟩ a) , a , refl _) = Image_∋_.im a

πᵏ -- alias
 kernel-quotient-projection : {𝓤 𝓦 : Universe} -- (pe : propext 𝓦)
                              (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}
                              (h : hom 𝑨 𝑩)
                             -----------------------------------
 →                             epi 𝑨 (𝑨 [ 𝑩 ]/ker h)

kernel-quotient-projection 𝑨 {𝑩} h = canonical-projection 𝑨 (kercon 𝑨{𝑩} h)

πᵏ = kernel-quotient-projection
\end{code}


--------------------------------------

[← UALib.Homomorphisms.Basic](UALib.Homomorphisms.Basic.html)
<span style="float:right;">[UALib.Homomorphisms.Noether →](UALib.Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}
