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

open Congruence

hom-kernel-is-compatible : {𝓤 𝓦 : Universe}
                           (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
 →                         compatible 𝑨 (KER-rel ∣ h ∣)

hom-kernel-is-compatible 𝑨 {𝑩} h f {𝒂}{𝒂'} Kerhab = γ
 where
  γ : ∣ h ∣ ((f ̂ 𝑨) 𝒂)    ≡ ∣ h ∣ ((f ̂ 𝑨) 𝒂')
  γ = ∣ h ∣ ((f ̂ 𝑨) 𝒂)    ≡⟨ ∥ h ∥ f 𝒂 ⟩
      (f ̂ 𝑩) (∣ h ∣ ∘ 𝒂)  ≡⟨ ap (λ - → (f ̂ 𝑩) -) (gfe λ x → Kerhab x) ⟩
      (f ̂ 𝑩) (∣ h ∣ ∘ 𝒂') ≡⟨ (∥ h ∥ f 𝒂')⁻¹ ⟩
      ∣ h ∣ ((f ̂ 𝑨) 𝒂')   ∎

hom-kernel-is-equivalence : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
 →                          IsEquivalence (KER-rel ∣ h ∣)

hom-kernel-is-equivalence 𝑨 h = map-kernel-IsEquivalence ∣ h ∣

\end{code}

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.

\begin{code}

kercon : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩) → Congruence 𝑨

kercon 𝑨 {𝑩} h = mkcon (KER-rel ∣ h ∣)(hom-kernel-is-compatible 𝑨 {𝑩} h)
                                     (hom-kernel-is-equivalence 𝑨 {𝑩} h)

\end{code}

From this congruence we construct the corresponding quotient.

\begin{code}

kerquo : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆

kerquo 𝑨{𝑩} h = 𝑨 ╱ (kercon 𝑨{𝑩} h)

-- NOTATION.
_[_]/ker_ : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
𝑨 [ 𝑩 ]/ker h = kerquo 𝑨 {𝑩} h

\end{code}

Given an algebra 𝑨 and a congruence θ, the canonical epimorphism from an algebra 𝑨 to 𝑨 ╱ θ is defined as follows.

\begin{code}

canonical-epi : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆) (θ : Congruence{𝓤}{𝓦} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
canonical-epi 𝑨 θ = cπ , cπ-is-hom , cπ-is-epic
 where
  cπ : ∣ 𝑨 ∣ → ∣ 𝑨 ╱ θ ∣
  cπ a = ⟦ a ⟧{⟨ θ ⟩}

  cπ-is-hom : is-homomorphism 𝑨 (𝑨 ╱ θ) cπ
  cπ-is-hom _ _ = 𝓇ℯ𝒻𝓁

  cπ-is-epic : Epic cπ
  cπ-is-epic (.(⟨ θ ⟩ a) , a , refl _) = Image_∋_.im a

\end{code}

To obtain the homomorphism part (or "hom reduct") of the canonical epimorphism, we apply `epi-to-hom`.

\begin{code}

canonical-hom : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆)(θ : Congruence{𝓤}{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
canonical-hom 𝑨 θ = epi-to-hom (𝑨 ╱ θ) (canonical-epi 𝑨 θ)

\end{code}

We combine the foregoing to define a function that takes 𝑆-algebras 𝑨 and 𝑩, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from 𝑨 onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of 𝑨 modulo the kernel of h.)

\begin{code}

πker : {𝓤 𝓦 : Universe}
       (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
       -------------------------------------------------
 →     epi 𝑨 (𝑨 [ 𝑩 ]/ker h)

πker 𝑨 {𝑩} h = canonical-epi 𝑨 (kercon 𝑨{𝑩} h)

\end{code}


The kernel of the canonical projection of 𝑨 onto 𝑨 / θ is equal to θ, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.

\begin{code}

ker-in-con : {𝓤 𝓦 : Universe}
             (𝑨 : Algebra 𝓤 𝑆)(θ : Congruence{𝓤}{𝓦} 𝑨)(x y : ∣ 𝑨 ∣ )
 →           ⟨ kercon 𝑨 {𝑨 ╱ θ} (canonical-hom 𝑨 θ) ⟩ x y  →  ⟨ θ ⟩ x y

ker-in-con 𝑨 θ x y hyp = ╱-refl 𝑨 {θ} hyp

\end{code}


--------------------------------------

[← UALib.Homomorphisms.Basic](UALib.Homomorphisms.Basic.html)
<span style="float:right;">[UALib.Homomorphisms.Noether →](UALib.Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}


<!--
θ is contained in the kernel of the canonical projection onto 𝑨 / θ.
con-in-ker : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆) (θ : Congruence{𝓤}{𝓦} 𝑨)
 → ∀ x y → (⟨ θ ⟩ x y) → (⟨ (kercon 𝑨 {𝑨 ╱ θ} (canonical-hom{𝓤}{𝓦} 𝑨 θ)) ⟩ x y)
con-in-ker 𝑨 θ x y hyp = γ
 where
  h : hom 𝑨 (𝑨 ╱ θ)
  h = canonical-hom 𝑨 θ

  κ : Congruence 𝑨
  κ = kercon 𝑨 {𝑨 ╱ θ} h

  γ : ⟦ x ⟧ {⟨ θ ⟩}≡ ⟦ y ⟧{⟨ θ ⟩}
  γ = {!!}
-->
