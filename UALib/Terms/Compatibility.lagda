---
layout: default
title : UALib.Terms.Compatibility module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="term-compatibility-theorems">Term Compatibility Theorems</a>

This section presents the [UALib.Terms.Compatibility][] module of the [Agda Universal Algebra Library][].

In this module, we prove that every term commutes with every homomorphism and is compatible with every congruence.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)

open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Terms.Compatibility
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Terms.Operations{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

#### Homomorphisms commute with terms

We first prove an extensional version of this fact.

\begin{code}

comm-hom-term : {𝓤 𝓦 𝓧 : Universe} → funext 𝓥 𝓦
 →              {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
                (h : hom 𝑨 𝑩) (t : Term) (a : X → ∣ 𝑨 ∣)
               ------------------------------------------------------
 →              ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

comm-hom-term _ 𝑨 𝑩 h (generator x) a = 𝓇ℯ𝒻𝓁

comm-hom-term fe 𝑨 𝑩 h (node f args) a =
 ∣ h ∣((f ̂ 𝑨) λ i₁ → (args i₁ ̇ 𝑨) a)    ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a ) ⟩
 (f ̂ 𝑩)(λ i₁ →  ∣ h ∣((args i₁ ̇ 𝑨) a))  ≡⟨ ap (_ ̂ 𝑩)(fe (λ i₁ → comm-hom-term fe 𝑨 𝑩 h (args i₁) a))⟩
 (f ̂ 𝑩)(λ r → (args r ̇ 𝑩)(∣ h ∣ ∘ a))    ∎

\end{code}

Here is an intensional version.

\begin{code}

comm-hom-term-intensional : global-dfunext → {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
 →       (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) (t : Term)
         ------------------------------------------------------------------
 →         ∣ h ∣ ∘ (t ̇ 𝑨) ≡ (t ̇ 𝑩) ∘ (λ a → ∣ h ∣ ∘ a)

comm-hom-term-intensional gfe 𝑨 𝑩 h (generator x) = 𝓇ℯ𝒻𝓁

comm-hom-term-intensional gfe {X = X} 𝑨 𝑩 h (node f args) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ 𝑨) (λ i → (args i ̇ 𝑨) a))
      ≡ (λ a → (f ̂ 𝑩)(λ i → (args i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣
  γ = (λ a → ∣ h ∣ ((f ̂ 𝑨)(λ i → (args i ̇ 𝑨) a)))  ≡⟨ gfe (λ a → ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a )) ⟩
      (λ a → (f ̂ 𝑩)(λ i → ∣ h ∣ ((args i ̇ 𝑨) a)))  ≡⟨ ap (λ - → (λ a → (f ̂ 𝑩)(- a))) ih ⟩
      (λ a → (f ̂ 𝑩)(λ i → (args i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣  ∎
    where
     IH : (a : X → ∣ 𝑨 ∣)(i : ∥ 𝑆 ∥ f)
      →   (∣ h ∣ ∘ (args i ̇ 𝑨)) a ≡ ((args i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a
     IH a i = intensionality (comm-hom-term-intensional gfe 𝑨 𝑩 h (args i)) a

     ih : (λ a → (λ i → ∣ h ∣ ((args i ̇ 𝑨) a)))
           ≡ (λ a → (λ i → ((args i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a))
     ih = gfe λ a → gfe λ i → IH a i

\end{code}

#### Compatibility of terms and congruences

If t : Term, θ : Con 𝑨, then a θ b → t(a) θ t(b)). The statement and proof of this obvious but important fact may be formalized in Agda as follows.

\begin{code}

compatible-term : {𝓤 : Universe}{X : 𝓤 ̇}
                  (𝑨 : Algebra 𝓤 𝑆)(t : Term{𝓤}{X})(θ : Con 𝑨)
                 ------------------------------------------------
 →                compatible-fun (t ̇ 𝑨) ∣ θ ∣

compatible-term 𝑨 (generator x) θ p = p x

compatible-term 𝑨 (node f args) θ p = snd ∥ θ ∥ f λ x → (compatible-term 𝑨 (args x) θ) p

compatible-term' : {𝓤 : Universe} {X : 𝓤 ̇}
                   (𝑨 : Algebra 𝓤 𝑆)(t : Term{𝓤}{X}) (θ : Con 𝑨)
                 ---------------------------------------------------
 →                 compatible-fun (t ̇ 𝑨) ∣ θ ∣

compatible-term' 𝑨 (generator x) θ p = p x
compatible-term' 𝑨 (node f args) θ p = snd ∥ θ ∥ f λ x → (compatible-term' 𝑨 (args x) θ) p
\end{code}

--------------------------------------

[← UALib.Terms.Operations](UALib.Terms.Operations.html)
<span style="float:right;">[UALib.Subalgebras →](UALib.Subalgebras.html)</span>

{% include UALib.Links.md %}
