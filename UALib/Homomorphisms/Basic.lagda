---
layout: default
title : UALib.Homomorphisms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

[UALib.Homomorphisms ↑](UALib.Homomorphisms.html)

### <a id="basic-definitions">Basic Definitions</a>

This section describes the [UALib.Homomorphisms.Basic] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)

module UALib.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import UALib.Relations.Congruences{𝑆 = 𝑆} public
open import UALib.Prelude.Preliminaries using (_≡⟨_⟩_; _∎) public

compatible-op-map : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)
                    (𝑓 : ∣ 𝑆 ∣)(g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇

compatible-op-map 𝑨 𝑩 𝑓 g = ∀ 𝒂 → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)
 --(infered type  𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)

op_interpreted-in_and_commutes-with : {𝓠 𝓤 : Universe}
  (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓠 𝑆) (𝑩 : Algebra 𝓤 𝑆)
  (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g = compatible-op-map 𝑨 𝑩 𝑓 g

is-homomorphism : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
is-homomorphism 𝑨 𝑩 g = ∀ (𝑓 : ∣ 𝑆 ∣) → compatible-op-map 𝑨 𝑩 𝑓 g

hom : {𝓠 𝓤 : Universe} → Algebra 𝓠 𝑆 → Algebra 𝓤 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

\end{code}

#### Examples

\begin{code}

𝒾𝒹 : {𝓤 : Universe} (A : Algebra 𝓤 𝑆) → hom A A
𝒾𝒹 _ = (λ x → x) , λ _ _ → 𝓇ℯ𝒻𝓁

id-is-hom : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → is-homomorphism 𝑨 𝑨 (𝑖𝑑 ∣ 𝑨 ∣)
id-is-hom = λ _ _ → refl _

--Equalizers of functions
𝑬 : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}(g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}(g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓦
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x

𝑬𝑯-is-closed : {𝓤 𝓦 : Universe} → funext 𝓥 𝓦
 →              {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
                (g h : hom 𝑨 𝑩) {𝑓 : ∣ 𝑆 ∣ } (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →              ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
               --------------------------------------------------
 →               ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑨}{𝑩} g h {𝑓} 𝒂 p =
                  (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)) ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
                  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
                  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
                  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)   ∎
\end{code}

--------------------------------------

{% include UALib.Links.md %}
