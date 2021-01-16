---
layout: default
title : UALib.Varieties.ModelTheory module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="types-for-theories-and-models">Types for Theories and Models</a>

This section presents the [UALib.Varieties.ModelTheory][] module of the [Agda Universal Algebra Library][].

We define the binary "models" relation ⊧, with infix so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊧ p ≋ q`, relating algebras (or classes of algebras) to the identities that they satisfy. We also prove a few useful facts about ⊧.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Varieties.ModelTheory
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Subalgebras.Subalgebras{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

#### Modeling

\begin{code}

_⊧_≈_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Algebra 𝓤 𝑆 → Term{𝓧}{X} → Term → 𝓤 ⊔ 𝓧 ̇
𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →      Term{𝓧}{X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇
_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}

#### Equational theories and classes

\begin{code}

Th : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →   Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

MOD : (𝓤 𝓧 : Universe)(X : 𝓧 ̇) → Pred (Term{𝓧}{X} × Term{𝓧}{X}) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)
MOD 𝓤 𝓧 X ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

Mod : {𝓤 𝓧 : Universe}(X : 𝓧 ̇) → Pred (Term{𝓧}{X} × Term{𝓧}{X}) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)
Mod X ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

mod : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Term{𝓧}{X} × Term{𝓧}{X}) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)
mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

\end{code}


#### ⊧-≅ compatibility

The binary relation ⊧ would be of little use to us if it were not an algebraic invariant.

\begin{code}

⊧-≅
 ⊧-transport : {𝓠 𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
                 (p q : Term{𝓧}{X}) → (𝑨 ⊧ p ≈ q) → (𝑨 ≅ 𝑩) → 𝑩 ⊧ p ≈ q
⊧-transport {𝓠}{𝓤}{𝓧}{X}{𝑨}{𝑩} p q Apq (f , g , f∼g , g∼f) = γ
 where
  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ x →
      (p ̇ 𝑩) x ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      (p ̇ 𝑩) (∣ 𝒾𝒹 𝑩 ∣ ∘ x) ≡⟨ ap (λ - → (p ̇ 𝑩) -) (gfe λ i → ((f∼g)(x i))⁻¹)  ⟩
      (p ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘ x) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 f p (∣ g ∣ ∘ x))⁻¹ ⟩
      ∣ f ∣ ((p ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ ap (λ - → ∣ f ∣ (- (∣ g ∣ ∘ x))) Apq ⟩
      ∣ f ∣ ((q ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ comm-hom-term gfe 𝑨 𝑩 f q (∣ g ∣ ∘ x) ⟩
      (q ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘  x) ≡⟨ ap (λ - → (q ̇ 𝑩) -) (gfe λ i → (f∼g) (x i)) ⟩
      (q ̇ 𝑩) x ∎

⊧-≅ = ⊧-transport -- (alias)

\end{code}

#### ⊧-lift compatibility

The ⊧ relation is also compatible with the lift operation.

\begin{code}

lift-alg-⊧ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
       (𝑨 : Algebra 𝓤 𝑆)(p q : Term{𝓧}{X})
  →    𝑨 ⊧ p ≈ q → (lift-alg 𝑨 𝓦) ⊧ p ≈ q
lift-alg-⊧ 𝑨 p q Apq = ⊧-≅ p q Apq lift-alg-≅

lower-alg-⊧ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)
                             (p q : Term{𝓧}{X})
 →                           lift-alg 𝑨 𝓦 ⊧ p ≈ q → 𝑨 ⊧ p ≈ q
lower-alg-⊧ {𝓤}{𝓦}{𝓧}{X} 𝑨 p q lApq = ⊧-≅ p q lApq (sym-≅ lift-alg-≅)

lower-class : {𝓤 𝓦 : Universe} → Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) → Pred (Algebra 𝓤 𝑆)(OV (𝓤 ⊔ 𝓦))
lower-class {𝓤}{𝓦}𝒦 = λ (𝑨 : Algebra 𝓤 𝑆) → lift-alg 𝑨 𝓦 ∈ 𝒦

\end{code}

---------------------------------

[↑ UALib.Varieties](UALib.Varieties.html)
<span style="float:right;">[UALib.Varieties.EquationalLogic →](UALib.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}

