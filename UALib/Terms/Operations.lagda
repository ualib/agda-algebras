---
layout: default
title : UALib.Terms.Operations module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="term-operation-types">Term Operation Types</a>

This section presents the [UALib.Terms.Operations][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)

open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Terms.Operations
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Terms.Free{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

When we interpret a term in an algebra we call the resulting function a **term operation**.  Given a term `𝑝 : Term` and an algebra 𝑨, we denote by `𝑝 ̇ 𝑨` the **interpretation** of 𝑝 in 𝑨.  This is defined inductively as follows:

1. if 𝑝 is `x : X` (a variable) and if `𝒂 : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then define `(𝑝 ̇ 𝑨) 𝒂 = 𝒂 x`;
2. if 𝑝 = 𝑓 𝒔, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol and `𝒔 : ∥ 𝑆 ∥ f → 𝑻 X` is an (`∥ 𝑆 ∥ f`)-tuple of terms and
    `𝒂 : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define `(𝑝 ̇ 𝑨) 𝒂 = ((𝑓 𝒔) ̇ 𝑨) 𝒂 = (𝑓 ̂ 𝑨) λ i → ((𝒔 i) ̇ 𝑨) 𝒂``

In the [Agda UALib][] term interpretation is defined as follows.

\begin{code}

_̇_ : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ } → Term{𝓧}{X} → (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
((generator x) ̇ 𝑨) 𝒂 = 𝒂 x
((node f args) ̇ 𝑨) 𝒂 = (f ̂ 𝑨) λ i → (args i ̇ 𝑨) 𝒂
\end{code}

Observe that intepretation of a term is the same as `free-lift` (modulo argument order).

\begin{code}

free-lift-interpretation : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }
                           (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)(p : Term)
 →                         (p ̇ 𝑨) h ≡ free-lift 𝑨 h p

free-lift-interpretation 𝑨 h (generator x) = 𝓇ℯ𝒻𝓁
free-lift-interpretation 𝑨 h (node f args) = ap (f ̂ 𝑨) (gfe λ i → free-lift-interpretation 𝑨 h (args i))
lift-hom-interpretation : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }
                          (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)(p : Term)
 →                        (p ̇ 𝑨) h ≡ ∣ lift-hom 𝑨 h ∣ p

lift-hom-interpretation = free-lift-interpretation

\end{code}

Here we want (𝒕 : X → ∣ 𝑻(X) ∣) → ((p ̇ 𝑻(X)) 𝒕) ≡ p 𝒕... but what is (𝑝 ̇ 𝑻(X)) 𝒕 ?

By definition, it depends on the form of 𝑝 as follows:

* if 𝑝 = (generator x), then (𝑝 ̇ 𝑻(X)) 𝒕 = ((generator x) ̇ 𝑻(X)) 𝒕 = 𝒕 x

* if 𝑝 = (node f args), then (𝑝 ̇ 𝑻(X)) 𝒕 = ((node f args) ̇ 𝑻(X)) 𝒕 = (f ̂ 𝑻(X)) λ i → (args i ̇ 𝑻(X)) 𝒕

Let h : hom 𝑻 𝑨. Then by comm-hom-term, ∣ h ∣ (p ̇ 𝑻(X)) 𝒕 = (p ̇ 𝑨) ∣ h ∣ ∘ 𝒕

* if p = (generator x), then

   ∣ h ∣ p ≡ ∣ h ∣ (generator x)
          ≡ λ 𝒕 → 𝒕 x) (where 𝒕 : X → ∣ 𝑻(X) ∣ )
          ≡ (λ 𝒕 → (∣ h ∣ ∘ 𝒕) x)

   ∣ h ∣ p ≡ ∣ h ∣ (λ 𝒕 → 𝒕 x) (where 𝒕 : X → ∣ 𝑻(X) ∣ )
          ≡ (λ 𝒕 → (∣ h ∣ ∘ 𝒕) x)

* if p = (node f args), then

   ∣ h ∣ p ≡ ∣ h ∣  (p ̇ 𝑻(X)) 𝒕 = ((node f args) ̇ 𝑻(X)) 𝒕 = (f ̂ 𝑻(X)) λ i → (args i ̇ 𝑻(X)) 𝒕

We claim that if p : ∣ 𝑻(X) ∣ then there exists 𝓅 : ∣ 𝑻(X) ∣ and 𝒕 : X → ∣ 𝑻(X) ∣ such that p ≡ (𝓅 ̇ 𝑻(X)) 𝒕. We prove this fact as follows.

\begin{code}
term-op-interp1 : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term)
 →                node f args ≡ (f ̂ 𝑻 X) args

term-op-interp1 = λ f args → 𝓇ℯ𝒻𝓁

term-op-interp2 : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term{𝓧}{X}}
 →                a1 ≡ a2  →  node f a1 ≡ node f a2

term-op-interp2 f a1≡a2 = ap (node f) a1≡a2

term-op-interp3 : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term}
 →                a1 ≡ a2  →  node f a1 ≡ (f ̂ 𝑻 X) a2

term-op-interp3 f {a1}{a2} a1a2 = (term-op-interp2 f a1a2) ∙ (term-op-interp1 f a2)

term-gen : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣)
 →         Σ 𝓅 ꞉ ∣ 𝑻 X ∣ , p ≡ (𝓅 ̇ 𝑻 X) generator

term-gen (generator x) = (generator x) , 𝓇ℯ𝒻𝓁
term-gen (node f args) = node f (λ i → ∣ term-gen (args i) ∣) ,
                                term-op-interp3 f (gfe λ i → ∥ term-gen (args i) ∥)

tg : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣) → Σ 𝓅 ꞉ ∣ 𝑻 X ∣ , p ≡ (𝓅 ̇ 𝑻 X) generator
tg p = term-gen p

term-equality : {𝓧 : Universe}{X : 𝓧 ̇}(p q : ∣ 𝑻 X ∣)
 →              p ≡ q → (∀ t → (p ̇ 𝑻 X) t ≡ (q ̇ 𝑻 X) t)
term-equality p q (refl _) _ = refl _

term-equality' : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓤 𝑆}(p q : ∣ 𝑻 X ∣)
 →              p ≡ q → (∀ 𝒂 → (p ̇ 𝑨) 𝒂 ≡ (q ̇ 𝑨) 𝒂)
term-equality' p q (refl _) _ = refl _

term-gen-agreement : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣)
 →               (p ̇ 𝑻 X) generator ≡ (∣ term-gen p ∣ ̇ 𝑻 X) generator
term-gen-agreement (generator x) = 𝓇ℯ𝒻𝓁
term-gen-agreement {𝓧}{X}(node f args) = ap (f ̂ 𝑻 X) (gfe λ x → term-gen-agreement (args x))

term-agreement : {𝓧 : Universe}{X : 𝓧 ̇}(p : ∣ 𝑻 X ∣)
 →            p ≡ (p ̇ 𝑻 X) generator
term-agreement p = snd (term-gen p) ∙ (term-gen-agreement p)⁻¹
\end{code}

-----------------------------------

#### <a id="interpretation-of-terms-in-product-algebras>Interpretation of terms in product algebras</a>

\begin{code}
interp-prod : {𝓧 𝓤 : Universe} → funext 𝓥 𝓤
 →            {X : 𝓧 ̇}(p : Term){I : 𝓤 ̇}
              (𝒜 : I → Algebra 𝓤 𝑆)(x : X → ∀ i → ∣ (𝒜 i) ∣)
              --------------------------------------------------------
 →            (p ̇ (⨅ 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

interp-prod _ (generator x₁) 𝒜 x = 𝓇ℯ𝒻𝓁

interp-prod fe (node f t) 𝒜 x =
 let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
  (f ̂ ⨅ 𝒜)(λ x₁ → (t x₁ ̇ ⨅ 𝒜) x)                             ≡⟨ ap (f ̂ ⨅ 𝒜)(fe IH) ⟩
  (f ̂ ⨅ 𝒜)(λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁)(λ j₁ → x j₁ i₁)))     ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
  (λ i₁ → (f ̂ 𝒜 i₁) (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))   ∎

interp-prod2 : {𝓤 𝓧 : Universe} → global-dfunext
 →             {X : 𝓧 ̇}(p : Term){I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆)
               ----------------------------------------------------------------------
 →             (p ̇ ⨅ 𝒜) ≡ λ(args : X → ∣ ⨅ 𝒜 ∣) → (λ i → (p ̇ 𝒜 i)(λ x → args x i))

interp-prod2 _ (generator x₁) 𝒜 = 𝓇ℯ𝒻𝓁

interp-prod2 gfe {X} (node f t) 𝒜 = gfe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
  let IH = λ x → interp-prod gfe (t x) 𝒜  in
  let tA = λ z → t z ̇ ⨅ 𝒜 in
   (f ̂ ⨅ 𝒜)(λ s → tA s tup)                          ≡⟨ ap (f ̂ ⨅ 𝒜)(gfe λ x → IH x tup) ⟩
   (f ̂ ⨅ 𝒜)(λ s → λ j → (t s ̇ 𝒜 j)(λ ℓ → tup ℓ j))  ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ ℓ → tup ℓ i))) ∎

\end{code}

--------------------------------------

[← UALib.Terms.Free](UALib.Terms.Free.html)
<span style="float:right;">[UALib.Terms.Compatibility →](UALib.Terms.Compatibility.html)</span>

{% include UALib.Links.md %}
