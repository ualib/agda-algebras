---
layout: default
title : UALib.Terms.Operations module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="term-operations">Term Operations</a>

This section presents the [UALib.Terms.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a particular algebra, and we prove some compatibility properties of term operations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)

module UALib.Terms.Operations {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Terms.Basic{𝑆 = 𝑆}{gfe} renaming (generator to ℊ) public

\end{code}

**Notation**. In the line above, we renamed for notational convenience the `generator` constructor of the `Term` type, so from now on we use `ℊ` in place of `generator`.

When we interpret a term in an algebra we call the resulting function a **term operation**.  Given a term `𝑝` and an algebra `𝑨`, we denote by `𝑝 ̇ 𝑨` the **interpretation** of `𝑝` in `𝑨`.  This is defined inductively as follows.

1. If `𝑝` is a variable symbol `x : X` and if `𝒂 : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then `(𝑝 ̇ 𝑨) 𝒂 := 𝒂 x`.

2. If `𝑝 = 𝑓 𝒕`, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol, if `𝒕 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of terms, and if `𝒂 : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define `(𝑝 ̇ 𝑨) 𝒂 = (𝑓 𝒕 ̇ 𝑨) 𝒂 := (𝑓 ̂ 𝑨) λ i → (𝒕 i ̇ 𝑨) 𝒂`.

Thus the interpretation of a term is defined by induction on the structure of the term, and the definition is formally implemented in the [UALib][] as follows.

\begin{code}

_̇_ : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ } → Term X → (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

((ℊ x) ̇ 𝑨) 𝒂 = 𝒂 x

((node 𝑓 𝒕) ̇ 𝑨) 𝒂 = (𝑓 ̂ 𝑨) λ i → (𝒕 i ̇ 𝑨) 𝒂

\end{code}

It turns out that the intepretation of a term is the same as the `free-lift` (modulo argument order).

\begin{code}

free-lift-interp : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }
                   (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)(p : Term X)
 →                 (p ̇ 𝑨) h ≡ (free-lift 𝑨 h) p

free-lift-interp 𝑨 h (ℊ x) = 𝓇ℯ𝒻𝓁
free-lift-interp 𝑨 h (node f 𝒕) = ap (f ̂ 𝑨) (gfe λ i → free-lift-interp 𝑨 h (𝒕 i))

\end{code}

What if the algebra 𝑨 in question happens to be `𝑻 X` itself?   Assume the map `h : X → ∣ 𝑻 X ∣` is the identity. We expect that `∀ 𝒔 → (p ̇ 𝑻 X) 𝒔  ≡  p 𝒔`. But what is `(𝑝 ̇ 𝑻 X) 𝒔` exactly?

By definition, it depends on the form of 𝑝 as follows:

* if `𝑝 = ℊ x`, then `(𝑝 ̇ 𝑻 X) 𝒔 := (ℊ x ̇ 𝑻 X) 𝒔 ≡ 𝒔 x`

* if `𝑝 = node 𝑓 𝒕`, then `(𝑝 ̇ 𝑻 X) 𝒔 := (node 𝑓 𝒕 ̇ 𝑻 X) 𝒔 = (𝑓 ̂ 𝑻 X) λ i → (𝒕 i ̇ 𝑻 X) 𝒔`

Now, assume `ϕ : hom 𝑻 𝑨`. Then by `comm-hom-term`, we have `∣ ϕ ∣ (p ̇ 𝑻 X) 𝒔 = (p ̇ 𝑨) ∣ ϕ ∣ ∘ 𝒔`.

* if `p = ℊ x`, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x)
          ≡ ∣ ϕ ∣ (λ h → h x)  (where h : X → ∣ 𝑻(X) ∣ )
          ≡ λ h → (∣ ϕ ∣ ∘ h) x

* if `p = node 𝑓 𝒕`, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (p ̇ 𝑻 X) 𝒔 = (node 𝑓 𝒕 ̇ 𝑻 X) 𝒔 = (𝑓 ̂ 𝑻 X) λ i → (𝒕 i ̇ 𝑻 X) 𝒔

We claim that for all `p : Term X` there exists `q : Term X` and `h : X → ∣ 𝑻 X ∣` such that `p ≡ (q ̇ 𝑻 X) h`. We prove this fact as follows.

\begin{code}

module _ {𝓧 : Universe}{X : 𝓧 ̇} where

 term-interp : (𝑓 : ∣ 𝑆 ∣){𝒔 𝒕 : ∥ 𝑆 ∥ 𝑓 → Term X} → 𝒔 ≡ 𝒕 → node 𝑓 𝒔 ≡ (𝑓 ̂ 𝑻 X) 𝒕
 term-interp 𝑓 {𝒔}{𝒕} st = ap (node 𝑓) st


 term-gen : (p : ∣ 𝑻 X ∣) → Σ q ꞉ ∣ 𝑻 X ∣ , p ≡ (q ̇ 𝑻 X) ℊ

 term-gen (ℊ x) = (ℊ x) , 𝓇ℯ𝒻𝓁

 term-gen (node 𝑓 𝒕) = node 𝑓 (λ i → ∣ term-gen (𝒕 i) ∣) , term-interp 𝑓 (gfe λ i → ∥ term-gen (𝒕 i) ∥)


 term-gen-agreement : (p : ∣ 𝑻 X ∣) → (p ̇ 𝑻 X) ℊ ≡ (∣ term-gen p ∣ ̇ 𝑻 X) ℊ

 term-gen-agreement (ℊ x) = 𝓇ℯ𝒻𝓁

 term-gen-agreement (node f 𝒕) = ap (f ̂ 𝑻 X) (gfe λ x → term-gen-agreement (𝒕 x))

 term-agreement : (p : ∣ 𝑻 X ∣) → p ≡ (p ̇ 𝑻 X) ℊ
 term-agreement p = snd (term-gen p) ∙ (term-gen-agreement p)⁻¹

\end{code}



#### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇ } where

 interp-prod : {𝓦 : Universe}(p : Term X){I : 𝓦 ̇}
               (𝒜 : I → Algebra 𝓤 𝑆)(x : X → ∀ i → ∣ (𝒜 i) ∣)
               ------------------------------------------------
  →            (p ̇ (⨅ 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

 interp-prod (ℊ x₁) 𝒜 x = 𝓇ℯ𝒻𝓁

 interp-prod (node f t) 𝒜 x =
  let IH = λ x₁ → interp-prod (t x₁) 𝒜 x in
   (f ̂ ⨅ 𝒜)(λ x₁ → (t x₁ ̇ ⨅ 𝒜) x)                             ≡⟨ ap (f ̂ ⨅ 𝒜)(gfe IH) ⟩
   (f ̂ ⨅ 𝒜)(λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁)(λ j₁ → x j₁ i₁)))     ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (λ i₁ → (f ̂ 𝒜 i₁) (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))  ∎


 interp-prod2 : (p : Term X){I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆)
                --------------------------------------------------------------
  →             (p ̇ ⨅ 𝒜) ≡ λ(𝒕 : X → ∣ ⨅ 𝒜 ∣) → (λ i → (p ̇ 𝒜 i)(λ x → 𝒕 x i))

 interp-prod2 (ℊ x₁) 𝒜 = 𝓇ℯ𝒻𝓁

 interp-prod2 (node f t) 𝒜 = gfe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
   let IH = λ x → interp-prod (t x) 𝒜  in
   let tA = λ z → t z ̇ ⨅ 𝒜 in
    (f ̂ ⨅ 𝒜)(λ s → tA s tup)                          ≡⟨ ap (f ̂ ⨅ 𝒜)(gfe λ x → IH x tup) ⟩
    (f ̂ ⨅ 𝒜)(λ s → λ j → (t s ̇ 𝒜 j)(λ ℓ → tup ℓ j))   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ ℓ → tup ℓ i))) ∎

\end{code}




#### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

comm-hom-term : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
                {𝑨 : Algebra 𝓤 𝑆} (𝑩 : Algebra 𝓦 𝑆)
                (h : hom 𝑨 𝑩) (t : Term X) (a : X → ∣ 𝑨 ∣)
                -----------------------------------------
 →              ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

comm-hom-term  𝑩 h (ℊ x) a = 𝓇ℯ𝒻𝓁

comm-hom-term {𝑨 = 𝑨} 𝑩 h (node 𝑓 𝒕) a =
 ∣ h ∣((𝑓 ̂ 𝑨) λ i₁ → (𝒕 i₁ ̇ 𝑨) a)    ≡⟨ ∥ h ∥ 𝑓 ( λ r → (𝒕 r ̇ 𝑨) a ) ⟩
 (𝑓 ̂ 𝑩)(λ i₁ →  ∣ h ∣((𝒕 i₁ ̇ 𝑨) a))  ≡⟨ ap (_ ̂ 𝑩)(gfe (λ i₁ → comm-hom-term 𝑩 h (𝒕 i₁) a))⟩
 (𝑓 ̂ 𝑩)(λ r → (𝒕 r ̇ 𝑩)(∣ h ∣ ∘ a))    ∎

\end{code}

Next we prove that every term is compatible with every congruence relation. That is, if `t : Term X` and `θ : Con 𝑨`, then `a θ b → t(a) θ t(b)`.

\begin{code}

module _ {𝓤 : Universe}{X : 𝓤 ̇} where

 compatible-term : (𝑨 : Algebra 𝓤 𝑆)(t : Term X)(θ : Con 𝑨)
                   -----------------------------------------
  →                compatible-fun (t ̇ 𝑨) ∣ θ ∣

 compatible-term 𝑨 (ℊ x) θ p = p x

 compatible-term 𝑨 (node 𝑓 𝒕) θ p = snd ∥ θ ∥ 𝑓 λ x → (compatible-term 𝑨 (𝒕 x) θ) p

\end{code}

--------------------------------------

[← UALib.Terms.Basic](UALib.Terms.Basic.html)
<span style="float:right;">[UALib.Subalgebras →](UALib.Subalgebras.html)</span>

{% include UALib.Links.md %}



<!--
Here is an intensional version.

\begin{code}

comm-hom-term-intensional : global-dfunext → {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
 →                          (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)(t : Term X)
                            -------------------------------------------------------------
 →                          ∣ h ∣ ∘ (t ̇ 𝑨) ≡ (t ̇ 𝑩) ∘ (λ a → ∣ h ∣ ∘ a)

comm-hom-term-intensional gfe 𝑨 𝑩 h (ℊ x) = 𝓇ℯ𝒻𝓁

comm-hom-term-intensional gfe {X = X} 𝑨 𝑩 h (node f 𝒕) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ 𝑨) (λ i → (𝒕 i ̇ 𝑨) a)) ≡ (λ a → (f ̂ 𝑩)(λ i → (𝒕 i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣
  γ = (λ a → ∣ h ∣ ((f ̂ 𝑨)(λ i → (𝒕 i ̇ 𝑨) a)))     ≡⟨ gfe (λ a → ∥ h ∥ f ( λ r → (𝒕 r ̇ 𝑨) a )) ⟩
      (λ a → (f ̂ 𝑩)(λ i → ∣ h ∣ ((𝒕 i ̇ 𝑨) a)))     ≡⟨ ap (λ - → (λ a → (f ̂ 𝑩)(- a))) ih ⟩
      (λ a → (f ̂ 𝑩)(λ i → (𝒕 i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣ ∎
   where
    IH : ∀ a i → (∣ h ∣ ∘ (𝒕 i ̇ 𝑨)) a ≡ ((𝒕 i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a
    IH a i = intensionality (comm-hom-term-intensional gfe 𝑨 𝑩 h (𝒕 i)) a

    ih : (λ a → (λ i → ∣ h ∣ ((𝒕 i ̇ 𝑨) a))) ≡ (λ a → (λ i → ((𝒕 i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a))
    ih = gfe λ a → gfe λ i → IH a i

\end{code}

-->
