---
layout: default
title : Terms.Operations module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="term-operations">Term Operations</a>

This section presents the [Terms.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a particular algebra, and we prove some compatibility properties of term operations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Terms.Operations {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Terms.Basic{𝑆 = 𝑆}{gfe} renaming (generator to ℊ) public

\end{code}

**Notation**. In the line above, we renamed for notational convenience the `generator` constructor of the `Term` type, so from now on we use `ℊ` in place of `generator`.

When we interpret a term in an algebra we call the resulting function a **term operation**.  Given a term `𝑝` and an algebra `𝑨`, we denote by `𝑝 ̇ 𝑨` the **interpretation** of `𝑝` in `𝑨`.  This is defined inductively as follows.

1. If `𝑝` is a variable symbol `x : X` and if `𝑎 : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then `(𝑝 ̇ 𝑨) 𝑎 := 𝑎 x`.

2. If `𝑝 = 𝑓 𝑡`, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol, if `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of terms, and if `𝑎 : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define `(𝑝 ̇ 𝑨) 𝑎 = (𝑓 𝑡 ̇ 𝑨) 𝑎 := (𝑓 ̂ 𝑨) (λ i → (𝑡 i ̇ 𝑨) 𝑎)`.

Thus the interpretation of a term is defined by induction on the structure of the term, and the definition is formally implemented in the [UALib][] as follows.

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇ } where

 _̇_ : Term X → (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 (ℊ x ̇ 𝑨) 𝑎 = 𝑎 x

 (node 𝑓 𝑡 ̇ 𝑨) 𝑎 = (𝑓 ̂ 𝑨) λ i → (𝑡 i ̇ 𝑨) 𝑎

\end{code}

It turns out that the intepretation of a term is the same as the `free-lift` (modulo argument order and assuming function extensionality).

\begin{code}

 free-lift-interp : dfunext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)(p : Term X)
  →                 (p ̇ 𝑨) h ≡ (free-lift 𝑨 h) p

 free-lift-interp _ 𝑨 h (ℊ x) = refl
 free-lift-interp fe 𝑨 h (node 𝑓 𝑡) = ap (𝑓 ̂ 𝑨) (fe λ i → free-lift-interp fe 𝑨 h (𝑡 i))

\end{code}

If the algebra 𝑨 happens to be `𝑻 X`, then we expect that `∀ 𝑠` we have `(p ̇ 𝑻 X) 𝑠  ≡  p 𝑠`. But what is `(𝑝 ̇ 𝑻 X) 𝑠` exactly? By definition, it depends on the form of 𝑝 as follows:

* if `𝑝 = ℊ x`, then `(𝑝 ̇ 𝑻 X) 𝑠 := (ℊ x ̇ 𝑻 X) 𝑠 ≡ 𝑠 x`

* if `𝑝 = node 𝑓 𝑡`, then `(𝑝 ̇ 𝑻 X) 𝑠 := (node 𝑓 𝑡 ̇ 𝑻 X) 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑡 i ̇ 𝑻 X) 𝑠`

Now, assume `ϕ : hom 𝑻 𝑨`. Then by `comm-hom-term`, we have `∣ ϕ ∣ (p ̇ 𝑻 X) 𝑠 = (p ̇ 𝑨) ∣ ϕ ∣ ∘ 𝑠`.

* if `p = ℊ x` (and `𝑡 : X → ∣ 𝑻 X ∣`), then

  `∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x) ≡ ∣ ϕ ∣ (λ 𝑡 → h 𝑡) ≡ λ 𝑡 → (∣ ϕ ∣ ∘ 𝑡) x`

* if `p = node 𝑓 𝑡`, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (p ̇ 𝑻 X) 𝑠 = (node 𝑓 𝑡 ̇ 𝑻 X) 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑡 i ̇ 𝑻 X) 𝑠

We claim that for all `p : Term X` there exists `q : Term X` and `𝔱 : X → ∣ 𝑻 X ∣` such that `p ≡ (q ̇ 𝑻 X) 𝔱`. We prove this fact as follows.

\begin{code}

term-interp : {𝓧 : Universe}{X : 𝓧 ̇} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X}
 →            𝑠 ≡ 𝑡 → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡

term-interp 𝑓 {𝑠}{𝑡} st = ap (node 𝑓) st

module _ {𝓧 : Universe}{X : 𝓧 ̇}{fe : dfunext 𝓥 (ov 𝓧)} where

 term-gen : (p : ∣ 𝑻 X ∣) → Σ q ꞉ ∣ 𝑻 X ∣ , p ≡ (q ̇ 𝑻 X) ℊ
 term-gen (ℊ x) = (ℊ x) , refl
 term-gen (node 𝑓 𝑡) = node 𝑓 (λ i → ∣ term-gen (𝑡 i) ∣) , term-interp 𝑓 (fe λ i → ∥ term-gen (𝑡 i) ∥)


 term-gen-agreement : (p : ∣ 𝑻 X ∣) → (p ̇ 𝑻 X) ℊ ≡ (∣ term-gen p ∣ ̇ 𝑻 X) ℊ
 term-gen-agreement (ℊ x) = refl
 term-gen-agreement (node f 𝑡) = ap (f ̂ 𝑻 X) (fe λ x → term-gen-agreement (𝑡 x))

 term-agreement : (p : ∣ 𝑻 X ∣) → p ≡ (p ̇ 𝑻 X) ℊ
 term-agreement p = snd (term-gen p) ∙ (term-gen-agreement p)⁻¹

\end{code}



#### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>

Note that while in the previous section it sufficed to postulate a local version of function extensionality, here we are using the global version (`global-dfunext`), though we are not sure whether this is necessary or we could remove it with some effort.<sup>[1](Terms.Operations.html#fn1)</sup>

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇ } where

 interp-prod : {𝓦 : Universe}(p : Term X){I : 𝓦 ̇}
               (𝒜 : I → Algebra 𝓤 𝑆)(𝑎 : X → ∀ i → ∣ 𝒜 i ∣)
               -----------------------------------------------
  →            (p ̇ (⨅ 𝒜)) 𝑎 ≡ (λ i → (p ̇ 𝒜 i) (λ j → 𝑎 j i))

 interp-prod (ℊ x₁) 𝒜 𝑎 = refl

 interp-prod (node 𝑓 𝑡) 𝒜 𝑎 = let IH = λ x → interp-prod (𝑡 x) 𝒜 𝑎
  in
  (𝑓 ̂ ⨅ 𝒜)(λ x → (𝑡 x ̇ ⨅ 𝒜) 𝑎)                      ≡⟨ ap (𝑓 ̂ ⨅ 𝒜)(gfe IH) ⟩
  (𝑓 ̂ ⨅ 𝒜)(λ x → (λ i → (𝑡 x ̇ 𝒜 i)(λ j → 𝑎 j i)))   ≡⟨ refl ⟩
  (λ i → (𝑓 ̂ 𝒜 i) (λ x → (𝑡 x ̇ 𝒜 i)(λ j → 𝑎 j i)))  ∎


 interp-prod2 : (p : Term X){I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆)
                --------------------------------------------------------------
  →             (p ̇ ⨅ 𝒜) ≡ λ(𝑡 : X → ∣ ⨅ 𝒜 ∣) → (λ i → (p ̇ 𝒜 i)(λ x → 𝑡 x i))

 interp-prod2 (ℊ x₁) 𝒜 = refl

 interp-prod2 (node f t) 𝒜 = gfe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
  let IH = λ x → interp-prod (t x) 𝒜  in
  let tA = λ z → t z ̇ ⨅ 𝒜 in
  (f ̂ ⨅ 𝒜)(λ s → tA s tup)                          ≡⟨ ap(f ̂ ⨅ 𝒜)(gfe λ x → IH x tup)⟩
  (f ̂ ⨅ 𝒜)(λ s → λ j → (t s ̇ 𝒜 j)(λ ℓ → tup ℓ j))   ≡⟨ refl ⟩
  (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ ℓ → tup ℓ i))) ∎

\end{code}




#### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

module _ {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇} where

 comm-hom-term : {𝑨 : Algebra 𝓤 𝑆} (𝑩 : Algebra 𝓦 𝑆)
                 (h : hom 𝑨 𝑩) (t : Term X) (a : X → ∣ 𝑨 ∣)
                 -----------------------------------------
  →              ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

 comm-hom-term  𝑩 h (ℊ x) a = refl

 comm-hom-term {𝑨} 𝑩 h (node 𝑓 𝑡) a = ∣ h ∣((𝑓 ̂ 𝑨)λ i → (𝑡 i ̇ 𝑨) a)    ≡⟨ i  ⟩
                                     (𝑓 ̂ 𝑩)(λ i →  ∣ h ∣((𝑡 i ̇ 𝑨) a))  ≡⟨ ii ⟩
                                     (𝑓 ̂ 𝑩)(λ r → (𝑡 r ̇ 𝑩)(∣ h ∣ ∘ a)) ∎
  where
  i  = ∥ h ∥ 𝑓(λ r → (𝑡 r ̇ 𝑨) a)
  ii = ap (𝑓 ̂ 𝑩)(gfe (λ i → comm-hom-term 𝑩 h (𝑡 i) a))

\end{code}

To conclude this module, we prove that every term is compatible with every congruence relation. That is, if `t : Term X` and `θ : Con 𝑨`, then `a θ b → t(a) θ t(b)`. (Recall, the compatibility relation `|:` was defined in [Relations.Discrete][].)

\begin{code}

open Congruence

module _ {𝓤 : Universe}{X : 𝓤 ̇} where

 _∣:_ : {𝑨 : Algebra 𝓤 𝑆}(t : Term X)(θ : Con 𝑨)
        -----------------------------------------
  →     (t ̇ 𝑨) |: ∣ θ ∣

 ((ℊ x) ∣: θ) p = p x

 ((node 𝑓 𝑡) ∣: θ) p = snd ∥ θ ∥ 𝑓 λ x → ((𝑡 x) ∣: θ) p


\end{code}

For the sake of comparison, here is the analogous theorem using `compatible-fun`.

\begin{code}

 compatible-term : {𝑨 : Algebra 𝓤 𝑆}(t : Term X)(θ : Con 𝑨)
                   -----------------------------------------
  →                compatible-fun (t ̇ 𝑨) ∣ θ ∣

 compatible-term (ℊ x) θ p = λ y z → z x

 compatible-term (node 𝑓 𝑡) θ u v p = snd ∥ θ ∥ 𝑓 λ x → ((compatible-term (𝑡 x) θ) u v) p


\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">We plan to resolve this before the next major release of the [Agda UALib][].</span>

<br>
<br>

[← Terms.Basic](Terms.Basic.html)
<span style="float:right;">[Subalgebras →](Subalgebras.html)</span>

{% include UALib.Links.md %}



<!--
Here is an intensional version.

comm-hom-term-intensional : global-dfunext → {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
 →                          (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)(t : Term X)
                            -------------------------------------------------------------
 →                          ∣ h ∣ ∘ (t ̇ 𝑨) ≡ (t ̇ 𝑩) ∘ (λ a → ∣ h ∣ ∘ a)

comm-hom-term-intensional gfe 𝑨 𝑩 h (ℊ x) = refl

comm-hom-term-intensional gfe {X = X} 𝑨 𝑩 h (node f 𝑡) = γ
 where
  γ : ∣ h ∣ ∘ (λ a → (f ̂ 𝑨) (λ i → (𝑡 i ̇ 𝑨) a)) ≡ (λ a → (f ̂ 𝑩)(λ i → (𝑡 i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣
  γ = (λ a → ∣ h ∣ ((f ̂ 𝑨)(λ i → (𝑡 i ̇ 𝑨) a)))     ≡⟨ gfe (λ a → ∥ h ∥ f ( λ r → (𝑡 r ̇ 𝑨) a )) ⟩
      (λ a → (f ̂ 𝑩)(λ i → ∣ h ∣ ((𝑡 i ̇ 𝑨) a)))     ≡⟨ ap (λ - → (λ a → (f ̂ 𝑩)(- a))) ih ⟩
      (λ a → (f ̂ 𝑩)(λ i → (𝑡 i ̇ 𝑩) a)) ∘ _∘_ ∣ h ∣ ∎
   where
    IH : ∀ a i → (∣ h ∣ ∘ (𝑡 i ̇ 𝑨)) a ≡ ((𝑡 i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a
    IH a i = extfun (comm-hom-term-intensional gfe 𝑨 𝑩 h (𝑡 i)) a

    ih : (λ a → (λ i → ∣ h ∣ ((𝑡 i ̇ 𝑨) a))) ≡ (λ a → (λ i → ((𝑡 i ̇ 𝑩) ∘ _∘_ ∣ h ∣) a))
    ih = gfe λ a → gfe λ i → IH a i

-->
