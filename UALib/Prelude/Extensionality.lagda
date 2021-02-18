---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Prelude.Extensionality where

open import UALib.Prelude.Inverses public
open import UALib.Prelude.Preliminaries using (_∼_; 𝓤ω; Π; Ω; 𝓟; ⊆-refl-consequence; _∈₀_; _⊆₀_; _holds) public

\end{code}




#### <a id="function-extensionality">Function extensionality</a>

Extensional equality of functions, or function extensionality, means that any two point-wise equal functions are equal. As [MHE points out](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua), this is known to be not provable or disprovable in Martin-Löf type theory. It is an independent statement, which MHE abbreviates as `funext`.  Here is how this notion is given a type in the [Type Topology][] library

```agda
funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g
```

For readability we occasionally use the following alias for the `funext` type.

\begin{code}

extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B} → f ∼ g → f ≡ g

\end{code}

Pointwise equality of functions is typically what one means in informal settings when one says that two functions are equal.  Here is how MHE defines pointwise equality of (dependent) function in [Type Topology][].

```agda
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x
infix 0 _∼_
```

In fact, if one assumes the [univalence axiom], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

\begin{code}

dep-extensionality : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
dep-extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
  {f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

\end{code}

Sometimes we need extensionality principles that work at all universe levels, and Agda is capable of expressing such principles, which belong to the special 𝓤ω type, as follows:

\begin{code}

∀-extensionality : 𝓤ω
∀-extensionality = ∀  {𝓤 𝓥} → extensionality 𝓤 𝓥

∀-dep-extensionality : 𝓤ω
∀-dep-extensionality = ∀ {𝓤 𝓥} → dep-extensionality 𝓤 𝓥

\end{code}

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


\begin{code}

extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

\end{code}




#### <a id="function-intensionality">Function intensionality</a>

This is the opposite of function extensionality and is defined as follows.

\begin{code}

intens -- alias
 intensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ≡ g  →  (x : A)
                  -----------------
 →                f x ≡ g x

intensionality 𝓇ℯ𝒻𝓁 _  = 𝓇ℯ𝒻𝓁
intens = intensionality

\end{code}

Of course, the intensionality principle has an analogue for dependent function types.

\begin{code}

dintensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } {f g : (x : A) → B x}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                f x ≡ g x

dintensionality 𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁

\end{code}




-------------------------------------

[← UALib.Prelude.Inverses](UALib.Prelude.Inverses.html)
<span style="float:right;">[UALib.Algebras →](UALib.Algebras.html)</span>

{% include UALib.Links.md %}
