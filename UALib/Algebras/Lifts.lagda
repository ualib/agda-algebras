---
layout: default
title : UALib.Algebras.Lifts module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This section presents the [UALib.Algebras.Lifts][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Algebras.Lifts where

open import UALib.Algebras.Products public
\end{code}

#### The noncumulative hierarchy

The hierarchy of universe levels in Agda looks like this:

𝓤₀ : 𝓤₁, &nbsp; 𝓤₁ : 𝓤₂, &nbsp; 𝓤₂ : 𝓤₃, …

This means that the type level of 𝓤₀ is 𝓤₁, and for each `n` The type level of 𝓤ₙ is 𝓤ₙ₊₁.

It is important to note, however, this does *not* imply that 𝓤₀ : 𝓤₂ and 𝓤₀ : 𝓤₃, and so on.  In other words, Agda's universe hierarchy is **noncummulative**.  This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand (in this author's experience) a noncummulative hierarchy can sometimes make for a nonfun proof assistant.

Luckily, there are ways to overcome this technical issue, and we describe some such techniques we developed specifically for our domain.

#### Lifting and lowering

Let us be more concrete about what is at issue here by giving an example. Agda will often complain with errors like the following:

```
Birkhoff.lagda:498,20-23
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺)
when checking that the expression SP𝒦 has type
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346
```

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda` file, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the [Agda Standard Library][] (in the `Level` module), is defined as follows.

\begin{code}

record Lift {𝓤 𝓦 : Universe} (X : 𝓤 ̇) : 𝓤 ⊔ 𝓦 ̇  where
 constructor lift
 field lower : X
open Lift

\end{code}

Next, we give various ways to lift function types.

\begin{code}

lift-dom : {𝓧 𝓨 𝓦 : Universe}{X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓧}{𝓦} X → Y)
lift-dom f = λ x → (f (lower x))

lift-cod : {𝓧 𝓨 𝓦 : Universe}{X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (X → Lift{𝓨}{𝓦} Y)
lift-cod f = λ x → lift (f x)

lift-fun : {𝓧 𝓨 𝓦 𝓩 : Universe}{X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓧}{𝓦} X → Lift{𝓨}{𝓩} Y)
lift-fun f = λ x → lift (f (lower x))

\end{code}

We will also need to know that lift and lower compose to the identity.

\begin{code}

lower∼lift : {𝓧 𝓦 : Universe}{X : 𝓧 ̇} → lower{𝓧}{𝓦} ∘ lift ≡ 𝑖𝑑 X
lower∼lift = refl _

lift∼lower : {𝓧 𝓦 : Universe}{X : 𝓧 ̇} → lift ∘ lower ≡ 𝑖𝑑 (Lift{𝓧}{𝓦} X)
lift∼lower = refl _

\end{code}

Now, getting more "domain-specific," we show how to lift algebraic operation types and then, finally, algebra types themselves.

\begin{code}

module _ {𝑆 : Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)} where

 lift-op : {𝓤 : Universe}{I : 𝓥 ̇}{A : 𝓤 ̇}
  →        ((I → A) → A) → (𝓦 : Universe)
  →        ((I → Lift{𝓤}{𝓦}A) → Lift{𝓤}{𝓦}A)
 lift-op f 𝓦 = λ x → lift (f (λ i → lower (x i)))

 open algebra

 lift-alg-record-type : {𝓤 : Universe} → algebra 𝓤 𝑆 → (𝓦 : Universe) → algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-alg-record-type 𝑨 𝓦 = mkalg (Lift (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → lift-op ((op 𝑨) f) 𝓦)

 lift-∞-algebra lift-alg : {𝓤 : Universe} → Algebra 𝓤 𝑆 → (𝓦 : Universe) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-∞-algebra 𝑨 𝓦 = Lift ∣ 𝑨 ∣ , (λ (f : ∣ 𝑆 ∣) → lift-op (∥ 𝑨 ∥ f) 𝓦)
 lift-alg = lift-∞-algebra

\end{code}

---------------

[← UALib.Algebras.Products](UALib.Algebras.Products.html)
<span style="float:right;">[UALib.Relations →](UALib.Relations.html)</span>

{% include UALib.Links.md %}
