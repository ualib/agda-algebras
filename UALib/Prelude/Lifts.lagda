---
layout: default
title : Prelude.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This section presents the [UALib.Prelude.Lifts][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Lifts where

open import Prelude.Inverses public

\end{code}

#### The noncumulative hierarchy

The hierarchy of universe levels in Agda looks like this:

𝓤₀ : 𝓤₁, &nbsp; 𝓤₁ : 𝓤₂, &nbsp; 𝓤₂ : 𝓤₃, …

This means that the type level of 𝓤₀ is 𝓤₁, and for each `n` The type level of 𝓤ₙ is 𝓤ₙ₊₁.

It is important to note, however, this does *not* imply that 𝓤₀ : 𝓤₂ and 𝓤₀ : 𝓤₃, and so on.  In other words, Agda's universe hierarchy is **noncummulative**.  This makes it possible to treat universe levels more generally and precisely, which is nice. On the other hand (in this author's experience) a noncummulative hierarchy can sometimes make for a nonfun proof assistant.

Luckily, there are ways to overcome this technical issue. We describe general lifting and lowering functions below, and then later, in the section on [Lifts of algebras](https://ualib.gitlab.io/Algebras.Algebras.html#lifts-of-algebras), we'll see the domain-specific analogs of these tools which turn out to have some nice properties that make them very effective for resolving universe level problems when working with algebra datatypes.

#### Lifting and lowering

Let us be more concrete about what is at issue here by giving an example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺) <br>
when checking that the expression SP𝒦 has type <br>
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346 <br>
</samp>

First of all, we must know how to interpret such errors. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

A general `Lift` record type, similar to the one found in the `Level` module of the [Agda Standard Library][], is defined as follows.

\begin{code}

record Lift {𝓦 𝓤 : Universe} (X : 𝓤 ̇) : 𝓤 ⊔ 𝓦 ̇  where
 constructor lift
 field lower : X
open Lift

\end{code}

Next, we give various ways to lift function types.

\begin{code}

module _ {𝓦 𝓧 𝓨 : Universe} where

 lift-dom : {X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓦}{𝓧} X → Y)
 lift-dom f = λ x → (f (lower x))

 lift-cod : {X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (X → Lift{𝓦}{𝓨} Y)
 lift-cod f = λ x → lift (f x)


module _ {𝓦 𝓩 𝓧 𝓨 : Universe} where

 lift-fun : {X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓦}{𝓧} X → Lift{𝓩}{𝓨} Y)
 lift-fun f = λ x → lift (f (lower x))

\end{code}

For example, `lift-dom` takes a function `f` defined on the domain `X : 𝓧 ̇` and returns a function defined on the domain `Lift{𝓦}{𝓧} X : 𝓧 ⊔ 𝓦 ̇`, whose type lives in the universe `𝓧 ⊔ 𝓦`.

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that `lift` and `lower` compose to the identity. Later, there will be some situations that require these facts, so we formalize them and their (trivial) proofs.

\begin{code}

lower∼lift : {𝓦 𝓧 : Universe}{X : 𝓧 ̇} → lower{𝓦}{𝓧} ∘ lift ≡ 𝑖𝑑 X
lower∼lift = 𝓇ℯ𝒻𝓁

lift∼lower : {𝓦 𝓧 : Universe}{X : 𝓧 ̇} → lift ∘ lower ≡ 𝑖𝑑 (Lift{𝓦}{𝓧} X)
lift∼lower = 𝓇ℯ𝒻𝓁

\end{code}


---------------

<p></p>

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}
