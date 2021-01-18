---
layout: default
title : UALib.Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="basic-definitions">Basic definitions</a>

This section presents the [UALib.Terms.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Terms.Basic
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Homomorphisms.HomomorphicImages{𝑆 = 𝑆}{gfe} hiding (Universe; _̇) public

\end{code}

-----------------------------------------------

#### <a id="the-inductive-type-of-terms">The inductive type of terms</a>

We define a type called `Term` which, not surprisingly, represents the type of terms. The type `X :  𝒰 ̇` represents an arbitrary collection of variable symbols.

\begin{code}

data Term {𝓧 : Universe}{X : 𝓧 ̇} : 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ̇  where
  generator : X → Term{𝓧}{X}
  node : (f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓧}{X}) → Term

open Term

\end{code}

--------------------------------------

[↑ UALib.Terms](UALib.Terms.html)
<span style="float:right;">[UALib.Terms.Free →](UALib.Terms.Free.html)</span>

{% include UALib.Links.md %}
