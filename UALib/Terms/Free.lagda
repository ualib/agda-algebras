---
layout: default
title : UALib.Terms.Free module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="the-term-algebra">The Term Algebra</a>

This section presents the [UALib.Terms.Free][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Terms.Free
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Terms.Basic{𝑆 = 𝑆}{gfe}{𝕏} hiding (Algebra) public

\end{code}

-------------------------------------------------


--------------------------------------

[← UALib.Terms.Basic](UALib.Terms.Basic.html)
<span style="float:right;">[UALib.Terms.Operations →](UALib.Terms.Operations.html)</span>

{% include UALib.Links.md %}



<!-- term-op : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓧}{X} ) → Term
term-op f args = node f args -->

