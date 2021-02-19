---
layout: default
title : UALib.Subalgebras.Homomorphisms module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="homomorphisms-and-subuniverses">Homomorphisms and subuniverses</a>

This section presents the [UALib.Subalgebras.Homomorphisms][]  module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Subalgebras.Homomorphisms {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Subalgebras.Properties{𝑆 = 𝑆}{gfe} public

\end{code}




---------------------------------

[← UALib.Subalgebras.Properties](UALib.Subalgebras.Properties.html)
<span style="float:right;">[UALib.Subalgebras.Subalgebras →](UALib.Subalgebras.Subalgebras.html)</span>

{% include UALib.Links.md %}
