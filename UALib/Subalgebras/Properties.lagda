---
layout: default
title : UALib.Subalgebras.Properties module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Subalgebras.Properties {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Subalgebras.Generation{𝑆 = 𝑆}{gfe} renaming (generator to ℊ) public

---------------------------------

[← UALib.Subalgebras.Generation](UALib.Subalgebras.Generation.html)
<span style="float:right;">[UALib.Subalgebras.Subalgebras →](UALib.Subalgebras.Subalgebras.html)</span>

{% include UALib.Links.md %}
