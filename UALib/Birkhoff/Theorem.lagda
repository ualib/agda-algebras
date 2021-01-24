---
layout: default
title : UALib.Birkhoff.Theorem (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="the-hsp-theorem-in-agda">The HSP Theorem in Agda</a>

This section presents the [UALib.Birkhoff.Theorem][] module of the [Agda Universal Algebra Library][].

We now have all the pieces in place so that it is all but trivial to string together these pieces to complete the proof of Birkhoff's celebrated HSP theorem asserting that every variety is defined by a set of identities (is an "equational class").

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Birkhoff.Theorem
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {𝓤 : Universe} {X : 𝓤 ̇}
 where


open import UALib.Birkhoff.Lemmata {𝑆 = 𝑆}{gfe}{𝕏}{𝓤}{X} public

open the-free-algebra {𝓤}{𝓤}{X}


module Birkhoffs-Theorem
 {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 -- extensionality assumptions:
           {hfe : hfunext (OV 𝓤)(OV 𝓤)}
           {pe : propext (OV 𝓤)}
           {ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q)}
           {ssA : ∀ C → is-subsingleton (𝒞{OV 𝓤}{OV 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C)}
 where

 open the-relatively-free-algebra {𝓤}{𝓤}{X}{𝒦}
 open  HSPLemmata {𝒦 = 𝒦}{hfe}{pe}{ssR}{ssA}

 -- Birkhoff's theorem: every variety is an equational class.
 birkhoff : is-set ∣ ℭ ∣ → Mod X (Th 𝕍) ⊆ 𝕍

 birkhoff Cset {𝑨} MThVA = γ
  where
   T : Algebra (OV 𝓤) 𝑆
   T = 𝑻 X

   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst (𝕏 𝑨)

   h₀E : Epic h₀
   h₀E = snd (𝕏 𝑨)

   ϕ : Σ h ꞉ (hom 𝔽 𝑨) , Epic ∣ h ∣
   ϕ = (𝔉-lift-hom 𝑨 h₀) , 𝔉-lift-of-epic-is-epic 𝑨 h₀ h₀E

   AiF : 𝑨 is-hom-image-of 𝔽
   AiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) ) , refl-≅

   γ : 𝑨 ∈ 𝕍
   γ = vhimg (𝔽∈𝕍 Cset) AiF

\end{code}

Some readers familiar with Birkhoff's theorem might worry that we haven't acheived our goal because they may be used to seeing it presented as an "if and only if" assertion.  Those fears are quickly put to rest by observing that the converse of the result just proved is that every equational class is closed under HSP, and we already proved thatin the [Equation Preservation](UALib.Varieties.Preservation.html) module. Indeed, there we proved the identity preservation lemmas,

* [H-id1](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#964) 𝒦 ⊧ p ≋ q → H 𝒦 ⊧ p ≋ q
* [S-id1](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#2592) 𝒦 ⊧ p ≋ q → S 𝒦 ⊧ p ≋ q
* [P-id1](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#4111) 𝒦 ⊧ p ≋ q → P 𝒦 ⊧ p ≋ q

from which it follows that every equational class is closed under H, S, and P.

--------------------------------------------

[← UALib.Birkhoff.Lemmata](UALib.Birkhoff.Lemmata.html)
<span style="float:right;">[UALib.Birkhoff ↑](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}

