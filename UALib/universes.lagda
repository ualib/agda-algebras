---
layout: default
title : universes module (from the Type Topology library of Martin Escardo)
date : 2021-01-12
author: Martin Escardo
---

<!--
FILE: universes.lagda
AUTHOR: Martin Escardo
REF: This file was adapted from the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
-->

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module universes where

open import Agda.Primitive
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          ) public

variable
 𝓞 𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe

\end{code}

The following should be the only use of the Agda keyword 'Set' in this development:

\begin{code}

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Set 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

\end{code}

This is mainly to avoid naming implicit arguments:

\begin{code}

universe-of : (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤

infix  1 _̇
\end{code}
