---
layout: default
title : Overture.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This is the [Overture.Lifts][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality renaming (_≡_ to infix 0 _≡_)
open import Function using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)

-- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries using (Type; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; 𝑖𝑑)

module Overture.Lifts where


\end{code}

