---
layout: default
title : "Overture.Operations module (The Agda Universal Algebra Library)"
date : "2022-06-17"
author: "the agda-algebras development team"
---

### <a id="Operations">Operations</a>

This is the [Overture.Operations][] module of the [Agda Universal Algebra Library][].

For consistency and readability, we reserve two universe variables for special
purposes.

The first of these is `𝓞` which we used in the [Overture.Signatures][]
as the universe of the type of *operation symbols* of a signature.

The second is `𝓥` which we reserve for types representing *arities* of relations or operations.

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`,
which gives us a very general way to represent an operation as a function type with
domain `I → A` (the type of "tuples") and codomain `A`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Operations where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( Level ; _⊔_ )

private variable a b ρ 𝓥 : Level

-- The type of operations on A of arity I
Op : Type a → Type 𝓥 → Type (a ⊔ 𝓥)
Op A I = (I → A) → A

\end{code}

For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op A I` as follows.

\begin{code}

-- Example (projections)
π : {I : Type 𝓥} {A : Type a } → I → Op A I
π i = λ x → x i

\end{code}

Occasionally we want to extract the arity of a given operation symbol.

\begin{code}

-- return the arity of a given operation symbol
arity[_] : {I : Type 𝓥} {A : Type a } → Op A I → Type 𝓥
arity[_] {I = I} f = I
\end{code}

-----------

<span style="float:left;">[← Overture.Signatures](Overture.Signatures.html)</span>
<span style="float:right;">[Base →](Base.html)</span>


{% include UALib.Links.md %}

