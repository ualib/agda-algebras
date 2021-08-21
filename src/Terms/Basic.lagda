---
layout: default
title : Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the agda-algebras development team][]
---

### <a id="basic-definitions">Basic Definitions</a>

This is the [Terms.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic

module Terms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive using ( Level ) renaming ( Set to Type )
open import Data.Product   using ( _,_ )

open import Overture.Preliminaries    using ( ∣_∣ ; ∥_∥ )
open import Algebras.Products {𝑆 = 𝑆} using ( ov )

private variable χ : Level

\end{code}

#### The type of terms

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `𝑓 𝑡` such that `𝑓 : ∣ 𝑆 ∣` and `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ 𝑓` is the arity of the operation symbol 𝑓.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

\begin{code}

data Term (X : Type χ ) : Type (ov χ)  where
 ℊ : X → Term X    -- (ℊ for "generator")
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X

\end{code}

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.



#### The term algebra

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `𝑓 : ∣ 𝑆 ∣`, denote by `𝑓 ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `𝑡 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑻 X ∣` to the formal term `𝑓 𝑡`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `𝑓 ̂ (𝑻 X)`, one for each symbol `𝑓` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

\begin{code}

𝑻 : (X : Type χ ) → Algebra (ov χ) 𝑆
𝑻 X = Term X , node

\end{code}


------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

