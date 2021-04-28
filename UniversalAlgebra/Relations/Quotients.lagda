---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
open import Data.Product  using (_,_; Σ; Σ-syntax; _×_)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Unary using (Pred; _⊆_)

open import Overture.Preliminaries using (Type; 𝓤; 𝓥; 𝓦; -Σ)
open import Relations.Discrete using (ker)


module Relations.Quotients where

\end{code}



#### <a id="equivalence-classes">Equivalence relations</a>

Let `𝓤 : Universe` be a universe and `A : Type 𝓤` a type.  In [Relations.Discrete][] we defined a type representing a binary relation on A.  In this module we will define types for binary relations that have special properties. The most important special properties of relations are the ones we now define.

\begin{code}


Refl : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Refl _≈_ = ∀{x} → x ≈ x

Symm : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Symm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x

Antisymm : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Antisymm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x → x ≡ y

Trans : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Trans _≈_ = ∀{x}{y}{z} → x ≈ y → y ≈ z → x ≈ z

\end{code}


A binary relation is called a *preorder* if it is reflexive and transitive. An *equivalence relation* is a symmetric preorder. The property of being an equivalence relation is represented in the [Agda Standard Library][] by a record type called `IsEquivalence`, which is similar to the one we define here.


Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary relation over `A` and `p` is of record type `IsEquivalence R` with fields containing the three proofs showing that `R` is an equivalence relation.

A prominent example of an equivalence relation is the kernel of any function.

\begin{code}

ker-IsEquivalence : {A : Type 𝓤}{B : Type 𝓦}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { refl = refl ; sym = λ x → sym x ; trans = λ x y → trans x y }

\end{code}

#### <a id="equivalence-classes">Equivalence classes (blocks)</a>

If `R` is an equivalence relation on `A`, then for each `u : A` there is an *equivalence class* (or *equivalence block*, or `R`-*block*) containing `u`, which we denote and define by `[ u ] := {v : A | R u v}`.

\begin{code}

[_] : {A : Type 𝓤} → A → {R : Rel A 𝓦} → Pred A 𝓦
[ u ]{R} = R u

infix 60 [_]

\end{code}


Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]` as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.  We represent this characterization of an `R`-block as follows.

\begin{code}

IsBlock : {A : Type 𝓤}(C : Pred A 𝓦){R : Rel A 𝓦} → Type(𝓤 ⊔ lsuc 𝓦)
IsBlock {A = A} C {R} = Σ[ u ꞉ A ] C ≡ [ u ]{R}

\end{code}

Thus, a proof of `IsBlock C` is a pair `(u , p)`, with `u : A` and `p` is a proof of `C ≡ [ u ] {R}`.

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all `R`-blocks.<sup>[1](Relations.Quotients.html#fn1)</sup>

\begin{code}

module _ {𝓤 𝓦 : Level} where

 _/_ : (A : Type 𝓤 ) → Rel A 𝓦 → Type(𝓤 ⊔ lsuc 𝓦)
 A / R = Σ[ C ꞉ Pred A 𝓦 ] IsBlock C {R}

 infix -1 _/_

\end{code}

We use the following type to represent an \ab R-block with a designated representative.

\begin{code}

⟪_⟫ : {A : Type 𝓤} → A → {R : Rel A 𝓦} → A / R
⟪ a ⟫{R} = [ a ]{R} , (a  , refl)

\end{code}

Dually, the next type provides an *elimination rule*.<sup>[2](Relations.Quotients.html#fn2)</sup>

\begin{code}

⌞_⌟ : {A : Type 𝓤}{R : Rel A 𝓦} → A / R  → A
⌞ C , a , p ⌟ = a

\end{code}

Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.

It will be convenient to have the following subset inclusion lemmas on hand when working with quotient types.

\begin{code}

private variable A : Type 𝓤 ; x y : A ; R : Rel A 𝓦
open IsEquivalence

/-subset : IsEquivalence R → R x y →  [ x ]{R} ⊆  [ y ]{R}
/-subset Req Rxy {z} Rxz = IsEquivalence.trans Req (IsEquivalence.sym Req Rxy) Rxz

/-supset : IsEquivalence R → R x y →  [ y ]{R} ⊆ [ x ]{R}
/-supset Req Rxy {z} Ryz = IsEquivalence.trans Req Rxy Ryz

\end{code}

An example application of these is the `block-ext` type in the [Relations.Extensionality] module.

--------------------------------------


<sup>1</sup><span class="footnote" id="fn1">**Unicode Hints** ([agda2-mode][]). `\cl ↝ ⌞`; `\clr ↝ ⌟`.</span>


<br>
<br>


[← Relations.Continuous](Relations.Continuous.html)
<span style="float:right;">[Relations.Truncation →](Relations.Truncation.html)</span>

{% include UALib.Links.md %}

