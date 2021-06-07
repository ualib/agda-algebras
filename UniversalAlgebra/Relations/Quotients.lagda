---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: [the ualib/agda-algebras development team][]
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Quotients where

open import Agda.Builtin.Equality                 using    (_≡_  ; refl      )
open import Data.Product                          using    ( _,_ ; Σ
                                                           ; Σ-syntax        )
                                                  renaming ( proj₁ to fst
                                                           ; proj₂ to snd    )
open import Agda.Primitive                        using    ( _⊔_             )
                                                  renaming ( Set   to Type
                                                           ; Setω  to Typeω  )
open import Level                                 renaming ( suc   to lsuc
                                                           ; zero  to ℓ₀     )
open import Relation.Binary                       using    ( IsEquivalence   )
                                                  renaming ( Rel   to BinRel )
open import Relation.Binary.PropositionalEquality using    ( sym  ; trans    )
open import Relation.Unary                        using    ( Pred ; _⊆_      )
open import Relations.Discrete                    using    ( ker             )

private variable α β ρ 𝓥 : Level

\end{code}



#### <a id="equivalence-classes">Equivalence relations</a>

A binary relation is called a *preorder* if it is reflexive and transitive. An *equivalence relation* is a symmetric preorder. The property of being an equivalence relation is represented in the [Agda Standard Library][] by a record type called `IsEquivalence`.

Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary relation over `A` and `p` is of record type `IsEquivalence R` with fields containing the three proofs showing that `R` is an equivalence relation.

A prominent example of an equivalence relation is the kernel of any function.

\begin{code}

ker-IsEquivalence : {A : Type α}{B : Type β}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { refl = refl ; sym = λ x → sym x ; trans = λ x y → trans x y }

\end{code}

#### <a id="equivalence-classes">Equivalence classes (blocks)</a>

If `R` is an equivalence relation on `A`, then for each `u : A` there is an *equivalence class* (or *equivalence block*, or `R`-*block*) containing `u`, which we denote and define by `[ u ] := {v : A | R u v}`.

\begin{code}

[_] : {A : Type α} → A → {R : BinRel A ρ} → Pred A ρ
[ u ]{R} = R u

infix 60 [_]

\end{code}


Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]` as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.  We represent this characterization of an `R`-block as follows.

\begin{code}

record IsBlock {A : Type α}(P : Pred A ρ){R : BinRel A ρ} : Type(α ⊔ lsuc ρ) where
  constructor R-block
  field
    block-u : A
    P≡[u] : P ≡ [ block-u ]{R}

\end{code}

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all `R`-blocks.<sup>[1](Relations.Quotients.html#fn1)</sup>

\begin{code}

_/_ : (A : Type α ) → BinRel A ρ → Type(α ⊔ lsuc ρ)
A / R = Σ[ P ∈ Pred A _ ] IsBlock P {R}

infix -1 _/_

\end{code}

We use the following type to represent an \ab R-block with a designated representative.

\begin{code}

⟪_⟫ : {A : Type α} → A → {R : BinRel A ρ} → A / R
⟪ a ⟫{R} = [ a ]{R} , R-block a refl

\end{code}

Dually, the next type provides an *elimination rule*.<sup>[2](Relations.Quotients.html#fn2)</sup>

\begin{code}

⌞_⌟ : {A : Type α}{R : BinRel A ρ} → A / R  → A
⌞ _ , R-block a _ ⌟ = a

\end{code}

Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.

It will be convenient to have the following subset inclusion lemmas on hand when working with quotient types.

\begin{code}

private variable A : Type α ; x y : A ; R : BinRel A ρ
open IsEquivalence

/-subset : IsEquivalence R → R x y →  [ x ]{R} ⊆ [ y ]{R}
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

-----------------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team

