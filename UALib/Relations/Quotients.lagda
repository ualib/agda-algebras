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

module Relations.Quotients where

open import Relations.Discrete public

\end{code}

**N.B.**. We import [Relations.Discrete][] since we don't yet need any of the types defined in the [Relations.Continuous][] module.


#### <a id="properties-of-binary-relations">Properties of binary relations</a>

Let `𝓤 : Universe` be a universe and `A : 𝓤 ̇` a type.  In [Relations.Discrete][] we defined a type representing a binary relation on A.  In this module we will define types for binary relations that have special properties. The most important special properties of relations are the ones we now define.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 Refl : {A : 𝓤 ̇} → Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 Refl _≈_ = ∀{x} → x ≈ x

 Symm : {A : 𝓤 ̇} → Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 Symm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x

 Antisymm : {A : 𝓤 ̇} → Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 Antisymm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x → x ≡ y

 Trans : {A : 𝓤 ̇} → Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 Trans _≈_ = ∀{x}{y}{z} → x ≈ y → y ≈ z → x ≈ z

\end{code}

The [Type Topology][] library defines the following *uniqueness-of-proofs* principle for binary relations.

\begin{code}

module hide-is-subsingleton-valued where

 is-subsingleton-valued : {A : 𝓤 ̇} → Rel A 𝓦 → 𝓤 ⊔ 𝓦 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)

open import MGS-Quotient using (is-subsingleton-valued) public

\end{code}

Thus, if `R : Rel A 𝓦`, then `is-subsingleton-valued R` is the assertion that for each pair `x y : A` there can be at most one proof that `R x y` holds.

In the [Relations.Truncation][] module we introduce a number of similar but more general types used in the [Agda UALib][] to represent *uniqueness-of-proofs principles* for relations of arbitrary arity over arbitrary types.


#### <a id="equivalence-classes">Equivalence relations</a>

A binary relation is called a *preorder* if it is reflexive and transitive. An *equivalence relation* is a symmetric preorder. We define the property of being an equivalence relation as the following record type.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 record IsEquivalence {A : 𝓤 ̇}(R : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field rfl : Refl R ; sym : Symm R ; trans : Trans R

\end{code}

And we define the type of equivalence relations over a given type `A` as follows.

\begin{code}

 Equivalence : 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺ ̇
 Equivalence A = Σ R ꞉ Rel A 𝓦 , IsEquivalence R

\end{code}

Thus, if we have `(R ,  p) : Equivalence A`, then `R` denotes a binary relation over `A` and `p` is of record type `IsEquivalence R` with fields containing the three proofs showing that `R` is an equivalence relation.


An easy first example of an equivalence relation is the kernel of any function. We prove that such a kernel is an equivalence relation on the domain of the function as follows.

\begin{code}

 ker-IsEquivalence : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B) → IsEquivalence (ker f)
 ker-IsEquivalence f = record { rfl = refl; sym = λ z → ≡-sym z ; trans = λ p q → ≡-trans p q }

\end{code}

#### <a id="equivalence-classes">Equivalence classes (blocks)</a>

If R is an equivalence relation on A, then for each `u : A`, there is an *equivalence class* (or *equivalence block*) containing `u`, which we denote and define by `[ u ] {R}` := all `v : A` such that `R u v`.

\begin{code}

 [_] : {A : 𝓤 ̇} → A → {R : Rel A 𝓦} → Pred A 𝓦
 [ u ]{R} = R u

 infix 60 [_]

\end{code}


Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]` as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.  We represent this characterization of an `R`-block as follows.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}

\end{code}

Thus, a proof of the assertion `IsBlock C` is a dependent pair `(u , p)`, with ` u : A` and `p` is a proof of `C ≡ [ u ] {R}`.

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all `R`-blocks.

\begin{code}

 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓦 → 𝓤 ⊔ (𝓦 ⁺) ̇
 A / R = Σ C ꞉ Pred A 𝓦 , IsBlock C {R}

 infix -1 _/_

\end{code}

Thus, a block of `R` is a pair `(C , p)` consisting of a predicate `C` and a proof `p : IsBlock C`.

The following serves as a kind of *introduction rule*.

\begin{code}

 ⟪_⟫ : {A : 𝓤 ̇} → A → {R : Rel A 𝓦} → A / R
 ⟪ a ⟫{R} = [ a ]{R} , (a  , refl)

\end{code}

Dually, the next type provides an *elimination rule*. Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.<sup>[1](Relations.Quotients.html#fn1)</sup>

\begin{code}

 ⌞_⌟ : {A : 𝓤 ̇}{R : Rel A 𝓦} → A / R  → A
 ⌞ _ , a , _ ⌟ = a

\end{code}

Later we will need the following tools for working with the quotient types defined above.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{x y : A}{R : Rel A 𝓦} where

 open IsEquivalence
 /-subset : IsEquivalence R → R x y →  [ x ]{R} ⊆  [ y ]{R}
 /-subset Req Rxy {z} Rxz = (trans Req) ((sym Req) Rxy) Rxz

 /-supset : IsEquivalence R → R x y →  [ y ]{R} ⊆ [ x ]{R}
 /-supset Req Rxy {z} Ryz = (trans Req) Rxy Ryz

 /-≐ : IsEquivalence R → R x y →  [ x ]{R} ≐ [ y ]{R}
 /-≐ Req Rxy = /-subset Req Rxy , /-supset Req Rxy

\end{code}

(An example application of `/-≐` is the `class-extensionality` lemma in the [Relations.Truncation] module.)

--------------------------------------


<sup>1</sup><span class="footnote" id="fn1">**Unicode Hints** ([agda2-mode][]). `\cl ↝ ⌞`; `\clr ↝ ⌟`.</span>


<br>
<br>


[← Relations.Continuous](Relations.Continuous.html)
<span style="float:right;">[Relations.Truncation →](Relations.Truncation.html)</span>

{% include UALib.Links.md %}


<!-- We represent the property of being a preorder using a record type as follows.
module _ {𝓤 𝓦 : Universe} where
 record IsPreorder {A : 𝓤 ̇}(R : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field rfl : Refl R ; trans : Trans R
We define the type preorders as follows.
 Preorder : 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺ ̇
 Preorder A = Σ R ꞉ Rel A 𝓦 , IsPreorder R
-->
