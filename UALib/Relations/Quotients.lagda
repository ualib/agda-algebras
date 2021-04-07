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

A binary relation is called a *preorder* if it is reflexive and transitive. An *equivalence relation* is a symmetric preorder.


\begin{code}

module _ {𝓤 𝓦 : Universe} where

 record IsPreorder {A : 𝓤 ̇}(_≈_ : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field rfl : Refl _≈_; trans : Trans _≈_

 Preorder : (A : 𝓤 ̇) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Preorder A = Σ R ꞉ Rel A 𝓦 , IsPreorder R

 record IsEquivalence {A : 𝓤 ̇}(_≈_ : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field rfl : Refl _≈_; sym : Symm _≈_; trans : Trans _≈_

 Equivalence : (A : 𝓤 ̇) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Equivalence A = Σ R ꞉ Rel A 𝓦 , IsEquivalence R

\end{code}

An easy first example of an equivalence relation is the kernel of any function.

\begin{code}

 ker-IsEquivalence : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B) → IsEquivalence (ker f)
 ker-IsEquivalence f = record { rfl = refl; sym = λ z → ≡-sym z ; trans = λ p q → ≡-trans p q }

\end{code}

#### Truncated preorders and equivalences

Using the `is-subsingleton-valued` type defined earlier, we can define the type of preorders and equivalences that have "unique identity proofs" as follows.

\begin{code}

 -- truncated preorder type
 record IsPreord {A : 𝓤 ̇}(R : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field is-preorder : IsPreorder R
        is-truncated : is-subsingleton-valued R

 Preord : (A : 𝓤 ̇) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Preord A = Σ R ꞉ Rel A 𝓦 , IsPreord R

 -- truncated equivalence relation type
 record IsEqv {A : 𝓤 ̇}(_≈_ : Rel A 𝓦) : 𝓤 ⊔ 𝓦 ̇ where
  field is-equivalence : IsEquivalence _≈_
        is-truncated : is-subsingleton-valued _≈_

 Eqv : (A : 𝓤 ̇) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Eqv A = Σ R ꞉ Rel A 𝓦 , IsEqv R

\end{code}



#### <a id="equivalence-classes">Equivalence classes (blocks)</a>

If R is an equivalence relation on A, then for each `𝑎 : A`, there is an *equivalence class* (or *equivalence block*) containing 𝑎, which we denote and define by [ 𝑎 ] R := all `𝑏 : A` such that R 𝑎 𝑏.

\begin{code}

 [_]_ : {A : 𝓤 ̇} → A → Rel A 𝓦 → Pred A 𝓦
 [ 𝑎 ] R = λ x → R 𝑎 x

 infix 60 [_]_

\end{code}


Thus, `x ∈ [ a ] R` if and only if `R a x`, as desired.  We often refer to `[ 𝑎 ] R` as the `R`-*block containing* `𝑎`. We represent an `R`-blocks by the collection of its members, as follows.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ a ꞉ A , C ≡ [ a ] R

\end{code}

Thus, a a block of `R` is a pair `(C , p)` consisting of a predicate `C` and a proof `p : IsBlock R C` such that `reps p` is a dependent pair `(a , q)`, with ` a : A` and such that `q` is a proof of `C ≡ [ a ] R`.

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ 𝑎 ] R ∣  𝑎 : A}` of all `R`-blocks.

\begin{code}

 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓦 → 𝓤 ⊔ (𝓦 ⁺) ̇
 A / R = Σ C ꞉ Pred A 𝓦 , IsBlock C {R}

 infix -1 _/_

\end{code}

We use the following type to represent an `R`-block with a designated representative.

\begin{code}

 ⟪_⟫ : {A : 𝓤 ̇} → A → {R : Rel A 𝓦} → A / R
 ⟪ a ⟫ {R} = [ a ] R , (a  , refl)

 infix 60 ⟪_⟫

\end{code}

This serves as a kind of *introduction rule*.  Dually, the next type provides an *elimination rule*. Here `C` is a predicate and `p` is a proof of `C ≡ [ a ] R`.<sup>[1](Relations.Quotients.html#fn1)</sup>

\begin{code}

 ⌞_⌟ : {A : 𝓤 ̇}{R : Rel A 𝓦} → A / R  → A
 ⌞ C , (a , p) ⌟ = a

\end{code}

Later we will need the following tools for working with the quotient types defined above.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{x y : A}{R : Rel A 𝓦} where

 open IsEquivalence
 /-subset : IsEquivalence R → R x y →  [ x ] R  ⊆  [ y ] R
 /-subset Req Rxy {z} Rxz = (trans Req) ((sym Req) Rxy) Rxz

 /-supset : IsEquivalence R → R x y →  [ y ] R ⊆ [ x ] R
 /-supset Req Rxy {z} Ryz = (trans Req) Rxy Ryz

 /-≐ : IsEquivalence R → R x y →  [ x ] R  ≐  [ y ] R
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


