---
layout: default
title : UALib.Relations.Binary module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="binary-relation-and-kernel-types">Binary Relation and Kernel Types</a>

This section presents the [UALib.Relations.Binary][] module of the [Agda Universal Algebra Library][].

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model these as predicates over the type `A × A`, or as relations of type `A → A → 𝓡 ̇` (for some universe 𝓡). We define these below.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Relations.Binary where

open import UALib.Relations.Unary public

module _ {𝓤 : Universe} where

 REL : {𝓡 : Universe} → 𝓤 ̇ → 𝓡 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓡 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇

\end{code}


#### Kernels

The kernel of a function can be defined in many ways. For example,

\begin{code}

 KER : {𝓡 : Universe} {A : 𝓤 ̇ } {B : 𝓡 ̇ } → (A → B) → 𝓤 ⊔ 𝓡 ̇
 KER {𝓡} {A} g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

\end{code}

or as a unary relation (predicate) over the Cartesian product,

\begin{code}

 KER-pred : {𝓡 : Universe} {A : 𝓤 ̇}{B : 𝓡 ̇} → (A → B) → Pred (A × A) 𝓡
 KER-pred g (x , y) = g x ≡ g y

\end{code}

or as a relation from `A` to `B`,

\begin{code}

 Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
 Rel A 𝓝 = REL A A 𝓝

 KER-rel : {𝓡 : Universe}{A : 𝓤 ̇ } {B : 𝓡 ̇ } → (A → B) → Rel A 𝓡
 KER-rel g x y = g x ≡ g y

\end{code}

#### <a id="binary-examples">Examples</a>

\begin{code}
 ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
 ker = KER{𝓤}

 ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
 ker-rel = KER-rel {𝓤}

 ker-pred : {A B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
 ker-pred = KER-pred {𝓤}

 --The identity relation.
 𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎 {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

 --...as a binary relation...
 𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
 𝟎-rel a b = a ≡ b

 --...as a binary predicate...
 𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
 𝟎-pred (a , a') = a ≡ a'

 𝟎-pred' : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎-pred' {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

 --...on the domain of an algebra...

 𝟎-alg-rel : {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝓤 𝑆} → 𝓤 ̇
 𝟎-alg-rel {𝑨 = 𝑨} = Σ a ꞉ ∣ 𝑨 ∣ , Σ b ꞉ ∣ 𝑨 ∣ , a ≡ b

 -- The total relation A × A
 𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
 𝟏 a b = 𝟙
\end{code}

#### Properties of binary relations

\begin{code}
 reflexive : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 reflexive _≈_ = ∀ x → x ≈ x

 symmetric : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 transitive : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

 is-subsingleton-valued : {𝓡 : Universe}{A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)
\end{code}

#### Binary relation truncation

[The section on Truncation](UALib.Preface.html#truncation) in the preface describes the concept of truncation for "proof-relevant" mathematics.

Given a binary relation `P`, it may be necessary or desirable to assume that there is at most one way to prove that a given pair of elements is `P`-related.  This may be called "proof-irrelevance" since, if we have two proofs of `x P y`, then we can assume that the proofs are indistinguishable or that any distinctions are irrelevant.  We enforce this strong assumption of truncation at the first level in the following definition using MHE's `is-subsingleton` type: we say that `(x , y)` belongs to `P` or `x` and `y` are `P`-related if and only if both P x y` and `is-subsingleton (P x y)`.

\begin{code}

 Rel₀ : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
 Rel₀ A 𝓝 = Σ P ꞉ (A → A → 𝓝 ̇) , ∀ x y → is-subsingleton (P x y)

\end{code}

We will define a **set** to be a type `X` with the following property: for all `x y : X` there is at most one proof that `x ≡ y`.  In other words, `X` is a set if and only if it satisfies

```agda
∀ x y : X → is-subsingleton(x ≡ y)
```

#### <a id="implication">Implication</a>

We denote and define implication as follows.

\begin{code}

-- (syntactic sugar)
_on_ : {𝓤 𝓥 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓥 ̇}{C : 𝓦 ̇}
 →     (B → B → C) → (A → B) → (A → A → C)

_*_ on g = λ x y → g x * g y


_⇒_ : {𝓤 𝓥 𝓦 𝓧 : Universe}{A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →    REL A B 𝓦 → REL A B 𝓧 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ̇

P ⇒ Q = ∀ {i j} → P i j → Q i j

infixr 4 _⇒_

\end{code}

Here is a more general version that we borrow from the standard library and translate into MHE/UALib notation.

\begin{code}

_=[_]⇒_ : {𝓤 𝓥 𝓡 𝓢 : Universe}{A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →        Rel A 𝓡 → (A → B) → Rel B 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇

P =[ g ]⇒ Q = P ⇒ (Q on g)

infixr 4 _=[_]⇒_

\end{code}


--------------------------------------

[← UALib.Relations.Unary](UALib.Relations.Unary.html)
<span style="float:right;">[UALib.Relations.Equivalences →](UALib.Relations.Equivalences.html)</span>

{% include UALib.Links.md %}
