---
layout: default
title : UALib.Relations.Binary module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="relations-binary-and-higher">Relations, Binary and Beyond</a>

This section presents the [UALib.Relations.Binary][] module of the [Agda Universal Algebra Library][].

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model these as predicates over the type `A × A`, or as relations of type `A → A → 𝓡 ̇` (for some universe 𝓡). We define these below.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Binary where

open import Relations.Unary public

module _ {𝓤 : Universe} where

 REL : {𝓡 : Universe} → 𝓤 ̇ → 𝓡 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓡 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇

\end{code}


#### <a id="kernels">Kernels</a>

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

#### <a id="examples">Examples</a>

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


 open import MGS-MLTT using (𝟙)

 -- The total relation A × A
 𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
 𝟏 a b = 𝟙
\end{code}



#### <a id="implication">Implication</a>

We denote and define implication for binary predicates (relations) as follows.

\begin{code}

-- (syntactic sugar)
_on_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇}{B : 𝓨 ̇}{C : 𝓩 ̇}
 →     (B → B → C) → (A → B) → (A → A → C)

R on g = λ x y → R (g x) (g y)


_⇒_ : {𝓦 𝓧 𝓨 𝓩 : Universe}{A : 𝓦 ̇ } {B : 𝓧 ̇ }
 →    REL A B 𝓨 → REL A B 𝓩 → 𝓦 ⊔ 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇

P ⇒ Q = ∀ {i j} → P i j → Q i j

infixr 4 _⇒_

\end{code}

We can combine `_on_` and _⇒_ to define a nice, general implication operation. This is borrowed from the [Agda Standard Library][]; we have merely translated into [Type Topology][]/[UALib][] notation.

\begin{code}

_=[_]⇒_ : {𝓦 𝓧 𝓨 𝓩 : Universe}{A : 𝓦 ̇ } {B : 𝓧 ̇ }
 →        Rel A 𝓨 → (A → B) → Rel B 𝓩 → 𝓦 ⊔ 𝓨 ⊔ 𝓩 ̇

P =[ g ]⇒ Q = P ⇒ (Q on g)

infixr 4 _=[_]⇒_

\end{code}


#### <a id="relations-of-arbitrary-arity>Relations of arbitrary arity</a>

Generalizing, we could view the types `Pred` and `Rel` as special cases of a type that represents relations of arbitrary arity.  To do so, we use a function type, say, `I → A`, to represent the collection of tuples of potential inhabitants of a relation. (This is the same approach we will use later in the [Algebras.Signatures][] module) to represent operations of arbitrary arity in signatures of algebraic structures.)  Below we define the type `GenRel` to represents a predicate or relation of arbitrary arity of a single type `A`. We call `GenRel` the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing **arities** of relations or operations.

\begin{code}

GenRel : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
GenRel I A 𝓦 = (I → A) → 𝓦 ̇

\end{code}

While we're at it, why not use the full power of dependent types to define a completely general relation type?  That is, we could let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` need not be enumerable).

\begin{code}

DepRel : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
DepRel I A 𝓦 = Π A → 𝓦 ̇

\end{code}

We call `DepRel` the type of **dependent relations**.

--------------------------------------

[← Relations.Unary](Relations.Unary.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
