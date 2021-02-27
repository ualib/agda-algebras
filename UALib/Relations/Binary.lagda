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

Given types `A` and `B`, a binary relation from `A` to `B` is not the same as a unary predicate over the type `A → B`.  The binary relation has type `A → (B → 𝓝 ̇)` whereas a unary predicate over `A → B` has type `(A → B) → 𝓝 ̇` .

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


#### <a id="compatibility-with-binary-relations">Compatibility with binary relations</a>

Before discussing general and dependent relations, we pause to define some types that are useful for asserting and proving facts about *compatibility* of functions with binary relations. The first definition simply lifts a binary relation on `A` to a binary relation on tuples of type `I → A`. N.B. This is not to be confused with the sort of (universe) lifting that we defined in the [Prelude.Lifts][] module.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe}{I : 𝓥 ̇}{A : 𝓤 ̇} where

 lift-rel : Rel A 𝓦 → (I → A) → (I → A) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R 𝑎 𝑎' = ∀ i → R (𝑎 i) (𝑎' i)

 compatible-fun : (f : (I → A) → A)(R : Rel A 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

\end{code}

We used the slick implication notation in the definition of `compatible-fun`, but we could have defined it more explicitly, like so.

\begin{code}

 compatible-fun' : (f : (I → A) → A)(R : Rel A 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun' f R  = ∀ 𝑎 𝑎' → (lift-rel R) 𝑎 𝑎' → R (f 𝑎) (f 𝑎')

\end{code}

However, this is a rare case in which the more elegant syntax may result in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)


#### <a id="relations-of-arbitrary-arity">Relations of arbitrary arity</a>

Generalizing, we could view the types `Pred` and `Rel` as special cases of a type that represents relations of arbitrary arity.  To do so, we use a function type, say, `I → A`, to represent the collection of tuples of potential inhabitants of a relation. (This is the same approach we will use later in the [Algebras.Signatures][] module to represent operations of arbitrary arity in signatures of algebraic structures.)

In this subsection we define the type `GenRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

\begin{code}

GenRel : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
GenRel I A 𝓦 = (I → A) → 𝓦 ̇

\end{code}

While we're at it, why not exploit the power of dependent types to define a completely general relation type?  That is, we could let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` need not be enumerable).

\begin{code}

DepRel : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
DepRel I A 𝓦 = Π A → 𝓦 ̇

\end{code}

We call `DepRel` the type of **dependent relations**.


#### <a id="compatibility-with-general-and-dependent-relations">Compatibility with general and dependent relations</a>

Finally, we define types that are useful for asserting and proving facts about *compatibility* of functions with general and dependent relations.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe} {I J : 𝓥 ̇} {A : 𝓤 ̇} where

 lift-gen-rel : GenRel I A 𝓦 → (I → (J → A)) → 𝓥 ⊔ 𝓦 ̇
 lift-gen-rel R 𝕒 = ∀ (j : J) → R (λ i → (𝕒 i) j)

 gen-compatible-fun : (I → (J → A) → A) → GenRel I A 𝓦 → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 gen-compatible-fun 𝕗 R  = ∀ 𝕒 → (lift-gen-rel R) 𝕒 → R (λ i → (𝕗 i) (𝕒 i))

\end{code}

In the definition of `gen-compatible-fun`, we let Agda infer the type of `𝕒`, which is `I → (J → A)`.

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics instead of the semantics.  In fact, we should probably pause here to discuss these semantics, lest the more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝕒 : I → (J → A)` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, recall that a general relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Next consider the function `lift-gen-rel`.  For each general relation `R`, the type `lift-gen-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝕒 : I → (J → A)` such that `lift-gen-rel R 𝕒` holds.

It helps to visualize such `J`-tuples as columns and imagine for simplicity that `J` is a finite set, say, `{1, 2, ..., J}`.  Picture a couple of these columns, say, the i-th and k-th, like so.

```
𝕒 i 1      𝕒 k 1
𝕒 i 2      𝕒 k 2
𝕒 i 3      𝕒 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝕒 i J      𝕒 k J
```

Now `lift-gen-rel R 𝕒` is defined by `∀ j → R (λ i → (𝕒 i) j)` which represents the assertion that each row of the `I` columns shown above (which evidently is an `I`-tuple) belongs to the original relation `R`.

Next, let's dissect the definition of `gen-compatible-fun`.  Here, `𝕗 : I → (J → A) → A` denotes an `I`-tuple of `J`-ary operations on `A`.  That is, for each `i : I`, the function `𝕗 i` takes a `J`-tuple `𝕒 i : J → A` and evaluates to some `(𝕗 i) (𝕒 i) : A`.

Finally, digest all the types involved in these definitions and note how nicely they align (as they must if type-checking is to succeed!).  For example, `𝕒 : I → (J → A)` is precisely the type on which the relation `lift-gen-rel R` is defined.

Having made peace with lifts of general relations and what it means for them to be compatibile with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe} {I J : 𝓥 ̇} {A : I → 𝓤 ̇} where

 lift-dep-rel : DepRel I A 𝓦 → ((i : I) → (J → (A i))) → 𝓥 ⊔ 𝓦 ̇
 lift-dep-rel R 𝕒 = ∀ (j : J) → R (λ i → (𝕒 i) j)

 dep-compatible-fun : ((i : I) → (J → (A i)) → (A i)) → DepRel I A 𝓦 → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 dep-compatible-fun 𝕗 R  = ∀ 𝕒 → (lift-dep-rel R) 𝕒 → R (λ i → (𝕗 i)(𝕒 i))

\end{code}

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → (J → (A i))`.


--------------------------------------

[← Relations.Unary](Relations.Unary.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
