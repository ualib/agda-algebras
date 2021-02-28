---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Continuous Relations</a>

This section presents the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `GenRel` to be the type `(I → A) → 𝓦 ̇` and we will call `GenRel` the type of **general relations**.  This generalizes the unary and binary relations we saw earlier in the sense that general relations can have arbitrarily large arities. However, relations of type `GenRel` are not completely general because they are defined over a single type.

Just as `Rel A 𝓦` was the "single-sorted" special case of the "multisorted" `REL A B 𝓦` type, so too will `GenRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇ ` of types, we may have a relation from `A i` to `A i'` to `A i''` to ….  We will refer to such relations as **dependent relations** because in order to define a type to represent them, we absolutely need depedent types.  The `DepRel` type that we define [below](Relations.General.html#dependent-relations) captures this completely general notion of relation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Continuous where

open import Relations.Discrete public

\end{code}

#### <a id="general-relations">General relations</a>

In this subsection we define the type `GenRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

\begin{code}

GenRel : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
GenRel I A 𝓦 = (I → A) → 𝓦 ̇

\end{code}


#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with general relations.

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


#### <a id="dependent-relations">Dependent relations</a>

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` may not even be enumerable).

\begin{code}

DepRel : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
DepRel I A 𝓦 = Π A → 𝓦 ̇

\end{code}

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

Above we made peace with lifts of general relations and what it means for such relations to be compatibile with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe} {I J : 𝓥 ̇} {A : I → 𝓤 ̇} where

 lift-dep-rel : DepRel I A 𝓦 → ((i : I) → (J → (A i))) → 𝓥 ⊔ 𝓦 ̇
 lift-dep-rel R 𝕒 = ∀ (j : J) → R (λ i → (𝕒 i) j)

 dep-compatible-fun : ((i : I) → (J → (A i)) → (A i)) → DepRel I A 𝓦 → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 dep-compatible-fun 𝕗 R  = ∀ 𝕒 → (lift-dep-rel R) 𝕒 → R (λ i → (𝕗 i)(𝕒 i))

\end{code}

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → (J → (A i))`.


--------------------------------------

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
