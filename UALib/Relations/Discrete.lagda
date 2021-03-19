---
layout: default
title : UALib.Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="unary-relations">Discrete Relations</a>

This section presents the [UALib.Relations.Discrete][] module of the [Agda Universal Algebra Library][], which covers *unary* and *binary relations*.  We refer to these as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* we introduce in the next module ([Relations.Continuous][]). We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Discrete where

open import Prelude.Lifts public

\end{code}

#### <a id="unary-relations">Unary relations</a>

In set theory, given two sets `A` and `P`, we say that `P` is a *subset* of `A`, and we write `P ⊆ A`, just in case `∀ x (x ∈ P → x ∈ A)`. We need a mechanism for representing this notion in Agda. A typical approach is to use a *predicate* type, denoted by `Pred`.

Given two universes `𝓤 𝓦` and a type `A : 𝓤 ̇`, the type `Pred A 𝓦` represents *properties* that inhabitants of type `A` may or may not satisfy.  We write `P : Pred A 𝓤` to represent the semantic concept of the collection of inhabitants of `A` that satisfy (or belong to) `P`. Here is the definition.<sup>[1](Relations.Discrete.html#fn1)</sup>
(which is similar to the one found in the `Relation/Unary.agda` file of the [Agda Standard Library][]).

\begin{code}

module _ {𝓤 : Universe} where

 Pred : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Pred A 𝓦 = A → 𝓦 ̇

\end{code}

Later we consider predicates over the class of algebras in a given signature.  In the [Algebras][] module we will define the type `Algebra 𝓤 𝑆` of `𝑆`-algebras with domain type `𝓤 ̇`, and the type `Pred (Algebra 𝓤 𝑆) 𝓤`, will represent classes of `𝑆`-algebras with certain properties.


#### <a id="membership-and-inclusion-relations">Membership and inclusion relations</a>

Like the [Agda Standard Library][], the [UALib][] includes types that represent the *element inclusion* and *subset inclusion* relations from set theory. For example, given a predicate `P`, we may represent that  "`x` belongs to `P`" or that "`x` has property `P`," by writing either `x ∈ P` or `P x`.  The definition of `∈` is standard. Nonetheless, here it is.<sup>[1]</sup>

\begin{code}

module _ {𝓧 𝓨 : Universe} {A : 𝓧 ̇ } where

 _∈_ : A → Pred A 𝓨 → 𝓨 ̇
 x ∈ P = P x

\end{code}

The "subset" relation is denoted, as usual, with the `⊆` symbol (cf. `Relation/Unary.agda` in the [Agda Standard Library][]).

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } where

 _⊆_ : Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

 infix 4 _⊆_


\end{code}

#### <a id="the-extensionality-axiom">The axiom of extensionality</a>

In type theory everything is represented as a type and, as we have just seen, this includes subsets.  Equality of types is a nontrivial matter, and thus so is equality of subsets when represented as unary predicates.  Fortunately, it is straightforward to write down the type that represents what we typically means in informal mathematics for two subsets to be equal. In the [UALib][] we denote this type by `≐` and define it as follows.<sup>[2](Relations.Discrete.html#fn2)</sup>

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } where

 _≐_ : Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 infix 4 _≐_

\end{code}

Thus, a proof of `P ≐ Q` is a pair `(p , q)` where where `p : P ⊆ Q` and `q : Q ⊆ P` are proofs of the first and second inclusions, respectively. If `P` and `Q` are definitionally equal (i.e., `P ≡ Q`), then both `P ⊆ Q` and `Q ⊆ P` hold, so `P ≐ Q` also holds, as we now confirm.

\begin{code}

module _ {𝓧 𝓨 : Universe}{A : 𝓧 ̇} where

 Pred-≡ : {P Q : Pred A 𝓨} → P ≡ Q → P ≐ Q
 Pred-≡ refl = (λ z → z) , (λ z → z)

\end{code}

The converse is not provable in [MLTT][]. However, we can define its type and postulate that it holds axiomatically, if we wish.  This is called the *axiom of extensionality* and a type that represents this axiom is the following.

\begin{code}

module _ {𝓧 : Universe} where

 ext-axiom : 𝓧 ̇ → (𝓨 : Universe) → 𝓧 ⊔ 𝓨 ⁺ ̇
 ext-axiom A 𝓨 = ∀ (P Q : Pred A 𝓨) → P ≐ Q → P ≡ Q

\end{code}

Note that the type `ext-axiom` does not itself postulate the axiom of extensionality.  It merely defines the axiom.  If we want to postulate it, we must assume we have a witness, or inhabitant of the type. We could do this in Agda in a number of ways, but probably the easiest is to simply add the witness as a parameter to a module, like so.<sup>[3](Relations.Discrete#fn3)</sup>

\begin{code}

module ext-axiom-postulated {𝓧 𝓨 : Universe}{A : 𝓧 ̇} {ea : ext-axiom A 𝓨} where

\end{code}

We treat other notions of extensionality in the [Relations.Truncation][] module.



#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later. The first provides convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } {B : 𝓨 ̇ } where

 Im_⊆_ : (A → B) → Pred B 𝓩 → 𝓧 ⊔ 𝓩 ̇
 Im f ⊆ S = ∀ x → f x ∈ S

\end{code}

The following inductive type represents *disjoint union*.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}

data _⊎_ {𝓧 𝓨 : Universe}(A : 𝓧 ̇) (B : 𝓨 ̇) : 𝓧 ⊔ 𝓨 ̇ where
 inj₁ : (x : A) → A ⊎ B
 inj₂ : (y : B) → A ⊎ B

\end{code}

And this can be used to represent *union*, as follows.

\begin{code}

_∪_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇} → Pred A 𝓨 → Pred A 𝓩 → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

infixr 1 _⊎_ _∪_

\end{code}

The *empty set* is naturally represented by the *empty type*, `𝟘`.<sup>[2](Relations.Discrete#fn2), [4](Relations.Discrete#fn4)</sup>

\begin{code}

open import Empty-Type using (𝟘)

∅ : {𝓧 : Universe}{A : 𝓧 ̇} → Pred A 𝓤₀
∅ _ = 𝟘

\end{code}


Before closing our little predicates toolbox, let's insert a type that provides a natural way to represent *singletons*.

\begin{code}

｛_｝ : {𝓧 : Universe}{A : 𝓧 ̇} → A → Pred A _
｛ x ｝ = x ≡_

\end{code}


--------------------------------------


#### <a id="binary-relations">Binary Relations</a>

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model such a relation as a (unary) predicate over the type `A × A`, or as a relation of type `A → A → 𝓡 ̇` (for some universe 𝓡). Note, however, this is not the same as a unary predicate over the function type `A → A` since the latter has type  `(A → A) → 𝓡 ̇`, while a binary relation should have type `A → (A → 𝓡 ̇)`.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

\begin{code}

module _ {𝓤 𝓡 : Universe} where

 REL : 𝓤 ̇ → 𝓡 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓡 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇

\end{code}

In the special case, where `𝓤 ≡ 𝓡` and `A ≡ B`, we have

\begin{code}

module _ {𝓤 : Universe} where

 Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
 Rel A 𝓝 = REL A A 𝓝

\end{code}


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, a (unary) predicate type, a (curried) Sigma type, or an (uncurried) Sigma type.


\begin{code}

module _ {𝓤 𝓡 : Universe}{A : 𝓤 ̇}{B : 𝓡 ̇} where

 ker : (A → B) → Rel A 𝓡
 ker g x y = g x ≡ g y

 kernel : (A → B) → Pred (A × A) 𝓡
 kernel g (x , y) = g x ≡ g y

 ker-sigma : (A → B) → 𝓤 ⊔ 𝓡 ̇
 ker-sigma g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

 ker-sigma' : (A → B) → 𝓤 ⊔ 𝓡 ̇
 ker-sigma' g = Σ (x , y) ꞉ (A × A) , g x ≡ g y

\end{code}


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented using any one of the following four types.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}

module _ {𝓤 : Universe}{A : 𝓤 ̇ } where

 𝟎 : Rel A 𝓤
 𝟎 a b = a ≡ b

 𝟎-pred : Pred (A × A) 𝓤
 𝟎-pred (a , a') = a ≡ a'

 𝟎-sigma : 𝓤 ̇
 𝟎-sigma = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

 𝟎-sigma' : 𝓤 ̇
 𝟎-sigma' = Σ (x , y) ꞉ (A × A) , x ≡ y

\end{code}

The *total relation* over `A`, which in set theory is the full Cartesian product `A × A`, could be represented using the one-element type from the `Unit-Type` module of [Type Topology][], as follows.

\begin{code}

 open import Unit-Type using (𝟙)

 𝟏 : Rel A 𝓤₀
 𝟏 a b = 𝟙
\end{code}



#### <a id="implication">Implication</a>

We denote and define implication for binary predicates (relations) as follows. (These are borrowed from the [Agda Standard Library][]; we have merely translated them into [Type Topology][]/[UALib][] notation.)

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇}{B : 𝓨 ̇}{C : 𝓩 ̇} where

 _on_ : (B → B → C) → (A → B) → (A → A → C)
 R on g = λ x y → R (g x) (g y)


module _ {𝓦 𝓧 𝓨 𝓩 : Universe}{A : 𝓦 ̇ } {B : 𝓧 ̇ } where

 _⇒_ : REL A B 𝓨 → REL A B 𝓩 → 𝓦 ⊔ 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ⇒ Q = ∀ {i j} → P i j → Q i j

 infixr 4 _⇒_

\end{code}

The `_on_` and `_⇒_` types combine to give a nice, general implication operation.

\begin{code}

module _ {𝓦 𝓧 𝓨 𝓩 : Universe}{A : 𝓦 ̇ } {B : 𝓧 ̇ } where

 _=[_]⇒_ : Rel A 𝓨 → (A → B) → Rel B 𝓩 → 𝓦 ⊔ 𝓨 ⊔ 𝓩 ̇
 P =[ g ]⇒ Q = P ⇒ (Q on g)

 infixr 4 _=[_]⇒_

\end{code}


#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

Before discussing general and dependent relations, we pause to define some types that are useful for asserting and proving facts about *compatibility* of functions with binary relations. The first definition simply lifts a binary relation on `A` to a binary relation on tuples of type `I → A`. N.B. This is not to be confused with the sort of (universe) lifting that we defined in the [Prelude.Lifts][] module.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe}{I : 𝓥 ̇}{A : 𝓤 ̇} where

 lift-rel : Rel A 𝓦 → (I → A) → (I → A) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R u v = ∀ i → R (u i) (v i)

 compatible-fun : (f : (I → A) → A)(R : Rel A 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

\end{code}

We used the slick implication notation in the definition of `compatible-fun`, but we could have defined it more explicitly, like so.

\begin{code}

 compatible-fun' : (f : (I → A) → A)(R : Rel A 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun' f R  = ∀ u v → (lift-rel R) u v → R (f u) (f v)

\end{code}

However, this is a rare case in which the more elegant syntax may result in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">cf. `Relation/Unary.agda` in the [Agda Standard Library][].</span>

<sup>2</sup><span class="footnote" id="fn2">**Unicode Hints**. In [agda2-mode][] type `\doteq` or `\.=` to produce `≐`; type `\u+` or `\uplus` to produce `⊎`; type `\b0` to produce `𝟘`; type `\B0` to produce `𝟎`.</span>

<sup>3</sup><span class="footnote" id="fn3">Agda also has a `postulate` mechanism that we could use, but this would require omitting the `--safe` pragma from the `OPTIONS` directive at the start of the module.</span>

<sup>4</sup><span class="footnote" id="fn5">The empty type is defined in the `Empty-Type` module of [Type Topology][] as an inductive type with no constructors: `data 𝟘 {𝓤} : 𝓤 ̇ where -- (empty body)`</span>


<p></p>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}


