---
layout: default
title : Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="unary-relations">Discrete Relations</a>

This is the [Relations.Discrete][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Core using (REL; Rel; _⇒_;_=[_]⇒_)
open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝)

open import Overture.Preliminaries using (Type; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; -Σ)

module Relations.Discrete where

\end{code}

#### <a id="unary-relations">Unary relations</a>

In set theory, given two sets `A` and `P`, we say that `P` is a *subset* of `A`, and we write `P ⊆ A`, just in case `∀ x (x ∈ P → x ∈ A)`. We need a mechanism for representing this notion in Agda. A typical approach is to use a *predicate* type, denoted by `Pred`.

Given two universes `𝓤 𝓦` and a type `A : Type 𝓤`, the type `Pred A 𝓦` represents *properties* that inhabitants of type `A` may or may not satisfy.  We write `P : Pred A 𝓤` to represent the semantic concept of the collection of inhabitants of `A` that satisfy (or belong to) `P`. Here is the definition.<sup>[1](Relations.Discrete.html#fn1)</sup>

```agda
 Pred : Type 𝓤 → (𝓦 : Level) → Type(𝓤 ⊔ lsuc 𝓦)
 Pred A 𝓦 = A → Type 𝓦
```


Later we consider predicates over the class of algebras in a given signature.  In the [Algebras][] module we will define the type `Algebra 𝓤 𝑆` of `𝑆`-algebras with domain type `Type 𝓤`, and the type `Pred (Algebra 𝓤 𝑆) 𝓤`, will represent classes of `𝑆`-algebras with certain properties.


#### <a id="membership-and-inclusion-relations">Membership, inclusion, and unions</a>

The [UniversalAlgebra][] imports types that represent the *element inclusion* and *subset inclusion* relations from the [Agda Standard Library][]. For example, given a predicate `P`, we may represent that  "`x` belongs to `P`" or that "`x` has property `P`," by writing either `x ∈ P` or `P x`.  The "subset" relation is denoted, as usual, by the `⊆` symbol. The definitions of `∈` and `⊆`is standard.

```agda
 _∈_ : {A : Type 𝓤} → A → Pred A 𝓦 → Type 𝓦
 x ∈ P = P x

 _⊆_ : {A : Type 𝓤 } → Pred A 𝓦 → Pred A 𝓩 → Type (𝓤 ⊔ 𝓦 ⊔ 𝓩)
 P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q
```

Unions are represented using the following inductive type.<sup>[2](Relations.Discrete#fn2)</sup>

```agda
 data _⊎_ (A : Type 𝓤) (B : Type 𝓦) : Type (𝓤 ⊔ 𝓦) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

 _∪_ : {A : Type 𝓤} → Pred A 𝓦 → Pred A 𝓩 → Pred A (𝓦 ⊔ 𝓩)
 P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q
```


\end{code}

Next we define convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

\begin{code}

Im_⊆_ : {A : Type 𝓤}{B : Type 𝓦} → (A → B) → Pred B 𝓩 → Type (𝓤 ⊔ 𝓩)
Im f ⊆ S = ∀ x → f x ∈ S

\end{code}


The *empty set* is naturally represented by the *empty type*, `∅`.<sup>[2](Relations.Discrete#fn2), [4](Relations.Discrete#fn4)</sup>


```agda
 ∅ : {A : Type 𝓤} → Pred A lzero
 ∅ = λ _ → ⊥
```


Here's a type that provides a natural way to encode *singleton* sets.

```agda
｛_｝ : {A : Type 𝓤} → A → Pred A 𝓤
｛ x ｝ = x ≡_
```


--------------------------------------


#### <a id="binary-relations">Binary Relations</a>

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model such a relation as a (unary) predicate over the type `A × A`, or as a relation of type `A → A → Type 𝓦` (for some universe 𝓦). Note, however, this is not the same as a unary predicate over the function type `A → A` since the latter has type  `(A → A) → Type 𝓦`, while a binary relation should have type `A → (A → Type 𝓦)`.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

```agda
 REL : Type 𝓤 → Type 𝓦 → (𝓩 : Level) → Type (𝓤 ⊔ 𝓦 ⊔ lsuc 𝓩)
 REL A B 𝓩 = A → B → Type 𝓩
```

In the special case where `𝓦 ≡ 𝓤` and `B ≡ A` we have

```agda
 Rel : Type 𝓤 → (𝓩 : Level) → Type (𝓤 ⊔ lsuc 𝓩)
 Rel A 𝓩 = REL A A 𝓩
```


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, a (unary) predicate type, a (curried) Sigma type, or an (uncurried) Sigma type.


\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where

 ker : (A → B) → Rel A 𝓦
 ker g x y = g x ≡ g y

 kernel : (A → B) → Pred (A × A) 𝓦
 kernel g (x , y) = g x ≡ g y

 ker-sigma : (A → B) → Type (𝓤 ⊔ 𝓦)
 ker-sigma g = Σ[ x ꞉ A ] Σ[ y ꞉ A ] g x ≡ g y

 ker-sigma' : (A → B) → Type (𝓤 ⊔ 𝓦)
 ker-sigma' g = Σ[ (x , y) ꞉ (A × A) ] g x ≡ g y

\end{code}


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented using any one of the following four types.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}

module _ {A : Type 𝓤 } where

 𝟎 : Rel A 𝓤
 𝟎 x y = x ≡ y

 𝟎-pred : Pred (A × A) 𝓤
 𝟎-pred (x , y) = x ≡ y

 𝟎-sigma : Type 𝓤
 𝟎-sigma = Σ[ x ꞉ A ] Σ[ y ꞉ A ] x ≡ y

 𝟎-sigma' : Type 𝓤
 𝟎-sigma' = Σ[ (x , y) ꞉ A × A ] x ≡ y

\end{code}



#### <a id="implication">Implication</a>

The [Agda Standard Library][] defines the following types representing *implication* for binary relations.

```agda
 _on_ : {A : Type 𝓤}{B : Type 𝓦}{C : Type 𝓩} → (B → B → C) → (A → B) → (A → A → C)
 R on g = λ x y → R (g x) (g y)

 _⇒_ : {A : Type 𝓤}{B : Type 𝓦} → REL A B 𝓧 → REL A B 𝓨 → Type(𝓤 ⊔ 𝓦 ⊔ 𝓧 ⊔ 𝓨)
 P ⇒ Q = ∀ {i j} → P i j → Q i j

 infixr 4 _⇒_
```

The `_on_` and `_⇒_` types combine to give a nice, general implication operation.


```agda
 _=[_]⇒_ : {A : Type 𝓤}{B : Type 𝓦} → Rel A 𝓧 → (A → B) → Rel B 𝓨 → Type(𝓤 ⊔ 𝓧 ⊔ 𝓨)
 P =[ g ]⇒ Q = P ⇒ (Q on g)

 infixr 4 _=[_]⇒_
```


#### <a id="operation-type">Operation type and compatibility</a>

**Notation**. For consistency and readability, throughout the [UniversalAlgebra][] library we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

In the next subsection, we will define types that are useful for asserting and proving facts about *compatibility* of *operations* with relations, but first we need a general type with which to represent operations.  Here is the definition, which we justify below.

\begin{code}

--The type of operations
Op : Type 𝓥 → Type 𝓤 → Type(𝓤 ⊔ 𝓥)
Op I A = (I → A) → A

\end{code}

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type 𝓥`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

\begin{code}

π : {I : Type 𝓥 } {A : Type 𝓤 } → I → Op I A
π i x = x i

\end{code}

Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A 𝓦` be an `I`-ary operation and a binary relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`,

&nbsp;&nbsp; `Π i ꞉ I , R (u i) (v i)` &nbsp; `→` &nbsp; `R (f u) (f v)`.<sup>[6](Relations.Discrete#fn6)</sup>

Here is how we implement this in the [UniversalAlgebra][] library.

\begin{code}

eval-rel : {A : Type 𝓤}{I : Type 𝓥} → Rel A 𝓦 → Rel (I → A)(𝓥 ⊔ 𝓦)
eval-rel R u v = ∀ i → R (u i) (v i)

_|:_ : {A : Type 𝓤}{I : Type 𝓥} → Op I A → Rel A 𝓦 → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}

The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.<sup>[5](Relations.Discrete#fn5)</sup>

In case it helps the reader, we note that instead of using the slick implication notation, we could have defined the `|:` relation more explicitly, like so.

\begin{code}

compatible-op : {A : Type 𝓤}{I : Type 𝓥} → (f : Op I A)(R : Rel A 𝓦) → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

\end{code}

However, this is a rare case in which the more elegant syntax used to define `|:` sometimes results in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> cf. `Relation/Unary.agda` in the [Agda Standard Library][].</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints** ([agda2-mode][]) `\.=` ↝ `≐`, `\u+` ↝ `⊎`, `\b0` ↝ `𝟘`, `\B0` ↝ `𝟎`.</span>

<sup>3</sup><span class="footnote" id="fn3">Agda also has a `postulate` mechanism that we could use, but this would require omitting the `--safe` pragma from the `OPTIONS` directive at the start of the module.</span>

<sup>4</sup><span class="footnote" id="fn4">The empty type is defined in the `Empty-Type` module of [Type Topology][] as an inductive type with no constructors: `data 𝟘 {𝓤} : Type 𝓤 where -- (empty body)`</span>

<sup>5</sup><span class="footnote" id="fn5">Initially we called the first function `lift-rel` because it "lifts" a binary relation on `A` to a binary relation on tuples of type `I → A`.  However, we renamed it `eval-rel` to avoid confusion with the universe level `Lift` type defined in the [Overture.Lifts][] module, or with `free-lift` ([Terms.Basic][]) which "lifts" a map defined on generators to a map on the thing being generated.</span>

<sup>6</sup><span class="footnote" id="fn6"> The symbol `|:` we use to denote the compatibility relation comes from Cliff Bergman's universal algebra textbook [Bergman (2012)][].

<br>
<br>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}



<!-- UNUSED STUFF

The *total relation* over `A`, which in set theory is the full Cartesian product `A × A`, could be represented using the one-element type from the `Unit-Type` module of [Type Topology][], as follows.

 open import Unit-Type using (𝟙)
 𝟏 : Rel A lzero
 𝟏 a b = 𝟙
-->
