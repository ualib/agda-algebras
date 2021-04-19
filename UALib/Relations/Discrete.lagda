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

module Relations.Discrete where

open import Overture.Lifts public

\end{code}

In this module we define types that represent *unary* and *binary relations*.  We refer to these as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* we introduce in the next module ([Relations.Continuous][]). We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).


#### <a id="unary-relations">Unary relations</a>

In set theory, given two sets `A` and `P`, we say that `P` is a *subset* of `A`, and we write `P ⊆ A`, just in case `∀ x (x ∈ P → x ∈ A)`. We need a mechanism for representing this notion in Agda. A typical approach is to use a *predicate* type, denoted by `Pred`.

Given two universes `𝓤 𝓦` and a type `A : 𝓤 ̇`, the type `Pred A 𝓦` represents *properties* that inhabitants of type `A` may or may not satisfy.  We write `P : Pred A 𝓤` to represent the semantic concept of the collection of inhabitants of `A` that satisfy (or belong to) `P`. Here is the definition.<sup>[1](Relations.Discrete.html#fn1)</sup>

\begin{code}

Pred : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
Pred A 𝓦 = A → 𝓦 ̇

\end{code}

Later we consider predicates over the class of algebras in a given signature.  In the [Algebras][] module we will define the type `Algebra 𝓤 𝑆` of `𝑆`-algebras with domain type `𝓤 ̇`, and the type `Pred (Algebra 𝓤 𝑆) 𝓤`, will represent classes of `𝑆`-algebras with certain properties.


#### <a id="membership-and-inclusion-relations">Membership and inclusion relations</a>

Like the [Agda Standard Library][], the [UALib][] includes types that represent the *element inclusion* and *subset inclusion* relations from set theory. For example, given a predicate `P`, we may represent that  "`x` belongs to `P`" or that "`x` has property `P`," by writing either `x ∈ P` or `P x`.  The definition of `∈` is standard. Nonetheless, here it is.<sup>[1](Relations.Discrete.html#fn1)</sup>

\begin{code}

_∈_ : {A : 𝓤 ̇} → A → Pred A 𝓦 → 𝓦 ̇
x ∈ P = P x

\end{code}

The "subset" relation is denoted, as usual, with the `⊆` symbol.<sup>[1](Relations.Discrete.html#fn1)</sup>

\begin{code}

_⊆_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓩 → 𝓤 ⊔ 𝓦 ⊔ 𝓩 ̇
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

infix 4 _⊆_


\end{code}




#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later. The first is an inductive type representing *disjoint union*.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}
infixr 1 _⊎_ _∪_

data _⊎_ (A : 𝓤 ̇) (B : 𝓦 ̇) : 𝓤 ⊔ 𝓦 ̇ where
 inj₁ : (x : A) → A ⊎ B
 inj₂ : (y : B) → A ⊎ B

\end{code}

And this can be used to represent *union*, as follows.

\begin{code}

_∪_ : {A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓩 → Pred A (𝓦 ⊔ 𝓩)
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q


\end{code}

Next we define convenient notation for asserting that the image of a function (the first argument) is contained in a predicate (the second argument).

\begin{code}

Im_⊆_ : {A : 𝓤 ̇}{B : 𝓦 ̇} → (A → B) → Pred B 𝓩 → 𝓤 ⊔ 𝓩 ̇
Im f ⊆ S = ∀ x → f x ∈ S

\end{code}


The *empty set* is naturally represented by the *empty type*, `𝟘`.<sup>[2](Relations.Discrete#fn2), [4](Relations.Discrete#fn4)</sup>

\begin{code}

open import Empty-Type using (𝟘)

∅ : {A : 𝓤 ̇} → Pred A 𝓤₀
∅ _ = 𝟘

\end{code}


Before closing our little predicates toolbox, let's insert a type that provides a natural way to encode *singletons*.

\begin{code}

｛_｝ : {A : 𝓤 ̇} → A → Pred A _
｛ x ｝ = x ≡_

\end{code}


--------------------------------------


#### <a id="binary-relations">Binary Relations</a>

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model such a relation as a (unary) predicate over the type `A × A`, or as a relation of type `A → A → 𝓦 ̇` (for some universe 𝓦). Note, however, this is not the same as a unary predicate over the function type `A → A` since the latter has type  `(A → A) → 𝓦 ̇`, while a binary relation should have type `A → (A → 𝓦 ̇)`.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we define first and treat binary relations on a single `A` as a special case.

\begin{code}

REL : 𝓤 ̇ → 𝓦 ̇ → (𝓩 : Universe) → 𝓤 ⊔ 𝓦 ⊔ 𝓩 ⁺ ̇
REL A B 𝓩 = A → B → 𝓩 ̇

\end{code}

In the special case, where `𝓦 ≡ 𝓤` and `B ≡ A`, we have

\begin{code}

Rel : 𝓤 ̇ → (𝓩 : Universe) → 𝓤 ⊔ 𝓩 ⁺ ̇
Rel A 𝓩 = REL A A 𝓩

\end{code}


#### <a id="kernels">Kernels</a>

The *kernel* of `f : A → B` is defined informally by `{(x , y) ∈ A × A : f x = f y}`. This can be represented in type theory and Agda in a number of ways, each of which may be useful in a particular context. For example, we could define the kernel to be an inhabitant of a (binary) relation type, a (unary) predicate type, a (curried) Sigma type, or an (uncurried) Sigma type.


\begin{code}

module _ {A : 𝓤 ̇}{B : 𝓦 ̇} where

 ker : (A → B) → Rel A 𝓦
 ker g x y = g x ≡ g y

 kernel : (A → B) → Pred (A × A) 𝓦
 kernel g (x , y) = g x ≡ g y

 ker-sigma : (A → B) → 𝓤 ⊔ 𝓦 ̇
 ker-sigma g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

 ker-sigma' : (A → B) → 𝓤 ⊔ 𝓦 ̇
 ker-sigma' g = Σ (x , y) ꞉ (A × A) , g x ≡ g y

\end{code}


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented using any one of the following four types.<sup>[2](Relations.Discrete#fn2)</sup>

\begin{code}

module _ {A : 𝓤 ̇ } where

 𝟎 : Rel A 𝓤
 𝟎 x y = x ≡ y

 𝟎-pred : Pred (A × A) 𝓤
 𝟎-pred (x , y) = x ≡ y

 𝟎-sigma : 𝓤 ̇
 𝟎-sigma = Σ x ꞉ A , Σ y ꞉ A , x ≡ y

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

We define the following types representing *implication* for binary relations. (These are borrowed from the [Agda Standard Library][]; we merely translate them into [Type Topology][]/[UALib][] notation.)

\begin{code}

_on_ : {A : 𝓤 ̇}{B : 𝓦 ̇}{C : 𝓩 ̇} → (B → B → C) → (A → B) → (A → A → C)
R on g = λ x y → R (g x) (g y)

_⇒_ : {A : 𝓤 ̇}{B : 𝓦 ̇} → REL A B 𝓧 → REL A B 𝓨 → 𝓤 ⊔ 𝓦 ⊔ 𝓧 ⊔ 𝓨 ̇
P ⇒ Q = ∀ {i j} → P i j → Q i j

infixr 4 _⇒_

\end{code}

The `_on_` and `_⇒_` types combine to give a nice, general implication operation.

\begin{code}

_=[_]⇒_ : {A : 𝓤 ̇}{B : 𝓦 ̇} → Rel A 𝓧 → (A → B) → Rel B 𝓨 → 𝓤 ⊔ 𝓧 ⊔ 𝓨 ̇
P =[ g ]⇒ Q = P ⇒ (Q on g)

infixr 4 _=[_]⇒_

\end{code}


#### <a id="operation-type">Operation type and compatibility</a>

**Notation**. For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

In the next subsection, we will define types that are useful for asserting and proving facts about *compatibility* of *operations* with relations, but first we need a general type with which to represent operations.  Here is the definition, which we justify below.

\begin{code}

--The type of operations
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

\end{code}

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`. For example, the `I`-*ary projection operations* on `A` are represented as inhabitants of the type `Op I A` as follows.

\begin{code}

π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
π i x = x i

\end{code}

Now suppose `A` and `I` are types and let `𝑓 : Op I` and `R : Rel A 𝓦` be an `I`-ary operation and a binary relation on `A`, respectively. We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`,

&nbsp;&nbsp; `Π i ꞉ I , R (u i) (v i)` &nbsp; `→` &nbsp; `R (f u) (f v)`.<sup>[6](Relations.Discrete#fn6)</sup>

Here is how we implement this in the [UALib][].

\begin{code}

eval-rel : {A : 𝓤 ̇}{I : 𝓥 ̇} → Rel A 𝓦 → Rel (I → A)(𝓥 ⊔ 𝓦)
eval-rel R u v = Π i ꞉ _ , R (u i) (v i)

_|:_ : {A : 𝓤 ̇}{I : 𝓥 ̇} → Op I A → Rel A 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}

The function `eval-rel` "lifts" a binary relation to the corresponding `I`-ary relation.<sup>[5](Relations.Discrete#fn5)</sup>

In case it helps the reader, we note that instead of using the slick implication notation, we could have defined the `|:` relation more explicitly, like so.

\begin{code}

compatible-fun : {A : 𝓤 ̇}{I : 𝓥 ̇} → (f : Op I A)(R : Rel A 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
compatible-fun f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

\end{code}

However, this is a rare case in which the more elegant syntax used to define `|:` sometimes results in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> cf. `Relation/Unary.agda` in the [Agda Standard Library][].</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints** ([agda2-mode][]) `\.=` ↝ `≐`, `\u+` ↝ `⊎`, `\b0` ↝ `𝟘`, `\B0` ↝ `𝟎`.</span>

<sup>3</sup><span class="footnote" id="fn3">Agda also has a `postulate` mechanism that we could use, but this would require omitting the `--safe` pragma from the `OPTIONS` directive at the start of the module.</span>

<sup>4</sup><span class="footnote" id="fn4">The empty type is defined in the `Empty-Type` module of [Type Topology][] as an inductive type with no constructors: `data 𝟘 {𝓤} : 𝓤 ̇ where -- (empty body)`</span>

<sup>5</sup><span class="footnote" id="fn5">Initially we called the first function `lift-rel` because it "lifts" a binary relation on `A` to a binary relation on tuples of type `I → A`.  However, we renamed it `eval-rel` to avoid confusion with the universe level `Lift` type defined in the [Overture.Lifts][] module, or with `free-lift` ([Terms.Basic][]) which "lifts" a map defined on generators to a map on the thing being generated.</span>

<sup>6</sup><span class="footnote" id="fn6"> The symbol `|:` we use to denote the compatibility relation comes from Cliff Bergman's universal algebra textbook [Bergman (2012)][].

<br>
<br>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}





<!--

#### <a id="the-extensionality-axiom">The axiom of extensionality</a>

In type theory everything is represented as a type and, as we have just seen, this includes subsets.  Equality of types is a nontrivial matter, and thus so is equality of subsets when represented as unary predicates.  Fortunately, it is straightforward to write down the type that represents what we typically means in informal mathematics for two subsets to be equal. In the [UALib][] we denote this type by `≐` and define it as follows.<sup>[2](Relations.Discrete.html#fn2)</sup>

_≐_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓩 → 𝓤 ⊔ 𝓦 ⊔ 𝓩 ̇
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

infix 4 _≐_

Thus, a proof of `P ≐ Q` is a pair `(p , q)` where where `p : P ⊆ Q` and `q : Q ⊆ P` are proofs of the first and second inclusions, respectively. If `P` and `Q` are definitionally equal (i.e., `P ≡ Q`), then both `P ⊆ Q` and `Q ⊆ P` hold, so `P ≐ Q` also holds, as we now confirm.

Pred-≡ : {A : 𝓤 ̇}{P Q : Pred A 𝓦} → P ≡ Q → P ≐ Q
Pred-≡ refl = (λ z → z) , (λ z → z)

The converse is not provable in [MLTT][]. However, we can postulate that it holds as an axiom if we wish.  This is called the *axiom of extensionality* and a type that represents it is the following.
ext-axiom : 𝓤 ̇ → (𝓦 : Universe) →  𝓤 ⊔ 𝓦 ⁺ ̇
ext-axiom A 𝓦 = ∀ (P Q : Pred A 𝓦) → P ≐ Q → P ≡ Q

Note that the type `ext-axiom` does not itself postulate the axiom of extensionality.  It merely says what it is.  If we want to postulate it, we must assume we have a witness, or inhabitant of the type. We could do this in Agda in a number of ways, but probably the easiest is to simply add the witness as a parameter to a module, like so.<sup>[3](Relations.Discrete#fn3)</sup>

module ext-axiom-postulated {A : 𝓤 ̇} {ea : ext-axiom A 𝓦} where

Other notions of extensionality come up often in the [UALib][]; see, for example, [Overture.extensionality][] or [Relations.Truncation][].
-->
