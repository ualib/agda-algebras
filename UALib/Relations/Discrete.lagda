---
layout: default
title : UALib.Relations.Discrete module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="unary-relations">Discrete Relations</a>

This section presents the [UALib.Relations.Discrete][] module of the [Agda Universal Algebra Library][], which covers *unary* and *binary relations*.  We refer to these as "discrete relations" to contrast them with the *general* and *dependent relations* we take up in the next module ([Relations.Continuous][]). We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Discrete where

open import Prelude.Lifts public

\end{code}

#### <a id="unary-relations">Unary relations</a>

We need a mechanism for implementing the notion of subsets in Agda. A typical one is called `Pred` (for predicate). More generally, `Pred A 𝓤` can be viewed as the type of a property that elements of type `A` might satisfy. We write `P : Pred A 𝓤` to represent the semantic concept of a collection of elements of type `A` that satisfy the property `P`.

Here is the definition, which is similar to the one found in the`Relation/Unary.agda` file of the [Agda Standard Library][].

\begin{code}

module _ {𝓤 : Universe} where

 Pred : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Pred A 𝓦 = A → 𝓦 ̇

\end{code}



Below we will often consider predicates over the class of all algebras of a particular type. We will define the type of algebras `Algebra 𝓤 𝑆` (for some universe level 𝓤). Like all types, `Algebra 𝓤 𝑆` itself has a type which happens to be 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ (as we will see in the module [UALib.Algebras](UALib.Algebras.Algebras.html)). Therefore, the type of `Pred (Algebra 𝓤 𝑆) 𝓤` will be 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ as well.

The inhabitants of the type `Pred (Algebra 𝓤 𝑆)` 𝓤 are maps of the form `𝑨 → 𝓤 ̇`; given an algebra `𝑨 : Algebra 𝓤 𝑆`, we have `Pred 𝑨 𝓤 = 𝑨 → 𝓤 ̇`.



#### <a id="membership-and-inclusion-relations">Membership and inclusion relations</a>

We introduce notation so that we may indicate that `x` "belongs to" or "inhabits" at type `P`, or that `x` "has property" `P`, by writing either `x ∈ P` or `P x` (cf. `Relation/Unary.agda` in the [Agda Standard Library][]).

\begin{code}

module _ {𝓧 𝓨 : Universe} {A : 𝓧 ̇ } where

 _∈_ : A → Pred A 𝓨 → 𝓨 ̇
 x ∈ P = P x

 open import MGS-MLTT using (¬) public

 _∉_ : A → Pred A 𝓨 → 𝓨 ̇
 x ∉ P = ¬ (x ∈ P)

 infix 4 _∈_ _∉_

\end{code}

The "subset" relation is denoted, as usual, with the `⊆` symbol (cf. `Relation/Unary.agda` in the [Agda Standard Library][]).

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } where

 _⊆_ : Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

 infix 4 _⊆_


module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } where

 _⊇_ : Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ⊇ Q = Q ⊆ P

 infix 4 _⊇_

\end{code}

#### <a id="the-extensionality-axiom">The axiom of extensionality</a>

In type theory everything is represented as a type and, as we have just seen, this includes subsets.  Equality of types is a nontrivial matter, and thus so is equality of subsets when represented as unary predicates.  Fortunately, it is straightforward to write down the type that represents what we typically means in informal mathematics for two subsets to be equal. In the [UALib][] we denote this type by `≐` and define it as follows.<sup>[1](Relations.Discrete.html#fn1)</sup>

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } where

 _≐_ : Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 infix 4 _≐_

\end{code}

Thus, a proof of `P ≐ Q` is a pair `(p , q)` where `p` is a proof of the first inclusion (that is, `p : P ⊆ Q`)  and `q` is a proof of the second.

If `P` and `Q` are definitionally equal (i.e., `P ≡ Q`), then of course both `P ⊆ Q` and `P ⊇ Q` hold, so `P ≐ Q` holds.

\begin{code}

module _ {𝓧 𝓨 : Universe}{A : 𝓧 ̇} where

 Pred-≡ : {P Q : Pred A 𝓨} → P ≡ Q → P ≐ Q
 Pred-≡ refl = (λ z → z) , (λ z → z)

\end{code}

The converse is not provable in [MLTT][]. However, we can define its type and postulate that it holds axiomatically, if we wish.  This is called the *axiom of extensionality*.

\begin{code}

module _ {𝓧 : Universe} where

 ext-axiom : 𝓧 ̇ → (𝓨 : Universe) → 𝓧 ⊔ 𝓨 ⁺ ̇
 ext-axiom A 𝓨 = ∀ (P Q : Pred A 𝓨) → P ≐ Q → P ≡ Q

\end{code}

We treat this axiom in greater generally and detail in the [Relations.Truncation][] module.



#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later.  Hopefully the meaning of each is self-explanatory.

\begin{code}
module _ {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } {B : 𝓨 ̇ } where

 Im_⊆_ : (A → B) → Pred B 𝓩 → 𝓧 ⊔ 𝓩 ̇
 Im_⊆_ f S = ∀ x → f x ∈ S


img : {𝓧 : Universe}{X Y : 𝓧 ̇ }(f : X → Y)(P : Pred Y 𝓧) → Im f ⊆ P → X → Σ P
img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁


module _ {𝓧 𝓨 : Universe}{A : 𝓧 ̇} where

 Pred-refl : {P Q : Pred A 𝓨} → P ≡ Q → (a : A) → a ∈ P → a ∈ Q
 Pred-refl refl _ = λ z → z

 Pred-≡→⊆ : {P Q : Pred A 𝓨} → P ≡ Q → (P ⊆ Q)
 Pred-≡→⊆ refl = (λ z → z)

 Pred-≡→⊇ : {P Q : Pred A 𝓨} → P ≡ Q → (P ⊇ Q)
 Pred-≡→⊇ refl = (λ z → z)


-- Disjoint Union.
data _⊎_ {𝓧 𝓨 : Universe}(A : 𝓧 ̇) (B : 𝓨 ̇) : 𝓧 ⊔ 𝓨 ̇ where
 inj₁ : (x : A) → A ⊎ B
 inj₂ : (y : B) → A ⊎ B
infixr 1 _⊎_


-- Union.
_∪_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇} → Pred A 𝓨 → Pred A 𝓩 → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q
infixr 1 _∪_


open import MGS-MLTT using (𝟘)

-- The empty set.
∅ : {𝓧 : Universe}{A : 𝓧 ̇} → Pred A 𝓤₀
∅ = λ _ → 𝟘

-- Singletons.
｛_｝ : {𝓧 : Universe}{A : 𝓧 ̇} → A → Pred A _
｛ x ｝ = x ≡_

\end{code}



#### <a id="predicate-transport">Predicate transport</a>

The following is a pair of useful "transport" lemmas for predicates.

\begin{code}

module _ {𝓧 𝓨 : Universe} where

 cong-app-pred : {A : 𝓧 ̇ }{B₁ B₂ : Pred A 𝓨}
                 (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                ------------------------------
  →                         x ∈ B₂
 cong-app-pred x x∈B₁ refl = x∈B₁

 cong-pred : {A : 𝓧 ̇ }{B : Pred A 𝓨}
             (x y : A) →  x ∈ B  →  x ≡ y
             ----------------------------
  →                       y ∈ B
 cong-pred x .x x∈B refl = x∈B

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


Similarly, the *identity relation* (which is equivalent to the kernel of an injective function) can be represented as an inhabitant of any one four types.

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

The *total relation*, which in set theory is the set `𝑨 × 𝑨`, could be represented as an inhabitant of a relation type, as follows.

\begin{code}

 open import MGS-MLTT using (𝟙)

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

<sup>1</sup><span class="footnote" id="fn1"> In [agda2-mode][] type `\doteq` or `\.=` to produce `≐`.</span>

<p></p>

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Continuous →](Relations.Continuous.html)</span>

{% include UALib.Links.md %}
