---
layout: default
title : UALib.Relations.Unary module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="unary-relations">Unary Relations</a>

This section presents the [UALib.Relations.Unary][] module of the [Agda Universal Algebra Library][].

We need a mechanism for implementing the notion of subsets in Agda. A typical one is called `Pred` (for predicate). More generally, `Pred A 𝓤` can be viewed as the type of a property that elements of type `A` might satisfy. We write `P : Pred A 𝓤` to represent the semantic concept of a collection of elements of type `A` that satisfy the property `P`.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Unary where

open import Prelude.Lifts public

\end{code}

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

module _ {𝓧 𝓨 : Universe} where

 _∈_ : {A : 𝓧 ̇ } → A → Pred A 𝓨 → 𝓨 ̇
 x ∈ P = P x

 open import MGS-MLTT using (¬) public

 _∉_ : {A : 𝓧 ̇ } → A → Pred A 𝓨 → 𝓨 ̇
 x ∉ P = ¬ (x ∈ P)

 infix 4 _∈_ _∉_

\end{code}

The "subset" relation is denoted, as usual, with the `⊆` symbol (cf. `Relation/Unary.agda` in the [Agda Standard Library][]).

\begin{code}

_⊆_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } → Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } → Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
P ⊇ Q = Q ⊆ P

infix 4 _⊆_ _⊇_

\end{code}

In type theory everything is a type. As we have just seen, this includes subsets.  Since the notion of equality for types is usually a nontrivial matter, it may be nontrivial to represent equality of subsets.  Fortunately, it is straightforward to write down a type that represents what it means for two subsets to be the in informal (pencil-paper) mathematics.  In the [Agda UALib][] we denote this **subset equality** by =̇ and define it as follows.

\begin{code}

_≐_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } → Pred A 𝓨 → Pred A 𝓩 → 𝓧 ⊔ 𝓨 ⊔ 𝓩 ̇
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

infix 4 _≐_  -- type ≐ as `\.=` in agda2-mode

\end{code}



#### <a id="predicates-toolbox">Predicates toolbox</a>

Here is a small collection of tools that will come in handy later.  Hopefully the meaning of each is self-explanatory.

\begin{code}

_∈∈_ : {𝓧 𝓨 𝓩 : Universe}{A : 𝓧 ̇ } {B : 𝓨 ̇ } → (A  →  B) → Pred B 𝓩 → 𝓧 ⊔ 𝓩 ̇
_∈∈_ f S = (x : _) → f x ∈ S

Pred-refl : {𝓧 𝓨 : Universe}{A : 𝓧 ̇}{P Q : Pred A 𝓨}
 →          P ≡ Q → (a : A) → a ∈ P → a ∈ Q
Pred-refl (refl _) _ = λ z → z

Pred-≡ : {𝓧 𝓨 : Universe}{A : 𝓧 ̇}{P Q : Pred A 𝓨}
 →          P ≡ Q → P ≐ Q
Pred-≡ (refl _) = (λ z → z) , λ z → z

Pred-≡→⊆ : {𝓧 𝓨 : Universe}{A : 𝓧 ̇}{P Q : Pred A 𝓨}
 →          P ≡ Q → (P ⊆ Q)
Pred-≡→⊆ (refl _) = (λ z → z)

Pred-≡→⊇ : {𝓧 𝓨 : Universe}{A : 𝓧 ̇}{P Q : Pred A 𝓨}
 →          P ≡ Q → (P ⊇ Q)
Pred-≡→⊇ (refl _) = (λ z → z)

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

Im_⊆_ : {𝓧 𝓨 𝓩 : Universe} {A : 𝓧 ̇ } {B : 𝓨 ̇ } → (A → B) → Pred B 𝓩 → 𝓧 ⊔ 𝓩 ̇
Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

img : {𝓧 : Universe}{X : 𝓧 ̇ } {Y : 𝓧 ̇ }
      (f : X → Y) (P : Pred Y 𝓧)
 →    Im f ⊆ P →  X → Σ P
img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁

\end{code}



#### <a id="predicate-transport">Predicate transport</a>

The following is a pair of useful "transport" lemmas for predicates.

\begin{code}

module _ {𝓧 𝓨 : Universe} where

 cong-app-pred : {A : 𝓧 ̇ }{B₁ B₂ : Pred A 𝓨}
                 (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                ------------------------------
  →                         x ∈ B₂
 cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

 cong-pred : {A : 𝓧 ̇ }{B : Pred A 𝓨}
             (x y : A) →  x ∈ B  →  x ≡ y
             ----------------------------
  →                       y ∈ B
 cong-pred x .x x∈B (refl _ ) = x∈B

\end{code}


--------------------------------------

[↑ Relations](Relations.html)
<span style="float:right;">[Relations.Binary →](Relations.Binary.html)</span>

{% include UALib.Links.md %}
