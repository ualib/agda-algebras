---
layout: default
title : Demos.TYPES2021 module for talk introducing the Agda Universal Algebra Library
date : 2021-06-15
author: William DeMeo
---

# The Agda Universal Algebra Library

## and Birkhoff's Theorem in Dependent Type Theory

**Conference** TYPES 2021
**Session** Proof Assistant Applications
**Author** William DeMeo

### Coauthors

This is joint work with

* Jacques Carette
* Venanzio Capretta
* Hyeyoung Shin
* Siva Somayyajula

### References

* Source code url:  
  https://github.com/ualib/agda-algebras](https://github.com/ualib/agda-algebras

* Documentation url:  
  https://ualib.gitlab.io/UALib.html](https://ualib.gitlab.io/UALib.html

* Slides from the first talk about (the idea for) this project:  
  https://github.com/OPLSS/participant-talks-2018/blob/master/demeo-talk-oplss2018.pdf


---

### Introduction

The Agda Universal Algebra Library (UALib): a collection of types and programs 
(theorems and proofs) formalizing general (universal) algebra in dependent type theory using Agda.

#### Current Scope

* **Operations** of arbitrary arity over an arbitrary type (single-sorted)

* **Relations** of arbitrary arity over arbitrary type families (multi-sorted)

* **Signatures** of operation and relation symbols and their arities.

* **Algebraic structures** general types representing algebras of a given
  signature.

* **Homomorphisms** between algebraic structures with domain and codomain of same signature
  (but maybe from different universe levels); the basic isomorphism theorems of abstract algebra.

* **Terms**

* **Subuniverses** and **Substructures**

* **Varieties** and **Equational Logic**

* **Birkhoff's HSP Theorem**

---

### Introduction

#### Features

* **General** Algebraic/relational structures are more general than those of
  "classical" universal algebra.

* **Constructive** Classical axioms (Choice, Excluded Middle) are never used.
  
* **Universe polymorphic**


#### Bugs

* **Noncomputational** Extensionality of functions, propositions, or predicates
  used for proving certain theorems (but not globally, and we are working on
  removing these instances).

* **Specialized** Currently only single-sorted structures are covered (but we
  are working on a multi-sorted version)

---

### Logical Foundations

We use the following Agda `OPTIONS` *pragma* to specify the logical axioms and deduction rules we wish to
assume when the program is type-checked to verify its correctness.

In the UALib (agda-algebras), every source file begins with

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

* `--without-K`   →  no K axiom (essentially, we have "proof relevance", not UIP).

* `--exact-split` →  allow only definitions that behave like *judgmental* equalities.

* `--safe`        →  nothing is postulated outright---non-MLTT axioms must be explicit


---

\begin{code}

open import Demos.TYPES2021-imports

module Demos.TYPES2021  {𝓞 𝓥 : Level} where

variable α β γ ρ χ 𝓘 : Level

\end{code}

**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

\begin{code}

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

\end{code}


---

### General Relation Types

In Set theory, an n-ary relation on a set `A` is a subset of `A × A × ⋯ × A`.

We could model these as predicates over `A × A × ⋯ × A` or as relations of type

   `A → A → ⋯ → A → Type β`   (for some universe `β`).

This is awkward... would need to know the arity in advance, and then form an
n-fold arrow...?

Easier and more general to

* Define an arbitrary *arity type*  `I : Type 𝓥`

* Define the type of `I`-ary relations on `A`  as  `(I → A) → Type β`

As a special case, we could then define n-ary relations (`n ∈ ℕ`) by 
taking `I` to be an n-element type (e.g., `Fin n`).

---

#### Continuous Relations

By a "continuous relation" we mean a relation of arbitrary arity.

Let   I : Arity 𝓥   be such an arity type.

Let's define an alias for arity types.

\begin{code}

Arity : (𝓥 : Level) → Type (lsuc 𝓥)
Arity 𝓥 = Type 𝓥

\end{code}

A continuous relation of arity I over a single sort   A : Type α
represents the set theoretic notion of a subset of the Cartesian power Aᴵ.

\begin{code}

Rel : Type α → {I : Arity 𝓥 } → {ρ : Level} → Type _
Rel A {I} {ρ} = (I → A) → Type ρ

\end{code}

We call these "continuous" since their arity types may represent an uncountable
set or continuum rather than a discrete or enumerable set.



---


### Dependent Relations

We can remove the single-sorted restriction by using dependent types.

For an arbitrary family, 𝒜 : I → Type α, imagine a relation

     from  𝒜 i  to  𝒜 j  to  𝒜 k  to  …                 (*)

In set theory, such a relation is a subset of the product Π(i : I) 𝒜 i.

Again, the set represented by the "indexing" type I might not even be enumerable
so (*) is misleading; we should have said something like "to(i : I) 𝒜 i"

The `RelΠ` type manifests this general notion of relation.

\begin{code}

 -- The type of arbitrarily multi-sorted relations of arbitrary arity

RelΠ : (I : Arity 𝓥 ) → (I → Type α) → {ρ : Level} → Type _
RelΠ I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

\end{code}

We refer to such relations as "dependent relations" because their definition
requires dependent types.


---

\begin{code}
 -- slightly better syntax for dependent relations
RelΠ-syntax : (I : Arity 𝓥 ) → (I → Type α) → {ρ : Level} → Type _
RelΠ-syntax I 𝒜 {ρ} = RelΠ I 𝒜 {ρ}
syntax RelΠ-syntax I (λ i → 𝒜) = RelΠ[ i ∈ I ] 𝒜
infix 6 RelΠ-syntax
\end{code}


---


### Operation type and compatibility

**Notation**. We reserve two universe level variables for special purposes.

1. 𝓞 is (the universe level) for types of *operation symbols*.

2. 𝓥 is for types representing *arities* of relations or operations.

The type `Op` encodes the arity of an operation as an arbitrary type `I : Type
𝓥`, which gives us a very general way to represent an operation as a function
type with domain `I → A` (the type of "tuples") and codomain `A`.

\begin{code}

-- Operations on A of arity I
Op : Type α → {I : Arity 𝓥 } → Type _
Op A {I} = (I → A) → A

\end{code}

We may think of Op A {I} as Aᴵ → A, the collection of functions that map
each tuple in Aᴵ to an element of A. For example, the I-ary projection
operations on A are

\begin{code}

π : {I : Arity 𝓥 } {A : Type α } → I → Op A
π i x = x i

\end{code}

Now suppose `A` and `I` are types and let `𝑓 : Op A {I}` and `R : BinRel A β` be an `I`-ary operation and
a binary relation on `A`, respectively.

We say `𝑓` and `R` are *compatible* and we write `𝑓 |: R` just in case `∀ u v : I → A`, 

`Π i ꞉ I , R (u i) (v i)  →  R (f u) (f v)`.

Here is how we implement this in the agda-algebras library.

\begin{code}

-- First lift the relation from pairs in A × A to pairs in Aᴵ × Aᴵ.

eval-rel : {A : Type α}{I : Arity 𝓥 } → BinRel A ρ → BinRel (I → A) (𝓥 ⊔ ρ)
eval-rel R u v = ∀ i → R (u i) (v i)

\end{code}

Then "f preserves R" if ∀ (u , v) we have

    u v ∈ (eval-rel R)  implies  (f u) (f v) ∈ R.

\begin{code}

_preserves_ : {A : Type α}{I : Arity 𝓥 } → Op A{I} → BinRel A ρ → Type _
f preserves R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)


 -- Shorthand notation for preserves,
 -- (defined using fancy notation from the Agda std lib)

_|:_ : {A : Type α}{I : Arity 𝓥 } → Op A{I} → BinRel A ρ → Type _
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}

---

#### Compatibility of general operations and relations

A relation R is "compatible" with an operation 𝑓 if for every tuple t of tuples belonging
to R, the tuple whose elements are the result of applying 𝑓 to sections of t also belongs to R.

The following types manifest this notion, making it easy to assert that a given operation
is compatible with a given relation.

\begin{code}

eval-Rel : {I : Arity 𝓥 }{A : Type α} → Rel A {I}{ρ} → (J : Arity 𝓥 ) → (I → J → A) → Type _
eval-Rel R J t = ∀ (j : J) → R λ i → t i j

compatible-Rel : {I J : Arity 𝓥 }{A : Type α} → Op(A){J} → Rel A {I}{ρ} → Type _
compatible-Rel 𝑓 R  = ∀ t → eval-Rel R arity[ 𝑓 ] t → R λ i → 𝑓 (t i)

\end{code}

Here the inferred type of `t` is `I → J → A`


---

#### Compatibility of general operations and relations

The analogous type for dependent relations looks more complicated, but the idea is equally
simple.

\begin{code}

eval-REL : {I J : Arity 𝓥 }{𝒜 : I → Type α}
  →         RelΠ I 𝒜 {ρ}                -- "subsets" of Π[ i ∈ I ] 𝒜 i
                                        -- Π[ i ∈ I ] 𝒜 i is a type of (dependent) "tuples"
  →         ((i : I) → J → 𝒜 i)         -- an I-tuple of (𝒥 i)-tuples
  →         Type _

eval-REL{I = I}{J}{𝒜} R t = ∀ j → R λ i → (t i) j


compatible-REL : {I J : Arity 𝓥 }{𝒜 : I → Type α}
  →              (∀ i → Op (𝒜 i){J})  -- for each i, an operation of type  (J → 𝒜 i) → 𝒜 i
  →              RelΠ I 𝒜 {ρ}         -- a subset of Π[ i ∈ I ] 𝒜 i
                                      -- where Π[ i ∈ I ] 𝒜 i is a "set" of (dependent) "tuples"
  →              Type _

compatible-REL {I = I}{J}{𝒜} 𝑓 R = Π[ t ∈ ((i : I) → J → 𝒜 i) ] eval-REL R t


\end{code}

The first of these is an *evaluation* function which "lifts" an `I`-ary relation to an `(I
→ J)`-ary relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the
"`I`-slices" (or "rows") of the `J`-tuples belong to the original relation. The second
definition denotes compatibility of an operation with a continuous relation. 

(See note [1] below for heuristic explanation.)

---

### Types for General Algebraic Structures

#### Signature of an Algebra

Classically, a *signature* `𝑆 = (𝐶, 𝐹, 𝑅, ρ)` consists of three (possibly empty) sets
(denoting constant, function, and relation symbols) and a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁`
assigning an *arity* to each symbol.

Often (but not always) `𝑁` is the natural numbers.

An *algebraic signature* is a signature for algebraic structures; that is,

  𝑆 = (𝐹, ρ)

where `𝐹` is a set of of *operation symbols* and `ρ : 𝐹 → 𝑁` is an arity function.

Heuristically, the arity `ρ 𝑓` of an operation symbol `𝑓 ∈ 𝐹` may be thought
of as the "number of arguments" that `𝑓` takes as "input".

If the arity of `𝑓` is `n`, then we call `𝑓` an `n`-*ary* operation symbol.

(See note [2] for more details.)


---


#### Signature Types

We represent the *signature* of an algebraic structure using the following Sigma type.

\begin{code}

Signature : (𝓞 𝓥 : Level) → Type (lsuc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)

\end{code}

Thus a signature is a pair `(F , ρ)`, where `F : Type 𝓞` and `ρ : F → Type 𝓥`.

We define special syntax for the first and second projections: `∣_∣` and `∥_∥`.

If `𝑆 : Signature 𝓞 𝓥`, then

* ∣ 𝑆 ∣ = F is the set of operation symbols, and
* ∥ 𝑆 ∥ = the arity function.

If `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, then `∥ 𝑆 ∥ 𝑓` is the arity of `𝑓`.

---

#### Example (Monoid).

Here is how we could encode the signature for monoids as an inhabitant of `Signature 𝓞 ℓ₀`.

\begin{code}


data monoid-op {𝓞 : Level} : Type 𝓞 where
 e : monoid-op; · : monoid-op

monoid-sig : {𝓞 : Level} → Signature 𝓞 ℓ₀
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }

\end{code}

This signature consists of two operation symbols, `e` and `·`, and a
function `λ { e → 𝟘; · → 𝟚 }` which maps

* `e` to the empty type 𝟘 (since `e` is the nullary identity) and
* `·` to the two element type 𝟚 (since `·` is binary).

---

#### Algebras in Theory

An *algebraic structure* (or *algebra*) in the signature `𝑆 = (𝐹, ρ)` is denoted by `𝑨 = (A, Fᴬ)` and consists of

* `A` = a *nonempty* set (or type), called the *carrier* (or *universe*) of the algebra;

* `Fᴬ = { fᴬ ∣ f ∈ F, fᴬ : (ρ𝑓 → A) → A }, a collection of *operations* on `A`;

* a (potentially empty) collection of *identities* satisfied by elements and operations.

(See note [3] for more details.)


---

#### Algebra in Type Theory

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe level `α`, we define the type of
`𝑆`-*algebras with domain type* `Type α` as follows.

\begin{code}

Algebra : (α : Level)(𝑆 : Signature 𝓞 𝓥) → Type (ov α)

Algebra α 𝑆 = Σ[ A ∈ Type α ]                   -- the domain
              ∀ (f : ∣ 𝑆 ∣) → Op A {∥ 𝑆 ∥ f}    -- the basic operations


\end{code}

---

#### Truncation?

It would be more precise to refer to inhabitants of `Algebra α 𝑆` as ∞-*algebras* because
their domains can be of arbitrary type and need not be truncated at some particular
universe level.

We might take this opportunity to define the type of 0-*algebras*, that is, algebras whose
domains are "sets" (where identity proofs are unique), which is probably closer in spirit
to classical universal algebra.

While such truncation to sets is sometimes required, our experience has shown that much
of the theory can be formalized more generally.

It seems preferable to work with general (∞-)algebras throughout and then explicitly require
additional principles (e.g., unique identity proofs) only when necessary.

---

#### Algebras as Inhabitants of Record Types

Some prefer to use record types for things like algebraic structures, and for those folks
we offer the following.

\begin{code}

record algebra (α : Level) (𝑆 : Signature 𝓞 𝓥) : Type(lsuc(𝓞 ⊔ 𝓥 ⊔ α)) where
 constructor mkalg
 field
  carrier : Type α
  opsymbol : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → carrier) → carrier

\end{code}

This representation of algebras as inhabitants of a record type is logically equivalent to
the one using Sigma types in the sense that there is an (obvious) bi-implication between
the two definitions.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra α 𝑆 → Algebra α 𝑆
 algebra→Algebra 𝑨 = (carrier 𝑨 , opsymbol 𝑨)

 Algebra→algebra : Algebra α 𝑆 → algebra α 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥

\end{code}

---

#### Operation interpretation syntax

A convenient shorthand for the interpretation of an operation symbol which looks somewhat
like the standard notation one finds in the literature is obtained as follows.

\begin{code}

 _̂_ : ∀ 𝑓 (𝑨 : Algebra α 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

\end{code}

If `𝑓 : ∣ 𝑆 ∣` is an operation symbol, and `a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the
appropriate arity, then `(𝑓 ̂ 𝑨) a` denotes the operation `𝑓` interpreted in `𝑨` and
evaluated at `a`.


---

#### Level Lifting Algebra Types

One encounters difficulties when working with a noncumulative universe hierarchy like Agda's.

We provide some domain-specific level lifting and level lowering methods---bespoke tools
for our operation and algebra types.

\begin{code}

 open Lift

 Lift-alg-op : {I : Arity 𝓥} {A : Type α} → Op A {I} → (β : Level) → Op (Lift β A) {I}
 Lift-alg-op f β = λ x → lift (f (λ i → lower (x i)))


 Lift-Alg : Algebra α 𝑆 → (β : Level) → Algebra (α ⊔ β) 𝑆
 Lift-Alg 𝑨 β = Lift β ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-alg-op (𝑓 ̂ 𝑨) β)

\end{code}

What makes `Lift-Alg` useful for resolving type level errors involving algebras is the
nice structure-preserving properties it possesses.  Indeed, we prove the following facts.

+ `Lift-Alg` is a homomorphism
+ `Lift-Alg` is an algebraic invariant (preserves isomorphism)
+ `Lift-Alg` is a "subalgebraic invariant" (lift of a subalgebra is a subalgebra)
+ `Lift-Alg` preserves identities

---


#### Compatibility of Binary Relations with Algebras

We now define the function `compatible` so that, if `𝑨` is an algebra and `R` a binary
relation, then `compatible 𝑨 R` is the assertion that `R` is *compatible* with
all basic operations of `𝑨`.

The formal definition is immediate since all the work is already done by the "preserves" relation
defined earlier.

\begin{code}

 compatible : (𝑨 : Algebra α 𝑆) → BinRel ∣ 𝑨 ∣ ρ → Type _
 compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) preserves R

\end{code}

---

#### COMPATIBILITY OF CONTINUOUS RELATIONS

We defined functions `compatible-Rel` (`compatible-REL`) to represent the assertion that
a given continuous (dependent) relation is compatible with a given operation.

The following represent compatibility of a continuous (dependent) relation with all
operations of an algebra.

\begin{code}

 compatible-Rel-alg : {I : Arity 𝓥} (𝑨 : Algebra α 𝑆) → Rel ∣ 𝑨 ∣ {I}{ρ} → Type _
 compatible-Rel-alg {I = I}𝑨 R = ∀ 𝑓 → compatible-Rel{I = I}{J = ∥ 𝑆 ∥ 𝑓} (𝑓 ̂ 𝑨) R


 compatible-REL-alg : {I : Arity 𝓥} (𝒜 : I → Algebra α 𝑆) → RelΠ I (λ i → ∣ 𝒜  i ∣) {ρ} → Type _
 compatible-REL-alg 𝒜 R = ∀ 𝑓 →  compatible-REL (λ i → 𝑓 ̂ (𝒜 i)) R

\end{code}


---

#### PRODUCT ALGEBRAS


Recall the informal definition of a *product* of `𝑆`-algebras.

Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the *product* `⨅ 𝒜` is the
algebra with

* carrier: the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`

* operations: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π[ 𝑖 ∈ I ] J → 𝒜 𝑖` is an
 `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖`, then

  `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

\begin{code}
 module _ {𝓘 : Level}{I : Type 𝓘 } where

  ⨅ : (𝒜 : I → Algebra α 𝑆 ) → Algebra (𝓘 ⊔ α) 𝑆

  ⨅ 𝒜 = ( ∀ (i : I) → ∣ 𝒜 i ∣ ) ,           -- domain of the product algebra
          λ 𝑓 𝑎 i → (𝑓 ̂ 𝒜 i) λ x → 𝑎 x i   -- basic operations of the product algebra

\end{code}

Here is how one could define a type representing the product of algebras inhabiting the
record type `algebra`.

\begin{code}

  open algebra

  ⨅' : (𝒜 : I → algebra α 𝑆) → algebra (𝓘 ⊔ α) 𝑆

  ⨅' 𝒜 =

   record { carrier = ∀ i → carrier (𝒜 i)                        -- domain
          ; opsymbol = λ 𝑓 𝑎 i → (opsymbol (𝒜 i)) 𝑓 λ x → 𝑎 x i  -- basic operations
          }

\end{code}


---

#### PRODUCTS OF ARBITRARY CLASSES OF ALGEBRAS

One of our goals is to formally express and prove properties of *classes of algebras*.

Fixing a signature `𝑆` and a universe `α`, we represent classes of `𝑆`-algebras with
domains in `Type α` as predicates over the `Algebra α 𝑆` type.

Such predicates inhabit the type `Pred (Algebra α 𝑆) β`, for some universe β.

If `𝒦` is such a class of algebras, we write `𝒦 : Pred (Algebra α 𝑆) β` and we prove

  PS(𝒦) ⊆ SP(𝒦 )

which asserts that products of subalgebras of algebras in `𝒦` are subalgebras of products
of algebras in `𝒦`.

This turns out to be a nontrivial exercise and it requires that we first define a type
representing products over arbitrary (nonindexed) families such as `𝒦`.

---

#### PRODUCTS OF ARBITRARY CLASSES

Observe that `Π 𝒦` is certainly not what we want.

(Recall `Pred (Algebra α 𝑆) β` is the function type `Algebra α 𝑆 → Type β`, and the
semantics of the latter takes `𝒦 𝑨` to mean `𝑨 ∈ 𝒦`. Thus, by definition, 

 Π 𝒦   :=   Π[ 𝑨 ∈ (Algebra α 𝑆) ] 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,

which simply asserts that every inhabitant of `Algebra α 𝑆` belongs to `𝒦`.

We need a type that indexes the class `𝒦`, and a function `𝔄` that maps an index to the
inhabitant of `𝒦` at that index.

But `𝒦` is a predicate (of type `(Algebra α 𝑆) → Type β`) and the type `Algebra α 𝑆` seems
rather nebulous in that there is no natural indexing class with which to "enumerate" all
inhabitants of `Algebra α 𝑆` belonging to `𝒦`.

---

#### PRODUCTS OF ARBITRARY CLASSES

The solution is to essentially take `𝒦` itself to be the indexing type, at least
heuristically that is how one can view the type `ℑ` that we now define.

\begin{code}

 module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  -- The index for the product of algebras in 𝒦.
  ℑ : Type (ov α)
  ℑ = Σ[ 𝑨 ∈ Algebra α 𝑆 ] 𝑨 ∈ 𝒦

\end{code}

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ`
to the corresponding algebra.

---

#### PRODUCTS OF ARBITRARY CLASSES

Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨`
belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply
the first projection.

\begin{code}

  𝔄 : ℑ → Algebra α 𝑆
  𝔄 i = ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

  class-product : Algebra (ov α) 𝑆
  class-product = ⨅ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can
think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the
`(𝑨 , p)`-th component.



---


### CONGRUENCE RELATIONS

A *congruence relation* of an algebra `𝑨` is an equivalence relation that is
compatible with the basic operations of `𝑨`.

This concept can be represented by a number of alternative but equivalent types.

We define a record type `IsCongruence` to represent the property of being a congruence.

\begin{code}

 record IsCongruence (𝑨 : Algebra α 𝑆)(θ : BinRel ∣ 𝑨 ∣ ρ) : Type(𝓞 ⊔ 𝓥 ⊔ lsuc (ρ ⊔ α))  where
  constructor mkcon
  field       is-equivalence : IsEquivalence θ
              is-compatible  : compatible 𝑨 θ

\end{code}

We define a Sigma type `Con` to represent the type of congruences of a given algebra.

\begin{code}

 Con : (𝑨 : Algebra α 𝑆) → {ρ : Level} → Type _
 Con 𝑨 {ρ} = Σ[ θ ∈ ( BinRel ∣ 𝑨 ∣ ρ ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in
the sense that each implies the other. One implication is the "uncurry" operation and the
other is the second projection.

---

#### QUOTIENT ALGEBRAS

In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a
congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted
by `𝑨 / θ` and Agda allows us to define and express quotients using this standard
notation.

\begin{code}

 _╱_ : (𝑨 : Algebra α 𝑆) → Con 𝑨 {ρ} → Algebra (α ⊔ lsuc ρ) 𝑆

 𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)  ,                                  -- domain of the quotient algebra
          λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.block-u ∥ 𝑎 i ∥) ⟫  -- operations of the quotient algebra

\end{code}


Finally, the following elimination rule is sometimes useful (but it 'cheats' a lot by baking in
a large amount of extensionality that is miraculously true).

\begin{code}

 open IsCongruence

 /-≡ : {𝑨 : Algebra α 𝑆}(θ : Con 𝑨 {ρ}){u v : ∣ 𝑨 ∣} → ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
 /-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}


---


#### HOMOMORPHISMS

If `𝑨` and `𝑩` are `𝑆`-algebras, then a *homomorphism* from `𝑨` to `𝑩` is a function

  `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣`

from the domain of `𝑨` to the domain of `𝑩` that is *compatible* (or *commutes*) with all
of the basic operations of the signature; that is,

∀ (𝑓 : ∣ 𝑆 ∣) (a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a)`.

To formalize this concept, we first define a type representing the assertion that a
function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` commutes with a single basic operation `𝑓`.

\begin{code}

 module _ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) where

  compatible-op-map : ∣ 𝑆 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _

  compatible-op-map 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

\end{code}


---


#### HOMOMORPHISMS

Type `hom 𝑨 𝑩` of homomorphisms from `𝑨` to `𝑩` is defined using the type
`is-homomorphism` representing the property of being a homomorphism.

\begin{code}

  is-homomorphism : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _
  is-homomorphism g = ∀ 𝑓  →  compatible-op-map 𝑓 g

  hom : Type _
  hom = Σ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) is-homomorphism

  -- Examples. The identity hom.
 𝒾𝒹 : (𝑨 : Algebra α 𝑆) → hom 𝑨 𝑨
 𝒾𝒹 _ = id , λ 𝑓 𝑎 → refl

\end{code}


---


#### HOMOMORPHISM THEOREM

1. The composition of homomorphisms is again a homomorphism.

\begin{code}

 module _ (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆) where


  ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪

  ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal

   where
   open ≡-Reasoning

   Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)

   Goal 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a) ≡⟨ cong h ( ghom 𝑓 a ) ⟩
              h ((𝑓 ̂ 𝑩)(g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
              (𝑓 ̂ 𝑪)(h ∘ g ∘ a) ∎

\end{code}


---


#### HOMOMORPHISM THEOREM

2. `lift` and `lower` are (the maps of) homomorphisms.

\begin{code}

 open Lift

 𝓁𝒾𝒻𝓉 : (𝑨 : Algebra α 𝑆) → hom 𝑨 (Lift-Alg 𝑨 β)
 𝓁𝒾𝒻𝓉 _ = lift , λ 𝑓 𝑎 → refl

 𝓁ℴ𝓌ℯ𝓇 : (𝑨 : Algebra α 𝑆) → hom (Lift-Alg 𝑨 β) 𝑨
 𝓁ℴ𝓌ℯ𝓇 _ = lower , λ 𝑓 𝑎 → refl

\end{code}

---



#### HOMOMORPHISM FACTORIZATION


If `τ : hom 𝑨 𝑩`, `ν : hom 𝑨 𝑪`, `ν` is surjective, and `ker ν ⊆ ker τ`, then there exists
`φ : hom 𝑪 𝑩` such that `τ = φ ∘ ν` so the following diagram commutes:


   𝑨 --- ν ->> 𝑪
    \         .
     \       .
      τ     φ
       \   .
        \ .
         V
         𝑩


\begin{code}

 module _ {𝑨 : Algebra α 𝑆}{𝑪 : Algebra γ 𝑆} where

  HomFactor : funext α β → swelldef 𝓥 γ
   →          (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
   →          kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
              --------------------------------------------------
   →          Σ[ φ ∈ (hom 𝑪 𝑩)] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣

  HomFactor fxy wd 𝑩 τ ν Kντ νE = (φ , φIsHomCB) , τφν
   where
    νInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
    νInv = SurjInv ∣ ν ∣ νE

    η : ∀ c → ∣ ν ∣ (νInv c) ≡ c
    η c = SurjInvIsRightInv ∣ ν ∣ νE c

    φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
    φ = ∣ τ ∣ ∘ νInv

    ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
    ξ a = (η (∣ ν ∣ a))⁻¹

    τφν : ∣ τ ∣ ≡ φ ∘ ∣ ν ∣
    τφν = fxy λ x → Kντ (ξ x)

    open ≡-Reasoning
    φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
    φIsHomCB 𝑓 c = φ ((𝑓 ̂ 𝑪) c) ≡⟨ cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) (λ i → (η (c i))⁻¹)) ⟩
                   φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
                   φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ cong-app(τφν ⁻¹)((𝑓 ̂ 𝑨)(νInv ∘ c))⟩
                   ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
                   (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎

\end{code}


---


#### HOMOMORPHISM FACTORIZATION

If in addition we assume τ is epic, then so is φ.


\begin{code}

  HomFactorEpi : funext α β → swelldef 𝓥 γ
   →             (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
   →             kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
   →             IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
                 ---------------------------------------------
   →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣

  HomFactorEpi fxy wd 𝑩 τ ν kerincl νe τe = (fst ∣ φF ∣ ,(snd ∣ φF ∣ , φE)), ∥ φF ∥
   where
    φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣
    φF = HomFactor fxy wd 𝑩 τ ν kerincl νe

    φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
    φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

    φE : IsSurjective φ
    φE = epic-factor  ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe

\end{code}



---



### ISOMORPHISMS


Two structures are *isomorphic* provided there are homomorphisms going back and forth
between them which compose to the identity map.


\begin{code}

 _≅_ : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → Type _

 𝑨 ≅ 𝑩 =  Σ[ f ∈ hom 𝑨 𝑩 ] Σ[ g ∈ hom 𝑩 𝑨 ]

           ( (∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣) )

\end{code}

Recall, `f ≈ g` means f and g are *extensionally* (or pointwise) equal.



---


#### ISOMORPHISM IS AN EQUIVALENCE RELATION

\begin{code}

 ≅-refl : {𝑨 : Algebra α 𝑆} → 𝑨 ≅ 𝑨
 ≅-refl {𝑨 = 𝑨} = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , (λ a → refl) , (λ a → refl)

 ≅-sym : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} →  𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
 ≅-sym h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

 ≅-trans : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆}
  →        𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

 ≅-trans {𝑨 = 𝑨} {𝑩}{𝑪} ab bc = f , g , τ , ν
  where
  f1 : hom 𝑨 𝑩
  f1 = ∣ ab ∣
  f2 : hom 𝑩 𝑪
  f2 = ∣ bc ∣
  f : hom 𝑨 𝑪
  f = ∘-hom 𝑨 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = fst ∥ bc ∥
  g2 : hom 𝑩 𝑨
  g2 = fst ∥ ab ∥
  g : hom 𝑪 𝑨
  g = ∘-hom 𝑪 𝑨 g1 g2

  τ : ∣ f ∣ ∘ ∣ g ∣ ≈ ∣ 𝒾𝒹 𝑪 ∣
  τ x = (cong ∣ f2 ∣(∣ snd ∥ ab ∥ ∣ (∣ g1 ∣ x)))∙(∣ snd ∥ bc ∥ ∣) x

  ν : ∣ g ∣ ∘ ∣ f ∣ ≈ ∣ 𝒾𝒹 𝑨 ∣
  ν x = (cong ∣ g2 ∣(∥ snd ∥ bc ∥ ∥ (∣ f1 ∣ x)))∙(∥ snd ∥ ab ∥ ∥) x

\end{code}


---


#### LIFT IS AN ALGEBRAIC INVARIANT

The lift operation preserves isomorphism.

  𝑨 ≅ 𝑩   →   Lift-Alg 𝑨 𝓧   ≅  Lift-Alg 𝑩 𝓨

In fact, we even have 𝑨 ≅ Lift-Alg 𝑨 𝓧.

This is why the lift is a workable solution to the technical problems
arising from noncumulativity of Agda's universe hierarchy.

\begin{code}

 open Lift

 Lift-≅ : {𝑨 : Algebra α 𝑆} → 𝑨 ≅ (Lift-Alg 𝑨 β)
 Lift-≅ {β = β}{𝑨 = 𝑨} = 𝓁𝒾𝒻𝓉 𝑨 , 𝓁ℴ𝓌ℯ𝓇 𝑨 , cong-app lift∼lower , cong-app (lower∼lift{β = β})

 Lift-hom : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆} (ℓᵇ : Level)
  →         hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)

 Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
  where
  lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
  lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → refl) fhom

  Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
  Goal = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ){f ∘ lower}{lift} lABh λ _ _ → refl


 Lift-Alg-iso : {𝑨 : Algebra α 𝑆}{𝓧 : Level}
                {𝑩 : Algebra β 𝑆}{𝓨 : Level}
                -----------------------------------------
  →             𝑨 ≅ 𝑩 → (Lift-Alg 𝑨 𝓧) ≅ (Lift-Alg 𝑩 𝓨)

 Lift-Alg-iso A≅B = ≅-trans (≅-trans (≅-sym Lift-≅) A≅B) Lift-≅

\end{code}


---


#### LIFT IS ASSOCIATIVE

\begin{code}

 Lift-Alg-assoc : (𝑨 : Algebra α 𝑆)

  →               Lift-Alg 𝑨 (β ⊔ γ) ≅ (Lift-Alg (Lift-Alg 𝑨 β) γ)

 Lift-Alg-assoc{β = β}{γ} 𝑨 = ≅-trans (≅-trans Goal Lift-≅) Lift-≅
  where
  Goal : Lift-Alg 𝑨 (β ⊔ γ) ≅ 𝑨
  Goal = ≅-sym Lift-≅

\end{code}



---


#### PRODUCTS PRESERVE ISOMORPHISMS

Products of isomorphic families of algebras are themselves isomorphic.

(The proof here requires function extensionality.)


\begin{code}

 module _ {𝓘 : Level}{I : Type 𝓘}
          {fiu : funext 𝓘 α}{fiw : funext 𝓘 β}     -- we postulate function extensionality here
          where

   ⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : I → Algebra β 𝑆}

    →    (∀ (i : I) → 𝒜 i ≅ ℬ i) → ⨅ 𝒜 ≅ ⨅ ℬ

   ⨅≅ {𝒜 = 𝒜}{ℬ} AB = Goal
    where
    ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
    ϕ a i = ∣ fst (AB i) ∣ (a i)

    ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
    ϕhom 𝑓 a = fiw (λ i → ∥ fst (AB i) ∥ 𝑓 (λ x → a x i))

    ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
    ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

    ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
    ψhom 𝑓 𝒃 = fiu (λ i → snd ∣ snd (AB i) ∣ 𝑓 (λ x → 𝒃 x i))

    ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
    ϕ~ψ 𝒃 = fiw λ i → fst ∥ snd (AB i) ∥ (𝒃 i)

    ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
    ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

    Goal : ⨅ 𝒜 ≅ ⨅ ℬ
    Goal = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

\end{code}


---


#### ISOMORPHIC PRODUCTS WITH A LIFT


A nearly identical proof goes through for isomorphisms of lifted products.

\begin{code}

 module _ {𝓘 : Level}{I : Type 𝓘}
          {fizw : funext (𝓘 ⊔ γ) β}{fiu : funext 𝓘 α} -- function extensionality postulates
          where

   Lift-Alg-⨅≅ : {𝒜 : I → Algebra α 𝑆}{ℬ : (Lift γ I) → Algebra β 𝑆}
    →            (∀ i → 𝒜 i ≅ ℬ (lift i)) → Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ

   Lift-Alg-⨅≅ {𝒜 = 𝒜}{ℬ} AB = Goal
    where
    ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
    ϕ a i = ∣ fst (AB  (lower i)) ∣ (a (lower i))

    ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
    ϕhom 𝑓 a = fizw (λ i → (∥ fst (AB (lower i)) ∥) 𝑓 (λ x → a x (lower i)))

    ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
    ψ b i = ∣ fst ∥ AB i ∥ ∣ (b (lift i))

    ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
    ψhom 𝑓 𝒃 = fiu (λ i → (snd ∣ snd (AB i) ∣) 𝑓 (λ x → 𝒃 x (lift i)))

    ϕ~ψ : ϕ ∘ ψ ≈ ∣ 𝒾𝒹 (⨅ ℬ) ∣
    ϕ~ψ 𝒃 = fizw λ i → fst ∥ snd (AB (lower i)) ∥ (𝒃 i)

    ψ~ϕ : ψ ∘ ϕ ≈ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
    ψ~ϕ a = fiu λ i → snd ∥ snd (AB i) ∥ (a i)

    A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
    A≅B = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

    Goal : Lift-Alg (⨅ 𝒜) γ ≅ ⨅ ℬ
    Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}



---

### HOMOMORPHIC IMAGES

What is (for our purposes) the most useful way to represent the class of
*homomorphic images* of a single algebra in dependent type theory is

\begin{code}

 _IsHomImageOf_ : (𝑩 : Algebra β 𝑆) (𝑨 : Algebra α 𝑆) → Type _
 𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

 HomImages : Algebra α 𝑆 → Type _
 HomImages {α = α}𝑨 = Σ[ 𝑩 ∈ Algebra α _ ] 𝑩 IsHomImageOf 𝑨

\end{code}

Given an 𝑆-algebra `𝑨 : Algebra α 𝑆`, the type `HomImages 𝑨` denotes the class of algebras
`𝑩 : Algebra β 𝑆` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.



---




#### IMAGES OF A CLASS OF ALGEBRAS

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a
given algebra is a homomorphic image of some algebra in the class, as well as a type that
represents all such homomorphic images.

\begin{code}

 IsHomImageOfClass : Pred (Algebra α 𝑆)(lsuc α) → Algebra α 𝑆 → Type _
 IsHomImageOfClass 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra _ _ ] ((𝑨 ∈ 𝒦) × (𝑩 IsHomImageOf 𝑨))

 HomImageOfClass : Pred (Algebra α 𝑆) (lsuc α) → Type _
 HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra _ _ ] IsHomImageOfClass 𝒦 𝑩

\end{code}


---


#### LIFTING TOOLS

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's
HSP theorem). The first states and proves the simple fact that the lift of an epimorphism
is an epimorphism.

\begin{code}

 open Lift
 open ≡-Reasoning

 Lift-epi-is-epi : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level)(h : hom 𝑨 𝑩)
  →                IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom ℓᵃ {𝑩} ℓᵇ h ∣

 Lift-epi-is-epi {β = β}{𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ h hepi y = eq (lift a) η
  where
   lh : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
   lh = Lift-hom ℓᵃ {𝑩} ℓᵇ h

   ζ : Image ∣ h ∣ ∋ (lower y)
   ζ = hepi (lower y)

   a : ∣ 𝑨 ∣
   a = Inv ∣ h ∣ ζ

   ν : lift (∣ h ∣ a) ≡ ∣ Lift-hom ℓᵃ {𝑩} ℓᵇ h ∣ (lift a)
   ν = cong (λ - → lift (∣ h ∣ (- a))) (lower∼lift {Level-of-Carrier 𝑨}{β})

   η : y ≡ ∣ lh ∣ (lift a)
   η = y               ≡⟨ (cong-app lift∼lower) y ⟩
       lift (lower y)  ≡⟨ cong lift (InvIsInv ∣ h ∣ ζ)⁻¹ ⟩
       lift (∣ h ∣ a)  ≡⟨ ν ⟩
       ∣ lh ∣ (lift a) ∎

 Lift-Alg-hom-image : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level)
  →                   𝑩 IsHomImageOf 𝑨
  →                   (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)

 Lift-Alg-hom-image {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ ((φ , φhom) , φepic) = Goal
  where
  lφ : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
  lφ = Lift-hom ℓᵃ {𝑩} ℓᵇ (φ , φhom)

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epi ℓᵃ {𝑩} ℓᵇ (φ , φhom) φepic
  Goal : (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf _
  Goal = lφ , lφepic

\end{code}

---


#### TERMS

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable
symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`:
`X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of
`X ⊎ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n`
the sets `𝑇ₙ` of *words* over `X ⊎ ∣ 𝑆 ∣` as follows (cf. Bergman 2012, Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `𝑓 𝑡` such that `𝑓 : ∣ 𝑆 ∣` and `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑇ₙ`.
(Recall, `∥ 𝑆 ∥ 𝑓` is the arity of the operation symbol 𝑓.)

The collection of *terms* in the signature `𝑆` over `X` is `Term X := ⋃ₙ 𝑇ₙ`.



---



#### THE INDUCTIVE TYPE OF TERMS


By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, so an inductive type can be used to represent the
semantic notion of terms in type theory. Indeed, here is one such representation.

\begin{code}

 data Term (X : Type χ ) : Type (𝓞 ⊔ 𝓥 ⊔ lsuc χ)  where

  ℊ : X → Term X       -- (ℊ for "generator")

  node : (f : ∣ 𝑆 ∣)(𝑡 : ∥ 𝑆 ∥ f → Term X) → Term X

\end{code}

**Notation**. `X` represents an arbitrary collection of variable symbols.

`ov χ` is our shorthand for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`

Thus each term is a tree with an operation symbol at each `node` and a variable symbol at
each leaf (`generator`).


---

#### THE TERM ALGEBRA

If the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we
can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the
signature* `𝑆` *over* `X`.

\begin{code}

 open Term public

 𝑻 : (X : Type χ ) → Algebra (𝓞 ⊔ 𝓥 ⊔ lsuc χ) 𝑆
 𝑻 X = Term X , node

\end{code}


Terms are viewed as acting on other terms, so both the domain and basic operations of the
algebra are the terms themselves.

+ `𝑓 ̂ (𝑻 X)` is the operation on `Term X` that maps a tuple `𝑡 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑻 X ∣` of
  terms to the formal term `𝑓 𝑡`.

+ `𝑻 X` is the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `𝑓 ̂ (𝑻 X)`, one
  for each symbol `𝑓` in `∣ 𝑆 ∣`. 


---


#### THE UNIVERSAL PROPERTY of 𝑻 X

The term algebra `𝑻 X` is *absolutely free* for 𝑆-algebras:

For every 𝑆-algebra `𝑨`,

1. Every function in `𝑋 → ∣ 𝑨 ∣` lifts to a homomorphism in `hom (𝑻 X) 𝑨`;

2. The homomorphism of item 1 is unique.

Starting with the fact that every map in `X → ∣ 𝑨 ∣` lifts to a map in `∣ 𝑻 X ∣ → ∣ 𝑨 ∣`
by induction on the structure of the given term.

\begin{code}

 private variable X : Type χ

 free-lift : (𝑨 : Algebra α 𝑆)(h : X → ∣ 𝑨 ∣) → ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
 free-lift _ h (ℊ x)     = h x
 free-lift 𝑨 h (node f 𝑡) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h (𝑡 i))

\end{code}

---

#### EXISTECE

At the base step the term is a generator, `ℊ x`, and the free lift of `h`
agrees with `h`.

In the inductive step the term is `node f 𝑡` and the free lift is defined as
follows:

Assuming we know the image of each subterm `𝑡 i` under the free lift of `h`, define the
free lift at the full term by applying `f ̂ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

 lift-hom : (𝑨 : Algebra α 𝑆) → (X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
 lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → cong (f ̂ 𝑨) refl

\end{code}

---

#### UNIQUENESS

Finally, we prove that the homomorphism is unique.

This requires a weak form of function extensionality at universe levels `𝓥` and `α` which
we postulate by making it part of the premise in the following function type 
definition.

\begin{code}

 open ≡-Reasoning

 free-unique : swelldef 𝓥 α → (𝑨 : Algebra α 𝑆)(g h : hom (𝑻 X) 𝑨)
  →            (∀ x → ∣ g ∣ (ℊ x) ≡ ∣ h ∣ (ℊ x))
               ----------------------------------------
  →            ∀ (t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

 free-unique _ _ _ _ p (ℊ x) = p x

 free-unique wd 𝑨 g h p (node 𝑓 𝑡) =

  ∣ g ∣ (node 𝑓 𝑡)    ≡⟨ ∥ g ∥ 𝑓 𝑡 ⟩
  (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)  ≡⟨ wd (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)(∣ h ∣ ∘ 𝑡)(λ i → free-unique wd 𝑨 g h p (𝑡 i)) ⟩
  (𝑓 ̂ 𝑨)(∣ h ∣ ∘ 𝑡)  ≡⟨ (∥ h ∥ 𝑓 𝑡)⁻¹ ⟩
  ∣ h ∣ (node 𝑓 𝑡)    ∎

\end{code}

---

#### LIFT OF SURJECTIVE IS SURJECTIVE

Let's account for what we have proved thus far about the term algebra.

If we postulate a type `X : Type χ` (representing an arbitrary collection of variable
symbols) such that for each `𝑆`-algebra `𝑨` there is a map from `X` to the domain of `𝑨`,
then it follows that for every `𝑆`-algebra `𝑨` there is a homomorphism from `𝑻 X` to
`∣ 𝑨 ∣` that "agrees with the original map on `X`," by which we mean that for all `x : X`
the lift evaluated at `ℊ x` is equal to the original function evaluated at `x`.

If we further assume that each of the mappings from `X` to `∣ 𝑨 ∣` is *surjective*, then
the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we
now prove.

\begin{code}

 lift-of-epi-is-epi : (𝑨 : Algebra α 𝑆){h₀ : X → ∣ 𝑨 ∣}
  →                   IsSurjective h₀ → IsSurjective ∣ lift-hom 𝑨 h₀ ∣

 lift-of-epi-is-epi 𝑨 {h₀} hE y = Goal
  where
  h₀⁻¹y = Inv h₀ (hE y)

  η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (ℊ h₀⁻¹y)
  η = (InvIsInv h₀ (hE y))⁻¹

  Goal : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
  Goal = eq (ℊ h₀⁻¹y) η

\end{code}

The `lift-hom` and `lift-of-epi-is-epi` types will be called to action when such
epimorphisms are needed later (e.g., in the [Varieties][] module).

---

### TERM OPERATIONS

Here we define *term operations* which are simply terms interpreted in a particular
algebra, and we prove some compatibility properties of term operations.

When we interpret a term in an algebra we call the resulting function a *term operation*.

Given a term `p` and an algebra `𝑨`, we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in
`𝑨`.  This is naturally defined by induction on the structure of the term.

1. If `p` is a generator `ℊ x` and `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then
   `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = 𝑓 𝑡`, where `𝑓` is an operation symbol, if `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of
   terms, and if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define

   `𝑨 ⟦ p ⟧ a = 𝑨 ⟦ 𝑓 𝑡 ⟧ a := (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ a)`.

Here is the agda-algebras implementation.

\begin{code}

 _⟦_⟧ : (𝑨 : Algebra α 𝑆){X : Type χ } → Term X → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
 𝑨 ⟦ ℊ x ⟧ = λ η → η x
 𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → (𝑓 ̂ 𝑨) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

\end{code}


---


#### INTERPRETATION OF TERMS IN PRODUCT ALGEBRAS

\begin{code}

 module _ (wd : swelldef 𝓥 (β ⊔ α)){X : Type χ }{I : Type β} where

  open ≡-Reasoning
  interp-prod : (p : Term X)(𝒜 : I → Algebra α 𝑆)(a : X → Π[ i ∈ I ] ∣ 𝒜 i ∣)
   →            (⨅ 𝒜 ⟦ p ⟧) a ≡ λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x) i)

  interp-prod (ℊ _) 𝒜 a = refl
  interp-prod (node 𝑓 𝑡) 𝒜 a = wd ((𝑓 ̂ ⨅ 𝒜)) u v IH
   where
   u : ∀ x → ∣ ⨅ 𝒜 ∣
   u = λ x → (⨅ 𝒜 ⟦ 𝑡 x ⟧) a
   v : ∀ x i → ∣ 𝒜 i ∣
   v = λ x i → (𝒜 i ⟦ 𝑡 x ⟧)(λ j → a j i)
   IH : ∀ i → u i ≡ v i
   IH = λ x → interp-prod (𝑡 x) 𝒜 a

  interp-prod2 : funext (α ⊔ β ⊔ χ) (α ⊔ β) → (p : Term X)(𝒜 : I → Algebra α 𝑆)
   →             ⨅ 𝒜 ⟦ p ⟧ ≡ (λ a i → (𝒜 i ⟦ p ⟧) λ x → a x i)
  interp-prod2 _ (ℊ x₁) 𝒜 = refl
  interp-prod2 fe (node f t) 𝒜 = fe λ a → wd (f ̂ ⨅ 𝒜)(u a) (v a) (IH a)
   where
   u : ∀ a x → ∣ ⨅ 𝒜 ∣
   u a = λ x → (⨅ 𝒜 ⟦ t x ⟧) a
   v : ∀ (a : X → ∣ ⨅ 𝒜 ∣) → ∀ x i → ∣ 𝒜 i ∣
   v a = λ x i → (𝒜 i ⟦ t x ⟧)(λ z → (a z) i)
   IH : ∀ a x → (⨅ 𝒜 ⟦ t x ⟧) a ≡ λ i → (𝒜 i ⟦ t x ⟧)(λ z → (a z) i)
   IH a = λ x → interp-prod (t x) 𝒜 a

\end{code}

---

#### INTERPRETATION OF A TERM IS THE FREE-LIFT

It turns out that the intepretation of a term is the same as the `free-lift` (modulo
argument order and assuming function extensionality).

\begin{code}

 free-lift-interp : swelldef 𝓥 α → (𝑨 : Algebra α 𝑆){X : Type χ }(η : X → ∣ 𝑨 ∣)(p : Term X)
  →                 (𝑨 ⟦ p ⟧) η ≡ (free-lift 𝑨 η) p

 free-lift-interp _ 𝑨 η (ℊ x) = refl
 free-lift-interp wd 𝑨 η (node 𝑓 𝑡) = wd (𝑓 ̂ 𝑨) (λ z → (𝑨 ⟦ 𝑡 z ⟧) η)
                                       ((free-lift 𝑨 η) ∘ 𝑡)((free-lift-interp wd 𝑨 η) ∘ 𝑡)

\end{code}

If the algebra 𝑨 happens to be `𝑻 X`, then we expect that `∀ 𝑠` we have `(𝑻 X)⟦ p ⟧ 𝑠 ≡ p
𝑠`. But what is `(𝑻 X)⟦ p ⟧ 𝑠` exactly? By definition, it depends on the form of `p` as
follows: 

* if `p = ℊ x`, then `(𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ ℊ x ⟧ 𝑠 ≡ 𝑠 x`

* if `p = node 𝑓 𝑡`, then `(𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠`

Now, assume `ϕ : hom 𝑻 𝑨`. Then by `comm-hom-term`, we have `∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = 𝑨 ⟦ p ⟧ ∣ ϕ ∣ ∘ 𝑠`.

* if `p = ℊ x` (and `𝑡 : X → ∣ 𝑻 X ∣`), then

  `∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x) ≡ ∣ ϕ ∣ (λ 𝑡 → h 𝑡) ≡ λ 𝑡 → (∣ ϕ ∣ ∘ 𝑡) x`

* if `p = node 𝑓 𝑡`, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠

We claim that for all `p : Term X` there exists `q : Term X` and `𝔱 : X → ∣ 𝑻 X ∣` such that `p ≡ (𝑻 X)⟦ q ⟧ 𝔱`. We prove this fact as follows.

\begin{code}

 term-interp : {X : Type χ} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X} → 𝑠 ≡ 𝑡 → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡
 term-interp 𝑓 {𝑠}{𝑡} st = cong (node 𝑓) st

 term-interp' : swelldef 𝓥 (ov χ) → {X : Type χ} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X}
  →             (∀ i → 𝑠 i ≡ 𝑡 i) → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡
 term-interp' wd 𝑓 {𝑠}{𝑡} st = wd (node 𝑓) 𝑠 𝑡 st

 term-gen : swelldef 𝓥 (ov χ) → {X : Type χ}(p : ∣ 𝑻 X ∣) → Σ[ q ∈ ∣ 𝑻 X ∣ ] p ≡ (𝑻 X ⟦ q ⟧) ℊ
 term-gen _ (ℊ x) = (ℊ x) , refl
 term-gen wd (node 𝑓 t) = (node 𝑓 (λ i → ∣ term-gen wd (t i) ∣)) ,
                          term-interp' wd 𝑓 λ i → ∥ term-gen wd (t i) ∥

 term-gen-agreement : (wd : swelldef 𝓥 (ov χ)){X : Type χ}(p : ∣ 𝑻 X ∣) → (𝑻 X ⟦ p ⟧) ℊ ≡ (𝑻 X ⟦ ∣ term-gen wd p ∣ ⟧) ℊ
 term-gen-agreement _ (ℊ x) = refl
 term-gen-agreement wd {X} (node f t) = wd (f ̂ 𝑻 X) (λ x → (𝑻 X ⟦ t x ⟧) ℊ)
                                          (λ x → (𝑻 X ⟦ ∣ term-gen wd (t x) ∣ ⟧) ℊ) λ i → term-gen-agreement wd (t i)

 term-agreement : swelldef 𝓥 (ov χ) → {X : Type χ}(p : ∣ 𝑻 X ∣) → p ≡  (𝑻 X ⟦ p ⟧) ℊ
 term-agreement wd {X} p = ∥ term-gen wd p ∥ ∙ (term-gen-agreement wd p)⁻¹


\end{code}


#### COMPATIBILITY OF TERMS

We now prove two important facts about term operations.  The first of these, which is used
very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

 open ≡-Reasoning

 comm-hom-term : swelldef 𝓥 β → {𝑨 : Algebra α 𝑆} (𝑩 : Algebra β 𝑆)
                 (h : hom 𝑨 𝑩){X : Type χ}(t : Term X) (a : X → ∣ 𝑨 ∣)
                 -----------------------------------------
   →             ∣ h ∣ ((𝑨 ⟦ t ⟧) a) ≡ (𝑩 ⟦ t ⟧) (∣ h ∣ ∘ a)

 comm-hom-term _ 𝑩 h (ℊ x) a = refl
 comm-hom-term wd {𝑨} 𝑩 h (node 𝑓 𝑡) a = ∣ h ∣((𝑓 ̂ 𝑨) λ i →  (𝑨 ⟦ 𝑡 i ⟧) a)    ≡⟨ i  ⟩
                                          (𝑓 ̂ 𝑩)(λ i →  ∣ h ∣ ((𝑨 ⟦ 𝑡 i ⟧) a))  ≡⟨ ii ⟩
                                          (𝑓 ̂ 𝑩)(λ r → (𝑩 ⟦ 𝑡 r ⟧) (∣ h ∣ ∘ a)) ∎
  where i  = ∥ h ∥ 𝑓 λ r → (𝑨 ⟦ 𝑡 r ⟧) a
        ii = wd (𝑓 ̂ 𝑩) (λ i₁ → ∣ h ∣ ((𝑨 ⟦ 𝑡 i₁ ⟧) a))
                        (λ r → (𝑩 ⟦ 𝑡 r ⟧) (λ x → ∣ h ∣ (a x)))
                        λ j → comm-hom-term wd 𝑩 h (𝑡 j) a

\end{code}

To conclude this module, we prove that every term is compatible with every congruence
relation. That is, if `t : Term X` and `θ : Con 𝑨`, then `a θ b → t(a) θ t(b)`.

\begin{code}

 open IsCongruence

 _∣:_ : {𝑨 : Algebra α 𝑆}(t : Term X)(θ : Con 𝑨 {ρ}) → (𝑨 ⟦ t ⟧) |: ∣ θ ∣
 ((ℊ x) ∣: θ) p = p x
 ((node 𝑓 𝑡) ∣: θ) p = is-compatible ∥ θ ∥ 𝑓 _ _ λ i → (𝑡 i ∣: θ) p

\end{code}



---

### SUBUNIVERSES

Suppose 𝑨 is an algebra.  A subset B ⊆ ∣ 𝑨 ∣ is said to be **closed under the operations
of** 𝑨 if for each 𝑓 ∈ ∣ 𝑆 ∣ and all tuples 𝒃 : ∥ 𝑆 ∥ 𝑓 → 𝐵 the element (𝑓 ̂ 𝑨) 𝒃 belongs
to B.

If a subset B ⊆ 𝐴 is closed under the operations of 𝑨, then we call B a **subuniverse** of 𝑨.

We first show how to represent the collection of subuniverses of an algebra `𝑨`.

Since a subuniverse is viewed as a subset of the domain of `𝑨`, we define it as a
predicate on `∣ 𝑨 ∣`.  Thus, the collection of subuniverses is a predicate on predicates
on `∣ 𝑨 ∣`.

\begin{code}

 Subuniverses : (𝑨 : Algebra α 𝑆) → Pred (Pred ∣ 𝑨 ∣ β) _

 Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

\end{code}


---

#### SUBUNIVERSES AS RECORDS

Next we define a type to represent a single subuniverse of an algebra. If `𝑨` is the
algebra in question, then a subuniverse of `𝑨` is a subset of (i.e., predicate over) the
domain `∣ 𝑨 ∣` that belongs to `Subuniverses 𝑨`.

\begin{code}

 record Subuniverse {𝑨 : Algebra α 𝑆} : Type (ov(α ⊔ β)) where
  constructor mksub
  field       sset  : Pred ∣ 𝑨 ∣ β
              isSub : sset ∈ Subuniverses 𝑨
\end{code}


---

#### SUBUNIVERSE GENERATION

If `𝑨` is an algebra and `X ⊆ ∣ 𝑨 ∣` a subset of the domain of `𝑨`, then the **subuniverse
of** `𝑨` **generated by** `X` is typically denoted by `Sg`<sup>`𝑨`</sup>`(X)` and defined
to be the smallest subuniverse of `𝑨` containing `X`.  Equivalently,

Sgᴬ (X)  =  ⋂ { U : U is a subuniverse of 𝑨 and B ⊆ U }.

We define an inductive type, denoted by `Sg`, that represents the subuniverse generated by
a given subset of the domain of a given algebra, as follows.

\begin{code}

 data Sg (𝑨 : Algebra α 𝑆)(X : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
  where
  var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
  app : ∀ f a → Im a ⊆ Sg 𝑨 X → (f ̂ 𝑨) a ∈ Sg 𝑨 X

\end{code}

---

#### SUBUNIVERSE LEMMAS

By structural induction we prove `Sg X` is the smallest subuniverse of `𝑨` containing `X`.

\begin{code}

 sgIsSmallest : {𝓡 : Level}(𝑨 : Algebra α 𝑆){X : Pred ∣ 𝑨 ∣ β}(Y : Pred ∣ 𝑨 ∣ 𝓡)
  →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y  →  Sg 𝑨 X ⊆ Y

 sgIsSmallest _ _ _ XinY (var Xv) = XinY Xv
 sgIsSmallest 𝑨 Y YsubA XinY (app f a SgXa) = Yfa
  where
  IH : Im a ⊆ Y
  IH i = sgIsSmallest 𝑨 Y YsubA XinY (SgXa i)

  Yfa : (f ̂ 𝑨) a ∈ Y
  Yfa = YsubA f a IH

\end{code}

When the element of `Sg X` is constructed as `app f a SgXa`, we may assume (the induction
hypothesis) that the arguments in the tuple `a` belong to `Y`. Then the result of applying
`f` to `a` also belongs to `Y` since `Y` is a subuniverse.

---

#### SUBUNIVERSE LEMMAS

Here we formalize a few basic properties of subuniverses. First, the intersection of
subuniverses is again a subuniverse.

\begin{code}

 sub-intersection : {𝓘 : Level}{𝑨 : Algebra α 𝑆}{I : Type 𝓘}{𝒜 : I → Pred ∣ 𝑨 ∣ β}
  →                 (( i : I ) → 𝒜 i ∈ Subuniverses 𝑨)
                    ----------------------------------
  →                 ⋂ I 𝒜 ∈ Subuniverses 𝑨

 sub-intersection σ f a ν = λ i → σ i f a (λ x → ν x i)

\end{code}

In the proof above, we assume the following typing judgments:

```
 σ : ∀ i → 𝒜 i ∈ Subuniverses 𝑨
 f : ∣ 𝑆 ∣
 a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
 ν : Im 𝑎 ⊆ ⋂ I 𝒜
```
and we must prove `(f ̂ 𝑨) a ∈ ⋂ I 𝒜`. In this case, Agda will fill in the proof term
`λ i → σ i f a (λ x → ν x i)` automatically with the command `C-c C-a`.

---

#### SUBUNIVERSE LEMMAS

Next, subuniverses are closed under the action of term operations.

\begin{code}


 sub-term-closed : {X : Type χ}(𝑨 : Algebra α 𝑆){B : Pred ∣ 𝑨 ∣ β}
  →                (B ∈ Subuniverses 𝑨) → (t : Term X)(b : X → ∣ 𝑨 ∣)
  →                ((x : X) → (b x ∈ B)) → (𝑨 ⟦ t ⟧)b ∈ B

 sub-term-closed 𝑨 AB (ℊ x) b Bb = Bb x

 sub-term-closed 𝑨{B} σ (node f t)b ν =
   σ f  (λ z → (𝑨 ⟦ t z ⟧) b) λ x → sub-term-closed 𝑨{B} σ (t x) b ν

\end{code}

In the induction step of the foregoing proof, the typing judgments of the premise are the
following:

```
𝑨   : Algebra α 𝑆
B   : Pred ∣ 𝑨 ∣ β
σ   : B ∈ Subuniverses 𝑨
f   : ∣ 𝑆 ∣
t   : ∥ 𝑆 ∥ 𝑓 → Term X
b   : X → ∣ 𝑨 ∣
ν   : ∀ x → b x ∈ B
```
and the given proof term establishes the goal `𝑨 ⟦ node f t ⟧ b ∈ B`.

---

#### SUBUNIVERSE LEMMAS

Next we prove the important fact that homomorphisms are uniquely determined by their
values on a generating set.

\begin{code}

 open ≡-Reasoning

 hom-unique : swelldef 𝓥 β → {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
              (X : Pred ∣ 𝑨 ∣ α)  (g h : hom 𝑨 𝑩)
  →           ((x : ∣ 𝑨 ∣) → (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x))
              -------------------------------------------------
  →           (a : ∣ 𝑨 ∣) → (a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

 hom-unique _ _ _ _ σ a (var x) = σ a x

 hom-unique wd {𝑨}{𝑩} X g h σ fa (app 𝑓 a ν) = Goal
  where
  IH : ∀ x → ∣ g ∣ (a x) ≡ ∣ h ∣ (a x)
  IH x = hom-unique wd{𝑨}{𝑩} X g h σ (a x) (ν x)

  Goal : ∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)
  Goal = ∣ g ∣ ((𝑓 ̂ 𝑨) a)   ≡⟨ ∥ g ∥ 𝑓 a ⟩
         (𝑓 ̂ 𝑩)(∣ g ∣ ∘ a ) ≡⟨ wd (𝑓 ̂ 𝑩) (∣ g ∣ ∘ a) (∣ h ∣ ∘ a) IH ⟩
         (𝑓 ̂ 𝑩)(∣ h ∣ ∘ a)  ≡⟨ ( ∥ h ∥ 𝑓 a )⁻¹ ⟩
         ∣ h ∣ ((𝑓 ̂ 𝑨) a )  ∎

\end{code}

In the induction step, the following typing judgments are assumed:

```
wd  : swelldef 𝓥 β
𝑨   : Algebra α 𝑆
𝑩   : Algebra β 𝑆
X   : Pred ∣ 𝑨 ∣ α
g h  : hom 𝑨 𝑩
σ   : Π x ꞉ ∣ 𝑨 ∣ , (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x)
fa  : ∣ 𝑨 ∣
fa  = (𝑓 ̂ 𝑨) a
𝑓   : ∣ 𝑆 ∣
a   : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
ν   : Im a ⊆ Sg 𝑨 X
```

and, under these assumptions, we proved `∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)`.

---

### SUBALGEBRAS

Given algebras `𝑨 : Algebra α 𝑆` and `𝑩 : Algebra𝓦β 𝑆`, we say that `𝑩` is a
**subalgebra** of `𝑨` just in case `𝑩` can be *homomorphically embedded* in `𝑨`.

That is, there exists a map `h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣` that is a hom and embedding.

\begin{code}

 module _ {α β : Level} where

  _IsSubalgebraOf_ : (𝑩 : Algebra β 𝑆)(𝑨 : Algebra α 𝑆) → Type _
  𝑩 IsSubalgebraOf 𝑨 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

  Subalgebra : Algebra α 𝑆 → Type _
  Subalgebra 𝑨 = Σ[ 𝑩 ∈ (Algebra β 𝑆) ] 𝑩 IsSubalgebraOf 𝑨

\end{code}

An simpler alternative would be to proclaim `𝑩` is a subalgebra of `𝑨` iff there is an
injective homomorphism from `𝐵` into `𝑨`.

In preparation for the next major release of the agda-algebras library, we will
investigate the consequences of taking that path instead of the stricter embedding
requirement we chose for the definition of the type `IsSubalgebraOf`.


---


#### CONSEQUENCE OF FIRST HOMOMORPHISM THEOREM

We prove an important lemma that makes use of the `IsSubalgebraOf` type defined above.

If `𝑨` and `𝑩` are `𝑆`-algebras and `h : hom 𝑨 𝑩` a homomorphism from `𝑨` to `𝑩`, then the
quotient `𝑨 ╱ ker h` is (isomorphic to) a subalgebra of `𝑩`.  This is an easy corollary of
the First Homomorphism Theorem.

\begin{code}

 module _ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(h : hom 𝑨 𝑩)

          -- extensionality assumptions:
          (pe : pred-ext α β)(fe : swelldef 𝓥 β)

          -- truncation assumptions:
          (Bset : is-set ∣ 𝑩 ∣)
          (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣)

  where
  FirstHomCorollary|Set : (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) IsSubalgebraOf 𝑩
  FirstHomCorollary|Set = ϕhom , ϕinj
   where
    hh = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip
    ϕhom : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩
    ϕhom = ∣ hh ∣

    ϕinj : IsInjective ∣ ϕhom ∣
    ϕinj = ∣ snd ∥ hh ∥ ∣

\end{code}

---

If we apply the foregoing theorem to the special case in which the `𝑨` is term algebra `𝑻
X`, we obtain the following result which will be useful later.

\begin{code}

 module _ (X : Type χ)(𝑩 : Algebra β 𝑆)(h : hom (𝑻 X) 𝑩)

          -- extensionality assumptions:
          (pe : pred-ext (𝓞 ⊔ 𝓥 ⊔ lsuc χ) β)(fe : swelldef 𝓥 β)

          -- truncation assumptions:
          (Bset : is-set ∣ 𝑩 ∣)
          (buip : blk-uip (Term X) ∣ kercon fe {𝑩} h ∣)

  where
  free-quot-subalg : (ker[ 𝑻 X ⇒ 𝑩 ] h ↾ fe) IsSubalgebraOf 𝑩
  free-quot-subalg = FirstHomCorollary|Set{α = (𝓞 ⊔ 𝓥 ⊔ lsuc χ)}(𝑻 X) 𝑩 h pe fe Bset buip

\end{code}

For convenience, we define the following shorthand for the subalgebra relation.

\begin{code}

 _≤_ : Algebra β 𝑆 → Algebra α 𝑆 → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 𝑩 ≤ 𝑨 = 𝑩 IsSubalgebraOf 𝑨

\end{code}

From now on we will use `𝑩 ≤ 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.

---

#### SUBALGEBRAS OF A CLASS

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : Algebra β 𝑆`
denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is
a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express
this assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

\begin{code}

 module _ {α β : Level} where

  _IsSubalgebraOfClass_ : Algebra β 𝑆 → Pred (Algebra α 𝑆) γ → Type _

  𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ Algebra α 𝑆 ] Σ[ sa ∈ Subalgebra {α}{β} 𝑨 ] ((𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ sa ∣))

\end{code}

Using this type, we express the collection of all subalgebras of algebras in a class by the type `SubalgebraOfClass`, which we now define.

\begin{code}

  SubalgebraOfClass : Pred (Algebra α 𝑆)(ov α) → Type _
  SubalgebraOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra β 𝑆 ] 𝑩 IsSubalgebraOfClass 𝒦

\end{code}


---

#### SUBALGEBRA LEMMAS 1

We conclude this module by proving a number of useful facts about subalgebras. Some of the
formal statements below may appear to be redundant, and indeed they are to some extent.
However, each one differs slightly from the next, if only with respect to the explicitness
or implicitness of their arguments.  The aim is to make it as convenient as possible to
apply the lemmas in different situations.

First we show that the subalgebra relation is a *preorder*; i.e., it is a reflexive,
transitive binary relation.

\begin{code}

 ≤-reflexive : (𝑨 : Algebra α 𝑆) → 𝑨 ≤ 𝑨
 ≤-reflexive 𝑨 = (𝑖𝑑 ∣ 𝑨 ∣ , λ 𝑓 𝑎 → refl) , Injection.injective id-is-injective

 ≤-refl : {𝑨 : Algebra α 𝑆} → 𝑨 ≤ 𝑨
 ≤-refl {𝑨 = 𝑨} = ≤-reflexive 𝑨


 ≤-transitivity : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(𝑪 : Algebra γ 𝑆)
  →               𝑪 ≤ 𝑩 → 𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑨

 ≤-transitivity 𝑨 𝑩 𝑪 CB BA = (∘-hom 𝑪 𝑨 ∣ CB ∣ ∣ BA ∣) , Goal
  where
  Goal : IsInjective ∣ (∘-hom 𝑪 𝑨 ∣ CB ∣ ∣ BA ∣) ∣
  Goal = ∘-injective ∥ CB ∥ ∥ BA ∥

 ≤-trans : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆} → 𝑪 ≤ 𝑩 → 𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑨
 ≤-trans 𝑨 {𝑩}{𝑪} = ≤-transitivity 𝑨 𝑩 𝑪

\end{code}

---

#### SUBALGEBRA LEMMAS 2

Next we prove that if two algebras are isomorphic and one of them is a subalgebra of `𝑨`,
then so is the other.

\begin{code}
 open ≡-Reasoning

 iso→injective : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
  →              ((f , _ , _ , _) : 𝑨 ≅ 𝑩) → IsInjective ∣ f ∣
 iso→injective {𝑨 = 𝑨} (f , g , f∼g , g∼f) {x}{y} fxfy =
  x                  ≡⟨ (g∼f x)⁻¹ ⟩
  (∣ g ∣ ∘ ∣ f ∣) x  ≡⟨ cong ∣ g ∣ fxfy ⟩
  (∣ g ∣ ∘ ∣ f ∣) y  ≡⟨ g∼f y ⟩
  y                  ∎

 ≤-iso : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆}
  →      𝑪 ≅ 𝑩 → 𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑨

 ≤-iso 𝑨 {𝑩} {𝑪} CB BA = (g ∘ f , gfhom) , gfinj
  where
   f : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   f = fst ∣ CB ∣
   g : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   g = fst ∣ BA ∣

   gfinj : IsInjective (g ∘ f)
   gfinj = ∘-injective (iso→injective CB)(∥ BA ∥)

   gfhom : is-homomorphism 𝑪 𝑨 (g ∘ f)
   gfhom = ∘-is-hom 𝑪 𝑨 {f}{g} (snd ∣ CB ∣) (snd ∣ BA ∣)

\end{code}

---

#### SUBALGEBRA TRANSPORT LEMMAS

\begin{code}

 ≤-trans-≅ : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
  →          𝑨 ≤ 𝑩 → 𝑨 ≅ 𝑪 → 𝑪 ≤ 𝑩

 ≤-trans-≅ 𝑨 {𝑩} 𝑪 A≤B B≅C = ≤-iso 𝑩 (≅-sym B≅C) A≤B


 ≤-TRANS-≅ : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
  →          𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 ≤-TRANS-≅ 𝑨 𝑪 A≤B B≅C = (∘-hom 𝑨 𝑪 ∣ A≤B ∣ ∣ B≅C ∣) , Goal
  where
  Goal : IsInjective ∣ (∘-hom 𝑨 𝑪 ∣ A≤B ∣ ∣ B≅C ∣) ∣
  Goal = ∘-injective (∥ A≤B ∥)(iso→injective B≅C)


 ≤-mono : (𝑩 : Algebra β 𝑆){𝒦 𝒦' : Pred (Algebra α 𝑆) γ}
  →       𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

 ≤-mono 𝑩 KK' KB = ∣ KB ∣ , fst ∥ KB ∥ , KK' (∣ snd ∥ KB ∥ ∣) , ∥ (snd ∥ KB ∥) ∥

\end{code}

---


#### LIFTS OF SUBALGEBRAS


\begin{code}

 module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)}{𝑩 : Algebra α 𝑆} where

  Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-Alg 𝑩 α) IsSubalgebraOfClass 𝒦
  Lift-is-sub (𝑨 , (sa , (KA , B≅sa))) = 𝑨 , sa , KA , ≅-trans (≅-sym Lift-≅) B≅sa


 Lift-≤ : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{γ : Level} → 𝑩 ≤ 𝑨 → Lift-Alg 𝑩 γ ≤ 𝑨
 Lift-≤ 𝑨 B≤A = ≤-iso 𝑨 (≅-sym Lift-≅) B≤A

 ≤-Lift : (𝑨 : Algebra α 𝑆){γ : Level}{𝑩 : Algebra β 𝑆} → 𝑩 ≤ 𝑨 → 𝑩 ≤ Lift-Alg 𝑨 γ
 ≤-Lift 𝑨 {γ} {𝑩} B≤A = ≤-TRANS-≅ 𝑩 {𝑨} (Lift-Alg 𝑨 γ) B≤A Lift-≅


 Lift-≤-Lift : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level) → 𝑨 ≤ 𝑩 → Lift-Alg 𝑨 ℓᵃ ≤ Lift-Alg 𝑩 ℓᵇ
 Lift-≤-Lift {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ A≤B = ≤-trans (Lift-Alg 𝑩 ℓᵇ) (≤-trans 𝑩 lAA A≤B) B≤lB
  where

  lAA : (Lift-Alg 𝑨 ℓᵃ) ≤ 𝑨
  lAA = Lift-≤ 𝑨 {𝑨} ≤-refl

  B≤lB : 𝑩 ≤ Lift-Alg 𝑩 ℓᵇ
  B≤lB = ≤-Lift 𝑩 ≤-refl

\end{code}


---



### VARIETIES, MODEL THEORY, AND EQUATIONAL LOGIC

The binary "models" relation ⊧, relating algebras (or classes of algebras) to the
identities that they satisfy, is defined.

We prove some closure and invariance properties of ⊧.

In particular, we prove the following facts (which are needed, for example, in the proof the Birkhoff HSP Theorem).

* [Algebraic invariance]  ⊧  is an *algebraic invariant* (stable under isomorphism).

* [Subalgebraic invariance] ⊧ is a *subalgebraic invariant*
  (ids modeled by a class are also modeled by all subalgebras of algebras in the class)

* [Product invariance] ⊧ is preserved under the taking of products
  (ids modeled by a class are also modeled by all products of algebras in the class)

---


#### THE MODELS RELATION ⊧

The "models" relation ⊧ is a binary relation from algebras to equations.

For a pair p q of terms, `𝑨 ⊧ p ≈ q` means the identity ∀ x → p x ≡ q x holds in 𝑨.

For a class 𝒦, we write `𝒦 ⊧ p ≋ q` when `𝑨 ⊧ p ≈ q` holds for all 𝑨 ∈ 𝒦.

\begin{code}

 module _ {X : Type χ} where

  _⊧_≈_ : Algebra α 𝑆 → Term X → Term X → Type(α ⊔ χ)
  𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

  _⊧_≋_ : Pred(Algebra α 𝑆)(ov α) → Term X → Term X → Type(χ ⊔ ov α)
  𝒦 ⊧ p ≋ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}


---



#### SEMANTICS OF ⊧

The expression `𝑨 ⊧ p ≈ q` represents the assertion that the identity `p ≈ q` holds
when interpreted in the algebra `𝑨`; syntactically, `𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧`.

It should be emphasized that the expression  `𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧` interpreted
computationally as an *extensional equality* in the following sense:

For each "environment" `ρ :  X → ∣ 𝑨 ∣`, we have  `𝑨 ⟦ p ⟧ ρ  ≡ 𝑨 ⟦ q ⟧ ρ`.


---


#### EQUATIONAL THEORIES AND MODELS

The type `Th` is defined so that if 𝒦 is a class of algebras, then
`Th 𝒦` is the set of identities modeled by all members of 𝒦.

\begin{code}

 Th : {X : Type χ} → Pred (Algebra α 𝑆)(ov α) → Pred(Term X × Term X)(χ ⊔ ov α)
 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

\end{code}

If `ℰ` is a set of identities, then the class of algebras satisfying all identities
in ℰ is `Mod ℰ`, which is defined in agda-algebras as

\begin{code}

 Mod : {X : Type χ} → Pred(Term X × Term X)(χ ⊔ ov α) → Pred(Algebra α 𝑆) (ov (χ ⊔ α))
 Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

\end{code}


---

#### ALGEBRAIC INVARIANCE OF ⊧

The binary relation ⊧ would be practically useless if it were not an *algebraic invariant*
(i.e., invariant under isomorphism).

\begin{code}

 open ≡-Reasoning

 module _ (wd : SwellDef){X : Type χ}{𝑨 : Algebra α 𝑆}
          (𝑩 : Algebra β 𝑆)(p q : Term X) where

  ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q

  ⊧-I-invar Apq (f , g , f∼g , g∼f) x =
   (𝑩 ⟦ p ⟧) x                      ≡⟨ wd χ β (𝑩 ⟦ p ⟧) x (∣ f ∣ ∘ ∣ g ∣ ∘ x) (λ i → ( f∼g (x i))⁻¹) ⟩
   (𝑩 ⟦ p ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘ x)  ≡⟨ (comm-hom-term (wd 𝓥 β) 𝑩 f p (∣ g ∣ ∘ x))⁻¹ ⟩
   ∣ f ∣ ((𝑨 ⟦ p ⟧) (∣ g ∣ ∘ x))    ≡⟨ cong ∣ f ∣ (Apq (∣ g ∣ ∘ x))  ⟩
   ∣ f ∣ ((𝑨 ⟦ q ⟧) (∣ g ∣ ∘ x))    ≡⟨ comm-hom-term (wd 𝓥 β) 𝑩 f q (∣ g ∣ ∘ x) ⟩
   (𝑩 ⟦ q ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘  x) ≡⟨ wd χ β (𝑩 ⟦ q ⟧) (∣ f ∣ ∘ ∣ g ∣ ∘ x) x (λ i → ( f∼g (x i))) ⟩
   (𝑩 ⟦ q ⟧) x                      ∎

\end{code}


 As the proof makes clear, we show 𝑩 ⊧ p ≈ q by showing that `𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧ holds
 *extensionally*, that is, `∀ x, 𝑩 ⟦ p ⟧ x ≡ 𝑩 ⟦q ⟧ x`.

#### LIFT-INVARIANCE OF ⊧

The ⊧ relation is also invariant under the algebraic lift and lower operations.

\begin{code}

 module _ (wd : SwellDef){X : Type χ}{𝑨 : Algebra α 𝑆} where

  ⊧-Lift-invar : (p q : Term X) → 𝑨 ⊧ p ≈ q → Lift-Alg 𝑨 β ⊧ p ≈ q
  ⊧-Lift-invar p q Apq = ⊧-I-invar wd (Lift-Alg 𝑨 _) p q Apq Lift-≅

  ⊧-lower-invar : (p q : Term X) → Lift-Alg 𝑨 β ⊧ p ≈ q  →  𝑨 ⊧ p ≈ q
  ⊧-lower-invar p q lApq = ⊧-I-invar wd 𝑨 p q lApq (≅-sym Lift-≅)

\end{code}



#### SUBALGEBRAIC INVARIANCE OF ⊧

Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`, which
fact can be formalized as follows.

\begin{code}

 module _ (wd : SwellDef){𝓤 𝓦 : Level}{X : Type χ} where

  ⊧-S-invar : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆){p q : Term X}
   →          𝑨 ⊧ p ≈ q  →  𝑩 ≤ 𝑨  →  𝑩 ⊧ p ≈ q
  ⊧-S-invar {𝑨} 𝑩 {p}{q} Apq B≤A b = (∥ B≤A ∥) (ξ b)
   where
   h : hom 𝑩 𝑨
   h = ∣ B≤A ∣

   ξ : ∀ b → ∣ h ∣ ((𝑩 ⟦ p ⟧) b) ≡ ∣ h ∣ ((𝑩 ⟦ q ⟧) b)
   ξ b = ∣ h ∣((𝑩 ⟦ p ⟧) b)   ≡⟨ comm-hom-term (wd 𝓥 𝓤) 𝑨 h p b ⟩
        (𝑨 ⟦ p ⟧)(∣ h ∣ ∘ b) ≡⟨ Apq (∣ h ∣ ∘ b) ⟩
        (𝑨 ⟦ q ⟧)(∣ h ∣ ∘ b) ≡⟨ (comm-hom-term (wd 𝓥 𝓤) 𝑨 h q b)⁻¹ ⟩
        ∣ h ∣((𝑩 ⟦ q ⟧) b)   ∎

\end{code}

Next, identities modeled by a class of algebras is also modeled by all subalgebras of the
class.  In other terms, every term equation `p ≈ q` that is satisfied by all `𝑨 ∈ 𝒦` is
also satisfied by every subalgebra of a member of 𝒦.

 \begin{code}

  ⊧-S-class-invar : {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}(p q : Term X)
   →                𝒦 ⊧ p ≋ q → (𝑩 : SubalgebraOfClass 𝒦) → ∣ 𝑩 ∣ ⊧ p ≈ q
  ⊧-S-class-invar p q Kpq (𝑩 , 𝑨 , SA , (ka , BisSA)) = ⊧-S-invar 𝑩 {p}{q}((Kpq ka)) (h , hinj)
   where
   h : hom 𝑩 𝑨
   h = ∘-hom 𝑩 𝑨 (∣ BisSA ∣) ∣ snd SA ∣
   hinj : IsInjective ∣ h ∣
   hinj = ∘-injective (iso→injective BisSA) ∥ snd SA ∥

\end{code}


#### PRODUCT INVARIANCE OF ⊧

An identity satisfied by all algebras in an indexed collection is also satisfied by the
product of algebras in that collection.

\begin{code}

 module _ (fe : DFunExt)(wd : SwellDef){I : Type β}(𝒜 : I → Algebra α 𝑆){X : Type χ} where

  ⊧-P-invar : (p q : Term X) → (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
  ⊧-P-invar p q 𝒜pq a = goal
   where
   -- This is where function extensionality is used.
   ξ : (λ i → (𝒜 i ⟦ p ⟧) (λ x → (a x) i)) ≡ (λ i → (𝒜 i ⟦ q ⟧)  (λ x → (a x) i))
   ξ = fe β α λ i → 𝒜pq i (λ x → (a x) i)

   goal : (⨅ 𝒜 ⟦ p ⟧) a  ≡  (⨅ 𝒜 ⟦ q ⟧) a
   goal = (⨅ 𝒜 ⟦ p ⟧) a                      ≡⟨ interp-prod (wd 𝓥 (α ⊔ β)) p 𝒜 a ⟩
       (λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x)i))  ≡⟨ ξ ⟩
       (λ i → (𝒜 i ⟦ q ⟧)(λ x → (a x)i))  ≡⟨ (interp-prod (wd 𝓥 (α ⊔ β)) q 𝒜 a)⁻¹ ⟩
       (⨅ 𝒜 ⟦ q ⟧) a                      ∎

\end{code}

An identity satisfied by all algebras in a class is also satisfied by the product of
algebras in the class.

\begin{code}

  ⊧-P-class-invar : (𝒦 : Pred (Algebra α 𝑆)(ov α)){p q : Term X}
   →                𝒦 ⊧ p ≋ q → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ p ≈ q

  ⊧-P-class-invar 𝒦 {p}{q}σ K𝒜 = ⊧-P-invar p q λ i → σ (K𝒜 i)

\end{code}

Another fact that will turn out to be useful is that a product of a collection of algebras
models p ≈ q if the lift of each algebra in the collection models p ≈ q.

\begin{code}

  ⊧-P-lift-invar : (p q : Term X) → (∀ i → Lift-Alg (𝒜 i) β ⊧ p ≈ q)  →  ⨅ 𝒜 ⊧ p ≈ q
  ⊧-P-lift-invar p q α = ⊧-P-invar p q Aipq
   where
   Aipq : ∀ i → (𝒜 i) ⊧ p ≈ q
   Aipq i = ⊧-lower-invar wd p q (α i) --  (≅-sym Lift-≅)

\end{code}


#### HOMOMORPHIC INVARIANCE OF ⊧

If an algebra 𝑨 models an identity p ≈ q, then the pair (p , q) belongs to the kernel of
every homomorphism φ : hom (𝑻 X) 𝑨 from the term algebra to 𝑨; that is, every homomorphism
from 𝑻 X to 𝑨 maps p and q to the same element of 𝑨.

\begin{code}

 module _ (wd : SwellDef){X : Type χ}{𝑨 : Algebra α 𝑆} where

  ⊧-H-invar : {p q : Term X}(φ : hom (𝑻 X) 𝑨) → 𝑨 ⊧ p ≈ q  →  ∣ φ ∣ p ≡ ∣ φ ∣ q

  ⊧-H-invar {p}{q}φ β = ∣ φ ∣ p               ≡⟨ cong ∣ φ ∣(term-agreement(wd 𝓥 (ov χ)) p)⟩
                       ∣ φ ∣((𝑻 X ⟦ p ⟧) ℊ)  ≡⟨ comm-hom-term (wd 𝓥 α) 𝑨 φ p ℊ ⟩
                       (𝑨 ⟦ p ⟧) (∣ φ ∣ ∘ ℊ) ≡⟨ β (∣ φ ∣ ∘ ℊ ) ⟩
                       (𝑨 ⟦ q ⟧) (∣ φ ∣ ∘ ℊ) ≡⟨ (comm-hom-term (wd 𝓥 α)  𝑨 φ q ℊ )⁻¹ ⟩
                       ∣ φ ∣ ((𝑻 X ⟦ q ⟧) ℊ) ≡⟨(cong ∣ φ ∣ (term-agreement (wd 𝓥 (ov χ)) q))⁻¹ ⟩
                       ∣ φ ∣ q               ∎


\end{code}

More generally, an identity is satisfied by all algebras in a class if and only if that
identity is invariant under all homomorphisms from the term algebra `𝑻 X` into algebras of
the class. More precisely, if `𝒦` is a class of `𝑆`-algebras and `𝑝`, `𝑞` terms in the
language of `𝑆`, then,

```
  𝒦 ⊧ p ≈ q  ⇔  ∀ 𝑨 ∈ 𝒦,  ∀ φ : hom (𝑻 X) 𝑨,  φ ∘ (𝑻 X)⟦ p ⟧ = φ ∘ (𝑻 X)⟦ q ⟧.
```

\begin{code}

 module _ (wd : SwellDef){X : Type χ}{𝒦 : Pred (Algebra α 𝑆)(ov α)}  where

  -- ⇒ (the "only if" direction)
  ⊧-H-class-invar : {p q : Term X}
   →                𝒦 ⊧ p ≋ q → ∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∀ a → ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)
  ⊧-H-class-invar {p = p}{q} σ 𝑨 φ ka a = ξ
   where
   ξ : ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)
   ξ = ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a)  ≡⟨ comm-hom-term (wd 𝓥 α) 𝑨 φ p a ⟩
         (𝑨 ⟦ p ⟧)(∣ φ ∣ ∘ a)   ≡⟨ (σ ka) (∣ φ ∣ ∘ a) ⟩
         (𝑨 ⟦ q ⟧)(∣ φ ∣ ∘ a)   ≡⟨ (comm-hom-term (wd 𝓥 α) 𝑨 φ q a)⁻¹ ⟩
         ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)  ∎


  -- ⇐ (the "if" direction)
  ⊧-H-class-coinvar : {p q : Term X}
   →  (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∀ a → ∣ φ ∣ ((𝑻 X ⟦ p ⟧) a) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) a)) → 𝒦 ⊧ p ≋ q

  ⊧-H-class-coinvar {p}{q} β {𝑨} ka = goal
   where
   φ : (a : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
   φ a = lift-hom 𝑨 a

   goal : 𝑨 ⊧ p ≈ q
   goal a = (𝑨 ⟦ p ⟧)(∣ φ a ∣ ∘ ℊ)     ≡⟨(comm-hom-term (wd 𝓥 α) 𝑨 (φ a) p ℊ)⁻¹ ⟩
               (∣ φ a ∣ ∘ (𝑻 X ⟦ p ⟧)) ℊ  ≡⟨ β 𝑨 (φ a) ka ℊ ⟩
               (∣ φ a ∣ ∘ (𝑻 X ⟦ q ⟧)) ℊ  ≡⟨ (comm-hom-term (wd 𝓥 α) 𝑨 (φ a) q ℊ) ⟩
               (𝑨 ⟦ q ⟧)(∣ φ a ∣ ∘ ℊ)     ∎


\end{code}


---

### EQUATIONAL LOGIC

Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

A straight-forward verification confirms that H, S, and P are **closure operators**
(expansive, monotone, and idempotent).  A class 𝒦 of 𝑆-algebras is said to be *closed
under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, 𝒦 is *closed under
the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆
𝒦`). The operators H, S, and P can be composed with one another repeatedly, forming yet
more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to
which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under
isomorphism.

A **variety** is a class of algebras, in the same signature, that is closed under the
taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties
we define inductive types for the closure operators `H`, `S`, and `P` that are composable.
Separately, we define an inductive type `V` which simultaneously represents closure under
all three operators, `H`, `S`, and `P`.

We import some of these things from sub-modules.

\begin{code}
 open import Varieties.Closure.H {𝑆 = 𝑆} as VC-H public
 open import Varieties.Closure.S {𝑆 = 𝑆}as VC-S public
 open import Varieties.Closure.P {𝑆 = 𝑆} as VC-P public
 open import Varieties.Closure.V {𝑆 = 𝑆} as VC-V public

 open VC-H using (H) public
 open VC-S public
 open VC-P public
 open VC-V public
\end{code}

---


#### Closure Properties

The types defined above represent operators with useful closure properties. We now prove a
handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that we'll need
it later, so it too must be formalized.

\begin{code}

 S⊆SP : (𝒦 : Pred (Algebra α 𝑆)(ov α))
  →     S{α}{β} 𝒦 ⊆ S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦)

 S⊆SP {α} {β} 𝒦 {.(Lift-Alg 𝑨 β)}(sbase{𝑨} x) = siso spllA(≅-sym Lift-≅)
  where
  llA : Algebra (α ⊔ β) 𝑆
  llA = Lift-Alg (Lift-Alg 𝑨 β) (α ⊔ β)

  spllA : llA ∈ S (P 𝒦)
  spllA = sbase{α ⊔ β}{α ⊔ β} (pbase x)

 S⊆SP {α} {β} 𝒦 {.(Lift-Alg 𝑨 β)}(slift{𝑨} x) = subalgebra→S lAsc
  where
  splAu : 𝑨 ∈ S(P 𝒦)
  splAu = S⊆SP{α}{α} 𝒦 x

  Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
  Asc = S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} splAu

  lAsc : (Lift-Alg 𝑨 β) IsSubalgebraOfClass (P 𝒦)
  lAsc = Lift-Alg-subP' Asc

 S⊆SP {α} {β} 𝒦 {𝑩}(ssub{𝑨} sA B≤A) = ssub (subalgebra→S lAsc)( ≤-Lift 𝑨 B≤A )
  where
   lA : Algebra (α ⊔ β) 𝑆
   lA = Lift-Alg 𝑨 β

   splAu : 𝑨 ∈ S (P 𝒦)
   splAu = S⊆SP{α}{α} 𝒦 sA

   Asc : 𝑨 IsSubalgebraOfClass (P 𝒦)
   Asc = S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} splAu

   lAsc : lA IsSubalgebraOfClass (P 𝒦)
   lAsc = Lift-Alg-subP' Asc

 S⊆SP {α = α}{β} 𝒦 {𝑩}(siso{𝑨} sA A≅B) = siso{α ⊔ β}{α ⊔ β} lAsp lA≅B
  where
  lA : Algebra (α ⊔ β) 𝑆
  lA = Lift-Alg 𝑨 β

  lAsc : lA IsSubalgebraOfClass (P 𝒦)
  lAsc = Lift-Alg-subP' (S→subalgebra{α}{P{α}{α} 𝒦}{𝑨} (S⊆SP 𝒦 sA))

  lAsp : lA ∈ S(P 𝒦)
  lAsp = subalgebra→S{α ⊔ β}{α ⊔ β}{P{α}{β} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}


---

We need to formalize one more lemma before arriving the main objective of this section,
which is the proof of the inclusion PS⊆SP.

\begin{code}

 module _ {α β : Level} {𝒦 : Pred(Algebra α 𝑆)(ov α)} where

  lemPS⊆SP : hfunext β α → funext β α → {I : Type β}{ℬ : I → Algebra α 𝑆}
   →         (∀ i → (ℬ i) IsSubalgebraOfClass 𝒦)
   →         ⨅ ℬ IsSubalgebraOfClass (P{α}{β} 𝒦)

  lemPS⊆SP hwu fwu {I}{ℬ} B≤K = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜) , ξ , (⨅≅ {fiu = fwu}{fiw = fwu} B≅SA)
   where
   𝒜 : I → Algebra α 𝑆
   𝒜 = λ i → ∣ B≤K i ∣

   SA : I → Algebra α 𝑆
   SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

   B≅SA : ∀ i → ℬ i ≅ SA i
   B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥

   SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
   SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

   h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
   h = λ i → fst ∣ SA≤𝒜 i ∣

   hinj : ∀ i → IsInjective (h i)
   hinj = λ i → snd (snd ∣ ∥ B≤K i ∥ ∣)

   σ : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
   σ = λ x i → (h i) (x i)
   ν : is-homomorphism (⨅ SA) (⨅ 𝒜) σ
   ν = λ 𝑓 𝒂 → fwu λ i → (snd ∣ SA≤𝒜 i ∣) 𝑓 (λ x → 𝒂 x i)

   σinj : IsInjective σ
   σinj σxσy = fwu λ i → (hinj i)(cong-app σxσy i)

   ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
   ⨅SA≤⨅𝒜 = (σ , ν) , σinj

   ξ : ⨅ 𝒜 ∈ P 𝒦
   ξ = produ (λ i → P-expa (∣ snd ∥ B≤K i ∥ ∣))


\end{code}


---

#### PS(𝒦) ⊆ SP(𝒦)

Finally, we are in a position to prove that a product of subalgebras of algebras in a
class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

 module _ {fovu : funext (ov α) (ov α)}      -- ← extensionality postulate
          {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  PS⊆SP :
          hfunext (ov α)(ov α)               -- ← extensionality postulate

   →      P{ov α}{ov α} (S{α}{ov α} 𝒦) ⊆ S{ov α}{ov α} (P{α}{ov α} 𝒦)

  PS⊆SP _ (pbase (sbase x)) = sbase (pbase x)

  PS⊆SP _ (pbase (slift{𝑨} x)) = slift (S⊆SP{α}{ov α} 𝒦 (slift x))

  PS⊆SP _ (pbase{𝑩}(ssub{𝑨} sA B≤A)) = siso ( ssub (S⊆SP 𝒦 (slift sA))
                                              (Lift-≤-Lift (ov α) {𝑨} (ov α) B≤A) ) ≅-refl

  PS⊆SP _ (pbase (siso{𝑨}{𝑩} x A≅B)) = siso (S⊆SP 𝒦 (slift x)) ( Lift-Alg-iso A≅B )

  PS⊆SP hfe (pliftu x) = slift (PS⊆SP hfe x)

  PS⊆SP hfe (pliftw x) = slift (PS⊆SP hfe x)

  PS⊆SP hfe (produ{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
   where
    ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{α}{ov α} 𝒦)
    ξ i = S→subalgebra (PS⊆SP hfe (x i))

    η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov α}{ov α} (P{α}{ov α} 𝒦))
    η = lemPS⊆SP hfe fovu {I} {𝒜} ξ

  PS⊆SP hfe (prodw{I}{𝒜} x) = (S-mono (P-idemp)) (subalgebra→S η)
   where
    ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{α}{ov α} 𝒦)
    ξ i = S→subalgebra (PS⊆SP hfe (x i))

    η : ⨅ 𝒜 IsSubalgebraOfClass (P{ov α}{ov α} (P{α}{ov α} 𝒦))
    η = lemPS⊆SP hfe fovu  {I} {𝒜} ξ

  PS⊆SP hfe (pisow{𝑨}{𝑩} pA A≅B) = siso (PS⊆SP hfe pA) A≅B

\end{code}

---

#### MORE CLASS INCLUSIONS

We conclude this subsection with three more inclusion relations that will have bit parts
to play later (e.g., in the formal proof of Birkhoff's Theorem).

\begin{code}

 module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  P⊆V : P{α}{β} 𝒦 ⊆ V{α}{β} 𝒦

  P⊆V (pbase A∈K)    = vbase  A∈K
  P⊆V (pliftu A∈P)   = vlift  (P⊆V A∈P)
  P⊆V (pliftw A∈P)   = vliftw (P⊆V A∈P)
  P⊆V (produ Ai∈P)   = vprodu (P⊆V ∘ Ai∈P)
  P⊆V (prodw Ai∈P)   = vprodw (P⊆V ∘ Ai∈P)
  P⊆V (pisow A∈P A≅) = visow  (P⊆V A∈P) A≅


  SP⊆V : S{α ⊔ β}{α ⊔ β} (P{α}{β} 𝒦) ⊆ V 𝒦

  SP⊆V (sbase{𝑨} A∈P)        = P⊆V (pisow A∈P Lift-≅)
  SP⊆V (slift{𝑨} A∈SP)       = vliftw (SP⊆V A∈SP)
  SP⊆V (ssub{𝑨}{𝑩} A∈SP B≤A) = vssubw (SP⊆V A∈SP) B≤A
  SP⊆V (siso A∈SP A≅)        = visow (SP⊆V A∈SP) A≅

\end{code}

---

#### V IS CLOSED UNDER LIFT

As mentioned earlier, a technical hurdle that must be overcome when formalizing proofs in
Agda is the proper handling of universe levels. In particular, in the proof of the
Birkhoff's theorem, for example, we will need to know that if an algebra 𝑨 belongs to the
variety V 𝒦, then so does the lift of 𝑨.  Let us get the tedious proof of this technical
lemma out of the way.

Above we proved that `SP(𝒦) ⊆ V(𝒦)`, and we did so under fairly general assumptions about
the universe level parameters.  Unfortunately, this is sometimes not quite general enough,
so we now prove the inclusion again for the specific universe parameters that align with
subsequent applications of this result.


\begin{code}

 module _ {fe₀ : funext (ov α) α}
          {fe₁ : funext ((ov α) ⊔ (lsuc (ov α))) (lsuc (ov α))}
          {fe₂ : funext (ov α) (ov α)}
          {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  open Vlift {α}{fe₀}{fe₁}{fe₂}{𝒦}

  SP⊆V' : S{ov α}{lsuc (ov α)} (P{α}{ov α} 𝒦) ⊆ V 𝒦

  SP⊆V' (sbase{𝑨} x) = visow (VlA (SP⊆V (sbase x))) (≅-sym (Lift-Alg-assoc 𝑨))
  SP⊆V' (slift x) = VlA (SP⊆V x)

  SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw (VlA (SP⊆V spA)) B≤lA
   where
    B≤lA : 𝑩 ≤ Lift-Alg 𝑨 (lsuc (ov α))
    B≤lA = ≤-Lift 𝑨 B≤A

  SP⊆V' (siso{𝑨}{𝑩} x A≅B) = visow (VlA (SP⊆V x)) Goal
   where
    Goal : Lift-Alg 𝑨 (lsuc (ov α)) ≅ 𝑩
    Goal = ≅-trans (≅-sym Lift-≅) A≅B

\end{code}


#### ⨅ S(𝒦) ∈ SP(𝒦)

Finally, we prove a result that plays an important role, e.g., in the formal proof of
Birkhoff's Theorem. As we saw in [Algebras.Products][], the (informal) product `⨅ S(𝒦)` of
all subalgebras of algebras in 𝒦 is implemented (formally) in the [UniversalAlgebra][]
library as `⨅ 𝔄 S(𝒦)`. Our goal is to prove that this product belongs to `SP(𝒦)`. We do so
by first proving that the product belongs to `PS(𝒦)` and then applying the `PS⊆SP` lemma.

Before doing so, we need to redefine the class product so that each factor comes with a
map from the type `X` of variable symbols into that factor.  We will explain the reason
for this below.

\begin{code}

 module class-products-with-maps {α : Level}
  {X : Type α}
  {fe𝓕α : funext (ov α) α}
  {fe₁ : funext ((ov α) ⊔ (lsuc (ov α))) (lsuc (ov α))}
  {fe₂ : funext (ov α) (ov α)}
  (𝒦 : Pred (Algebra α 𝑆)(ov α))
  where

  ℑ' : Type (ov α)
  ℑ' = Σ[ 𝑨 ∈ (Algebra α 𝑆) ] ((𝑨 ∈ S{α}{α} 𝒦) × (X → ∣ 𝑨 ∣))

\end{code}

Notice that the second component of this dependent pair type is  `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.
In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`, until we
realized that adding the type `X → ∣ 𝑨 ∣` is quite useful. Later we will see exactly why,
but for now suffice it to say that a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as
an *ambient context*, or more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to
*variable symbols* in `X`.  When computing with or reasoning about products, while we
don't want to rigidly impose a context in advance, want do want to lay our hands on
whatever context is ultimately assumed.  Including the "context map" inside the index type
`ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ`
to the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 :
Algebra α 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the
corresponding algebra is simply the first projection.

\begin{code}

  𝔄' : ℑ' → Algebra α 𝑆
  𝔄' = λ (i : ℑ') → ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

  class-product' : Algebra (ov α) 𝑆
  class-product' = ⨅ 𝔄'

\end{code}

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, we view the triple `(𝑨 , p , h) ∈ ℑ` as an index over
the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection
of the product `⨅ 𝔄` onto the `(𝑨 , p, h)`-th component. 

\begin{code}

  class-prod-s-∈-ps : class-product' ∈ P{ov α}{ov α}(S 𝒦)
  class-prod-s-∈-ps = pisow psPllA (⨅≅ {fiu = fe₂}{fiw = fe𝓕α} llA≅A)

   where
   lA llA : ℑ' → Algebra (ov α) 𝑆
   lA i =  Lift-Alg (𝔄 i) (ov α)
   llA i = Lift-Alg (lA i) (ov α)

   slA : ∀ i → (lA i) ∈ S 𝒦
   slA i = siso (fst ∥ i ∥) Lift-≅

   psllA : ∀ i → (llA i) ∈ P (S 𝒦)
   psllA i = pbase (slA i)

   psPllA : ⨅ llA ∈ P (S 𝒦)
   psPllA = produ psllA

   llA≅A : ∀ i → (llA i) ≅ (𝔄' i)
   llA≅A i = ≅-trans (≅-sym Lift-≅)(≅-sym Lift-≅)

\end{code}


So, since `PS⊆SP`, we see that that the product of all subalgebras of a class `𝒦` belongs to `SP(𝒦)`.

\begin{code}

  class-prod-s-∈-sp : hfunext (ov α) (ov α) → class-product ∈ S(P 𝒦)
  class-prod-s-∈-sp hfe = PS⊆SP {fovu = fe₂} hfe class-prod-s-∈-ps

\end{code}


---

### EQUATION PRESERVATION

We show that identities are preserved by closure operators H, S, and P.

This will establish the easy direction of Birkhoff's HSP Theorem.

#### H PRESERVES IDENTITIES

First we prove that the closure operator H is compatible with identities that hold in the
given class.

\begin{code}

 module _ (wd : SwellDef){X : Type χ} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  H-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → H{β = α} 𝒦 ⊧ p ≋ q
  H-id1 p q σ (hbase x) = ⊧-Lift-invar wd p q (σ x)
  H-id1 p q σ (hhimg{𝑨}{𝑪} HA (𝑩 , ((φ , φh) , φE))) b = goal
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = (H-id1 p q σ) HA

   preim : X → ∣ 𝑨 ∣
   preim x = Inv φ (φE (b x))

   ζ : ∀ x → φ (preim x) ≡ b x
   ζ x = InvIsInv φ (φE (b x))

   goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
   goal = (𝑩 ⟦ p ⟧) b          ≡⟨ wd χ α (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
       (𝑩 ⟦ p ⟧)(φ ∘ preim) ≡⟨(comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) p preim)⁻¹ ⟩
       φ((𝑨 ⟦ p ⟧) preim)   ≡⟨ cong φ (IH preim) ⟩
       φ((𝑨 ⟦ q ⟧) preim)   ≡⟨ comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) q preim ⟩
       (𝑩 ⟦ q ⟧)(φ ∘ preim) ≡⟨ wd χ α (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
       (𝑩 ⟦ q ⟧) b          ∎

\end{code}

The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we
formalize it for completeness.

\begin{code}

  H-id2 : ∀ {β} → (p q : Term X) → H{β = β} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

  H-id2 p q Hpq KA = ⊧-lower-invar wd p q (Hpq (hbase KA))

\end{code}

---

#### S PRESERVES IDENTITIES

\begin{code}

  S-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → S{β = α} 𝒦 ⊧ p ≋ q

  S-id1 p q σ (sbase x) = ⊧-Lift-invar wd p q (σ x)
  S-id1 p q σ (slift x) = ⊧-Lift-invar wd p q ((S-id1 p q σ) x)

  S-id1 p q σ (ssub{𝑨}{𝑩} sA B≤A) = ⊧-S-class-invar wd p q goal ν
   where --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
   τ : 𝑨 ⊧ p ≈ q
   τ = S-id1 p q σ sA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq refl = τ

   goal : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   goal {𝑩} (inl x) = σ x
   goal {𝑩} (inr y) = Apq y

   ν : SubalgebraOfClass (λ z → (𝒦 ∪ ｛ 𝑨 ｝) (fst z , snd z))
   ν = (𝑩 , 𝑨 , (𝑩 , B≤A) , _⊎_.inj₂ refl , ≅-refl)

  S-id1 p q σ (siso{𝑨}{𝑩} x x₁) = ⊧-I-invar wd 𝑩 p q (S-id1 p q σ x) x₁

  -- Conversely,

  S-id2 : ∀{β}(p q : Term X) → S{β = β}𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q
  S-id2 p q Spq {𝑨} KA = ⊧-lower-invar wd p q (Spq (sbase KA))

\end{code}


---


#### P PRESERVES IDENTITIES

\begin{code}

 module _ (fe : DFunExt) (wd : SwellDef)  -- extensionality postulates

          {X : Type χ} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  P-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → P{β = α} 𝒦 ⊧ p ≋ q

  P-id1 p q σ (pbase x) = ⊧-Lift-invar wd p q (σ x)
  P-id1 p q σ (pliftu x) = ⊧-Lift-invar wd p q ((P-id1 p q σ) x)
  P-id1 p q σ (pliftw x) = ⊧-Lift-invar wd p q ((P-id1 p q σ) x)
  P-id1 p q σ (produ{I}{𝒜} x) = ⊧-P-lift-invar fe wd 𝒜  p q IH
   where
   IH : ∀ i → (Lift-Alg (𝒜 i) α) ⊧ p ≈ q
   IH i = ⊧-Lift-invar wd  p q ((P-id1 p q σ) (x i))
  P-id1 p q σ (prodw{I}{𝒜} x) = ⊧-P-lift-invar fe wd 𝒜  p q IH
   where
   IH : ∀ i → (Lift-Alg (𝒜 i) α) ⊧ p ≈ q
   IH i = ⊧-Lift-invar wd  p q ((P-id1 p q σ) (x i))
  P-id1 p q σ (pisow{𝑨}{𝑩} x y) = ⊧-I-invar wd 𝑩 p q (P-id1 p q σ x) y

 -- Conversely,

 module _  (wd : SwellDef){X : Type χ} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  P-id2 : ∀ {β}(p q : Term X) → P{β = β} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q
  P-id2 p q PKpq KA = ⊧-lower-invar wd p q (PKpq (pbase KA))

\end{code}


#### V PRESERVES IDENTITIES

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

\begin{code}

 module Vid (fe : DFunExt)(wd : SwellDef) -- extensionality postulates
            {X : Type χ} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  V-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{β = α} 𝒦 ⊧ p ≋ q

  V-id1 p q σ (vbase x) = ⊧-Lift-invar wd p q (σ x)
  V-id1 p q σ (vlift{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
  V-id1 p q σ (vliftw{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)

  V-id1 p q σ (vhimg{𝑨}{𝑪}VA (𝑩 , ((φ , φh) , φE))) b = goal
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q σ VA

   preim : X → ∣ 𝑨 ∣
   preim x = Inv φ (φE (b x))

   ζ : ∀ x → φ (preim x) ≡ b x
   ζ x = InvIsInv φ (φE (b x))

   goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
   goal = (𝑩 ⟦ p ⟧) b          ≡⟨ wd χ α (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
       (𝑩 ⟦ p ⟧)(φ ∘ preim) ≡⟨(comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) p preim)⁻¹ ⟩
       φ((𝑨 ⟦ p ⟧) preim)   ≡⟨ cong φ (IH preim) ⟩
       φ((𝑨 ⟦ q ⟧) preim)   ≡⟨ comm-hom-term (wd 𝓥 α) 𝑩 (φ , φh) q preim ⟩
       (𝑩 ⟦ q ⟧)(φ ∘ preim) ≡⟨ wd χ α (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
       (𝑩 ⟦ q ⟧) b          ∎

  V-id1 p q σ ( vssubw {𝑨}{𝑩} VA B≤A ) =
   ⊧-S-class-invar wd p q goal (𝑩 , 𝑨 , (𝑩 , B≤A) , inr refl , ≅-refl)
    where
    IH : 𝑨 ⊧ p ≈ q
    IH = V-id1 p q σ VA

    Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
    Asinglepq refl = IH

    goal : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    goal {𝑩} (inl x) = σ x
    goal {𝑩} (inr y) = Asinglepq y

  V-id1 p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
  V-id1 p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
  V-id1 p q σ (visou{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B
  V-id1 p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B


 -- conversely

 module _ (wd : SwellDef){X : Type χ}{𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  V-id2 : (p q : Term X) → (V{β = β} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
  V-id2 p q Vpq {𝑨} KA = ⊧-lower-invar wd p q (Vpq (vbase KA))

\end{code}

---

\begin{code}

 module Vid' (fe : DFunExt)(wd : SwellDef) {X : Type χ} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  open Vid fe wd {X}{𝒦} public

  V-id1' : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{β = β} 𝒦 ⊧ p ≋ q

  V-id1' p q σ (vbase x) = ⊧-Lift-invar wd p q (σ x)
  V-id1' p q σ (vlift{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1 p q σ) x)
  V-id1' p q σ (vliftw{𝑨} x) = ⊧-Lift-invar wd p q ((V-id1' p q σ) x)
  V-id1' p q σ (vhimg{𝑨}{𝑪} VA (𝑩 , ((φ , φh) , φE))) b = goal
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1' p q σ VA

   preim : X → ∣ 𝑨 ∣
   preim x = Inv φ (φE (b x))

   ζ : ∀ x → φ (preim x) ≡ b x
   ζ x = InvIsInv φ (φE (b x))

   goal : (𝑩 ⟦ p ⟧) b ≡ (𝑩 ⟦ q ⟧) b
   goal = (𝑩 ⟦ p ⟧) b          ≡⟨ wd χ _ (𝑩 ⟦ p ⟧) b (φ ∘ preim )(λ i → (ζ i)⁻¹)⟩
       (𝑩 ⟦ p ⟧)(φ ∘ preim) ≡⟨(comm-hom-term (wd 𝓥 _) 𝑩 (φ , φh) p preim)⁻¹ ⟩
       φ((𝑨 ⟦ p ⟧) preim)   ≡⟨ cong φ (IH preim) ⟩
       φ((𝑨 ⟦ q ⟧) preim)   ≡⟨ comm-hom-term (wd 𝓥 _) 𝑩 (φ , φh) q preim ⟩
       (𝑩 ⟦ q ⟧)(φ ∘ preim) ≡⟨ wd χ _ (𝑩 ⟦ q ⟧)(φ ∘ preim) b ζ ⟩
       (𝑩 ⟦ q ⟧) b          ∎

  V-id1' p q σ (vssubw {𝑨}{𝑩} VA B≤A) = ⊧-S-invar wd 𝑩 {p}{q}(V-id1' p q σ VA) B≤A
  V-id1' p q σ (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1 p q σ (V𝒜 i)
  V-id1' p q σ (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar fe wd 𝒜  p q λ i → V-id1' p q σ (V𝒜 i)
  V-id1' p q σ (visou {𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1 p q σ VA) A≅B
  V-id1' p q σ (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar wd 𝑩 p q (V-id1' p q σ VA)A≅B

\end{code}

---

#### CLASS IDENTITIES

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities
modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all
structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities
modeled by `𝒦`.   We formalize this observation as follows.

\begin{code}

 module _ (fe : DFunExt)(wd : SwellDef) -- extensionality postulates
          {X : Type χ} {𝒦 : Pred (Algebra α 𝑆)(ov α)} where

  𝕍 : Pred (Algebra (lsuc (ov α)) 𝑆) (lsuc (lsuc (ov α)))
  𝕍 = V{β = lsuc (ov α)} 𝒦

  𝒱 : Pred (Algebra (ov α) 𝑆) (lsuc (ov α))
  𝒱 = V{β = (ov α)} 𝒦

  open Vid' fe wd {X}{𝒦} public

  class-ids-⇒ : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  →  (p , q) ∈ Th 𝒱
  class-ids-⇒ p q pKq VCloA = V-id1' p q pKq VCloA

  class-ids-⇒' : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  →  (p , q) ∈ Th 𝕍
  class-ids-⇒' p q pKq VCloA = V-id1' p q pKq VCloA


  class-ids-⇐ : (p q : ∣ 𝑻 X ∣) → (p , q) ∈ Th 𝒱 →  𝒦 ⊧ p ≋ q
  class-ids-⇐ p q Thpq {𝑨} KA = ⊧-lower-invar wd p q (Thpq (vbase KA))


\end{code}

---

### FREE ALGEBRAS AND BIRKHOFF'S THEOREM

First we will define the relatively free algebra in a variety, which is the "freest"
algebra among (universal for) those algebras that model all identities holding in the
variety. Then we give a formal proof of Birkhoff's theorem which says that a variety is an
equational class. In other terms, a class `𝒦` of algebras is closed under the operators
`H`, `S`, and `P` if and only if 𝒦 is the class of algebras that satisfy some set of
identities.

---

#### THE FREE ALGEBRA IN THEORY

We formalize, for a given class `𝒦` of `𝑆`-algebras, the (relatively) free algebra in `S(P
𝒦)` over `X`.

We use the next definition to take a free algebra *for* a class `𝒦` and produce the free
algebra *in* `𝒦`.

Θ(𝒦, 𝑨) := {θ ∈ Con 𝑨 : 𝑨 / θ ∈ (S 𝒦)}   and     ψ(𝒦, 𝑨) := ⋂ Θ(𝒦, 𝑨).

Notice that `Θ(𝒦, 𝑨)` may be empty, in which case `ψ(𝒦, 𝑨) = 1` and then `𝑨 / ψ(𝒦, 𝑨)` is
trivial.

The free algebra is constructed by applying the above definitions to the special case in
which `𝑨` is the term algebra `𝑻 X` of `𝑆`-terms over `X`.

Since `𝑻 X` is free for (and in) the class of all `𝑆`-algebras, it follows that `𝑻 X` is
free for every class `𝒦` of `𝑆`-algebras. Of course, `𝑻 X` is not necessarily a member of
`𝒦`, but if we form the quotient of `𝑻 X` modulo the congruence `ψ(𝒦, 𝑻 X)`, which we
denote by `𝔉 := (𝑻 X) / ψ(𝒦, 𝑻 X)`, then it's not hard to see that `𝔉` is a subdirect
product of the algebras in `{(𝑻 𝑋) / θ}`, where `θ` ranges over `Θ(𝒦, 𝑻 X)`, so `𝔉`
belongs to `S(P 𝒦)`, and it follows that `𝔉` satisfies all the identities satisfied by all
members of `𝒦`.  Indeed, for each pair `p q : 𝑻 X`, if `𝒦 ⊧ p ≈ q`, then `p` and `q` must
belong to the same `ψ(𝒦, 𝑻 X)`-class, so `p` and `q` are identified in the quotient `𝔉`.

The `𝔉` that we have just defined is called the **free algebra over** `𝒦` **generated by**
`X` and (because of what we just observed) we may say that `𝔉` is free *in* `S(P 𝒦)`.

---

#### THE FREE ALGEBRA IN AGDA

Before we attempt to represent the free algebra in Agda we construct the congruence
`ψ(𝒦, 𝑻 𝑋)` described above.

First, we represent the congruence relation `ψCon`, modulo which `𝑻 X` yields the
relatively free algebra, `𝔉 𝒦 X := 𝑻 X ╱ ψCon`.  We let `ψ` be the collection of
identities `(p, q)` satisfied by all subalgebras of algebras in `𝒦`.

\begin{code}

 module _ {X : Type α}(𝒦 : Pred (Algebra α 𝑆) (ov α)) where

  𝓕 𝓕⁺ : Level
  𝓕 = ov α
  𝓕⁺ = lsuc (ov α)    -- (this will be the level of the relatively free algebra)


  ψ : Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) 𝓕

  ψ (p , q) = ∀(𝑨 : Algebra α 𝑆)(sA : 𝑨 ∈ S{α}{α} 𝒦)(h : X → ∣ 𝑨 ∣ )
                  →  (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q

\end{code}

---


#### THE FREE ALGEBRA IN AGDA

We convert the predicate ψ into a relation by currying.

\begin{code}

  ψRel : BinRel ∣ 𝑻 X ∣ 𝓕
  ψRel p q = ψ (p , q)

\end{code}

To express `ψRel` as a congruence of the term algebra `𝑻 X`, we must prove that

1. `ψRel` is compatible with the operations of `𝑻 X` (which are jsut the terms themselves) and
2. `ψRel` it is an equivalence relation.


---


#### THE FREE ALGEBRA IN AGDA

\begin{code}

  open ≡-Reasoning

  ψcompatible : swelldef 𝓥 α → compatible (𝑻 X) ψRel
  ψcompatible wd 𝑓 p q ψpq 𝑨 sA h = goal
   where
   φ : hom (𝑻 X) 𝑨
   φ = lift-hom 𝑨 h

   goal : ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p) ≡ ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)

   goal = ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p)  ≡⟨ ∥ φ ∥ 𝑓 p ⟩
          (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ p)  ≡⟨ wd (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ p) (∣ φ ∣ ∘ q) (λ i → ψpq i 𝑨 sA h) ⟩
          (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ q)  ≡⟨ (∥ φ ∥ 𝑓 q)⁻¹ ⟩
          ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)  ∎

  ψIsEquivalence : IsEquivalence ψRel
  ψIsEquivalence = record { refl = λ 𝑨 sA h → refl
                          ; sym = λ x 𝑨 sA h → (x 𝑨 sA h)⁻¹
                          ; trans = λ pψq qψr 𝑨 sA h → (pψq 𝑨 sA h) ∙ (qψr 𝑨 sA h) }
\end{code}

---

#### THE FREE ALGEBRA IN AGDA

We have collected all the pieces necessary to express the collection of identities
satisfied by all subalgebras of algebras in the class as a congruence relation of the term
algebra. We call this congruence `ψCon` and define it using the Congruence constructor
`mkcon`.

\begin{code}

  ψCon : swelldef 𝓥 α → Con (𝑻 X)
  ψCon wd = ψRel , mkcon ψIsEquivalence (ψcompatible wd)

\end{code}


---


#### THE HSP THEOREM

This section presents a formal proof of the Birkhoff HSP theorem.

To complete the proof of Birkhoff's HSP theorem, it remains to show that
`Mod X (Th (V 𝒦))` is contained in `V 𝒦`; that is, every algebra that models the equations
in `Th (V 𝒦)` belongs to `V 𝒦`.  This will prove that `V 𝒦` is an equational class.  (The
converse, that every equational class is a variety was already proved; see the remarks at
the end of this module.)

We accomplish this goal by constructing an algebra `𝔽` with the following properties:

1. `𝔽 ∈ V 𝒦` and

2. Every `𝑨 ∈ Mod X (Th (V 𝒦))` is a homomorphic image of `𝔽`.

We denote by `ℭ` the product of all subalgebras of algebras in `𝒦`, and by `homℭ` the
homomorphism from `𝑻 X` to `ℭ` defined as follows: `homℭ := ⨅-hom-co (𝑻 X) 𝔄s hom𝔄`.

Here, `⨅-hom-co` (defined in
[Homomorphisms.Basic](Homomorphisms.Basic.html#product-homomorphisms)) takes the term
algebra `𝑻 X`, a family `{𝔄s : I → Algebra α 𝑆}` of `𝑆`-algebras, and a family `hom𝔄 : ∀ i
→ hom (𝑻 X) (𝔄s i)` of homomorphisms and constructs the natural homomorphism `homℭ` from
`𝑻 X` to the product `ℭ := ⨅ 𝔄`.  The homomorphism `homℭ : hom (𝑻 X) (⨅ ℭ)` is natural in
the sense that the `i`-th component of the image of `𝑡 : Term X` under `homℭ` is the image
`∣ hom𝔄 i ∣ 𝑡` of 𝑡 under the i-th homomorphism `hom𝔄 i`.


---


#### 𝔽 ≤  ⨅ S(𝒦)

Now we come to a step in the Agda formalization of Birkhoff's theorem that is highly
nontrivial. We must prove that the free algebra embeds in the product ℭ of all subalgebras
of algebras in the class `𝒦`.  This is really the only stage in the proof of Birkhoff's
theorem that requires the truncation assumption that `ℭ` be a *set* (that is, `ℭ` has the
UIP property).


We will also need to assume several local function extensionality postulates and, as a
result, the next submodule will take as given the parameter `fe : (∀ a b → funext a b)`.

This allows us to postulate local function extensionality when and where we need it in the
proof. For example, if we want to assume function extensionality at universe levels 𝓥 and
α, we simply apply `fe` to those universes: `fe 𝓥 α`. (Earlier versions of the library
used just a single *global* function extensionality postulate at the start of most
modules, but we have since decided to exchange that elegant but crude option for greater
precision and transparency.)

\begin{code}

 module _ {α : Level}{fe : DFunExt}{wd : SwellDef}{X : Type α} {𝒦 : Pred (Algebra α 𝑆) (ov α)} where

  ℓ ℓᶠ : Level
  ℓ = ov α
  ℓᶠ = lsuc (ov α)    -- (this will be the level of the relatively free algebra)

  open class-products-with-maps {X = X}{fe ℓ α}{fe ℓᶠ ℓᶠ}{fe ℓ ℓ} 𝒦

\end{code}

---


We begin by constructing `ℭ`, using the approach described in the section on products of classes.

\begin{code}

  -- ℭ is the product of all subalgebras of algebras in 𝒦.
  ℭ : Algebra ℓ 𝑆
  ℭ = ⨅ 𝔄'

\end{code}

Observe that the inhabitants of `ℭ` are maps from `ℑ` to `{𝔄 i : i ∈ ℑ}`.  A homomorphism
from `𝑻 X` to `ℭ` is obtained as follows.

\begin{code}

  homℭ : hom (𝑻 X) ℭ
  homℭ = ⨅-hom-co 𝔄' (fe ℓ α){ℓ}(𝑻 X) λ i → lift-hom (𝔄' i)(snd ∥ i ∥)

\end{code}


---

#### THE FREE ALGEBRA

 As mentioned above, the initial version of the [Agda UniversalAlgebra][] used the free
 algebra `𝔉` developed above.  However, our new, more direct proof uses the algebra `𝔽`,
 which we now define, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X`
 to `𝔽`.

 We now define the algebra `𝔽`, which plays the role of the free algebra, along with the
 natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.

\begin{code}

  𝔽 : Algebra ℓᶠ 𝑆
  𝔽 = ker[ 𝑻 X ⇒ ℭ ] homℭ ↾ (wd 𝓥 (ov α))

  epi𝔽 : epi (𝑻 X) 𝔽
  epi𝔽 = πker (wd 𝓥 (ov α)) {ℭ} homℭ

  hom𝔽 : hom (𝑻 X) 𝔽
  hom𝔽 = epi-to-hom 𝔽 epi𝔽

  hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
  hom𝔽-is-epic = snd ∥ epi𝔽 ∥

\end{code}

---

We will need the following facts relating `homℭ`, `hom𝔽`, `and ψ`.

\begin{code}

  ψlemma0 : ∀ p q →  ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q  → (p , q) ∈ ψ 𝒦
  ψlemma0 p q phomℭq 𝑨 sA h = cong-app phomℭq (𝑨 , sA , h)

  ψlemma0-ap : {𝑨 : Algebra α 𝑆}{h : X → ∣ 𝑨 ∣} → 𝑨 ∈ S{α}{α} 𝒦
   →           kernel ∣ hom𝔽 ∣ ⊆ kernel (free-lift 𝑨 h)

  ψlemma0-ap {𝑨}{h} skA {p , q} x = goal where

   ν : ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q
   ν = ker-in-con {α = (ov α)}{ov α}{𝑻 X}{wd 𝓥 (lsuc (ov α))}(kercon (wd 𝓥 (ov α)) {ℭ} homℭ) {p}{q} x

   goal : (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
   goal = ((ψlemma0 p q) ν) 𝑨 skA h


\end{code}

---


We now use `ψlemma0-ap` to prove that every map `h : X → ∣ 𝑨 ∣`, from `X` to a subalgebra
`𝑨 ∈ S 𝒦` of `𝒦`, lifts to a homomorphism from `𝔽` to `𝑨`.

\begin{code}

  𝔽-lift-hom : (𝑨 : Algebra α 𝑆) → 𝑨 ∈ S{α}{α} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
  𝔽-lift-hom 𝑨 skA h = fst(HomFactor (fe ℓ α) (wd 𝓥 (lsuc (ov α)))  𝑨 (lift-hom 𝑨 h) hom𝔽 (ψlemma0-ap skA) hom𝔽-is-epic)

\end{code}

---


#### 𝒦 MODELS ψ

The goal of this subsection is to prove that `𝒦` models `ψ 𝒦`. In other terms, for all
pairs `(p , q) ∈ Term X × Term X` of terms, if `(p , q) ∈ ψ 𝒦`, then `𝒦 ⊧ p ≋ q`.

Next we define the lift of the natural embedding from `X` into 𝔽. We denote this
homomorphism by `𝔑 : hom (𝑻 X) 𝔽` and define it as follows.

\begin{code}

  open IsCongruence

  X↪𝔽 : X → ∣ 𝔽 ∣
  X↪𝔽 x = ⟪ ℊ x ⟫ -- (the implicit relation here is  ⟨ kercon (fe 𝓥 ℓ) ℭ homℭ ⟩ )

  𝔑 : hom (𝑻 X) 𝔽
  𝔑 = lift-hom 𝔽 X↪𝔽

\end{code}

---

It turns out that the homomorphism so defined is equivalent to `hom𝔽`.

\begin{code}
  open ≡-Reasoning

  hom𝔽-is-lift-hom : ∀ p → ∣ 𝔑 ∣ p ≡ ∣ hom𝔽 ∣ p
  hom𝔽-is-lift-hom (ℊ x) = refl
  hom𝔽-is-lift-hom (node 𝑓 𝒕) =
   ∣ 𝔑 ∣ (node 𝑓 𝒕)              ≡⟨ ∥ 𝔑 ∥ 𝑓 𝒕 ⟩
   (𝑓 ̂ 𝔽)(λ i → ∣ 𝔑 ∣(𝒕 i))      ≡⟨ cong(𝑓 ̂ 𝔽)(fe 𝓥 ℓᶠ (λ x → hom𝔽-is-lift-hom(𝒕 x))) ⟩
   (𝑓 ̂ 𝔽)(λ i → ∣ hom𝔽 ∣ (𝒕 i))  ≡⟨ (∥ hom𝔽 ∥ 𝑓 𝒕)⁻¹ ⟩
   ∣ hom𝔽 ∣ (node 𝑓 𝒕)           ∎

\end{code}

---

We need a three more lemmas before we are ready to tackle our main goal.

\begin{code}

  ψlemma1 : kernel ∣ 𝔑 ∣ ⊆ ψ 𝒦
  ψlemma1 {p , q} 𝔑pq 𝑨 sA h = goal
   where
    f : hom 𝔽 𝑨
    f = 𝔽-lift-hom 𝑨 sA h

    h' φ : hom (𝑻 X) 𝑨
    h' = ∘-hom (𝑻 X) 𝑨 𝔑 f
    φ = lift-hom 𝑨 h

    h≡φ : ∀ t → (∣ f ∣ ∘ ∣ 𝔑 ∣) t ≡ ∣ φ ∣ t
    h≡φ t = free-unique (wd 𝓥 α) 𝑨 h' φ (λ x → refl) t

    goal : ∣ φ ∣ p ≡ ∣ φ ∣ q
    goal = ∣ φ ∣ p             ≡⟨ (h≡φ p)⁻¹ ⟩
           ∣ f ∣ ( ∣ 𝔑 ∣ p )   ≡⟨ cong ∣ f ∣ 𝔑pq ⟩
           ∣ f ∣ ( ∣ 𝔑 ∣ q )   ≡⟨ h≡φ q ⟩
           ∣ φ ∣ q             ∎


  ψlemma2 : kernel ∣ hom𝔽 ∣ ⊆ ψ 𝒦
  ψlemma2 {p , q} hyp = ψlemma1 {p , q} goal
    where
     goal : (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q
     goal = (hom𝔽-is-lift-hom p) ∙ hyp ∙ (hom𝔽-is-lift-hom q)⁻¹


  ψlemma3 : ∀ p q → (p , q) ∈ ψ{X = X} 𝒦 → 𝒦 ⊧ p ≋ q
  ψlemma3 p q pψq {𝑨} kA h = goal
    where
    goal : (𝑨 ⟦ p ⟧) h ≡ (𝑨 ⟦ q ⟧) h
    goal = (𝑨 ⟦ p ⟧) h       ≡⟨ free-lift-interp (wd 𝓥 α) 𝑨 h p ⟩
           (free-lift 𝑨 h) p ≡⟨ pψq 𝑨 (siso (sbase kA) (≅-sym Lift-≅)) h ⟩
           (free-lift 𝑨 h) q ≡⟨ (free-lift-interp (wd 𝓥 α) 𝑨 h q)⁻¹  ⟩
           (𝑨 ⟦ q ⟧) h       ∎

\end{code}

---


With these results in hand, it is now trivial to prove the main theorem of this
subsection.

\begin{code}

  class-models-kernel : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝒦 ⊧ p ≋ q
  class-models-kernel p q hyp = ψlemma3 p q (ψlemma2 hyp)

  𝕍𝒦 : Pred (Algebra ℓᶠ 𝑆) (lsuc ℓᶠ)
  𝕍𝒦 = V{α = α}{β = ℓᶠ} 𝒦

  kernel-in-theory' : kernel ∣ hom𝔽 ∣ ⊆ Th (V 𝒦)
  kernel-in-theory' {p , q} pKq = (class-ids-⇒ fe wd p q (class-models-kernel p q pKq))

  kernel-in-theory : kernel ∣ hom𝔽 ∣ ⊆ Th 𝕍𝒦
  kernel-in-theory {p , q} pKq vkA x = class-ids-⇒' fe wd p q (class-models-kernel p q pKq) vkA x

  _↠_ : Type α → Algebra ℓᶠ 𝑆 → Type ℓᶠ
  X ↠ 𝑨 = Σ[ h ∈ (X → ∣ 𝑨 ∣) ] IsSurjective h

  𝔽-ModTh-epi : (𝑨 : Algebra ℓᶠ 𝑆) → (X ↠ 𝑨) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
  𝔽-ModTh-epi 𝑨 (η , ηE) AinMTV = goal
   where
   φ : hom (𝑻 X) 𝑨
   φ = lift-hom 𝑨 η

   φE : IsSurjective ∣ φ ∣
   φE = lift-of-epi-is-epi 𝑨 ηE

   pqlem2 : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
   pqlem2 p q hyp = λ x → AinMTV p q (kernel-in-theory hyp) x

   kerincl : kernel ∣ hom𝔽 ∣ ⊆ kernel ∣ φ ∣
   kerincl {p , q} x = ∣ φ ∣ p      ≡⟨ (free-lift-interp (wd 𝓥 ℓᶠ) 𝑨 η p)⁻¹ ⟩
                       (𝑨 ⟦ p ⟧) η  ≡⟨ pqlem2 p q x η ⟩
                       (𝑨 ⟦ q ⟧) η  ≡⟨ free-lift-interp (wd 𝓥 ℓᶠ) 𝑨 η q ⟩
                       ∣ φ ∣ q      ∎

   goal : epi 𝔽 𝑨
   goal = fst (HomFactorEpi (fe ℓ ℓᶠ) (wd 𝓥 (lsuc (ov α))) 𝑨 φ hom𝔽 kerincl hom𝔽-is-epic φE)

\end{code}

---



#### THE HOMOMORPHIC IMAGES OF 𝔽

Finally we come to one of the main theorems of this module; it asserts that every algebra
in `Mod X (Th 𝕍𝒦)` is a homomorphic image of 𝔽.  We prove this below as the function (or
proof object) `𝔽-ModTh-epi`.  Before that, we prove two auxiliary lemmas.

\begin{code}

  module _ (pe : pred-ext (ov α)(ov α))(wd : SwellDef) -- extensionality assumptions
           (Cset : is-set ∣ ℭ ∣)                       -- truncation assumptions
           (kuip : blk-uip(Term X)∣ kercon (wd 𝓥 (ov α)){ℭ}homℭ ∣)
   where

   𝔽≤ℭ : (ker[ 𝑻 X ⇒ ℭ ] homℭ ↾ (wd 𝓥 (ov α))) ≤ ℭ
   𝔽≤ℭ = FirstHomCorollary|Set (𝑻 X) ℭ homℭ pe (wd 𝓥 (ov α)) Cset kuip

\end{code}

The last piece we need to prove that every model of `Th 𝕍𝒦` is a homomorphic image of `𝔽`
is a crucial assumption that is taken for granted throughout informal universal
algebra---namely, that our collection `X` of variable symbols is arbitrarily large and
that we have an *environment* which interprets the variable symbols in every algebra
under consideration. In other terms, an environment provides, for every algebra `𝑨`, a
surjective mapping `η : X → ∣ 𝑨 ∣` from `X` onto the domain of `𝑨`.

We do *not* assert that for an arbitrary type `X` such surjective maps exist.  Indeed, our
`X` must is quite special to have this property.  Later, we will construct such an `X`,
but for now we simply postulate its existence. Note that this assumption that an
environment exists is only required in the proof of the theorem `𝔽-ModTh-epi`.

---

#### 𝔽 ∈ V(𝒦)

With this result in hand, along with what we proved earlier---namely,
`PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ V 𝒦`---it is not hard to show that `𝔽` belongs to `V 𝒦`.

\begin{code}

   𝔽∈SP : hfunext (ov α)(ov α) → 𝔽 ∈ (S{ℓ}{ℓᶠ} (P{α}{ℓ} 𝒦))
   𝔽∈SP hfe = ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

   𝔽∈𝕍 : hfunext (ov α)(ov α) → 𝔽 ∈ V 𝒦
   𝔽∈𝕍 hfe = SP⊆V' {α}{fe ℓ α}{fe ℓᶠ ℓᶠ}{fe ℓ ℓ}{𝒦} (𝔽∈SP hfe)

\end{code}















---


#### BIRKHOFF'S THEOREM in Agda


We develop the necessary ingredients above and combine them here.

\begin{code}

   Birkhoff : hfunext (ov α)(ov α) → (∀ 𝑨 → X ↠ 𝑨)

    →         Mod (Th (V 𝒦)) ⊆ V 𝒦

   Birkhoff hfe 𝕏 {𝑨} α =

    vhimg{𝑩 = 𝑨} (𝔽∈𝕍 hfe) (𝑨 , epi-to-hom 𝑨 φE , snd ∥ φE ∥)

    where
    φE : epi 𝔽 𝑨
    φE = 𝔽-ModTh-epi 𝑨 (𝕏 𝑨) α

\end{code}


The proof enlists the help of the 𝔽-ModTh-epi theorem which assumes a
suitable "environment"; this is manifested in the premise ∀ 𝑨 → X ↠ 𝑨.




---


#### THE CONVERSE

The converse  V 𝒦 ⊆ Mod X (Th (V 𝒦))  is a simple consequence of:

  Mod Th is a closure operator

Nonetheless, here's the proof.

\begin{code}

   Birkhoff-converse : V{α}{ℓ} 𝒦 ⊆ Mod{χ = α}{X = X} (Th (V 𝒦))
   Birkhoff-converse α p q pThq = pThq α

\end{code}

This completes the proof that every variety is an equational class.












---











                  T H A N K    Y O U  !!!














[the agda-algebras development team]: https://github.com/ualib/agda-algebras



---

































#### REFERENCES

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
[Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29)
[section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html)
[Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality)
[this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe)
[Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda)


----------------------------

Notes


[1] First, internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of `J`-tuples of
inhabitants of `A`. Next, recall that a continuous relation `R` denotes a certain
collection of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` "belongs to" or
"satisfies" `R`).  For such `R`, the type `eval-cont-rel R` represents a certain
collection of `I`-tuples of `J`-tuples, namely, the tuples `𝒶 : I → J → A` for which
`eval-cont-rel R 𝒶` holds. 

For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so
that we can write down a couple of the `J`-tuples as columns. For example, here are the
i-th and k-th columns (for some `i k : I`). 

```
𝒶 i 1      𝒶 k 1
𝒶 i 2      𝒶 k 2  <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒶 i J      𝒶 k J
```

Now `eval-cont-rel R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which asserts that each row
of the `I` columns shown above belongs to the original relation `R`. Finally,
`cont-compatible-op` takes a `J`-ary operation `𝑓 : Op J A` and an `I`-tuple `𝒶 : I → J →
A` of `J`-tuples, and determines whether the `I`-tuple `λ i → 𝑓 (𝑎 i)` belongs to `R`. 

---

[2] If `A` is a set and `𝑓` is a (`ρ 𝑓`)-ary operation on `A`, we often indicate this by
writing `𝑓 : A`<sup>ρ 𝑓</sup> `→ A`. On the other hand, the arguments of such an operation
form a (`ρ 𝑓`)-tuple, say, `(a 0, a 1, …, a (ρf-1))`, which may be viewed as the graph of
the function `a : ρ𝑓 → A`. When the codomain of `ρ` is `ℕ`, we may view `ρ 𝑓` as the
finite set `{0, 1, …, ρ𝑓 - 1}`. Thus, by identifying the `ρ𝑓`-th power `A`<sup>ρ 𝑓</sup>
with the type `ρ 𝑓 → A` of functions from `{0, 1, …, ρ𝑓 - 1}` to `A`, we identify the
function type `A`<sup>ρ f</sup> `→ A` with the function (or "functional") type `(ρ𝑓 → A) →
A`. 

**Example**. Suppose `𝑔 : (m → A) → A` is an `m`-ary operation on `A`, and `a : m → A` is
  an `m`-tuple on `A`. Then `𝑔 a` may be viewed as `𝑔 (a 0, a 1, …, a (m-1))`, which has
  type `A`. Suppose further that `𝑓 : (ρ𝑓 → B) → B` is a `ρ𝑓`-ary operation on `B`, let `a
  : ρ𝑓 → A` be a `ρ𝑓`-tuple on `A`, and let `h : A → B` be a function.  Then the following
  typing judgments obtain: `h ∘ a : ρ𝑓 → B` and we `𝑓 (h ∘ a) : B`. 


---

[3] Note that to each operation *symbol* `f ∈ F` corresponds an *operation* fᴬ of arity `ρf`;

we call such fᴬ the *interpretation* of the symbol f in the algebra `𝑨`.

We call an algebra in the signature `𝑆` an `𝑆`-*algebra*.  An algebra is called *finite*
if it has a finite domain, and is called *trivial* if its universe is a singleton.

Given two algebras `𝑨` and `𝑩`, we say that `𝑩` is a *reduct* of `𝑨` if both algebras have the
same domain and `𝑩` can be obtained from `𝑨` by simply removing some of the operations.





<!--

--UNUSED STUFF--

Level-of-Signature : {𝓞 𝓥 : Level} → Signature 𝓞 𝓥 → Level
Level-of-Signature {𝓞}{𝓥} _ = lsuc (𝓞 ⊔ 𝓥)

We could specialize and assume all arity types have universe level zero.

signature : (𝓞 : Level) → Type (lsuc 𝓞)
signature 𝓞 = Σ[ F ∈ Type 𝓞 ] (F → Type)

(We realized recently that everything we have done so far could be done with "little" arities types.)

record lilalgebra (α : Level) (𝑆 : signature 𝓞) : Type(lsuc(𝓞 ⊔ α)) where
 constructor mklilalg
 field
  carrier : Type α
  opsymbol : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → carrier) → carrier


##### <a id="the-universe-level-of-an-algebra">The universe level of an algebra</a>

Occasionally we will be given an algebra and we just need to know the universe level of its domain. The following utility function provides this.

-- Level-of-Alg : {𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → Level
-- Level-of-Alg {α = α} _ = ov α

-- Level-of-Carrier : {𝑆 : Signature 𝓞 𝓥} → Algebra α 𝑆 → Level
-- Level-of-Carrier {α = α} _ = α

-- and for records...
open algebra
Lift-algebra : {𝑆 : Signature 𝓞 𝓥} → algebra α 𝑆 → (β : Level) → algebra (α ⊔ β) 𝑆
Lift-algebra {𝑆 = 𝑆} 𝑨 β = mkalg (Lift β (carrier 𝑨)) (λ (f : ∣ 𝑆 ∣) → Lift-alg-op ((opsymbol 𝑨) f) β)




IsCongruence→Con : {𝑨 : Algebra α 𝑆}(θ : BinRel ∣ 𝑨 ∣ ρ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α 𝑆} → ((θ , _) : Con{α}{ρ} 𝑨) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥


#### <a id="example">Example</a>

We defined the *zero relation* `0[_]` in the [Relations.Discrete][] module.  We now build
the *trivial congruence*, which has `0[_]` as its underlying relation. Observe that `0[_]`
is equivalent to the identity relation `≡` and these are obviously both equivalence
relations. In fact, we already proved this of `≡` in the [Overture.Equality][] module, so
we simply apply the corresponding proofs. 

-- Example. The zero congruence of a structure.
0[_]Compatible : {α : Level}(𝑨 : Algebra α 𝑆){ρ : Level} → swelldef 𝓥 α → (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: (0[ ∣ 𝑨 ∣ ]{ρ})
0[ 𝑨 ]Compatible wd 𝑓 {i}{j} ptws0  = lift goal
  where
  goal : (𝑓 ̂ 𝑨) i ≡ (𝑓 ̂ 𝑨) j
  goal = wd (𝑓 ̂ 𝑨) i j (lower ∘ ptws0)

open IsCongruence
0Con[_] : {α : Level}(𝑨 : Algebra α 𝑆){ρ : Level} → swelldef 𝓥 α → Con{α}{α ⊔ ρ}  𝑨 
0Con[ 𝑨 ]{ρ} wd = let 0eq = 0[ ∣ 𝑨 ∣ ]Equivalence{ρ}  in
 ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ]Compatible wd)

A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.


𝟘[_╱_] : (𝑨 : Algebra α 𝑆)(θ : Con{α}{ρ} 𝑨) → BinRel (∣ 𝑨 ∣ / ∣ θ ∣)(α ⊔ lsuc ρ)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.

-- 𝟎[_╱_] : (𝑨 : Algebra α 𝑆)(θ : Con{α}{ρ} 𝑨){fe : funext 𝓥 (α ⊔ lsuc ρ)} → Con (𝑨 ╱ θ)
-- 𝟎[ 𝑨 ╱ θ ] {fe} = 𝟘[ 𝑨 ╱ θ ] , Δ (𝑨 ╱ θ) {fe}
𝟎[_╱_] : {α : Level}(𝑨 : Algebra α 𝑆){ρ : Level}(θ : Con {α}{ρ}𝑨) → swelldef 𝓥 (α ⊔ lsuc ρ)  → Con (𝑨 ╱ θ)
𝟎[_╱_] {α} 𝑨 {ρ} θ wd = let 0eq = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence  in
 ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ╱ θ ]Compatible {ρ} wd)




#### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

A *monomorphism* is an injective homomorphism and an *epimorphism* is a surjective homomorphism. These are represented in the [UniversalAlgebra][] library by the following types.

\begin{code}

-- is-monomorphism : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
-- is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsInjective g

-- mon : Algebra α 𝑆 → Algebra β 𝑆  → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
-- mon 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-monomorphism 𝑨 𝑩 g

-- is-epimorphism : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
-- is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

-- epi : Algebra α 𝑆 → Algebra β 𝑆  → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
-- epi 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epimorphism 𝑨 𝑩 g

\end{code}

It will be convenient to have a function that takes an inhabitant of `mon` (or `epi`) and extracts the homomorphism part, or *hom reduct* (that is, the pair consisting of the map and a proof that the map is a homomorphism).

\begin{code}

-- mon-to-hom : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆} → mon 𝑨 𝑩 → hom 𝑨 𝑩
-- mon-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

-- epi-to-hom : {𝑨 : Algebra α 𝑆}(𝑩 : Algebra β 𝑆) → epi 𝑨 𝑩 → hom 𝑨 𝑩
-- epi-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}






#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}

-- module _ {α β : Level}{𝑨 : Algebra α 𝑆} where

--  homker-comp : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆}(h : hom 𝑨 𝑩) → compatible 𝑨 (ker ∣ h ∣)
--  homker-comp wd {𝑩} h f {u}{v} kuv = ∣ h ∣((f ̂ 𝑨) u)   ≡⟨ ∥ h ∥ f u ⟩
--                                      (f ̂ 𝑩)(∣ h ∣ ∘ u) ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
--                                      (f ̂ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
--                                      ∣ h ∣((f ̂ 𝑨) v)   ∎


\end{code}

(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.

\begin{code}

 -- kercon : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆} → hom 𝑨 𝑩 → Con{α}{β} 𝑨
 -- kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.

\begin{code}

--  kerquo : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆} → hom 𝑨 𝑩 → Algebra (α ⊔ lsuc β) 𝑆
--  kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)


-- ker[_⇒_]_↾_ : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → hom 𝑨 𝑩 → swelldef 𝓥 β → Algebra (α ⊔ lsuc β) 𝑆
-- ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.

#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra α 𝑆} where

 -- πepi : (θ : Con{α}{β} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 -- πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
 --  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
 --  cπ-is-epic (C , R-block a refl ) =  Image_∋_.eq a refl

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.

\begin{code}

 -- πhom : (θ : Con{α}{β} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 -- πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)

\begin{code}

 -- πker : (wd : swelldef 𝓥 β){𝑩 : Algebra β 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 -- πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.

\begin{code}

 -- open IsCongruence

 -- ker-in-con : {wd : swelldef 𝓥 (α ⊔ lsuc β)}(θ : Con 𝑨)
 --  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 -- ker-in-con θ hyp = /-≡ θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

\begin{code}

-- module _ {𝓘 β : Level}{I : Type 𝓘}(ℬ : I → Algebra β 𝑆) where

 -- ⨅-hom-co : funext 𝓘 β → {α : Level}(𝑨 : Algebra α 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 -- ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra α 𝑆 and ℬ : I → Algebra β 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

\begin{code}

 -- ⨅-hom : funext 𝓘 β → {α : Level}(𝒜 : I → Algebra α 𝑆) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
 -- ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

 -- ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 -- ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.


If, in addition, we postulate extensionality of functions defined on the domain `ker[ 𝑨 ⇒ 𝑩 ] h`, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

 -- fe-NoetherHomUnique : {fuww : funext (α ⊔ lsuc β) β}(f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
 --  →                    ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
 --  →                    ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
 --  →                    ∣ f ∣ ≡ ∣ g ∣

 -- fe-NoetherHomUnique {fuww} f g hfk hgk = fuww (NoetherHomUnique f g hfk hgk)

\end{code}

The proof of `NoetherHomUnique` goes through for the special case of epimorphisms, as we now verify.

\begin{code}

 -- NoetherIsoUnique : (f g : epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
 --  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
 --  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
 --  →                 ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 -- NoetherIsoUnique f g hfk hgk = NoetherHomUnique (epi-to-hom 𝑩 f) (epi-to-hom 𝑩 g) hfk hgk

\end{code}




---

#### The First Homomorphism Theorem

Informally, every hom from `𝑨` to `𝑩` factors through the quotient `𝑨 ╱ ker h`.

Given `h : hom 𝑨 𝑩` there exists `φ : hom (𝑨 ╱ ker h) 𝑩` which, when composed with the
canonical projection `πker : 𝑨 ↠ 𝑨 ╱ ker h`, is equal to `h`; that is,

  `h = φ ∘ πker`.

Moreover, `φ` is a *monomorphism* and is unique.

Our formal proof of this theorem will require function extensionality, proposition
extensionality, and a couple of truncation assumptions.

The extensionality assumptions are postulated using `dfunext` and `pred-ext`.

As for truncation, to prove that `φ` is injective we require

+ `buip`: *uniqueness of (block) identity proofs*; given two blocks of the kernel there is
  at most one proof that the blocks are equal;

To prove that `φ` is an embedding we require

+ `Bset`: *uniqueness of identity proofs* in the codomain; that is, the codomain `∣ 𝑩 ∣`
  is assumed to be a *set*.

Note that the classical, informal statement of the first homomorphism theorem does not
demand that `φ` be an embedding (in our sense of having subsingleton fibers), and if we
left this out of the consequent of our formal theorem statement, then we could omit from
the antecedent the assumption that `∣ 𝑩 ∣` is a set.

\begin{code}

-- FirstHomTheorem|Set :
--     {𝑆 : Signature 𝓞 𝓥}
--     (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(h : hom 𝑨 𝑩)
--     (pe : pred-ext α β)(fe : swelldef 𝓥 β)                          -- extensionality assumptions
--     (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣) -- truncation assumptions
--     ----------------------------------------------------------------
--  →  Σ[ φ ∈ hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩  ]
--                             ( ( ∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker fe{𝑩}h ∣ )
--                               × IsInjective ∣ φ ∣  ×  is-embedding ∣ φ ∣  )

-- FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip = (φ , φhom) , refl , φmon , φemb
--  where
--   θ : Con 𝑨
--   θ = kercon fe{𝑩} h
--   ξ : IsEquivalence ∣ θ ∣
--   ξ = IsCongruence.is-equivalence ∥ θ ∥

--   φ : ∣ (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) ∣ → ∣ 𝑩 ∣
--   φ a = ∣ h ∣ ⌞ a ⌟

--   open ≡-Reasoning
--   φhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 φ
--   φhom 𝑓 a = ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌞ a x ⌟) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌞ a x ⌟)  ⟩
--              (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌞ a x ⌟))  ≡⟨ cong (𝑓 ̂ 𝑩) refl ⟩
--              (𝑓 ̂ 𝑩) (λ x → φ (a x))            ∎

--   φmon : IsInjective φ
--   φmon {_ , R-block u refl} {_ , R-block v refl} φuv = block-ext|uip pe buip ξ φuv

--   φemb : is-embedding φ
--   φemb = monic-is-embedding|Set φ Bset φmon

\end{code}

---

Below we will prove that the homomorphism `φ`, whose existence we just proved, is unique
(see `NoetherHomUnique`), but first we show that if we add to the hypotheses of the first
homomorphism theorem the assumption that `h` is surjective, then we obtain the so-called
*first isomorphism theorem*.  Naturally, we let `FirstHomTheorem|Set` do most of the work.
(Note that the proof also requires an additional local function extensionality postulate.) 

\begin{code}

-- FirstIsoTheorem|Set :
--      {𝑆 : Signature 𝓞 𝓥}
--      (𝑨 : Algebra α 𝑆) (𝑩 : Algebra β 𝑆) (h : hom 𝑨 𝑩)
--      (pe : pred-ext α β) (fe : swelldef 𝓥 β)                        -- extensionality assumptions
--      (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe{𝑩}h ∣)  -- truncation assumptions
--  →   IsSurjective ∣ h ∣
--      ---------------------------------------------------------------
--  →   Σ[ f ∈ (epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)]
--                           ( ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣ )
--                             × IsInjective ∣ f ∣ × is-embedding ∣ f ∣

-- FirstIsoTheorem|Set 𝑨 𝑩 h pe fe Bset buip hE =
--  (fmap , fhom , fepic) , refl , (snd ∥ FHT ∥)
--   where
--   FHT = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip

--   fmap : ∣ ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe ∣ → ∣ 𝑩 ∣
--   fmap = fst ∣ FHT ∣

--   fhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 fmap
--   fhom = snd ∣ FHT ∣

--   fepic : IsSurjective fmap
--   fepic b = Goal where
--    a : ∣ 𝑨 ∣
--    a = SurjInv ∣ h ∣ hE b

--    bfa : b ≡ fmap ⟪ a ⟫
--    bfa = ((SurjInvIsRightInv ∣ h ∣ hE) b)⁻¹

--    Goal : Image fmap ∋ b
--    Goal = Image_∋_.eq ⟪ a ⟫ bfa

\end{code}

Now we prove that the homomorphism `φ`, whose existence is guaranteed by `FirstHomTheorem|Set`, is unique.

\begin{code}

-- module _ {fe : swelldef 𝓥 β}{𝑆 : Signature 𝓞 𝓥}
--          (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(h : hom 𝑨 𝑩) where

--  open ≡-Reasoning

--  NoetherHomUnique : (f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
--   →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
--   →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
--   →                 ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 
--  NoetherHomUnique f g hfk hgk (_ , R-block a refl) =
--   ∣ f ∣ (_ , R-block a refl) ≡⟨ cong-app(hfk ⁻¹)a ⟩
--   ∣ h ∣ a                    ≡⟨ cong-app(hgk)a ⟩
--   ∣ g ∣ (_ , R-block a refl) ∎

\end{code}





--------------------------------------





-- Given an arbitrary subset `X` of the domain `∣ 𝑨 ∣` of an `𝑆`-algebra `𝑨`, the type `Sg X`
-- does indeed represent a subuniverse of `𝑨`. Proving this using the inductive type `Sg` is
-- trivial, as we see here.

-- \begin{code}

-- sgIsSub : {𝑨 : Algebra α 𝑆}{X : Pred ∣ 𝑨 ∣ β} → Sg 𝑨 X ∈ Subuniverses 𝑨
-- sgIsSub = app

-- \end{code}

-- Alternatively, we could express the preceeding fact using an inductive type representing
-- images of terms.

-- \begin{code}

--  data TermImage (𝑨 : Algebra α 𝑆)(Y : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
--   where
--   var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
--   app : ∀ 𝑓 𝑡 →  ((x : ∥ 𝑆 ∥ 𝑓) → 𝑡 x ∈ TermImage 𝑨 Y)  → (𝑓 ̂ 𝑨) 𝑡 ∈ TermImage 𝑨 Y

-- \end{code}

-- By what we proved above, it should come as no surprise that `TermImage 𝑨 Y` is a
-- subuniverse of 𝑨 that contains Y.

-- \begin{code}

--  TermImageIsSub : {𝑨 : Algebra α 𝑆}{Y : Pred ∣ 𝑨 ∣ β} → TermImage 𝑨 Y ∈ Subuniverses 𝑨
--  TermImageIsSub = app

--  Y-onlyif-TermImageY : {𝑨 : Algebra α 𝑆}{Y : Pred ∣ 𝑨 ∣ β} → Y ⊆ TermImage 𝑨 Y
--  Y-onlyif-TermImageY {a} Ya = var Ya

-- \end{code}

-- Since `Sg 𝑨 Y` is the smallest subuniverse containing Y, we obtain the following
-- inclusion.

-- \begin{code}

--  SgY-onlyif-TermImageY : (𝑨 : Algebra α 𝑆)(Y : Pred ∣ 𝑨 ∣ β) → Sg 𝑨 Y ⊆ TermImage 𝑨 Y
--  SgY-onlyif-TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y-onlyif-TermImageY

-- \end{code}

