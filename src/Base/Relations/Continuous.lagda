---
layout: default
title : "Base.Relations.Continuous module (The Agda Universal Algebra Library)"
date : "2021-02-28"
author: "[agda-algebras development team][]"
---

### <a id="continuous-relations">Continuous Relations</a>

This is the [Base.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Relations.Continuous where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )

-- Imports from agda-algebras ----------------------------------------------------
open import Base.Overture.Preliminaries using ( Π ; Π-syntax )
open import Base.Relations.Discrete     using ( Op ; arity[_] )

private variable α ρ : Level

\end{code}

#### <a id="motivation">Motivation</a>

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → Type β` (for some universe β).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : Type 𝓥`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → Type β`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we define `Rel` to be the type `(I → A) → Type β` and we call this the type of *continuous relations*.  This generalizes "discrete" relations (i.e., relations of finite arity---unary, binary, etc), defined in the standard library since inhabitants of the continuous relation type can have arbitrary arity.

The relations of type `Rel` not completely general, however, since they are defined over a single type. Said another way, they are *single-sorted* relations. We will remove this limitation when we define the type of *dependent continuous relations* later in the module. Just as `Rel A β` is the single-sorted special case of the multisorted `REL A B β` in the standard library, so too is our continuous version, `Rel I A β`, the single-sorted special case of a completely general type of relations. The latter represents relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

Concretely, given an arbitrary family `A : I → Type α` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `REL` type that we define [below](Base.Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

**Warning**! The type of binary relations in the standard library's `Relation.Binary` module is also called `Rel`.  Therefore, to use both the discrete binary relation from the standard library, and our continuous relation type, we recommend renaming the former when importing with a line like this

`open import Relation.Binary  renaming ( REL to BinREL ; Rel to BinRel )`



#### <a id="continuous-and-dependent-relations">Continuous and dependent relations</a>

Here we define the types `Rel` and `REL`. The first of these represents predicates of arbitrary arity over a single type `A`. As noted above, we call these *continuous relations*.
The definition of `REL` goes even further and exploits the full power of dependent types resulting in a completely general relation type, which we call the type of *dependent relations*.

Here, the tuples of a relation of type `REL I 𝒜 β` inhabit the dependent function type `𝒜 : I → Type α` (where the codomain may depend on the input coordinate `i : I` of the domain). Heuristically, we can think of an inhabitant of type `REL I 𝒜 β` as a relation from `𝒜 i` to `𝒜 j` to `𝒜 k` to …. (This is only a rough heuristic since `I` could denote an uncountable collection.)  See the discussion below for a more detailed explanation.

\begin{code}

module _ {𝓥 : Level} where

 ar : Type (lsuc 𝓥)
 ar = Type 𝓥

-- Relations of arbitrary arity over a single sort.
 Rel : Type α → ar → {ρ : Level} → Type (α ⊔ 𝓥 ⊔ lsuc ρ)
 Rel A I {ρ} = (I → A) → Type ρ

 Rel-syntax : Type α → ar → (ρ : Level) → Type (𝓥 ⊔ α ⊔ lsuc ρ)
 Rel-syntax A I ρ = Rel A I {ρ}

 syntax Rel-syntax A I ρ = Rel[ A ^ I ] ρ
 infix 6 Rel-syntax

 -- The type of arbitrarily multisorted relations of arbitrary arity
 REL : (I : ar) → (I → Type α) → {ρ : Level} → Type (𝓥 ⊔ α ⊔ lsuc ρ)
 REL I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

 REL-syntax : (I : ar) → (I → Type α) → {ρ : Level} → Type (𝓥 ⊔ α ⊔ lsuc ρ)
 REL-syntax I 𝒜 {ρ} = REL I 𝒜 {ρ}

 syntax REL-syntax I (λ i → 𝒜) = REL[ i ∈ I ] 𝒜
 infix 6 REL-syntax

\end{code}

#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

\begin{code}

 -- Lift a relation of tuples up to a relation on tuples of tuples.
 eval-Rel : {I : ar}{A : Type α} → Rel A I{ρ} → (J : ar) → (I → J → A) → Type (𝓥 ⊔ ρ)
 eval-Rel R J t = ∀ (j : J) → R λ i → t i j

\end{code}

A relation `R` is compatible with an operation `f` if for every tuple `t` of tuples
belonging to `R`, the tuple whose elements are the result of applying `f` to
sections of `t` also belongs to `R`.

\begin{code}

 compatible-Rel : {I J : ar}{A : Type α} → Op(A) J → Rel A I{ρ} → Type (𝓥 ⊔ α ⊔ ρ)
 compatible-Rel f R  = ∀ t → eval-Rel R arity[ f ] t → R λ i → f (t i)
 -- (inferred type of t is I → J → A)

\end{code}


#### <a id="compatibility-of-operations-with-dependent-relations">Compatibility of operations with dependent relations</a>

\begin{code}

 eval-REL :  {I J : ar}{𝒜 : I → Type α}
  →          REL I 𝒜 {ρ}          -- the relation type: subsets of Π[ i ∈ I ] 𝒜 i
                                  -- (where Π[ i ∈ I ] 𝒜 i is a type of dependent functions or "tuples")
  →          ((i : I) → J → 𝒜 i)  -- an I-tuple of (𝒥 i)-tuples
  →          Type (𝓥 ⊔ ρ)
 eval-REL{I = I}{J}{𝒜} R t = ∀ j → R λ i → (t i) j

 compatible-REL :  {I J : ar}{𝒜 : I → Type α}
  →                (∀ i → Op (𝒜 i) J)  -- for each i : I, an operation of type  Op(𝒜 i){J} = (J → 𝒜 i) → 𝒜 i
  →                REL I 𝒜 {ρ}         -- a subset of Π[ i ∈ I ] 𝒜 i
                                       -- (where Π[ i ∈ I ] 𝒜 i is a type of dependent functions or "tuples")
  →                Type (𝓥 ⊔ α ⊔ ρ)
 compatible-REL {I = I}{J}{𝒜} 𝑓 R  = Π[ t ∈ ((i : I) → J → 𝒜 i) ] eval-REL R t

\end{code}

The definition `eval-REL` denotes an *evaluation* function which lifts an `I`-ary relation to an `(I → J)`-ary relation.
The lifted relation will relate an `I`-tuple of `J`-tuples when the `I`-slices (or rows) of the `J`-tuples belong
to the original relation. The second definition, compatible-REL,  denotes compatibility of an operation with a continuous relation.


#### <a id="detailed-explanation-of-the-dependent-relation-type">Detailed explanation of the dependent relation type</a>

The last two definitions above may be hard to comprehend at first, so perhaps a more detailed explanation of the semantics of these deifnitions would help.

First, one should internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`.

Next, recall that a continuous relation `R` denotes a certain collection of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` belongs to `R`).
For such `R`, the type `eval-REL R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples `𝒶 : I → J → A` for which `eval-REL R 𝒶` holds.

For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write down a couple of the `J`-tuples as columns.
For example, here are the i-th and k-th columns (for some `i k : I`).

```
𝒶 i 1      𝒶 k 1
𝒶 i 2      𝒶 k 2  <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒶 i J      𝒶 k J
```

Now `eval-REL R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which asserts that each row of the `I` columns shown above belongs to the original relation `R`.
Finally, `compatible-REL` takes

*  an `I`-tuple (`λ i → (𝑓 i)`) of `J`-ary operations, where for each i the type of `𝑓 i` is `(J → 𝒜 i) → 𝒜 i`, and
*  an `I`-tuple (`𝒶 : I → J → A`) of `J`-tuples
and determines whether the `I`-tuple `λ i → (𝑓 i) (𝑎 i)` belongs to `R`.

--------------------------------------

<span style="float:left;">[← Base.Relations.Discrete](Base.Relations.Discrete.html)</span>
<span style="float:right;">[Base.Relations.Properties →](Base.Relations.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
