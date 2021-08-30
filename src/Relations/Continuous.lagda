---
layout: default
title : "Relations.Continuous module (The Agda Universal Algebra Library)"
date : "2021-02-28"
author: "[agda-algebras development team][]"
---

### <a id="continuous-relations">Continuous Relations</a>

This is the [Relations.Continuous][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Continuous where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )

-- Imports from agda-algebras ----------------------------------------------------
open import Overture.Preliminaries using ( Π ; Π-syntax )
open import Relations.Discrete     using ( Op ; arity[_] )

private variable α ρ : Level

\end{code}

#### <a id="motivation">Motivation</a>

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → Type β` (for some universe β).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : Type 𝓥`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → Type β`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `ContRel` to be the type `(I → A) → Type β` and we will call `ContRel` the type of *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type. Said another way, they are *single-sorted* relations. We will remove this limitation when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A β` was the single-sorted special case of the multisorted `REL A B β` type, so too will `ContRel I A β` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → Type α` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.



#### <a id="continuous-and-dependent-relations">Continuous and dependent relations</a>

Here we define the types `Rel` and `ΠΡ` ("Pi Rho"). The first of these represents predicates of arbitrary arity over a single type `A`; we call these *continuous relations*.
To define `ΠΡ`, the type of *dependent relations*, we exploit the full power of dependent types and provide a completely general relation type.

Here, the tuples of a relation of type `DepRel I 𝒜 β` will inhabit the dependent function type `𝒜 : I → Type α` (where the codomain may depend on the input coordinate `i : I` of the domain). Heuristically, we can think of an inhabitant of type `DepRel I 𝒜 β` as a relation from `𝒜 i` to `𝒜 j` to `𝒜 k` to …. (This is only a rough heuristic since `I` could denote an uncountable collection.


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
 ΠΡ : (I : ar) → (I → Type α) → {ρ : Level} → Type (𝓥 ⊔ α ⊔ lsuc ρ)
 ΠΡ I 𝒜 {ρ} = ((i : I) → 𝒜 i) → Type ρ

 ΠΡ-syntax : (I : ar) → (I → Type α) → {ρ : Level} → Type (𝓥 ⊔ α ⊔ lsuc ρ)
 ΠΡ-syntax I 𝒜 {ρ} = ΠΡ I 𝒜 {ρ}

 syntax ΠΡ-syntax I (λ i → 𝒜) = ΠΡ[ i ∈ I ] 𝒜
 infix 6 ΠΡ-syntax

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


#### <a id="compatibility-of-operations-with-pirho-types">Compatibility of operations with ΠΡ types</a>

\begin{code}

 eval-ΠΡ : {I J : ar}{𝒜 : I → Type α}
  →         ΠΡ I 𝒜 {ρ}            -- the relation type: subsets of Π[ i ∈ I ] 𝒜 i
                                  -- (where Π[ i ∈ I ] 𝒜 i is a type of dependent functions or "tuples")
  →         ((i : I) → J → 𝒜 i)  -- an I-tuple of (𝒥 i)-tuples
  →         Type (𝓥 ⊔ ρ)
 eval-ΠΡ{I = I}{J}{𝒜} R t = ∀ j → R λ i → (t i) j

 compatible-ΠΡ : {I J : ar}{𝒜 : I → Type α}
  →               (∀ i → Op (𝒜 i) J)  -- for each i : I, an operation of type  𝒪(𝒜 i){J} = (J → 𝒜 i) → 𝒜 i
  →               ΠΡ I 𝒜 {ρ}             -- a subset of Π[ i ∈ I ] 𝒜 i
                                         -- (where Π[ i ∈ I ] 𝒜 i is a type of dependent functions or "tuples")
  →               Type _
 compatible-ΠΡ {I = I}{J}{𝒜} 𝑓 R  = Π[ t ∈ ((i : I) → J → 𝒜 i) ] eval-ΠΡ R t

\end{code}

#### <a id="detailed-explanation">Detailed explanation</a>

The first of these is an *evaluation* function which "lifts" an `I`-ary relation to an `(I → J)`-ary relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the "`I`-slices" (or "rows") of the `J`-tuples belong to the original relation. The second definition denotes compatibility of an operation with a continuous relation.

Readers who find the syntax of the last two definitions nauseating might be helped by an explication of the semantics of these deifnitions. First, internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Next, recall that a continuous relation `R` denotes a certain collection of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` "belongs to" or "satisfies" `R`).  For such `R`, the type `eval-cont-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples `𝒶 : I → J → A` for which `eval-cont-rel R 𝒶` holds.

For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write down a couple of the `J`-tuples as columns. For example, here are the i-th and k-th columns (for some `i k : I`).

```
𝒶 i 1      𝒶 k 1
𝒶 i 2      𝒶 k 2  <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒶 i J      𝒶 k J
```

Now `eval-cont-rel R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which asserts that each row of the `I` columns shown above belongs to the original relation `R`. Finally, `cont-compatible-op` takes a `J`-ary operation `𝑓 : Op J A` and an `I`-tuple `𝒶 : I → J → A` of `J`-tuples, and determines whether the `I`-tuple `λ i → 𝑓 (𝑎 i)` belongs to `R`.

--------------------------------------

<span style="float:left;">[← Relations.Discrete](Relations.Discrete.html)</span>
<span style="float:right;">[Relations.Properties →](Relations.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
