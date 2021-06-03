{-
layout: default
title : Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: [agda-algebras development team][]
-}

-- Continuous Relations
-- ====================
--
-- This is the [Relations.Continuous][] module of the Agda Universal Algebra Library.


{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Continuous where

open import stdlib-imports
open import Relations.Discrete using (Op)

private variable 𝓤 𝓥 𝓦 : Level

-- Motivation
-- ----------
-- In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As
-- such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type
-- `A → A → ⋯ → A -- → Type 𝓦` (for some universe 𝓦).  To implement such a relation in type theory, we would
-- need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general
-- to instead define an arity type `I : Type 𝓥`, and define the type representing `I`-ary relations on `A` as
-- the function type `(I → A) → Type 𝓦`.  Then, if we are specifically interested in an n-ary relation for
-- some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

-- Below we will define `ContRel` to be the type `(I → A) → Type 𝓦` and we will call `ContRel` the type of
-- *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary,
-- binary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general,
-- however, since they are defined over a single type. Said another way, they are *single-sorted* relations.
-- We will remove this limitation when we define the type of *dependent continuous relations* at the end of
-- this module.

-- Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will
-- `ContRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will
-- represent relations that not only have arbitrary arities, but also are defined over arbitrary families of
-- types.

-- To be more concrete, given an arbitrary family `A : I → Type 𝓤` of types, we may have a relation from `A i`
-- to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be
-- enumerable.

-- We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because
-- the definition of a type that represents them requires depedent types.  The `DepRel` type that we define
-- [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of
-- relation.

-- Continuous and dependent relations
-- ----------------------------------
-- Here we define the types `ContRel` and `DepRel`. The first of these represents predicates of arbitrary
-- arity over a single type `A`; we call these *continuous relations*. To define `DepRel`, the type of
-- *dependent relations*, we exploit the full power of dependent types and provide a completely general
-- relation type.

ContRel : Type 𝓥 → Type 𝓤 → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
ContRel I A 𝓦 = (I → A) → Type 𝓦

DepRel : (I : Type 𝓥) → (I → Type 𝓤) → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
DepRel I 𝒜 𝓦 = ((i : I) → 𝒜 i) → Type 𝓦

-- Here, the tuples of a relation of type `DepRel I 𝒜 𝓦` will inhabit the dependent function type `𝒜 : I →
-- Type 𝓤` (where the codomain may depend on the input coordinate `i : I` of the domain). Heuristically, we
-- can think of an inhabitant of type `DepRel I 𝒜 𝓦` as a relation from `𝒜 i` to `𝒜 j` to `𝒜 k` to ….
-- (This is only a rough heuristic since `I` could denote an uncountable collection.)


-- Compatibility with general relations
-- ------------------------------------
-- It will be helpful to have some functions that make it easy to assert that a given operation is compatible
-- with a given relation.  The following functions serve this purpose.

module _ {I J : Type 𝓥} {A : Type 𝓤} where

 eval-cont-rel : ContRel I A 𝓦 → (I → J → A) → Type(𝓥 ⊔ 𝓦)
 eval-cont-rel R 𝒶 = ∀ (j : J) → R λ i → 𝒶 i j

 cont-compatible-op : Op J A → ContRel I A 𝓦 → Type(𝓥 ⊔ 𝓤 ⊔ 𝓦)
 cont-compatible-op 𝑓 R  = ∀ (𝒶 : (I → J → A)) → (eval-cont-rel R 𝒶 → R λ i → (𝑓 (𝒶 i)))

-- The first of these is an *evaluation* function which "lifts" an `I`-ary relation to an `(I → J)`-ary
-- relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the "`I`-slices" (or "rows") of
-- the `J`-tuples belong to the original relation. The second definition denotes compatibility of an operation
-- with a continuous relation.

-- Readers who find the syntax of the last two definitions nauseating might be helped by an explication of the
-- semantics of these deifnitions. First, internalize the fact that `𝒶 : I → J → A` denotes an `I`-tuple of
-- `J`-tuples of inhabitants of `A`. Next, recall that a continuous relation `R` denotes a certain collection
-- of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` "belongs to" or "satisfies" `R`).  For such `R`,
-- the type `eval-cont-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples
-- `𝒶 : I → J → A` for which `eval-cont-rel R 𝒶` holds.

-- For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write
-- down a couple of the `J`-tuples as columns. For example, here are the i-th and k-th columns (for some `i k
-- : I`).

-- 𝒶 i 1      𝒶 k 1
-- 𝒶 i 2      𝒶 k 2  <-- (a row of I such columns forms an I-tuple)
--   ⋮          ⋮
-- 𝒶 i J      𝒶 k J

-- Now `eval-cont-rel R 𝒶` is defined by `∀ j → R (λ i → 𝒶 i j)` which asserts that each row of the `I`
-- columns shown above belongs to the original relation `R`. Finally, `cont-compatible-op` takes a `J`-ary
-- operation `𝑓 : Op J A` and an `I`-tuple `𝒶 : I → J → A` of `J`-tuples, and determines whether the `I`-tuple
-- `λ i → 𝑓 (𝑎 i)` belongs to `R`.


-- Above we saw lifts of continuous relations and what it means for such relations to be compatible with
-- operations. We conclude this module by defining the (only slightly more complicated) lift of dependent
-- relations, and the type that represents compatibility of a dependent relation with an operation.

module _ {I J : Type 𝓥} {𝒜 : I → Type 𝓤} where

 eval-dep-rel : DepRel I 𝒜 𝓦 → (∀ i → (J → 𝒜 i)) → Type(𝓥 ⊔ 𝓦)
 eval-dep-rel R 𝒶 = ∀ j → R (λ i → (𝒶 i) j)

 dep-compatible-op : (∀ i → Op J (𝒜 i)) → DepRel I 𝒜 𝓦 → Type(𝓥 ⊔ 𝓤 ⊔ 𝓦)
 dep-compatible-op 𝑓 R  = ∀ 𝒶 → (eval-dep-rel R) 𝒶 → R λ i → (𝑓 i)(𝒶 i)

-- In the definition of `dep-compatible-op`, we let Agda infer the type of `𝒶`; in this case
-- `𝒶 : Π i ꞉ I , (J → 𝒜 i)`.


----------------------------

-- [agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
