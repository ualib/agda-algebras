---
layout: default
title : "Setoid.Subalgebras.Basic module (The Agda Universal Algebra Library)"
date : "2021-07-17"
author: "agda-algebras development team"
---

#### Subalgebras of setoid algebras

This is the [Setoid.Subalgebras.Basic][] module of the [Agda Universal Algebra Library][].

`𝑨` is a **subalgebra** of `𝑩`, written `𝑨 ≤ 𝑩`, just in case `𝑨` can be
*homomorphically embedded* in `𝑩`: there is a homomorphism from `𝑨` to `𝑩` whose
underlying map is injective.

Note that the notion of subalgebra that we define here is different from the
standard textbook definition, which defines a *subuniverse* to be a subset of
the carrier of an algebra that is closed under the operations (as we do in the
[Setoid.Subalgebras.Subuniverses][] module); a subalgebra is then a subuniverse
together with the operations of the larger algebra restricted to it.  Nothing in
our definition requires the carrier of a subalgebra of `𝑩` to be a subset of the
carrier of `𝑩`.[^1]

Our subalgebra relation `_≤_`{.AgdaFunction} is clearly reflexive and transitive,
so it is at least a *preorder*.  Whether `_≤_`{.AgdaFunction} it is antisymmetric
— that is, whether `𝑨 ≤ 𝑩`{.AgdaFunction} and `𝑩 ≤ 𝑨`{.AgdaFunction} imply `𝑨 ≈ 𝑩`
— depends on what we mean by `≈` in the definition of asymmetry.  If `≈` means
"on the nose" equality, then `_≤_` it is not antisymmetric; but that is arguably
the wrong notion of equality on algebras.  If `≈` to means isomorphism, then
`_≤_`{.AgdaFunction} is antisymmetric, and thus a partial order on (isomorphism
classes of) algebras.

This module defines the subalgebra relation `_≤_`{.AgdaFunction} and the several
ways of packaging it: as a record bundling both algebras, as a Σ-type over the
smaller algebra with the larger one fixed, and relative to a whole class rather
than to a single algebra.  The class-relative form `_≤c_`{.AgdaFunction} is the
one the closure operator `S`{.AgdaFunction} of [Setoid.Varieties.Closure][] is
built from.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Subalgebras.Basic where

open import Agda.Primitive using () renaming ( Set to Type )

-- imports from the Agda Standard Library ---------------------------------------------------
open import Data.Product          using ( _,_ ; Σ-syntax ) renaming ( _×_ to _∧_ )
open import Level                 using ( Level ; _⊔_ )
open import Relation.Binary       using ( REL )
open import Relation.Unary        using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture              using ( proj₁ ; proj₂ ; Signature ; 𝓞 ; 𝓥 )
open import Setoid.Algebras       using ( Algebra ; ov )
open import Setoid.Functions      using ( IsInjective )
open import Setoid.Homomorphisms  using ( hom ; mon ; mon→intohom ; kerquo ; FirstHomTheorem )

private variable α ρᵃ β ρᵇ ℓ : Level
```
-->

The relation comes in two directions and three packagings.

+  `_IsSubalgebraOf_`{.AgdaFunction}, with the infix alias `_≤_`{.AgdaFunction},
   is the relation itself: `𝑨 ≤ 𝑩` is the type of pairs `(h , inj)` with
   `h : hom 𝑨 𝑩` and `inj` a proof that the underlying map of `h` is injective.
+  `_IsSupalgebraOf_`{.AgdaFunction}, aliased `_≥_`{.AgdaFunction}, is the
   converse, and is *definitionally* the same type read the other way round:
   `𝑨 ≤ 𝑩` and `𝑩 ≥ 𝑨` both unfold to an injective homomorphism from `𝑨` into
   `𝑩`.
+  `mon→≤`{.AgdaFunction} turns a monomorphism into a proof of the subalgebra
   relation.  It is immediate, because `mon→intohom`{.AgdaFunction} of
   [Setoid.Homomorphisms.Basic][] already produces exactly this type.
+  `SubalgebraOf`{.AgdaRecord} bundles both algebras and the proof into a single
   record.  `Subalgebra`{.AgdaFunction} instead fixes the larger algebra and
   collects the smaller one with its embedding, so an inhabitant of
   `Subalgebra 𝑨` is a pair `(𝑩 , p)` with `p : 𝑩 ≤ 𝑨`.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
  _≥_   -- alias for supalgebra (aka overalgebra)
    _IsSupalgebraOf_ : Algebra {𝑆 = 𝑆} α ρᵃ → Algebra {𝑆 = 𝑆} β ρᵇ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective (proj₁ h)

  _≤_   -- alias for subalgebra relation
    _IsSubalgebraOf_ : Algebra {𝑆 = 𝑆} α ρᵃ → Algebra {𝑆 = 𝑆} β ρᵇ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective (proj₁ h)

  -- Syntactic sugar for sup/sub-algebra relations.
  𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩
  𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩

  mon→≤ : {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
  mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

  record SubalgebraOf : Type (ov {𝑆 = 𝑆} (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)) where
    field
      algebra : Algebra {𝑆 = 𝑆} α ρᵃ
      subalgebra : Algebra {𝑆 = 𝑆} β ρᵇ
      issubalgebra : subalgebra ≤ algebra

  Subalgebra : Algebra {𝑆 = 𝑆} α ρᵃ → {β ρᵇ : Level} → Type _
  Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (Algebra β ρᵇ) ] 𝑩 ≤ 𝑨

{- usage note: for 𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ, an inhabitant of `Subalgebra 𝑨` is a pair
   `(𝑩 , p) : Subalgebra 𝑨`  providing
   - `𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ` and
   - `p : 𝑩 ≤ 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴. -}
```

From now on we will use `𝑩 ≤ 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.

#### Subalgebras of classes of setoid algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : Algebra β ρᵇ`
denotes an arbitrary `𝑆`-algebra.  Consider the assertion that `𝑩` is a subalgebra of
an algebra in the class `𝒦`.  With the next definition we can express this
assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

```agda
  _≤c_
    _IsSubalgebraOfClass_ : Algebra {𝑆 = 𝑆} β ρᵇ → Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ → Type _
  𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ Algebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 ≤ 𝑨))

  𝑩 ≤c 𝒦 = 𝑩 IsSubalgebraOfClass 𝒦  -- (alias)

  record SubalgebraOfClass : Type (ov {𝑆 = 𝑆} (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ)) where
    field
      class : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ
      subalgebra : Algebra {𝑆 = 𝑆} β ρᵇ
      issubalgebraofclass : subalgebra ≤c class

  record SubalgebraOfClass' : Type (ov {𝑆 = 𝑆} (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ)) where
    field
      class : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ
      classalgebra : Algebra {𝑆 = 𝑆} α ρᵃ
      isclassalgebra : classalgebra ∈ class
      subalgebra : Algebra {𝑆 = 𝑆} β ρᵇ
      issubalgebra : subalgebra ≤ classalgebra

  -- The collection of subalgebras of algebras in class 𝒦.
  SubalgebrasOfClass : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ → {β ρᵇ : Level} → Type _
  SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 ≤c 𝒦
```


#### Consequences of First Homomorphism Theorem

As an example use-case of the `IsSubalgebraOf` type defined above, we prove the
following easy but useful corollary of the First Homomorphism Theorem (proved
in the [Setoid.Homomorphisms.Noether][] module): If `𝑨` and `𝑩` are `𝑆`-algebras
and `h : hom 𝑨 𝑩` a homomorphism from `𝑨` to `𝑩`, then the quotient `𝑨 ╱ ker h`
is (isomorphic to) a subalgebra of `𝑩`.

```agda
  FirstHomCorollary : {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} {𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}
    (hh : hom 𝑨 𝑩) → (kerquo hh) IsSubalgebraOf 𝑩
  FirstHomCorollary hh = proj₁ (FirstHomTheorem hh) , proj₂ (proj₂ (FirstHomTheorem hh))
```

---

[^1]: Note that we denote both the subalgebra and subuniverse relations by the
      same symbol, `_≤_`{.AgdaFunction}.  Which one is meant in a given context is
      determined by which module is imported in that context.
