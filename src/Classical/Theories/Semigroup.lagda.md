---
layout: default
file: "src/Classical/Theories/Semigroup.lagda.md"
title: "Classical.Theories.Semigroup module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-theories-semigroup">Equational theory of semigroups</a>

This is the [Classical.Theories.Semigroup][] module of the [Agda Universal Algebra Library][].

The semigroup theory is a single equation: associativity.  Following the conventions established in [`Classical.Structures.Semigroup`][Classical.Structures.Semigroup] (see [ADR-002][ADR-002]), the equation index is a named-constructor data type symmetric with the signature convention from [`Classical.Signatures.Semigroup`][Classical.Signatures.Semigroup], and the variable carrier `SemigroupVar` is a per-structure named enum whose constructors are the conventional metasyntactic letters for the structure's identities — keeping equations mathematically readable (`ℊ x · ℊ y` rather than `ℊ 0F · ℊ 1F`).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Semigroup where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive            using ()             renaming ( Set to Type )
open import Data.Fin.Base             using ( Fin )
open import Data.Fin.Patterns         using ( 0F ; 1F )
open import Data.Product              using ( _×_ ; _,_ )

-- Imports from agda-algebras -----------------------------------------------------
open import Classical.Signatures.Semigroup  using ( 𝑆ₛₘ ; Op-Semigroup ; ∙op )
open import Overture.Terms                  {𝑆 = 𝑆ₛₘ}  using ( Term ; ℊ ; node )
```

The variable carrier for terms over the semigroup signature.  The three constructors `x`, `y`, `z` are the variables that appear in the associativity equation.

```agda
data SemigroupVar : Type where
  x y z : SemigroupVar
```

The index type for the theory.  One constructor per equation in the theory; for semigroups this is just `assoc`.

```agda
data Eq-Semigroup : Type where
  assoc : Eq-Semigroup
```

Term-level infix sugar for the binary operation.  The bare symbol `_∙_` is reserved at the term level so that the equational theory's left- and right-hand sides read mathematically; per the constructor-naming convention `<symbol>op`, the operation symbol itself is `∙op`.  This local syntactic sugar is private — downstream consumers work directly with `node ∙op` or with the algebra's interpreted operation.

```agda
private
  infixl 7 _∙_
  _∙_ : Term SemigroupVar → Term SemigroupVar → Term SemigroupVar
  s ∙ t = node ∙op args
    where
      args : Fin 2 → Term SemigroupVar
      args 0F = s
      args 1F = t
```

The theory itself.  `Th-Semigroup` maps each equation index to a pair of terms representing the equation's left- and right-hand sides; per the `Setoid.Varieties.EquationalLogic.Modᵗ` indexed-equation form, an algebra `𝑨` models `Th-Semigroup` iff for every index `i`, `𝑨` satisfies the corresponding identity.

```agda
Th-Semigroup : Eq-Semigroup → Term SemigroupVar × Term SemigroupVar
Th-Semigroup assoc = (ℊ x ∙ ℊ y) ∙ ℊ z , ℊ x ∙ (ℊ y ∙ ℊ z)
```

--------------------------------------

<span style="float:left;">[← Classical.Theories](Classical.Theories.html)</span>
<span style="float:right;">[Classical.Structures.Semigroup →](Classical.Structures.Semigroup.html)</span>

{% include UALib.Links.md %}
