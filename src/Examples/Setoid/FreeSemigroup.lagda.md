---
layout: default
file: "src/Examples/Setoid/FreeSemigroup.lagda.md"
title: "Examples.Setoid.FreeSemigroup module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example: the free semigroup and term rewriting {#examples-setoid-freesemigroup}

This is the [Examples.Setoid.FreeSemigroup][] module of the [Agda Universal Algebra Library][].

A *semigroup* is a magma whose binary operation is associative.  Its signature is
the magma signature `Sig-Magma`{.AgdaFunction}; the whole content of the theory is
the single associativity equation.  The free semigroup on a set of generators is
therefore the relatively free algebra `𝔽[ X ]`{.AgdaFunction} of
[Setoid.Varieties.SoundAndComplete][], whose carrier equality is *derivable*
equality `E ⊢ X ▹ _≈_`{.AgdaDatatype} from the associativity rule.

In contrast to the free magma of [Examples.Setoid.FreeMagma][], where every
parenthesisation is a distinct element, here the two parenthesisations of a triple
are identified.  This module records that `𝔽[ X ]`{.AgdaFunction} is genuinely a
semigroup, exhibits that identification as an equality in the free semigroup, and
gives a small *term-rewriting* derivation that normalises associativity redexes
inside a larger term via congruence.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.FreeSemigroup where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive                       using () renaming ( Set to Type )
open import Data.Fin.Base                        using ( Fin )
open import Data.Fin.Patterns                    using ( 0F ; 1F ; 2F )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Magma           using ( Sig-Magma ; ∙-Op )
open import Overture.Terms       {𝑆 = Sig-Magma} using ( Term ; ℊ ; node )
open import Setoid.Algebras      {𝑆 = Sig-Magma} using ( 𝔻[_] )
open import Setoid.Varieties.SoundAndComplete {𝑆 = Sig-Magma}
  using ( Eq ; _≈̇_ ; _⊨_ ; _⊢_▹_≈_ ; module FreeAlgebra )

open import Relation.Binary using ( Setoid )

open _⊢_▹_≈_ using ( hyp ; app ; refl ; sym ; trans )
```

#### The associativity theory {#associativity-theory}

The syntactic product helper is the same as for the free magma.  The associativity
equation lives in the three-variable context `Fin 3`{.AgdaDatatype}; the three
generators are `ℊ 0F`, `ℊ 1F`, `ℊ 2F`.

```agda
_·_ : {X : Type} → Term X → Term X → Term X
s · t = node ∙-Op λ { 0F → s ; 1F → t }

-- the three generators of the free semigroup on Fin 3
g₀ g₁ g₂ : Term (Fin 3)
g₀ = ℊ 0F
g₁ = ℊ 1F
g₂ = ℊ 2F

-- (g₀ · g₁) · g₂  ≈̇  g₀ · (g₁ · g₂)
assoc-eq : Eq
assoc-eq = ((g₀ · g₁) · g₂) ≈̇ (g₀ · (g₁ · g₂))

-- a one-equation theory indexed by Fin 1
E : Fin 1 → Eq
E _ = assoc-eq

open FreeAlgebra E using ( 𝔽[_] )
```

#### The free algebra is a semigroup {#free-is-semigroup}

The free-algebra construction already proves that `𝔽[ X ]`{.AgdaFunction} *models*
every equation of the theory, so the free semigroup is, as expected, a semigroup.

```agda
free-semigroup-models-assoc : 𝔽[ Fin 3 ] ⊨ E
free-semigroup-models-assoc = FreeAlgebra.satisfies E
```

#### Associativity as an equality in the free semigroup {#assoc-equality}

The carrier equality of `𝔽[ X ]`{.AgdaFunction} *is* derivable equality, so the
associativity rule `hyp`{.AgdaInductiveConstructor} `0F` witnesses, on the nose,
that the two parenthesisations of `g₀ · g₁ · g₂` are equal elements of the free
semigroup — exactly the identification that the free magma withholds.

```agda
open Setoid 𝔻[ 𝔽[ Fin 3 ] ] using ( _≈_ )

assoc≈ : ((g₀ · g₁) · g₂) ≈ (g₀ · (g₁ · g₂))
assoc≈ = hyp 0F

-- and the symmetric reading, since derivable equality is symmetric
assoc≈˘ : (g₀ · (g₁ · g₂)) ≈ ((g₀ · g₁) · g₂)
assoc≈˘ = sym (hyp 0F)
```

#### Term rewriting inside a larger term {#term-rewriting}

Congruence (`app`{.AgdaInductiveConstructor}) lets us rewrite an associativity
*redex* wherever it occurs as a subterm.  Starting from a product whose *both*
factors are the redex `(g₀ · g₁) · g₂`{.AgdaFunction}, we normalise the left factor,
then the right, and chain the two steps with `trans`{.AgdaInductiveConstructor}.

```agda
-- the doubled redex  ((g₀·g₁)·g₂) · ((g₀·g₁)·g₂)
redex² : Term (Fin 3)
redex² = ((g₀ · g₁) · g₂) · ((g₀ · g₁) · g₂)

-- its fully right-nested normal form
nf² : Term (Fin 3)
nf² = (g₀ · (g₁ · g₂)) · (g₀ · (g₁ · g₂))

rewrite² : redex² ≈ nf²
rewrite² = trans left right
  where
  -- rewrite the left factor, leave the right untouched
  left : redex² ≈ ((g₀ · (g₁ · g₂)) · ((g₀ · g₁) · g₂))
  left = app λ { 0F → hyp 0F ; 1F → refl }
  -- rewrite the right factor
  right : ((g₀ · (g₁ · g₂)) · ((g₀ · g₁) · g₂)) ≈ nf²
  right = app λ { 0F → refl ; 1F → hyp 0F }
```

--------------------------------------

{% include UALib.Links.md %}
