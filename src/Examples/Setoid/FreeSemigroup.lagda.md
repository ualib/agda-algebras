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
open import Agda.Primitive                      using () renaming ( Set to Type )
open import Data.Fin.Base                       using ( Fin )
open import Data.Fin.Patterns                   using ( 0F ; 1F ; 2F ; 3F )
open import Relation.Binary                     using ( Setoid )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Magma          using ( Sig-Magma ; ∙-Op )
open import Overture.Terms {𝑆 = Sig-Magma}      using ( Term ; ℊ ; node )
open import Setoid.Algebras {𝑆 = Sig-Magma}     using ( 𝔻[_] )
open import Setoid.Terms.Basic {𝑆 = Sig-Magma}  using ( _≐_ ; ≐-isRefl ; Sub ; _[_] )
open import Setoid.Varieties.SoundAndComplete {𝑆 = Sig-Magma}
  using ( Eq ; _≈̇_ ; _⊨_ ; _⊢_▹_≈_ ; module FreeAlgebra )
open import Setoid.Varieties.FreeSubstitution {𝑆 = Sig-Magma}
  using ( sub▹ )
open _≐_      using ( gnl )
open _⊢_▹_≈_  using ( hyp ; app ; refl ; sym ; trans )
```

#### The Associativity Theory

The syntactic product helper is the same as for the free magma.  The associativity
equation lives in the three-variable context `Fin`{.AgdaDatatype} `3`; the three
generators are `ℊ 0F`, `ℊ 1F`, `ℊ 2F`.

```agda
_·_ : {X : Type} → Term X → Term X → Term X
s · t = node ∙-Op λ { 0F → s ; 1F → t }

-- the three generators of the free semigroup on Fin 3
private
  x y z : Term (Fin 3)
  x = ℊ 0F
  y = ℊ 1F
  z = ℊ 2F

assoc-eq : Eq
assoc-eq = (x · y) · z ≈̇  x · (y · z)

-- a one-equation theory indexed by Fin 1
E : Fin 1 → Eq
E _ = assoc-eq

open FreeAlgebra E using ( 𝔽[_] )
```

#### The free algebra is a semigroup

The free-algebra construction already proves that `𝔽[ X ]` *models* every equation of
the theory, so the free semigroup is, as expected, a semigroup.

```agda
free-semigroup-models-assoc : 𝔽[ Fin 3 ] ⊨ E
free-semigroup-models-assoc = FreeAlgebra.satisfies E
```

#### Associativity as an equality in the free semigroup

The carrier equality of `𝔽[ X ]` *is* derivable equality, so the
associativity rule `hyp`{.AgdaInductiveConstructor} `0F` witnesses, on the nose,
that the two parenthesisations of `x · y · z` are equal elements of the free
semigroup — exactly the identification that the free magma withholds.

```agda
open Setoid 𝔻[ 𝔽[ Fin 3 ] ] using ( _≈_ )

assoc≈ : (x · y) · z ≈ x · (y · z)
assoc≈ = hyp 0F

-- and the symmetric reading, since derivable equality is symmetric
assoc≈˘ : x · (y · z) ≈ (x · y) · z
assoc≈˘ = sym (hyp 0F)
```

#### Term rewriting inside a larger term

Congruence (`app`{.AgdaInductiveConstructor}) lets us rewrite an associativity
*redex* wherever it occurs as a subterm.  Starting from a product whose *both*
factors are the redex `(x · y) · z`{.AgdaFunction}, we normalise the left factor,
then the right, and chain the two steps with `trans`{.AgdaInductiveConstructor}.

```agda
-- the doubled redex  ((x·y)·z) · ((x·y)·z)
redex² : Term (Fin 3)
redex² = ((x · y) · z) · ((x · y) · z)

-- its fully right-nested normal form
nf² : Term (Fin 3)
nf² = (x · (y · z)) · (x · (y · z))

rewrite² : redex² ≈ nf²
rewrite² = trans left right
  where
  -- rewrite the left factor, leave the right untouched
  left : redex² ≈ ((x · (y · z)) · ((x · y) · z))
  left = app λ { 0F → hyp 0F ; 1F → refl }
  -- rewrite the right factor
  right : (x · (y · z)) · ((x · y) · z) ≈ nf²
  right = app λ { 0F → refl ; 1F → hyp 0F }
```

#### Instantiating associativity at arbitrary terms

`assoc≈` above is associativity for the three *generators* `x , y , z`.  To rewrite an
associativity redex whose factors are *arbitrary* terms `p , q , r`, we instantiate the
rule with the substitution `σ` sending the generators to `p , q , r` and use
`sub`{.AgdaInductiveConstructor}.  The catch (issue [M4-10][]) is that `sub` lands in
`_[ σ ]`-form, which is only *pointwise* equal to the readable rebuilt terms `(p · q) · r`
and `p · (q · r)`; `sub▹`{.AgdaFunction} ([Setoid.Varieties.FreeSubstitution][]) bridges
that gap, taking the two rebuild equalities — mechanical `gnl` / `≐-isRefl` matches, since
`(ℊ k) [ σ ]` reduces to the chosen term — and returning the readable derivation.

```agda
assoc▹ : {Γ : Type} (p q r : Term Γ) → E ⊢ Γ ▹ (p · q) · r ≈ p · (q · r)
assoc▹ {Γ} p q r = sub▹ (hyp 0F) σ blhs brhs
  where
  σ : Sub Γ (Fin 3)
  σ = λ { 0F → p ; 1F → q ; 2F → r }

  blhs : (p · q) · r ≐ ((x · y) · z) [ σ ]
  blhs = gnl λ { 0F → gnl (λ { 0F → ≐-isRefl ; 1F → ≐-isRefl }) ; 1F → ≐-isRefl }

  brhs : (x · (y · z)) [ σ ] ≐ p · (q · r)
  brhs = gnl λ { 0F → ≐-isRefl ; 1F → gnl (λ { 0F → ≐-isRefl ; 1F → ≐-isRefl }) }
```

#### A multi-step reassociation

With `assoc▹`{.AgdaFunction} in hand, a full reassociation chains cleanly.  Over four
generators, the left-combed `((a · b) · c) · d` rewrites to the right-combed
`a · (b · (c · d))` in two associativity steps — first at the top with first factor
`a · b`, then at the top of the result — composed with `trans`{.AgdaInductiveConstructor}.
This is the readable, `sub`-driven rewrite the issue asks for; no factor needs to match
the rule literally.

```agda
private
  a b c d : Term (Fin 4)
  a = ℊ 0F ; b = ℊ 1F ; c = ℊ 2F ; d = ℊ 3F

reassoc⁴ : E ⊢ Fin 4 ▹ ((a · b) · c) · d ≈ a · (b · (c · d))
reassoc⁴ = trans (assoc▹ (a · b) c d) (assoc▹ a b (c · d))
```

--------------------------------------

[M4-10]: https://github.com/ualib/agda-algebras/issues/362

{% include UALib.Links.md %}
