---
layout: default
file: "src/Examples/Setoid/FreeMagma.lagda.md"
title: "Examples.Setoid.FreeMagma module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example: the free magma on two generators

This is the [Examples.Setoid.FreeMagma][] module of the [Agda Universal Algebra Library][].

A *magma* is a carrier with a single binary operation and an *empty* equational
theory, so the absolutely free magma on a set `X`{.AgdaBound} of generators is
nothing more than the term algebra `𝑻`{.AgdaFunction} `X`{.AgdaBound} over the magma
signature `Sig-Magma`{.AgdaFunction}: its elements are the finite binary trees with
leaves labelled by generators.  This module exhibits a few concrete terms over two
generators and demonstrates the universal property — every assignment of the
generators into a concrete magma extends uniquely to a homomorphism, computed by
`free-lift`{.AgdaFunction}.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid.FreeMagma where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Nat                               using ( ℕ ; _∸_ )
open import Function                               using ( Func )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong₂ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Magma             using ( Sig-Magma ; ∙-Op )
open import Overture                               using ( proj₁ ; ArityOf )
open import Overture.Operations                    using ( Op )
open import Overture.Terms        {𝑆 = Sig-Magma}  using ( Term ; ℊ ; node )
open import Setoid.Algebras  using ( Algebra ; mkAlgebraₚ )
open import Setoid.Homomorphisms  using ( hom )
open import Setoid.Terms  using ( 𝑻 ; free-lift ; lift-hom )

open Func renaming ( to to _⟨$⟩_ )
```
-->

#### Building terms over the magma signature

The single binary operation symbol of `Sig-Magma`{.AgdaFunction} is
`∙-Op`{.AgdaInductiveConstructor}, of arity `Fin`{.AgdaDatatype} `2`.
We package the syntactic "multiply" of two terms into a readable infix helper, then
name the two generators.

```agda
-- Syntactic product of two terms: the node ∙-Op applied to (s , t).
_·_ : {X : Type} → Term X → Term X → Term X
s · t = node ∙-Op λ { 0F → s ; 1F → t }

-- The two generators of the free magma on Fin 2.
x y : Term (Fin 2)
x = ℊ 0F
y = ℊ 1F
```

A few distinct elements of the free magma, i.e. distinct binary trees:

```agda
xy xy·x x·yx : Term (Fin 2)
xy = x · y
xy·x = (x · y) · x
x·yx = x · (y · x)
```

Because the magma theory is empty, these are genuinely *different* elements of the
free magma — there is no associativity law to collapse `(x · y) · x` and `x · (y · x)`.
(Their identification is exactly what passing to the free *semigroup* would add; see
[Examples.Setoid.FreeSemigroup][].)

#### The universal property

To witness the universal property concretely we map into `(ℕ, ∸)`{.AgdaFunction} —
truncated subtraction — regarded as a magma over `Sig-Magma`{.AgdaFunction}.  We
deliberately pick a *non-associative* operation so that the syntactic distinction
between the two trees becomes a numerical one.

We assemble the algebra with the `mkAlgebraₚ`{.AgdaFunction} smart constructor of
[Setoid.Algebras.Basic][]: it takes the interpretation `f`{.AgdaBound} of each operation
symbol and a pointwise congruence `cong-f`{.AgdaBound}, and discharges the
`⟨ Sig-Magma ⟩`-congruence boilerplate (`{∙-Op , _} {.∙-Op , _} (refl , args≈)`) internally.
Only `f`{.AgdaBound} and `cong-f`{.AgdaBound} remain of the longhand
`record { Domain = ≡.setoid ℕ ; Interp = … }` this replaces.

```agda
ℕ∸-magma : Algebra 0ℓ 0ℓ
ℕ∸-magma = mkAlgebraₚ ℕ f cong-f
  where
  -- the single binary operation symbol, interpreted as truncated subtraction
  f : ∀ o → Op (ArityOf Sig-Magma o) ℕ
  f ∙-Op args = args 0F ∸ args 1F
  -- ∸ respects pointwise equality of its two arguments (the only obligation left)
  cong-f : ∀ o → {u v : ArityOf Sig-Magma o → ℕ} → (∀ i → u i ≡ v i) → f o u ≡ f o v
  cong-f ∙-Op args≈ = cong₂ _∸_ (args≈ 0F) (args≈ 1F)
```

Fix the assignment `0F ↦ 3`, `1F ↦ 5`.  The free lift evaluates each generator by
this assignment and each `∙-Op`{.AgdaInductiveConstructor} node by `∸`.  The tree
`(x · y) · x` evaluates to `(3 ∸ 5) ∸ 3 = 0`, whereas `x · (y · x)` evaluates to
`3 ∸ (5 ∸ 3) = 1` — different values, on the nose.

```agda
η : Fin 2 → ℕ
η 0F = 3
η 1F = 5

⟦_⟧η : Term (Fin 2) → ℕ
⟦_⟧η = free-lift {𝑨 = ℕ∸-magma} η

eval-xy·x : ⟦ xy·x ⟧η ≡ 0
eval-xy·x = refl

eval-x·yx : ⟦ x·yx ⟧η ≡ 1
eval-x·yx = refl
```

Because the free magma keeps the two parenthesisations apart, a non-associative
target can tell them apart numerically.  Finally, the free lift is not merely a
function but a homomorphism `𝑻 (Fin 2) ⟶ ℕ∸-magma`, supplied by
`lift-hom`{.AgdaFunction}:

```agda
ηhom : hom (𝑻 (Fin 2)) ℕ∸-magma
ηhom = lift-hom {𝑨 = ℕ∸-magma} η

-- The underlying map of the homomorphism is exactly the free lift.
ηhom-is-free-lift : ∀ t → (proj₁ ηhom) ⟨$⟩ t ≡ ⟦ t ⟧η
ηhom-is-free-lift _ = refl
```
