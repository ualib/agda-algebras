---
layout: default
file: "src/Setoid/Varieties/Maltsev.lagda.md"
title: "Setoid.Varieties.Maltsev module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

### The Maltsev condition as a theory interpretation

This is the [Setoid.Varieties.Maltsev][] module of the [Agda Universal Algebra Library][].

A **Maltsev term** for a variety `𝒱` is a ternary term `m` satisfying

    m(x, x, y) ≈ y      and      m(x, y, y) ≈ x,

and a variety has one exactly when it is congruence-permutable — the original, and
still paradigmatic, *Maltsev condition*.  This is general universal algebra: it is a
property of an arbitrary variety, phrased over an arbitrary signature, with no
commitment to any particular structure.

The module fixes the abstract data of the condition and frames it as a theory
interpretation ([Setoid.Varieties.Interpretation][]): the one-ternary-symbol
signature `Sig-Maltsev`, the two-equation theory `Th-Maltsev`, and the predicate
`HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ` — "`ℰ` admits a Maltsev term" is exactly
"the Maltsev theory interprets into `ℰ`".

A *worked* witness, that the variety of groups has the Maltsev term `x ∙ (y ⁻¹ ∙ z)`,
is structure-specific (it consumes the group operations and laws), so it lives one
layer up, in [Classical.Interpretations.Maltsev][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Fin.Base     using ( Fin )
open import Data.Fin.Patterns using ( 0F ; 1F ; 2F )
open import Data.Product      using ( _×_ ; _,_ )
open import Level             using ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures             using ( Signature )
import Overture.Terms as Terms
open import Setoid.Varieties.Interpretation using ( module Interpret )
```

#### The Maltsev signature and theory

`Sig-Maltsev` has a single ternary operation symbol; `Th-Maltsev` carries the two
Maltsev equations over the variable carrier `Fin 3` (`0F` for `x`, `1F` for `y`).

```agda
data Op-Maltsev : Type where
  m-Op : Op-Maltsev

ar-Maltsev : Op-Maltsev → Type
ar-Maltsev m-Op = Fin 3

Sig-Maltsev : Signature 0ℓ 0ℓ
Sig-Maltsev = Op-Maltsev , ar-Maltsev

-- The canonical 3-element tuple, as a *named* function (not an extended lambda),
-- so the worked-instance proofs can refer to it definitionally.
tri : {ℓ : Level} {A : Type ℓ} → A → A → A → Fin 3 → A
tri a b c 0F = a
tri a b c 1F = b
tri a b c 2F = c

open Terms {𝑆 = Sig-Maltsev} using ( Term ; ℊ ; node )

-- the ternary application m(a, b, c) as a Sig-Maltsev term
m : {X : Type} → Term X → Term X → Term X → Term X
m a b c = node m-Op (tri a b c)

private
  x y z : Term (Fin 3)
  x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F

data Eq-Maltsev : Type where
  mxxy≈y mxyy≈x : Eq-Maltsev

Th-Maltsev : Eq-Maltsev → Term (Fin 3) × Term (Fin 3)
Th-Maltsev mxxy≈y = m x x y , y   -- m(x, x, y) ≈ y
Th-Maltsev mxyy≈x = m x y y , x   -- m(x, y, y) ≈ x
```

#### The Maltsev condition

A theory `ℰ` (equivalently, its variety) *has a Maltsev term* — equivalently, is
congruence-permutable — exactly when the Maltsev theory interprets into it.  This is
the clean, signature-agnostic statement of the condition; a concrete variety
satisfies it by exhibiting an interpretation `Th-Maltsev ≼ ℰ`, i.e. a `ℰ`-term
witnessing the two Maltsev equations.

The target theory's signature is fixed at `(0ℓ , 0ℓ)`, matching `Sig-Maltsev` (the
interpretability relation `_≼_` relates theories over a common level pair); this is
no restriction for the finitary algebraic theories the Maltsev condition concerns.

```agda
module _
  {α ρ χ ι  : Level}
  {𝑆        : Signature 0ℓ 0ℓ}
  {X        : Type χ}
  {Idx      : Type ι}
  where
  open Terms {𝑆 = 𝑆} using () renaming (Term to Term')

  HasMaltsevTerm : (Idx → Term' X × Term' X) → Type (lsuc α ⊔ lsuc ρ ⊔ χ ⊔ ι)
  HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ
    where open Interpret α ρ
```

--------------------------------------

{% include UALib.Links.md %}
