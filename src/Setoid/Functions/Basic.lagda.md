---
layout: default
title : "Setoid.Functions.Basic module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### Setoid functions

This is the [Setoid.Functions.Basic][] module of the [Agda Universal Algebra Library][].

A **setoid function** `A ⟶ B` is the standard library's `Func`{.AgdaRecord}: a map
on carriers together with a proof that it respects the equalities of `A` and `B`.
Carrying the proof inside the function is the move the whole `Setoid/` tree rests
on, but it is worth being precise about what it does.  `cong`{.AgdaField} says
that *one* map sends related arguments to related results; it says nothing about
when two maps are the same.  Where two functions do have to be compared, the
library never asks for propositional equality of functions — which is what would
require extensionality — but uses an explicitly pointwise relation instead:
`function-equality`{.AgdaFunction} of [Setoid.Relations.Discrete][], and
`_≋_`{.AgdaFunction} of [Setoid.Categories.Algebra][] for homomorphisms.  The two
devices together are what keep the development extensionality-free.

This module holds the primitives everything else is built from, and nothing
deeper: the identity setoid function, composition, and the universe lifting of a
setoid.  They are gathered here so that the lifting lemmas in particular exist in
one place, rather than being re-derived wherever a level has to change.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Functions.Basic where

-- Imports from Agda and the Agda Standard Library -----------------------
open import Function         using ( id ; _∘_ ) renaming ( Func to _⟶_ )
open import Level            using ( Level ; Lift ; _⊔_ )
open import Relation.Binary  using ( Setoid )

private variable α ρᵃ β ρᵇ γ ρᶜ : Level
```
-->

Because a setoid function carries its own congruence proof, identity and
composition need no side conditions: each simply does to the proofs what it does
to the maps.

+  `𝑖𝑑`{.AgdaFunction} is the identity, whose congruence proof is itself the
   identity.
+  `_⊙_`{.AgdaFunction} is composition, taking the composite of the two maps and
   the composite of the two congruence proofs.  It is written right to left, so
   `f ⊙ g` applies `g` first.

The rest of the fence lifts a setoid to a higher universe level, which Agda's
non-cumulative universes make necessary.  `𝑙𝑖𝑓𝑡 ℓ`{.AgdaFunction} raises the level
of the carrier and leaves the equality alone, relating two lifted elements exactly
when the elements underneath them were related.  `liftFunc`{.AgdaFunction} is the
setoid function into the lift, and `lift∼lower`{.AgdaFunction} and
`lower∼lift`{.AgdaFunction} say that lifting and lowering are mutually inverse.
Both are proved by reflexivity alone, which is the point: the lifted equality *is*
the original equality read through `lower`, so there is nothing to transport.

```agda
𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { to = id ; cong = id }

open _⟶_ renaming ( to to _⟨$⟩_ )

_⊙_ :  {A : Setoid α ρᵃ}{B : Setoid β ρᵇ}{C : Setoid γ ρᶜ}
  →     B ⟶ C → A ⟶ B → A ⟶ C
f ⊙ g = record { to = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g); cong = (cong f) ∘ (cong g) }

module _ {𝑨 : Setoid α ρᵃ} where
  open Lift ; open Level ; open Setoid using (_≈_)
  open Setoid 𝑨 using ( sym ; trans ) renaming (Carrier to A ; _≈_ to _≈ₐ_ ; refl to reflₐ)

  𝑙𝑖𝑓𝑡 : ∀ ℓ → Setoid (α ⊔ ℓ) ρᵃ
  𝑙𝑖𝑓𝑡 ℓ = record  { Carrier = Lift ℓ A
                 ; _≈_ = λ x y → (lower x) ≈ₐ (lower y)
                 ; isEquivalence = record { refl = reflₐ ; sym = sym ; trans = trans }
                 }

  lift∼lower : (a : Lift β A) → (_≈_ (𝑙𝑖𝑓𝑡 β)) (lift (lower a)) a
  lift∼lower a = reflₐ

  lower∼lift : ∀ a → (lower {α}{β}) (lift a) ≈ₐ a
  lower∼lift _ = reflₐ

  liftFunc : {ℓ : Level} → 𝑨 ⟶ 𝑙𝑖𝑓𝑡 ℓ
  liftFunc = record { to = lift ; cong = id }
```
