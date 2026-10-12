---
layout: default
file: "src/Classical/Structures/Lattice/Free/Duality.lagda.md"
title: "Classical.Structures.Lattice.Free.Duality module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Duality for lattice terms

This is the [Classical.Structures.Lattice.Free.Duality][] module of the [Agda Universal Algebra Library][].

Every statement about lattices has a dual, obtained by exchanging meet and join
and reversing the order, and the dual of a theorem is a theorem.  For lattice
terms the exchange is a function, `dual`{.AgdaFunction}, which swaps the formal
operations `_∧̇_`{.AgdaInductiveConstructor} and `_∨̇_`{.AgdaInductiveConstructor}
and fixes the generators.  It is an involution (`dual-involutive`{.AgdaFunction}),
and it reverses Whitman's order (`dual-antitone`{.AgdaFunction}): each of the
rules of [Classical.Structures.Lattice.Free.Whitman][] is carried to its dual, so
a derivation of `s ≤ʷ t` is carried, rule by rule, to a derivation of
`dual t ≤ʷ dual s`.  In other words, `dual`{.AgdaFunction} is an isomorphism from
`FL(X)` onto its order dual.

The canonical forms of [Classical.Structures.Lattice.Free.Canonical][] use this
module to obtain the canonical form of a meet from that of a join, rather than
running the dual algorithm and repeating its proofs.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Duality where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                           using ( _,_ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; cong₂ ; subst₂ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Classical.Structures.Lattice.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ℊ≤∧ ; ∧≤∧ ; ℊ≤ℊ ; ℊ≤∨ˡ ; ℊ≤∨ʳ ; ∧ˡ≤ℊ ; ∧ʳ≤ℊ
         ; ∧ˡ≤∨ ; ∧ʳ≤∨ ; ∧≤∨ˡ ; ∧≤∨ʳ ; ≤∧ ; ≤∨ˡ ; ≤∨ʳ ; ∧ˡ≤ ; ∧ʳ≤ )

private variable
  χ : Level
  X : Type χ
  s t : LatTerm X
```
-->

#### The dual of a term

`dual t`{.AgdaFunction} is `t` with every formal meet replaced by a formal join
and every formal join by a formal meet.  Applying it twice gives back the term
(`dual-involutive`{.AgdaFunction}), by induction.

```agda
dual : LatTerm X → LatTerm X
dual (ℊ x)    = ℊ x
dual (s ∧̇ t)  = dual s ∨̇ dual t
dual (s ∨̇ t)  = dual s ∧̇ dual t

dual-involutive : (t : LatTerm X) → dual (dual t) ≡ t
dual-involutive (ℊ x)    = refl
dual-involutive (s ∧̇ t)  = cong₂ _∧̇_ (dual-involutive s) (dual-involutive t)
dual-involutive (s ∨̇ t)  = cong₂ _∨̇_ (dual-involutive s) (dual-involutive t)
```

#### The dual reverses the order

`dual-antitone`{.AgdaFunction} carries each rule to its dual, by induction on the
derivation.  Rule 2 (a join on the left) becomes rule 3 (a meet on the right) and
conversely; rule 4 (a generator below a join) becomes rule 5 (a meet above a
generator, now below the dual generator) and conversely; and each disjunct of
Whitman's condition becomes another disjunct of it.  Because the dispatch order
of `_≤ʷ_`{.AgdaDatatype} is not self-dual (a join on the left is split before a
meet on the right), the conclusions are rebuilt with the general introduction
and weakening lemmas `≤∧`{.AgdaFunction}, `≤∨ˡ`{.AgdaFunction}, and
`∧ˡ≤`{.AgdaFunction}, rather than with the constructors themselves.  With the
involution, the dual also reflects the order (`dual-reflects`{.AgdaFunction}),
and it preserves equality in the free lattice (`dual-cong`{.AgdaFunction}).

```agda
dual-antitone : s ≤ʷ t → dual t ≤ʷ dual s
dual-antitone (∨≤ p q)   = ≤∧ (dual-antitone p) (dual-antitone q)
dual-antitone (ℊ≤∧ p q)  = ∨≤ (dual-antitone p) (dual-antitone q)
dual-antitone (∧≤∧ p q)  = ∨≤ (dual-antitone p) (dual-antitone q)
dual-antitone (ℊ≤ℊ e)    = ℊ≤ℊ (sym e)
dual-antitone (ℊ≤∨ˡ p)   = ∧ˡ≤ (dual-antitone p)
dual-antitone (ℊ≤∨ʳ p)   = ∧ʳ≤ (dual-antitone p)
dual-antitone (∧ˡ≤ℊ p)   = ≤∨ˡ (dual-antitone p)
dual-antitone (∧ʳ≤ℊ p)   = ≤∨ʳ (dual-antitone p)
dual-antitone (∧ˡ≤∨ p)   = ≤∨ˡ (dual-antitone p)
dual-antitone (∧ʳ≤∨ p)   = ≤∨ʳ (dual-antitone p)
dual-antitone (∧≤∨ˡ p)   = ∧ˡ≤ (dual-antitone p)
dual-antitone (∧≤∨ʳ p)   = ∧ʳ≤ (dual-antitone p)

dual-reflects : dual t ≤ʷ dual s → s ≤ʷ t
dual-reflects {t = t} {s = s} p =
  subst₂ _≤ʷ_ (dual-involutive s) (dual-involutive t) (dual-antitone p)

dual-cong : s ≈ʷ t → dual s ≈ʷ dual t
dual-cong (p , q) = dual-antitone q , dual-antitone p
```
