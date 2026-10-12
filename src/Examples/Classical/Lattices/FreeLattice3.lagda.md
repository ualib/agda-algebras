---
layout: default
file: "src/Examples/Classical/Lattices/FreeLattice3.lagda.md"
title: "Examples.Classical.Lattices.FreeLattice3 module"
date: "2026-10-07"
author: "the agda-algebras development team"
---

### Worked example: computing in the free lattice on three generators

This is the [Examples.Classical.Lattices.FreeLattice3][] module of the [Agda Universal Algebra Library][].

The free lattice `FL(3)` on generators `x`, `y`, `z` is infinite, and every
question about its order is decided by Whitman's procedure
(`_≤ʷ?_`{.AgdaFunction} of [Classical.Structures.Lattice.Free.Whitman][]).  This
module asks a handful of such questions and lets Agda answer them by evaluation:
each theorem below is `from-yes` or `from-no` applied to a decision, so it type
checks only if the procedure computes the expected verdict, and a wrong
expectation fails to compile.  By Whitman's theorem
([Classical.Structures.Lattice.Free.Universal][]) each verdict is a fact about all
lattices: an inequality the procedure accepts holds in every lattice, and one it
rejects fails in some lattice, namely in `FL(3)` itself.

The last sections compute canonical forms
([Classical.Structures.Lattice.Free.Canonical][]) in the same way: each claimed
canonical form is an equation that holds by `refl`, so Agda runs the
canonicalization algorithm while checking the module.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Classical.Lattices.FreeLattice3 where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Fin.Base                        using ( Fin )
open import Data.Fin.Patterns                    using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                  using ( _≟_ )
open import Data.List.Base                       using ( [] ; _∷_ )
open import Relation.Binary.Definitions          using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary                     using ( ¬_ )
open import Relation.Nullary.Decidable.Core      using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Structures.Lattice.Free.Canonical     using ( genᶜ ; joinᶜ ; meetᶜ ; jgen
                                                                  ; jmeet ; mgen ; mjoin ; _≈ᶜ_
                                                                  ; module Canonicalization
                                                                  ; module Comparison )
open import Classical.Structures.Lattice.Free.Derivability  using ( E-Lattice ; ⊢? )
open import Classical.Structures.Lattice.Free.Term          using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_
                                                                  ; toTerm )
open import Classical.Structures.Lattice.Free.Whitman       using ( _≤ʷ_ ; _≈ʷ_
                                                                  ; module Decision
                                                                  ; ℊ≤ℊ ; ℊ≤∨ˡ ; ∧ˡ≤∨ )
open import Setoid.Varieties.SoundAndComplete               using ( _⊢_▹_≈_ )
```
-->

#### The generators

The three generators are the terms `ℊ 0F`, `ℊ 1F`, and `ℊ 2F` over `Fin 3`.  The
procedure compares generators (rule 1) with the standard library's decidable
equality of `Fin 3`, here `_≟₃_`{.AgdaFunction}, the instance at `Fin 3` of
`_≟_`{.AgdaFunction}; opening `Decision`{.AgdaModule} at it brings the decision
procedures `_≤ʷ?_`{.AgdaFunction} and `_≈ʷ?_`{.AgdaFunction} for `FL(3)` into
scope.

```agda
x y z : LatTerm (Fin 3)
x = ℊ 0F
y = ℊ 1F
z = ℊ 2F

_≟₃_ : DecidableEquality (Fin 3)
_≟₃_ = _≟_

open Decision _≟₃_ using ( _≤ʷ?_ ; _≈ʷ?_ )
```

#### A derivation by hand

An inhabitant of `s ≤ʷ t`{.AgdaDatatype} is a derivation by Whitman's rules, and
small ones can be written out.  The meet `x ∧ y` lies below the join `x ∨ z` by
Whitman's condition (rule 6, the disjunct `∧ˡ≤∨`{.AgdaInductiveConstructor}),
because its meetand `x` lies below the join (rule 4, the disjunct
`ℊ≤∨ˡ`{.AgdaInductiveConstructor}), because `x` is `x` (rule 1).

```agda
meet≤join : x ∧̇ y ≤ʷ x ∨̇ z
meet≤join = ∧ˡ≤∨ (ℊ≤∨ˡ (ℊ≤ℊ refl))
```

#### Distributivity fails

In a distributive lattice `x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)`.  In every lattice the
right side is below the left (`distrib-≥`{.AgdaFunction}), but the free lattice
does not satisfy the other inequality (`distrib-≰`{.AgdaFunction}).  By hand: the
left side is a meet and the right side a join, so only Whitman's condition
applies, and each of its four disjuncts fails.  The meetand `x` is not below the
join, since by rule 4 it would be below `x ∧ y` or `x ∧ z`, hence below `y` or
`z`.  The meetand `y ∨ z` is not below the join, since by rule 2 its joinand `y`
would be, and `y` is below neither joinand, not being below `x`.  And the whole
meet is below neither joinand, since by rule 3 it would be below `y` or below
`z`, which by rule 5 needs `x` or `y ∨ z` below that generator, and neither is.
The diamond `M₃` and the pentagon `N₅`, the two nondistributive lattices on five
elements, are both generated by three elements, hence images of `FL(3)`, and in
each the inequality fails under a suitable assignment of `x`, `y`, and `z`.

```agda
distrib-≥ : (x ∧̇ y) ∨̇ (x ∧̇ z) ≤ʷ x ∧̇ (y ∨̇ z)
distrib-≥ = from-yes ((x ∧̇ y) ∨̇ (x ∧̇ z) ≤ʷ? x ∧̇ (y ∨̇ z))

distrib-≰ : ¬ (x ∧̇ (y ∨̇ z) ≤ʷ (x ∧̇ y) ∨̇ (x ∧̇ z))
distrib-≰ = from-no (x ∧̇ (y ∨̇ z) ≤ʷ? (x ∧̇ y) ∨̇ (x ∧̇ z))
```

#### Modularity fails

The modular law is the weaker identity `x ∧ (y ∨ (x ∧ z)) = (x ∧ y) ∨ (x ∧ z)`,
the distributive law `x ∧ (y ∨ w) = (x ∧ y) ∨ (x ∧ w)` restricted to elements
`w = x ∧ z` below `x`.  It fails in `FL(3)` as well (`modular-≰`{.AgdaFunction}), as it must,
since the pentagon `N₅` is generated by three elements and is not modular.

```agda
modular-≰ : ¬ (x ∧̇ (y ∨̇ (x ∧̇ z)) ≤ʷ (x ∧̇ y) ∨̇ (x ∧̇ z))
modular-≰ = from-no (x ∧̇ (y ∨̇ (x ∧̇ z)) ≤ʷ? (x ∧̇ y) ∨̇ (x ∧̇ z))
```

#### Absorption holds

The two absorption laws of `Th-Lattice`{.AgdaFunction} hold in every lattice, so
the procedure must find both sides of each equal in `FL(3)`; equality is mutual
`_≤ʷ_`{.AgdaDatatype}, decided by `_≈ʷ?_`{.AgdaFunction}.

```agda
absorbˡ : x ∧̇ (x ∨̇ y) ≈ʷ x
absorbˡ = from-yes (x ∧̇ (x ∨̇ y) ≈ʷ? x)

absorbʳ : (x ∧̇ y) ∨̇ x ≈ʷ x
absorbʳ = from-yes ((x ∧̇ y) ∨̇ x ≈ʷ? x)
```

#### What the lattice axioms derive

Through the bridge of [Classical.Structures.Lattice.Free.Derivability][], the same
computations decide derivability in equational logic from the eight axioms of
`Th-Lattice`{.AgdaFunction}.  The distributive law is not a consequence of them
(`distrib-underivable`{.AgdaFunction}), a theorem proved here by evaluation; and
the first absorption law, translated to a `Term`{.AgdaDatatype}, is derivable
(`absorbˡ-derivable`{.AgdaFunction}), by a derivation the bridge constructs from
Whitman's verdict through Birkhoff's completeness theorem, not one written by
hand.

```agda
distrib-underivable :
  ¬ (E-Lattice ⊢ Fin 3 ▹ toTerm (x ∧̇ (y ∨̇ z)) ≈ toTerm ((x ∧̇ y) ∨̇ (x ∧̇ z)))
distrib-underivable = from-no (⊢? _≟₃_ (toTerm (x ∧̇ (y ∨̇ z))) (toTerm ((x ∧̇ y) ∨̇ (x ∧̇ z))))

absorbˡ-derivable : E-Lattice ⊢ Fin 3 ▹ toTerm (x ∧̇ (x ∨̇ y)) ≈ toTerm x
absorbˡ-derivable = from-yes (⊢? _≟₃_ (toTerm (x ∧̇ (x ∨̇ y))) (toTerm x))
```

#### Canonical forms

The canonical form of a term is computed by `canonical`{.AgdaFunction}, opened here
at the decidable equality of `Fin 3`.  The second absorption law reappears as a
computation: the canonical form of `(x ∧ y) ∨ x` is the generator `x`
(`canonical-absorbʳ`{.AgdaFunction}), since the joinand `x ∧ y` lies below the
joinand `x` and is deleted.

In `(x ∧ (y ∨ z)) ∨ y ∨ (x ∧ z)` the joinand `x ∧ z` lies below the joinand
`x ∧ (y ∨ z)` and is deleted, which leaves the join `(x ∧ (y ∨ z)) ∨ y`
(`canonical-delete`{.AgdaFunction}).  In `(x ∧ (y ∨ z)) ∨ y ∨ z` no joinand lies
below another, but the meetand `y ∨ z` of the joinand `x ∧ (y ∨ z)` lies below
the whole join, so condition 4 of Theorem 1.18 fails; the algorithm replaces the
meet by the joinands `y` and `z` of that meetand, and deleting the repeated
joinands leaves `y ∨ z` (`canonical-condition4`{.AgdaFunction}).  A join can also
collapse to a meet: `y ∧ z` lies below `(x ∨ y) ∧ (x ∨ z)`, so the canonical form
of their join is the meet (`canonical-meet`{.AgdaFunction}).

```agda
open Canonicalization _≟₃_ using ( canonical ; canonical-isCanonical )

canonical-absorbʳ : canonical ((x ∧̇ y) ∨̇ x) ≡ genᶜ 0F
canonical-absorbʳ = refl

canonical-delete :
  canonical ((x ∧̇ (y ∨̇ z)) ∨̇ (y ∨̇ (x ∧̇ z)))
  ≡ joinᶜ (jmeet (mgen 0F) (mjoin (jgen 1F) (jgen 2F ∷ []) ∷ [])) (jgen 1F ∷ [])
canonical-delete = refl

canonical-condition4 : canonical ((x ∧̇ (y ∨̇ z)) ∨̇ (y ∨̇ z)) ≡ joinᶜ (jgen 1F) (jgen 2F ∷ [])
canonical-condition4 = refl

canonical-meet :
  canonical (((x ∨̇ y) ∧̇ (x ∨̇ z)) ∨̇ (y ∧̇ z))
  ≡ meetᶜ (mjoin (jgen 0F) (jgen 1F ∷ [])) (mjoin (jgen 0F) (jgen 2F ∷ []) ∷ [])
canonical-meet = refl
```

#### Unique up to commutativity

Canonical forms are unique only up to the order of joinands and meetands
(Theorem 1.17).  The terms `x ∨ y` and `y ∨ x` have different canonical forms,
which list the same joinands in different orders (`canonical-x∨y`{.AgdaFunction},
`canonical-y∨x`{.AgdaFunction}), and the two forms are related by
`_≈ᶜ_`{.AgdaDatatype}, as the comparison of canonical forms decides
(`x∨y≈ᶜy∨x`{.AgdaFunction}).

```agda
open Comparison _≟₃_ using ( ≈ᶜ? ; _≈ᶠ?_ )

canonical-x∨y : canonical (x ∨̇ y) ≡ joinᶜ (jgen 0F) (jgen 1F ∷ [])
canonical-x∨y = refl

canonical-y∨x : canonical (y ∨̇ x) ≡ joinᶜ (jgen 1F) (jgen 0F ∷ [])
canonical-y∨x = refl

x∨y≈ᶜy∨x : canonical (x ∨̇ y) ≈ᶜ canonical (y ∨̇ x)
x∨y≈ᶜy∨x = from-yes (≈ᶜ? (canonical (x ∨̇ y)) (canonical (y ∨̇ x))
                         (canonical-isCanonical (x ∨̇ y)) (canonical-isCanonical (y ∨̇ x)))
```

#### Deciding equality by canonical forms

Comparing canonical forms is a second decision procedure for equality in `FL(3)`,
`_≈ᶠ?_`{.AgdaFunction}, which never runs Whitman's procedure on the two terms.  It
confirms the first absorption law (`absorbˡ-canonical`{.AgdaFunction}) and refutes
the distributive law (`distrib-≉-canonical`{.AgdaFunction}), as Whitman's
procedure did above.

```agda
absorbˡ-canonical : x ∧̇ (x ∨̇ y) ≈ʷ x
absorbˡ-canonical = from-yes (x ∧̇ (x ∨̇ y) ≈ᶠ? x)

distrib-≉-canonical : ¬ (x ∧̇ (y ∨̇ z) ≈ʷ (x ∧̇ y) ∨̇ (x ∧̇ z))
distrib-≉-canonical = from-no (x ∧̇ (y ∨̇ z) ≈ᶠ? (x ∧̇ y) ∨̇ (x ∧̇ z))
```
