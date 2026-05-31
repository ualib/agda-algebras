---
layout: default
file: "src/Examples/Classical/Lattices/L2Distributive.lagda.md"
title: "Examples.Classical.Lattices.L2Distributive module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example: `𝑳𝟚 = (Bool, _∧_, _∨_)` as a distributive lattice {#examples-classical-distributivelattice}

This is the [Examples.Classical.Lattices.L2Distributive][] module of the [Agda Universal Algebra Library][].

The two-element Boolean lattice `𝑳𝟚` is distributive, and this module promotes the
`Lattice` instance of [`Examples.Classical.Lattices.L2`][] to a full
[`DistributiveLattice`][Classical.Structures.DistributiveLattice], thus providing a complete
example of a (formal, verified) `DistributiveLattice` construction: all ten equations are
discharged by standard-library lemmas, and the new structure round-trips through stdlib's
`Algebra.Lattice.Bundles.DistributiveLattice`.

The eight lattice equations are exactly those used in the `Lattice` example; the two
new ones are the *left* distributivity laws, supplied directly by stdlib's
`∧-distribˡ-∨` (`x ∧ (y ∨ z) ≡ (x ∧ y) ∨ (x ∧ z)`) and `∨-distribˡ-∧`
(`x ∨ (y ∧ z) ≡ (x ∨ y) ∧ (x ∨ z)`).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Examples.Classical.Lattices.L2Distributive where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Bool using  ( Bool ; _∧_ ; _∨_ )
open import Data.Bool.Properties
  using  ( ∧-assoc ; ∧-comm ; ∧-idem ; ∨-assoc ; ∨-comm ; ∨-idem  ; ∧-distribˡ-∨ ; ∨-distribˡ-∧ )
  renaming ( ∧-abs-∨ to ∧-absorbs-∨ ; ∨-abs-∧ to ∨-absorbs-∧ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; trans )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.DistributiveLattice using ( ⟨_⟩ᵈˡ ; ⟪_⟫ᵈˡ )
open import Classical.Small.Structures.DistributiveLattice
  using ( DistributiveLattice ; eqsToDistributiveLattice )
import Classical.Structures.DistributiveLattice as Polymorphic
```

#### Deriving the second absorption equation {#absorbR}

As in the `Lattice` example, `eqsToDistributiveLattice` takes the second absorption
equation in the form `(a ∧ b) ∨ a ≡ a`; stdlib's `∨-absorbs-∧` is `a ∨ (a ∧ b) ≡ a`,
and one `∨-comm` step bridges them.

```agda
Bool-absorbʳ-dl : ∀ a b → (a ∧ b) ∨ a ≡ a
Bool-absorbʳ-dl a b = trans (∨-comm (a ∧ b) a) (∨-absorbs-∧ a b)
```

#### The distributive lattice `𝟚 = (Bool, _∧_, _∨_)` {#bool-distributive-lattice}

```agda
Bool-distributiveLattice : DistributiveLattice
Bool-distributiveLattice = eqsToDistributiveLattice Bool _∧_ _∨_
  ∧-assoc ∧-comm ∧-idem ∨-assoc ∨-comm ∨-idem ∧-absorbs-∨ Bool-absorbʳ-dl ∧-distribˡ-∨ ∨-distribˡ-∧
```

#### Acceptance checks {#acceptance}

The `DistributiveLattice-Op` accessors interpret to stdlib's `Bool._∧_` and
`Bool._∨_` on the nose, and the two left-distributivity laws hold (by `refl`, since
the operations evaluate definitionally on `Bool`).

```agda
open Polymorphic.DistributiveLattice-Op Bool-distributiveLattice
  renaming ( _∧_ to _∙∧_ ; _∨_ to _∙∨_ )

∙∧-is-∧-dl : ∀ (a b : Bool) → a ∙∧ b ≡ a ∧ b
∙∧-is-∧-dl a b = refl

∙∨-is-∨-dl : ∀ (a b : Bool) → a ∙∨ b ≡ a ∨ b
∙∨-is-∨-dl a b = refl
```

#### Round-trip through `Algebra.Lattice.Bundles.DistributiveLattice` {#roundtrip}

The bundle bridge round-trips on `Bool-distributiveLattice` pointwise on both
operations; both directions reduce by `refl` at the curried form.

```agda
open Polymorphic.DistributiveLattice-Op ⟪ ⟨ Bool-distributiveLattice ⟩ᵈˡ ⟫ᵈˡ using ()
  renaming ( _∧_ to _∙∧'_ ; _∨_ to _∙∨'_ )

roundtrip-∧-dl : ∀ (a b : Bool) → a ∙∧' b ≡ a ∧ b
roundtrip-∧-dl a b = refl

roundtrip-∨-dl : ∀ (a b : Bool) → a ∙∨' b ≡ a ∨ b
roundtrip-∨-dl a b = refl
```

--------------------------------------

{% include UALib.Links.md %}
