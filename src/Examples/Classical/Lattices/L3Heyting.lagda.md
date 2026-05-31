---
layout: default
file: "src/Examples/Classical/Lattices/L3Heyting.lagda.md"
title: "Examples.Classical.Lattices.L3Heyting module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example — the three-element chain as a finite Heyting algebra {#examples-classical-heytingchain3}

This is the [Examples.Classical.Lattices.L3Heyting][] module of the [Agda Universal Algebra Library][].

The three-element chain `𝟛 = {0 ≤ 1 ≤ 2}` is the smallest non-Boolean Heyting
algebra: as a lattice it is `(Fin 3, min, max)`, and because every chain is
distributive it is a
[`DistributiveLattice`][Classical.Structures.DistributiveLattice].
What makes it a *Heyting* algebra is a relative pseudocomplement (an implication)
`_⇒_` satisfying the residuation adjunction

    a ∧ b ≤ c  ⟺  a ≤ (b ⇒ c),

where `a ≤ b` is the meet order `a ∧ b ≡ a`.  The chain is presented *as a lattice
example* — concretely a distributive lattice — and the implication is supplied as an
extra operation whose residuation and Heyting identities are proved alongside.

Both the lattice operations and the implication are given by Cayley tables, and
every law — the ten distributive-lattice equations, the residuation adjunction, and
the Heyting identities — is discharged by *decision* over the finite carrier
(`from-yes` applied to an `all?`/`_≟_` decision), exactly as in the
[finite-group examples][Examples.Classical.CyclicGroup3].  A wrong table would make
the corresponding decision compute to `no`, and the example would fail to compile.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Examples.Classical.Lattices.L3Heyting where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Fin                                using ( Fin )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                     using ( _≟_ ; all? )
open import Data.Product                            using ( _×_ )
open import Data.Vec.Base                           using ( _∷_ ; [] )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core         using ( Dec ; _×-dec_ ; _→-dec_ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Overture.Cayley                                 using ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties                  using ( Associative? ; Commutative? ; Idempotent?
                                                                   ; Absorbsˡ? ; Absorbsʳ? ; Distributesˡ? )
open import Classical.Bundles.DistributiveLattice           using ( ⟨_⟩ᵈˡ ; ⟪_⟫ᵈˡ )
open import Classical.Properties.Lattice                    using ( module FiniteOrder )
open import Classical.Small.Structures.DistributiveLattice  using ( DistributiveLattice ; eqsToDistributiveLattice )
import Classical.Structures.DistributiveLattice as Polymorphic
```

#### The Cayley tables {#tables}

The carrier is `Fin 3`, ordered `0 ≤ 1 ≤ 2`, with top element `⊤ = 2`.  Meet is the
minimum, join is the maximum, and the implication `a ⇒ b` is the largest `x` with
`a ∧ x ≤ b` — on a chain this is `⊤` when `a ≤ b` and `b` otherwise.

| `∧` | 0 | 1 | 2 |   | `∨` | 0 | 1 | 2 |   | `⇒` | 0 | 1 | 2 |
|-----|---|---|---|---|-----|---|---|---|---|-----|---|---|---|
| 0   | 0 | 0 | 0 |   | 0   | 0 | 1 | 2 |   | 0   | 2 | 2 | 2 |
| 1   | 0 | 1 | 1 |   | 1   | 1 | 1 | 2 |   | 1   | 0 | 2 | 2 |
| 2   | 0 | 1 | 2 |   | 2   | 2 | 2 | 2 |   | 2   | 0 | 1 | 2 |

```agda
infixr 7 _∧_
infixr 6 _∨_
infixr 5 _⇒_

⊤ : Fin 3
⊤ = 2F

∧-table : Table 3
∧-table = (0F ∷ 0F ∷ 0F ∷ [])
        ∷ (0F ∷ 1F ∷ 1F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ [])
        ∷ []

∨-table : Table 3
∨-table = (0F ∷ 1F ∷ 2F ∷ [])
        ∷ (1F ∷ 1F ∷ 2F ∷ [])
        ∷ (2F ∷ 2F ∷ 2F ∷ [])
        ∷ []

⇒-table : Table 3
⇒-table = (2F ∷ 2F ∷ 2F ∷ [])
        ∷ (0F ∷ 2F ∷ 2F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ [])
        ∷ []

_∧_ _∨_ _⇒_ : Fin 3 → Fin 3 → Fin 3
_∧_ = ⟦ ∧-table ⟧
_∨_ = ⟦ ∨-table ⟧
_⇒_ = ⟦ ⇒-table ⟧
```

#### The chain as a distributive lattice {#chain-distributive-lattice}

The decidable law-checkers all come from `Overture.Operations.Properties`:
associativity, commutativity, and idempotency of each operation, and the
two-operation absorption and distributivity laws (`Absorbsˡ?`, `Absorbsʳ?`,
`Distributesˡ?`).  Note that the second distributivity law, `∨` over `∧`, is
`Distributesˡ?` with the two operations exchanged.

```agda
chain3 : DistributiveLattice
chain3 = eqsToDistributiveLattice (Fin 3) _∧_ _∨_
  (from-yes (Associative? _∧_)) (from-yes (Commutative? _∧_)) (from-yes (Idempotent? _∧_))
  (from-yes (Associative? _∨_)) (from-yes (Commutative? _∨_)) (from-yes (Idempotent? _∨_))
  (from-yes (Absorbsˡ? _∧_ _∨_)) (from-yes (Absorbsʳ? _∧_ _∨_))
  (from-yes (Distributesˡ? _∧_ _∨_)) (from-yes (Distributesˡ? _∨_ _∧_))
```

#### The residuation adjunction {#residuation}

The meet order `a ≤ b := a ∧ b ≡ a` and its decider `_≤?_` come from
`Classical.Properties.Lattice.FiniteOrder` (instantiated at `_∧_`).  The defining
property of the Heyting implication is the residuation adjunction between `_∧ b` and
`b ⇒_`: for all `a b c`, `(a ∧ b) ≤ c` holds iff `a ≤ (b ⇒ c)`.  Both directions are
decidable (each is an implication between decidable meet-order facts), so the
biconditional, quantified over the finite carrier, is decided and extracted by
`from-yes`.

```agda
open FiniteOrder _∧_

residuation? : Dec (∀ a b c → (a ∧ b ≤ c → a ≤ (b ⇒ c)) × (a ≤ (b ⇒ c) → a ∧ b ≤ c))
residuation? =
  all? (λ a →
    all? (λ b →
      all? (λ c →
        (a ∧ b ≤? c →-dec a ≤? (b ⇒ c)) ×-dec (a ≤? (b ⇒ c) →-dec a ∧ b ≤? c))))

residuation : ∀ a b c → ((a ∧ b) ≤ c → a ≤ (b ⇒ c)) × (a ≤ (b ⇒ c) → (a ∧ b) ≤ c)
residuation = from-yes residuation?
```

#### Heyting identities {#identities}

Three identities characteristic of the implication, each decided over the carrier:
`a ⇒ a ≡ ⊤` (reflexivity); `⊤ ⇒ a ≡ a` (the top element is the left unit of `⇒`);
and `a ∧ (a ⇒ b) ≡ a ∧ b` (the equational form of modus ponens).

```agda
⇒-refl? : Dec (∀ a → (a ⇒ a) ≡ ⊤)
⇒-refl? = all? (λ a → (a ⇒ a) ≟ ⊤)

⊤-unitˡ? : Dec (∀ a → (⊤ ⇒ a) ≡ a)
⊤-unitˡ? = all? (λ a → (⊤ ⇒ a) ≟ a)

modus-ponens? : Dec (∀ a b → a ∧ (a ⇒ b) ≡ a ∧ b)
modus-ponens? = all? (λ a → all? (λ b → (a ∧ (a ⇒ b)) ≟ (a ∧ b)))

⇒-refl : ∀ a → (a ⇒ a) ≡ ⊤
⇒-refl = from-yes ⇒-refl?

⊤-unitˡ : ∀ a → (⊤ ⇒ a) ≡ a
⊤-unitˡ = from-yes ⊤-unitˡ?

modus-ponens : ∀ a b → a ∧ (a ⇒ b) ≡ a ∧ b
modus-ponens = from-yes modus-ponens?
```

#### Acceptance checks {#acceptance}

The `DistributiveLattice-Op` accessors interpret to the tabulated meet and join on
the nose, and the bundle bridge round-trips, both discharged by `refl`.

```agda
open Polymorphic.DistributiveLattice-Op chain3 renaming ( _∧_ to _∙∧_ ; _∨_ to _∙∨_ )

∙∧-is-∧ : ∀ (a b : Fin 3) → a ∙∧ b ≡ a ∧ b
∙∧-is-∧ a b = refl

∙∨-is-∨ : ∀ (a b : Fin 3) → a ∙∨ b ≡ a ∨ b
∙∨-is-∨ a b = refl

open Polymorphic.DistributiveLattice-Op ⟪ ⟨ chain3 ⟩ᵈˡ ⟫ᵈˡ using ()
  renaming ( _∧_ to _∙∧'_ ; _∨_ to _∙∨'_ )

roundtrip-∧ : ∀ (a b : Fin 3) → a ∙∧' b ≡ a ∧ b
roundtrip-∧ a b = refl

roundtrip-∨ : ∀ (a b : Fin 3) → a ∙∨' b ≡ a ∨ b
roundtrip-∨ a b = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical](Examples.Classical.html)</span>

{% include UALib.Links.md %}
