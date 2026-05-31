---
layout: default
file: "src/Examples/Classical/Groups/KleinFourGroup.lagda.md"
title: "Examples.Classical.Groups.KleinFourGroup module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked Example: the Klein four-group `V₄` from a Cayley table

This is the [Examples.Classical.Groups.KleinFourGroup][] module of the [Agda Universal Algebra Library][].

The Klein four-group `V₄ ≅ ℤ/2ℤ × ℤ/2ℤ` is the smallest non-cyclic group.
We build it on the carrier `Fin 4`, identifying the four elements with
the two-bit codes `0 = (0,0)`, `1 = (1,0)`, `2 = (0,1)`, `3 = (1,1)`, so the group
operation is component-wise addition mod 2 — equivalently, bitwise *exclusive or* on
the index.  As with [`Examples.Classical.Groups.CyclicGroup3`][], the group axioms are
discharged by decision over the finite carrier.

The defining feature, in contrast to `ℤ/3ℤ`, is that every element is its own inverse
(the group has exponent `2`), so the inverse map is the identity.

The operation table (entry `a , b` is `a xor b`):

| · | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| 0 | 0 | 1 | 2 | 3 |
| 1 | 1 | 0 | 3 | 2 |
| 2 | 2 | 3 | 0 | 1 |
| 3 | 3 | 2 | 1 | 0 |

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups.KleinFourGroup where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin                                using ( Fin )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F ; 3F )
open import Data.Vec.Base                           using ( _∷_ ; [] )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                   using  ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties    using  ( Associative? ; Commutative?
                                                     ; LeftIdentity? ; RightIdentity?
                                                     ; LeftInverse? ; RightInverse? )
open import Classical.Bundles.Group           using  ( ⟨_⟩ᵍᵖ ; ⟪_⟫ᵍᵖ )
open import Classical.Small.Structures.Group  using  ( Group ; eqsToGroup )
import Classical.Structures.Group as Polymorphic
```

#### The Cayley table, the operation, and the inverse map

```agda
-- The bitwise-xor table on the two-bit codes 0..3.
v4-table : Table 4
v4-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ [])
         ∷ (1F ∷ 0F ∷ 3F ∷ 2F ∷ [])
         ∷ (2F ∷ 3F ∷ 0F ∷ 1F ∷ [])
         ∷ (3F ∷ 2F ∷ 1F ∷ 0F ∷ [])
         ∷ []

-- The operation it denotes.
_·_ : Fin 4 → Fin 4 → Fin 4
_·_ = ⟦ v4-table ⟧

-- Every element is its own inverse, so the inverse map is the identity.
v4-inv : Fin 4 → Fin 4
v4-inv x = x
```

#### The group `V₄`

```agda
v4-group : Group
v4-group = eqsToGroup (Fin 4) _·_ 0F v4-inv
  (from-yes (Associative?   _·_)) (from-yes (LeftIdentity?  _·_ 0F))
  (from-yes (RightIdentity? _·_ 0F)) (from-yes (LeftInverse?   _·_ 0F v4-inv))
  (from-yes (RightInverse?  _·_ 0F v4-inv))

open Polymorphic.Group-Op v4-group using ( _∙_ ; ε ; _⁻¹ )
```

#### `V₄` is abelian and has exponent 2

```agda
·-comm : ∀ a b → a · b ≡ b · a
·-comm = from-yes (Commutative? _·_)
```

#### Acceptance checks

The `Group-Op`{.AgdaModule} accessors interpret to the tabulated operation, to
`0F`{.AgdaInductiveConstructor}, and to the identity inverse map on the nose; discharged
by `refl`{.AgdaInductiveConstructor}.  In particular every element is its own inverse.

```agda
∙-is-· : ∀ (a b : Fin 4) → a ∙ b ≡ a · b
∙-is-· a b = refl

ε-is-0 : ε ≡ 0F
ε-is-0 = refl

⁻¹-is-self : ∀ (a : Fin 4) → a ⁻¹ ≡ a
⁻¹-is-self a = refl
```

The bundle bridge round-trips on `v4-group`{.AgdaFunction} pointwise on the operation,
the identity, and the inverse.

```agda
open Polymorphic.Group-Op ⟪ ⟨ v4-group ⟩ᵍᵖ ⟫ᵍᵖ using ()
  renaming ( _∙_ to _·′_ ; ε to ε′ ; _⁻¹ to _⁻¹′ )

roundtrip-∙ : ∀ (a b : Fin 4) → a ·′ b ≡ a · b
roundtrip-∙ a b = refl

roundtrip-ε : ε′ ≡ 0F
roundtrip-ε = refl

roundtrip-⁻¹ : ∀ (a : Fin 4) → a ⁻¹′ ≡ a
roundtrip-⁻¹ a = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical](Examples.Classical.html)</span>

{% include UALib.Links.md %}
