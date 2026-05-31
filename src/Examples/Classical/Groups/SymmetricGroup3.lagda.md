---
layout: default
file: "src/Examples/Classical/Groups/SymmetricGroup3.lagda.md"
title: "Examples.Classical.Groups.SymmetricGroup3 module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked Example: the symmetric group `S₃` from a Cayley table

This is the [Examples.Classical.Groups.SymmetricGroup3][] module of the [Agda Universal Algebra Library][].

The symmetric group `S₃` on three letters — equivalently the dihedral group `D₃` of
symmetries of an equilateral triangle — is the smallest *non-abelian* group.  The
canonical `Group`{.AgdaRecord} example in [`Examples.Classical.Groups.Group`][] is the
integers under addition, which is abelian; this module supplies a genuinely
non-commutative companion.

We present `S₃` through the dihedral generators: a rotation `r` with `r³ = e` and a
reflection `s` with `s² = e` and `s r = r² s`.  Every element is uniquely `rⁱ sʲ`
with `i ∈ {0,1,2}`, `j ∈ {0,1}`, and we encode it as the index `i + 3j` in `Fin 6` as
follows:

| index | 0 | 1 | 2 | 3 | 4 | 5 |
|-------|---|---|---|---|---|---|
| element | `e` | `r` | `r²` | `s` | `rs` | `r²s` |

The full multiplication table (entry `a , b` is the product `a · b`):

| · | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| 0 | 0 | 1 | 2 | 3 | 4 | 5 |
| 1 | 1 | 2 | 0 | 4 | 5 | 3 |
| 2 | 2 | 0 | 1 | 5 | 3 | 4 |
| 3 | 3 | 5 | 4 | 0 | 2 | 1 |
| 4 | 4 | 3 | 5 | 1 | 0 | 2 |
| 5 | 5 | 4 | 3 | 2 | 1 | 0 |

As before, the group axioms are decidable over the finite carrier and are discharged
by `from-yes`{.AgdaFunction}.  Associativity here is a decision over all `6³ = 216`
triples — exactly the case where a hand-written proof would be unreasonable and the
`Overture.Cayley`{.AgdaModule} approach pays off.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups.SymmetricGroup3 where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin                               using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Product                           using ( ∃-syntax ; _,_ )
open import Data.Vec.Base                          using ( _∷_ ; [] )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl )
open import Relation.Nullary.Negation.Core         using ( ¬_ ; contradiction )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                   using  ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties    using  ( Associative? ; Commutative?
                                                     ; LeftIdentity? ; RightIdentity?
                                                     ; LeftInverse? ; RightInverse? )
open import Classical.Bundles.Group           using ( ⟨_⟩ᵍᵖ ; ⟪_⟫ᵍᵖ )
open import Classical.Small.Structures.Group  using ( Group ; eqsToGroup )
import Classical.Structures.Group as Polymorphic
```

#### The Cayley table, the operation, and the inverse map

```agda
-- The S₃ ≅ D₃ multiplication table on the encoding e,r,r²,s,rs,r²s = 0..5.
s3-table : Table 6
s3-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
         ∷ (1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F ∷ [])
         ∷ (2F ∷ 0F ∷ 1F ∷ 5F ∷ 3F ∷ 4F ∷ [])
         ∷ (3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ [])
         ∷ (4F ∷ 3F ∷ 5F ∷ 1F ∷ 0F ∷ 2F ∷ [])
         ∷ (5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ [])
         ∷ []

-- The operation it denotes.
_·_ : Fin 6 → Fin 6 → Fin 6
_·_ = ⟦ s3-table ⟧

-- The inverse map.  The rotations r, r² invert each other; e and the three
-- reflections s, rs, r²s are each their own inverse.
s3-inv : Fin 6 → Fin 6
s3-inv 0F = 0F
s3-inv 1F = 2F
s3-inv 2F = 1F
s3-inv 3F = 3F
s3-inv 4F = 4F
s3-inv 5F = 5F
```

#### The group `S₃`

```agda
s3-group : Group
s3-group = eqsToGroup (Fin 6) _·_ 0F s3-inv
  (from-yes (Associative?   _·_)) (from-yes (LeftIdentity?  _·_ 0F))
  (from-yes (RightIdentity? _·_ 0F)) (from-yes (LeftInverse?   _·_ 0F s3-inv))
  (from-yes (RightInverse?  _·_ 0F s3-inv))

open Polymorphic.Group-Op s3-group using ( _∙_ ; ε ; _⁻¹ )
```

#### `S₃` is not abelian

The product `r · s = rs` (index `1 · 3 = 4`) differs from `s · r = r²s`
(index `3 · 1 = 5`), so the rotation and the reflection do not commute.
The witnessing inequality is the absurd pattern `λ ()`, since `4 ≡ 5` is uninhabited.

```agda
s3-noncomm : ∃[ a ] ∃[ b ] a · b ≢ b · a
s3-noncomm = 1F , 3F , λ ()
```

In negated-universal form — `S₃` admits no proof of commutativity — this follows by
feeding the witnessing pair to the assumed commutativity and deriving a contradiction.

```agda
s3-not-abelian : ¬ (∀ a b → a · b ≡ b · a)
s3-not-abelian comm = contradiction (comm 1F 3F) λ ()
```

#### Acceptance checks

The `Group-Op`{.AgdaModule} accessors interpret to the tabulated operation, to
`0F`{.AgdaInductiveConstructor}, and to `s3-inv`{.AgdaFunction} on the nose; discharged
by `refl`{.AgdaInductiveConstructor}.

```agda
∙-is-· : ∀ (a b : Fin 6) → a ∙ b ≡ a · b
∙-is-· a b = refl

ε-is-0 : ε ≡ 0F
ε-is-0 = refl

⁻¹-is-inv : ∀ (a : Fin 6) → a ⁻¹ ≡ s3-inv a
⁻¹-is-inv a = refl
```

The bundle bridge round-trips on `s3-group`{.AgdaFunction} pointwise on the operation,
the identity, and the inverse.

```agda
open Polymorphic.Group-Op ⟪ ⟨ s3-group ⟩ᵍᵖ ⟫ᵍᵖ using ()
  renaming ( _∙_ to _·′_ ; ε to ε′ ; _⁻¹ to _⁻¹′ )

roundtrip-∙ : ∀ (a b : Fin 6) → a ·′ b ≡ a · b
roundtrip-∙ a b = refl

roundtrip-ε : ε′ ≡ 0F
roundtrip-ε = refl

roundtrip-⁻¹ : ∀ (a : Fin 6) → a ⁻¹′ ≡ s3-inv a
roundtrip-⁻¹ a = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical](Examples.Classical.html)</span>

{% include UALib.Links.md %}
