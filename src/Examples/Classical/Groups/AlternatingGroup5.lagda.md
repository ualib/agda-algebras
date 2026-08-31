---
layout: default
file: "src/Examples/Classical/Groups/AlternatingGroup5.lagda.md"
title: "Examples.Classical.Groups.AlternatingGroup5 module"
date: "2026-08-30"
author: "the agda-algebras development team"
---

### Worked example: the alternating group `A₅`, certified simple

This is the [Examples.Classical.Groups.AlternatingGroup5][] module of the [Agda Universal Algebra Library][].

The alternating group `A₅` on five points is the smallest nonabelian simple
group.  This module constructs it concretely, on the carrier `Fin 60` with
propositional equality, and certifies its simplicity by finite computation:
the result is an inhabitant of `IsSimple`{.AgdaFunction} of
[Classical.Structures.Group.Simple][], the nonabelian-simple bundle
`IsNonabelianSimple`{.AgdaRecord}, and the discharged
`NontrivialCenterless`{.AgdaRecord} of [FLRP.WreathNoGo][], which is what
makes `A₅` an admissible base group for the Kurzweil entries of
[FLRP.Assumptions][].

The raw data lives in the generated companion
[Examples.Classical.Groups.AlternatingGroup5.Tables][]: the 60 by 60 Cayley
table on the lexicographic even-permutation encoding (index 0 is the
identity), the inverse vector, the action of each element on the five points,
and the simplicity certificate.  Nothing rests on the generator's authority:
every claim in the data is replayed here by decision procedures over the
finite carrier, exactly as in the certificate discipline of
[FLRP.Certificates][].

#### Presentation choice, with measurements

Two presentations were candidates, and the cost decided between them.

+  **A Cayley table with all laws decided**, as in
   [Examples.Classical.Groups.SymmetricGroup3][].  At `Fin 60` the
   associativity decision ranges over `60³ = 216000` triples of table
   lookups; measured on this module's table, `from-yes (Associative? _·_)`
   type-checks in 72 seconds at a peak of 13.8 GB of memory, which is
   hostile to both contributors and CI.
+  **A permutation presentation** over `setoidEqsToGroup`{.AgdaFunction},
   with near-definitional laws.  Rejected for a different reason: the carrier
   would be a setoid of functions, so the certificate replay below would have
   to transport memberships along pointwise equality through
   `respects`{.AgdaField} at every step, and the group would not plug into
   the `Fin`-indexed finite machinery as it stands.

The module takes a third route that keeps the table carrier and avoids the
cubic decision: `A₅` acts faithfully on its five points, the action tables
are data, and `assoc-from-action`{.AgdaFunction} of [Overture.Cayley][]
derives associativity from two quadratic decisions
(`ActionHom?`{.AgdaFunction} and `ActionFaithful?`{.AgdaFunction} of
[Overture.Operations.Properties][]).  Measured, the whole module type-checks
in under ten seconds at under a gigabyte, so it stays inside the plain
`make check` tier.

#### The simplicity certificate

Simplicity in implication form says: every normal subgroup `N` containing a
non-identity element `x` is everything.  The certificate witnesses this in
two stages, in the closure-term language of
[Classical.Structures.Group.NormalClosure][], and the two stages are decided
by `from-yes`{.AgdaFunction} below.

1.  For each of the 59 non-identity elements `x`, the two generators
    `s = (0 1 2 3 4)` and `t = (0 1 2)` are expressed as products of
    conjugates of `x` and of its inverse (`a5-seed-words-s`{.AgdaFunction},
    `a5-seed-words-t`{.AgdaFunction}); soundness of the term language puts
    both generators in `N`.
2.  Every element is expressed as a word in `s` and `t`
    (`a5-gen-words`{.AgdaFunction}), so `N` contains everything.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups.AlternatingGroup5 where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin.Base                          using ( Fin ; suc )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Fin.Properties                    using ( _≟_ ; all? )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Data.Vec.Base                          using ( lookup )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; subst )
open import Relation.Nullary.Negation.Core         using ( contradiction )
open import Relation.Unary                         using ( _∈_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                   using  ( ⟦_⟧ ; from-yes
                                                     ; assoc-from-action )
open import Overture.Operations.Properties    using  ( ActionHom? ; ActionFaithful?
                                                     ; LeftIdentity? ; RightIdentity?
                                                     ; LeftInverse? ; RightInverse? )
open import Classical.Small.Structures.Group  using  ( Group ; eqsToGroup )
open import Examples.Classical.Groups.AlternatingGroup5.Tables
                                              using  ( a5-mul-table ; a5-inv-vec
                                                     ; a5-act-table
                                                     ; a5-gen-s ; a5-gen-t
                                                     ; a5-gen-words
                                                     ; a5-seed-words-s
                                                     ; a5-seed-words-t )
open import FLRP.WreathNoGo                   using  ( NontrivialCenterless
                                                     ; nonabelianSimple→nontrivialCenterless )
open import Setoid.Algebras.Finite            using  ( FiniteAlgebra )
import Classical.Structures.Group as Polymorphic
```
-->

#### The group `A₅`

The tables denote the operation, the inverse, and the point action.

```agda
-- The multiplication read off the Cayley table.
_·_ : Fin 60 → Fin 60 → Fin 60
_·_ = ⟦ a5-mul-table ⟧

-- The inverse map.
a5-inv : Fin 60 → Fin 60
a5-inv a = lookup a5-inv-vec a

-- The action on the five points.
a5-act : Fin 60 → Fin 5 → Fin 5
a5-act a q = lookup (lookup a5-act-table a) q
```

Associativity comes from the faithful action, per the presentation note; the
remaining four laws are linear decisions over the carrier.

```agda
-- Associativity, through the faithful point action.
·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
·-assoc = assoc-from-action _·_ a5-act
            (from-yes (ActionHom? _·_ a5-act))
            (from-yes (ActionFaithful? a5-act))

-- The group: the identity is the identity permutation, at index 0.
a5-group : Group
a5-group = eqsToGroup (Fin 60) _·_ 0F a5-inv
  ·-assoc
  (from-yes (LeftIdentity?   _·_ 0F))
  (from-yes (RightIdentity?  _·_ 0F))
  (from-yes (LeftInverse?    _·_ 0F a5-inv))
  (from-yes (RightInverse?   _·_ 0F a5-inv))
```

The simplicity vocabulary, the normal-subgroup projections, and the
closure-term evaluator, all instantiated at `A₅`.

```agda
module S   = Polymorphic.Simple         a5-group 0ℓ
module MN  = Polymorphic.MinimalNormal  a5-group 0ℓ
module NW  = Polymorphic.NormalClosure  a5-group
```

#### Replaying the certificate

The three decided checks: the shared word table hits every element, and at
each non-identity element the two seed words evaluate to the generators.

```agda
-- The seed assignment of the shared word table: seed 0 is s, seed 1 is t.
genσ : Fin 2 → Fin 60
genσ 0F = a5-gen-s
genσ 1F = a5-gen-t

-- Decided: the word table expresses every element in the generators.
gen-words-ok : ∀ y → NW.⟦ lookup a5-gen-words y ⟧ genσ ≡ y
gen-words-ok = from-yes (all? (λ y → NW.⟦ lookup a5-gen-words y ⟧ genσ ≟ y))

-- Decided: at the i-th non-identity element, the s-word evaluates to s ...
seed-words-s-ok : ∀ i → NW.⟦ lookup a5-seed-words-s i ⟧ (λ _ → suc i) ≡ a5-gen-s
seed-words-s-ok =
  from-yes (all? (λ i → NW.⟦ lookup a5-seed-words-s i ⟧ (λ _ → suc i) ≟ a5-gen-s))

-- ... and the t-word to t.
seed-words-t-ok : ∀ i → NW.⟦ lookup a5-seed-words-t i ⟧ (λ _ → suc i) ≡ a5-gen-t
seed-words-t-ok =
  from-yes (all? (λ i → NW.⟦ lookup a5-seed-words-t i ⟧ (λ _ → suc i) ≟ a5-gen-t))
```

Simplicity, by replay.  A non-identity element of `Fin 60` is `suc i` for a
unique `i : Fin 59`, so the two certificate stages compose: soundness of the
closure terms puts the generators in `N`, then every element.

```agda
-- A₅ is simple: every normal subgroup containing a non-identity element
-- is everything.
a5-isSimple : S.IsSimple
a5-isSimple N N-nsg 0F       x∈N x≉ε y = contradiction refl x≉ε
a5-isSimple N N-nsg (suc i)  x∈N x≉ε y =
  subst (_∈ N) (gen-words-ok y)
        (NW.closure-sound sg nrm σ∈ (lookup a5-gen-words y))
  where
  sg   = MN.isSubgroup N-nsg
  nrm  = MN.isNormal N-nsg

  -- Stage 1: the generators lie in N, by the seed words at x = suc i.
  s∈N : a5-gen-s ∈ N
  s∈N = subst (_∈ N) (seed-words-s-ok i)
              (NW.closure-sound sg nrm (λ _ → x∈N) (lookup a5-seed-words-s i))

  t∈N : a5-gen-t ∈ N
  t∈N = subst (_∈ N) (seed-words-t-ok i)
              (NW.closure-sound sg nrm (λ _ → x∈N) (lookup a5-seed-words-t i))

  -- Stage 2 seeds: the word-table assignment lands in N.
  σ∈ : ∀ j → genσ j ∈ N
  σ∈ 0F = s∈N
  σ∈ 1F = t∈N
```

#### The nonabelian-simple bundle and its consequences

The generators do not commute, which makes the pair the nonabelianness
witness; the bundle then yields the positive triviality of the center, since
`Fin 60` has decidable equality.

```agda
-- s and t do not commute: s · t and t · s are distinct table entries.
a5-noncommuting : S.NoncommutingPair
a5-noncommuting = a5-gen-s , a5-gen-t , λ ()

-- A₅ is nonabelian simple.
a5-isNonabelianSimple : S.IsNonabelianSimple
a5-isNonabelianSimple = record
  { simple        = a5-isSimple
  ; noncommuting  = a5-noncommuting }

-- Identity equations are stable: the carrier equality is decidable.
a5-Stable-≈ε : S.Stable-≈ε
a5-Stable-≈ε = S.≈-dec→Stable-≈ε _≟_

-- The center of A₅ is trivial, positively.
a5-center-trivial : ∀ d → d ∈ S.center → d ≡ 0F
a5-center-trivial = S.center-trivial a5-Stable-≈ε a5-isNonabelianSimple
```

The FLRP-facing consequence: `A₅` discharges the `NontrivialCenterless`
record of [FLRP.WreathNoGo][], so it is an admissible base group for the
Kurzweil entries of [FLRP.Assumptions][] with the nonabelian-simple side
condition witnessed rather than assumed.

```agda
-- A₅ is nontrivial and centerless, as FLRP.WreathNoGo consumes it.
a5-nontrivialCenterless : NontrivialCenterless a5-group
a5-nontrivialCenterless =
  nonabelianSimple→nontrivialCenterless a5-group a5-Stable-≈ε a5-isNonabelianSimple
```

#### Finiteness

The carrier is its own enumeration, so the `FiniteAlgebra`{.AgdaRecord}
witness is immediate; downstream instantiations consume it wherever a finite
base group is an antecedent.

```agda
-- A₅ is a finite algebra: Fin 60 enumerates itself.
a5-finite : FiniteAlgebra (proj₁ a5-group)
a5-finite = record
  { _≟_       = _≟_
  ; card      = 60
  ; enum      = λ i → i
  ; enum-sur  = λ x → x , refl }
```

#### Acceptance checks

The `Group-Op`{.AgdaModule} accessors interpret to the tabulated operation,
to `0F`{.AgdaInductiveConstructor}, and to the inverse vector on the nose;
discharged by `refl`{.AgdaInductiveConstructor}.

```agda
open Polymorphic.Group-Op a5-group using ( _∙_ ; ε ; _⁻¹ )

∙-is-· : ∀ (a b : Fin 60) → a ∙ b ≡ a · b
∙-is-· a b = refl

ε-is-0 : ε ≡ 0F
ε-is-0 = refl

⁻¹-is-inv : ∀ (a : Fin 60) → a ⁻¹ ≡ a5-inv a
⁻¹-is-inv a = refl
```
