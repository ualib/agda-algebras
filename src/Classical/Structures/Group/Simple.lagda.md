---
layout: default
file: "src/Classical/Structures/Group/Simple.lagda.md"
title: "Classical.Structures.Group.Simple module"
date: "2026-08-30"
author: "the agda-algebras development team"
---

### Simple groups

This is the [Classical.Structures.Group.Simple][] module of the [Agda Universal Algebra Library][].

A group is **simple** when its only normal subgroups are the trivial subgroup and
the whole group.  This module states the notion in the form the library's proofs
consume and develops its first consequences:

+  `IsSimple`{.AgdaFunction}, the implication form: every normal subgroup
   containing a non-identity element is everything;
+  `NoncommutingPair`{.AgdaFunction} and the bundle
   `IsNonabelianSimple`{.AgdaRecord}, which adds a non-commuting pair to
   simplicity and derives the nontriviality witness from it;
+  the center as a normal subgroup (`center`{.AgdaFunction},
   `center-isNormalSubgroup`{.AgdaFunction}) and the triviality of the center of
   a nonabelian simple group (`center-¬¬trivial`{.AgdaFunction},
   `center-trivial`{.AgdaFunction});
+  core-freeness of every proper subgroup
   (`simple→core-¬¬trivial`{.AgdaFunction}, `simple→coreFree`{.AgdaFunction}).

#### Design note: the implication form, and where its limits bite

The textbook definition classifies every normal subgroup as trivial *or*
everything.  Stated over arbitrary equality-respecting predicates, that
disjunction is oracle-strength data, for exactly the reason recorded in
[Classical.Structures.Group.MaximalSubgroup][]: a membership predicate can encode
an arbitrary proposition, so the classifier would decide it up to double
negation, and no concrete group could inhabit the record in safe Agda.  The
implication form avoids the disjunction.  Given a normal subgroup together with a
member and a proof that the member is not the identity, it concludes that the
subgroup is everything.  The known consumers apply simplicity exactly this way,
by producing the non-identity member as data (the normal-subgroup structure
theory of powers of a simple group produces it from a commutator; the center
argument below produces it from the hypothesis under refutation), and a concrete
finite group can inhabit the implication form by finite computation, which the
disjunctive form forbids outright.

The implication form has a recorded limit: conclusions that are themselves
identity equations arrive only doubly negated.  To show a central element `d` is
the identity, one applies simplicity to the center at witness `d`; but the
hypothesis `¬ d ≈ ε` is exactly what a proof of `d ≈ ε` is trying to refute, so
the argument yields `¬ ¬ (d ≈ ε)` and stops.  The same bite appears in the
companion statement that every proper subgroup of a simple group is core-free:
the hypothesis wants a non-identity element of the core as data, and properness
supplies no such element.  The decision, recorded here rather than improvised per
consumer, is as follows: each of the two statements appears twice, once in
double-negation form with no side condition (`center-¬¬trivial`{.AgdaFunction},
`simple→core-¬¬trivial`{.AgdaFunction}), and once in positive form under
*stability of identity equations* (`Stable-≈ε`{.AgdaFunction}), the hypothesis
that `¬ ¬ (x ≈ ε)` implies `x ≈ ε`.  Stability follows from decidable equality
(`≈-dec→Stable-≈ε`{.AgdaFunction}), in the style of ADR-008's Layer D, so every
concrete finite instance discharges the antecedent outright; no separate
decidable-membership sibling of `IsSimple`{.AgdaFunction} is defined, because the
one classical ingredient is isolated in the stability antecedent and the
quantification over subgroup predicates can stay as it is.

#### A note on levels

Throughout, `𝒢`{.AgdaBound} is a group and `ℓ₀`{.AgdaBound} a base level.
Unlike [Classical.Structures.Group.MinimalNormal][], which instantiates its
subgroup lattice at `ℓ₀` itself, this module instantiates the normal-subgroup
vocabulary at the base level `ρ ⊔ ℓ₀`, so subgroup predicates live at
`L = α ⊔ ρ ⊔ ℓ₀`.  The subgroups this module feeds to `IsSimple`{.AgdaFunction}
are defined by equations (the center is a centralizer, the normal core is a meet
of conjugates), and equations live at level `ρ`; with `ρ` absorbed into `L`
those subgroups land at exactly the quantified level, with no lifting.  At the
level setting the FLRP program fixes (`α = ρ = ℓ₀ = 0ℓ`) this `L` is `0ℓ`,
exactly as in the sibling modules.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Simple where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using  ( Σ-syntax ; proj₁ ; proj₂ )
open import Data.Unit.Base   using  ( tt )
open import Level            using  ( Level ; _⊔_ ; lift ) renaming ( suc to lsuc )
open import Relation.Binary  using  ( Setoid )
open import Relation.Nullary using  ( ¬_ ; Dec ; Stable ; decidable-stable )
open import Relation.Unary   using  ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic            using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Centralizer      using  ( module Centralizer )
open import Classical.Structures.Group.MinimalNormal    using  ( module MinimalNormal )
open import Classical.Structures.Group.NormalCore       using  ( module Core )
open import Classical.Structures.Group.Subgroups        using  ( IsSubgroup ; fullSubgroup )
open import Classical.Structures.Group.SubgroupLattice  using  ( module GroupSublattice )
open import Setoid.Algebras.Basic                       using  ( 𝕌[_] ; 𝔻[_] )
```
-->

#### Simplicity, in implication form

```agda
module Simple {α ρ : Level} (𝒢 : Group α ρ) (ℓ₀ : Level) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using  ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢     using  ( _∙_ ; ε ; ∙-cong ; idˡ-law ; idʳ-law )
  open Centralizer 𝒢  using  ( C[_] ; C-isSubgroup ; C-isNormal )
  open GroupSublattice 𝒢 (ρ ⊔ ℓ₀)  using  ( L )
  open MinimalNormal 𝒢 (ρ ⊔ ℓ₀)    using  ( IsNormalSubgroup ; isSubgroup
                                          ; isNormal ; Triv )
```

The definition: whenever a normal subgroup contains an element that is not the
identity, it contains every element.  The trivial group inhabits this form
vacuously; the nonabelian-simple bundle below is what excludes it.

```agda
  -- Simplicity, implication form: every normal subgroup containing a
  -- non-identity element is everything.
  IsSimple : Type (α ⊔ ρ ⊔ lsuc L)
  IsSimple =  (N : Pred G L) → IsNormalSubgroup N
           →  ∀ x → x ∈ N → ¬ x ≈ ε
           →  ∀ y → y ∈ N
```

#### The nonabelian-simple bundle

Nonabelianness enters as positive data: a pair of elements that do not commute.
Either element of such a pair is automatically a non-identity element, so the
bundle need not carry a separate nontriviality witness; the two small lemmas
record the derivation once.

```agda
  -- A non-commuting pair, as positive data.
  NoncommutingPair : Type (α ⊔ ρ)
  NoncommutingPair = Σ[ a ∈ G ] Σ[ b ∈ G ] ¬ (a ∙ b ≈ b ∙ a)

  -- The left element of a non-commuting pair is not the identity ...
  noncommˡ-≉ε : {a b : G} → ¬ (a ∙ b ≈ b ∙ a) → ¬ a ≈ ε
  noncommˡ-≉ε {a} {b} nc a≈ε = nc (begin
    a ∙ b  ≈⟨ ∙-cong a≈ε ≈refl ⟩
    ε ∙ b  ≈⟨ idˡ-law b ⟩
    b      ≈⟨ ≈sym (idʳ-law b) ⟩
    b ∙ ε  ≈⟨ ∙-cong ≈refl (≈sym a≈ε) ⟩
    b ∙ a  ∎)

  -- ... and neither is the right element.
  noncommʳ-≉ε : {a b : G} → ¬ (a ∙ b ≈ b ∙ a) → ¬ b ≈ ε
  noncommʳ-≉ε {a} {b} nc b≈ε = nc (begin
    a ∙ b  ≈⟨ ∙-cong ≈refl b≈ε ⟩
    a ∙ ε  ≈⟨ idʳ-law a ⟩
    a      ≈⟨ ≈sym (idˡ-law a) ⟩
    ε ∙ a  ≈⟨ ∙-cong (≈sym b≈ε) ≈refl ⟩
    b ∙ a  ∎)
```

The bundle: a simple group together with a non-commuting pair.  The
nontriviality witness `elt`{.AgdaFunction} with `elt≉ε`{.AgdaFunction} is a
derived member rather than a field, so that instances carry no redundant data.

```agda
  record IsNonabelianSimple : Type (α ⊔ ρ ⊔ lsuc L) where
    field
      simple        : IsSimple
      noncommuting  : NoncommutingPair

    -- The nontriviality witness: the left element of the non-commuting pair.
    elt : G
    elt = proj₁ noncommuting

    elt≉ε : ¬ elt ≈ ε
    elt≉ε = noncommˡ-≉ε (proj₂ (proj₂ noncommuting))

  open IsNonabelianSimple public
```

#### The center is trivial

The center is the centralizer of the full subgroup, so its subgroup and
normality proofs come from [Classical.Structures.Group.Centralizer][] for free.

```agda
  -- The full subgroup, as a predicate.
  Full : Pred G (ρ ⊔ ℓ₀)
  Full = proj₁ (fullSubgroup 𝒢 (ρ ⊔ ℓ₀))

  -- The center: the centralizer of the full subgroup.
  center : Pred G L
  center = C[ Full ]

  -- The center is a normal subgroup.
  center-isNormalSubgroup : IsNormalSubgroup center
  center-isNormalSubgroup .isSubgroup = C-isSubgroup Full
  center-isNormalSubgroup .isNormal   = C-isNormal (λ g _ → lift tt)
```

A central element other than the identity makes the group abelian: the center is
a normal subgroup, so simplicity applied at the central witness makes the group
its own center.

```agda
  -- A non-identity central element makes the group abelian.
  central-≉ε→comm : IsSimple → ∀ d → d ∈ center → ¬ d ≈ ε → ∀ a b → a ∙ b ≈ b ∙ a
  central-≉ε→comm sim d d∈Z d≉ε a b =
    sim center center-isNormalSubgroup d d∈Z d≉ε a b (lift tt)
```

In a nonabelian simple group the non-commuting pair refutes the derived
commutativity, so a central element is not *not* the identity.  This is the
double-negation form the design note announces; it has no side condition.

```agda
  -- Layer S: a central element of a nonabelian simple group is ¬¬ the identity.
  center-¬¬trivial : IsNonabelianSimple → ∀ d → d ∈ center → ¬ ¬ (d ≈ ε)
  center-¬¬trivial nas d d∈Z d≉ε =
    nc (central-≉ε→comm (nas .simple) d d∈Z d≉ε a b)
    where
    a  = proj₁ (nas .noncommuting)
    b  = proj₁ (proj₂ (nas .noncommuting))
    nc = proj₂ (proj₂ (nas .noncommuting))
```

Eliminating the double negation is the one classical step, and it is exactly
stability of identity equations, which decidable equality supplies.

```agda
  -- Stability of identity equations: ¬ ¬ (x ≈ ε) can be eliminated.
  Stable-≈ε : Type (α ⊔ ρ)
  Stable-≈ε = ∀ x → Stable (x ≈ ε)

  -- Decidable equality gives stability, so every concrete finite instance
  -- discharges the antecedent outright.
  ≈-dec→Stable-≈ε : (∀ x y → Dec (x ≈ y)) → Stable-≈ε
  ≈-dec→Stable-≈ε dec x = decidable-stable (dec x ε)

  -- Layer D: with stable identity equations, the center of a nonabelian
  -- simple group is trivial.
  center-trivial : Stable-≈ε → IsNonabelianSimple → ∀ d → d ∈ center → d ≈ ε
  center-trivial st nas d d∈Z = st d (center-¬¬trivial nas d d∈Z)
```

#### Every proper subgroup is core-free

The normal core of a subgroup `H` is a normal subgroup inside `H`
([Classical.Structures.Group.NormalCore][]), so a non-identity element of the
core would make `H` everything.  For a proper `H` there is no such element,
with the same constructive caveat as for the center: the conclusion `x ≈ ε` is
doubly negated at Layer S and positive under stability.

```agda
  -- H is a proper subgroup: not every element lies in it.  (Stated negatively,
  -- as in the sibling modules: no argument below needs a witness.)
  Proper : Pred G L → Type (α ⊔ L)
  Proper H = ¬ (∀ x → x ∈ H)

  module _ (H : Pred G L) (H-sg : IsSubgroup 𝒢 H) where
    private module CoreH = Core 𝒢 H H-sg

    -- Layer S: in a simple group, an element of the core of a proper
    -- subgroup is ¬¬ the identity.
    simple→core-¬¬trivial : IsSimple → Proper H
      →  ∀ x → x ∈ proj₁ CoreH.core → ¬ ¬ (x ≈ ε)
    simple→core-¬¬trivial sim proper x x∈core x≉ε =
      proper (λ y → CoreH.core-⊆ (sim (proj₁ CoreH.core) core-nsg x x∈core x≉ε y))
      where
      core-nsg : IsNormalSubgroup (proj₁ CoreH.core)
      core-nsg = record  { isSubgroup  = CoreH.core-isSubgroup
                         ; isNormal    = CoreH.core-normal }

    -- Layer D: every proper subgroup of a simple group is core-free.
    simple→coreFree : Stable-≈ε → IsSimple → Proper H → proj₁ CoreH.core ⊆ Triv
    simple→coreFree st sim proper {x} x∈core =
      st x (simple→core-¬¬trivial sim proper x x∈core)
```
