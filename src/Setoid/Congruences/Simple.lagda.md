---
layout: default
file: "src/Setoid/Congruences/Simple.lagda.md"
title: "Setoid.Congruences.Simple module (The Agda Universal Algebra Library)"
date: "2026-08-31"
author: "the agda-algebras development team"
---

### Simple algebras

This is the [Setoid.Congruences.Simple][] module of the [Agda Universal Algebra Library][].

Classically, a *nontrivial* algebra is **simple** when its congruence lattice has
exactly two members: the diagonal, which relates only the setoid-equal pairs, and
the total congruence, which relates everything.  This module defines *simple*
as an implication, and keeps nontriviality out of the definition.[^1]

The module develops the following:

+  `RelatesDistinctPoints`{.AgdaFunction}: the positive data of a binary relation
   (in use, the relation of a congruence) relating a pair of provably distinct
   elements;
+  `IsSimple`{.AgdaFunction}, the implication definition of "simple algebra": a
   congruence relating a distinct pair relates every pair;
+  `trivial⇒simple`{.AgdaFunction}: the trivial algebra is simple vacuously;
+  `simple⇒total`{.AgdaFunction}: in a simple algebra, a congruence relating a
   distinct pair is the total congruence;
+  `nontrivial⇒𝟙-nonzero`{.AgdaFunction} and `simple⇒si`{.AgdaFunction}: a
   nontrivial simple algebra is subdirectly irreducible with the total congruence
   as its monolith, under a witness-extraction antecedent that the design note
   below explains.

The group-theoretic special case is `IsSimple`{.AgdaFunction} of
[Classical.Structures.Group.Simple][]; the identification of the two notions
through the normal-subgroup ↔ congruence correspondence is proved in
[Classical.Structures.Group.Congruences][].

#### Design note: the implication form

The textbook definition of a simple algebra classifies every congruence as
either the diagonal or the total congruence.  Stated over arbitrary congruences,
that disjunction is oracle-strength data, for exactly the reason recorded in
[Classical.Structures.Group.Simple][] and
[Classical.Structures.Group.MaximalSubgroup][]: relatedness under a congruence can
encode an arbitrary proposition, which the classifier would decide up to double
negation, and no concrete algebra with two provably distinct elements could
inhabit the disjunctive form in `--safe` Agda.  The definition here is therefore
an implication: if a congruence relates a pair of provably distinct elements,
then it relates every pair.

Two further choices mirror the group module.

+  **The witnessed pair is positive data**.  The hypothesis is the type
   `RelatesDistinctPoints`{.AgdaFunction}, an inhabitant of which is a pair
   packaged with its relatedness and distinctness proofs; this is deliberately not
   of the same shape as `Nonzero`{.AgdaFunction} in [Setoid.Congruences.Monolith][];
   the latter is a negation and carries no witness.  Consumers apply simplicity by
   producing the pair along with its relatedness and distinctness proofs.  The
   group-side equivalence of [Classical.Structures.Group.Congruences][] produces
   it from a non-identity member of a normal subgroup.
+  **Nontriviality stays out of the definition**.  The trivial algebra inhabits
   the implication form vacuously (`trivial⇒simple`{.AgdaFunction}); nontriviality
   witnesses live in bundles, exactly as `IsNonabelianSimple`{.AgdaRecord} handles
   the group side.

The implication form does not recover the disjunctive classification (a congruence
is either the diagonal or relates all pairs); deciding which disjunct
holds would decide, for an arbitrary congruence, whether it relates a distinct
pair.  The fact that the disjunctive readings (both here and on the group side)
are unreachable from the form that concrete instances inhabit is strong evidence
that the implication form is the right primitive.

??? note "A note on universe levels"

    `IsSimple`{.AgdaFunction} takes the congruence level `ℓ` as a parameter and
    quantifies over `Con`{.AgdaFunction}` 𝑨 ℓ` at that level, the same per-level
    discipline as the correspondence of [Classical.Structures.Group.Congruences][].
    The subdirect-irreducibility facts in this module instantiate it at the
    algebra's own relation level `ρ`, where the monolith vocabulary of
    [Setoid.Congruences.Monolith][] lives; the group-side equivalence instantiates
    it at the level `α ⊔ ρ ⊔ ℓ₀` of the group's subgroup predicates.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Congruences.Simple where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Empty        using ( ⊥-elim )
open import Data.Product      using ( _×_ ; _,_ ; ∃-syntax ; proj₁ )
open import Data.Unit.Base    using ( tt )
open import Level             using ( Level ; _⊔_ ; lift )
open import Relation.Binary   using ( Setoid ) renaming ( Rel to BinaryRel )
open import Relation.Nullary  using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                     using  ( 𝑆 )
open import Setoid.Algebras.Basic        using  ( ov ; Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic     using  ( Con ; 𝟙[_] )
open import Setoid.Congruences.Lattice   using  ( _≑_ )
open import Setoid.Congruences.Monolith  using  ( Nontrivial ; Trivial ; Nonzero
                                                ; IsMonolith
                                                ; IsSubdirectlyIrreducible )

private variable α ρ ℓ : Level
```
-->

#### Definition: simple algebra

Fix an algebra `𝑨`.  The hypothesis a consumer supplies is a related pair together
with a proof that the setoid equality distinguishes the two elements of the pair.
It is stated for an arbitrary binary relation on the carrier, since only the
relation of a congruence is ever inspected; everything below applies it to that
relation.

```agda
module _ (𝑨 : Algebra {𝑆 = 𝑆} α ρ) where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )

  -- The positive data: θ relates a pair of provably distinct elements.
  RelatesDistinctPoints : BinaryRel 𝕌[ 𝑨 ] ℓ → Type (α ⊔ ρ ⊔ ℓ)
  RelatesDistinctPoints _θ_ = ∃[ a ] ∃[ b ] a θ b × ¬ a ≈ b
```

An algebra is **simple** provided every congruence relating a pair of distinct
elements relates every pair.  (The trivial algebra satisfies the definition
vacuously.)

```agda
  -- Simple algebra, implication form: a congruence relating a pair of
  -- provably distinct elements relates every pair.
  IsSimple : (ℓ : Level) → Type (α ⊔ ρ ⊔ ov {𝑆 = 𝑆} ℓ)
  IsSimple ℓ = ((_θ_ , _) : Con 𝑨 ℓ) → RelatesDistinctPoints _θ_ → ∀ x y → x θ y
```

In the trivial algebra no congruence relates a distinct pair, so the hypothesis is
refutable and the implication holds vacuously; this is the formal record of the
decision to keep nontriviality out of the definition.

```agda
  -- The trivial algebra is simple vacuously: no congruence relates a distinct pair.
  trivial⇒simple : Trivial 𝑨 → IsSimple ℓ
  trivial⇒simple triv θ (a , b , _ , a≉b) = ⊥-elim (a≉b (triv a b))
```

#### Exactly two congruences, positively

The disjunctive slogan survives in the form concrete instances can use: a congruence
of a simple algebra that relates a distinct pair is the total congruence
`𝟙[ 𝑨 ]`{.AgdaFunction} of [Setoid.Congruences.Basic][], up to the mutual
containment `≑`{.AgdaFunction} that serves as equality of congruences.

```agda
  -- A congruence of a simple algebra relating a distinct pair is the total
  -- congruence.
  simple⇒total : IsSimple ℓ → (θ : Con 𝑨 ℓ) → RelatesDistinctPoints (proj₁ θ) → θ ≑ 𝟙[ 𝑨 ]
  simple⇒total simp θ wit = (λ _ → lift tt) , λ {x} {y} _ → simp θ wit x y
```

#### Relation to subdirect irreducibility

A nontrivial simple algebra is subdirectly irreducible, and its monolith is the
total congruence: every nonzero congruence is in fact total, so the total
congruence is the least nonzero one.

One step of this argument is not constructive.  The field `mono-least`{.AgdaField}
of `IsMonolith`{.AgdaRecord} consumes `Nonzero`{.AgdaFunction}, which is a
negation, while simplicity consumes the positive
`RelatesDistinctPoints`{.AgdaFunction} data, and extracting the witness from the
negation is a double-negation elimination.  The statement below therefore isolates
that step as an antecedent, a witness-extraction principle for nonzero
congruences, exactly as `Stable-≈ε`{.AgdaFunction} isolates the classical step in
[Classical.Structures.Group.Simple][].  The antecedent can be discharged by a
finite search wherever the congruences concerned are pointwise decidable over an
enumerated carrier; this is the approach `witness`{.AgdaFunction} takes in
[Classical.Structures.Group.MinimalNormalDescent][].  No such instance is built
here; the halves that are constructive outright are stated separately, so a
consumer holding positive data never pays for the extraction.

```agda
  -- In a nontrivial algebra the total congruence is nonzero.
  nontrivial⇒𝟙-nonzero : Nontrivial 𝑨 → Nonzero 𝑨 (𝟙[ 𝑨 ] {ℓ})
  nontrivial⇒𝟙-nonzero (a , b , a≉b) 𝟙⊆Δ = a≉b (𝟙⊆Δ (lift tt))
```

Assembling the pieces under the antecedent: nontriviality makes the total
congruence nonzero, extraction turns any nonzero congruence into a witnessed one,
and simplicity makes every witnessed congruence total, so the total congruence is
the least nonzero congruence, which is exactly the monolith.

```agda
  -- With a witness-extraction principle for nonzero congruences, a nontrivial
  -- simple algebra is subdirectly irreducible, with the total congruence as
  -- its monolith.
  simple⇒si : Nontrivial 𝑨 → IsSimple ρ
    →  ((θ : Con 𝑨 ρ) → Nonzero 𝑨 θ → RelatesDistinctPoints (proj₁ θ))
    →  IsSubdirectlyIrreducible 𝑨
  simple⇒si A-nt A-simp θ-rdp = A-nt , 𝟙[ 𝑨 ] , 𝟙-isMonolith
    where
    𝟙-isMonolith : IsMonolith 𝑨 𝟙[ 𝑨 ]
    𝟙-isMonolith =
      record  { mono-nonzero = nontrivial⇒𝟙-nonzero A-nt
              ; mono-least = λ θ nz {x}{y} _ → A-simp θ (θ-rdp θ nz) x y }
```

---

[^1]: The trivial algebra, whose diagonal and total congruences coincide, is simple
      vacuously (`trivial⇒simple`{.AgdaFunction}; see the design note below).
