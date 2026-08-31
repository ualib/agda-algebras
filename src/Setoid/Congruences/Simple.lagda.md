---
layout: default
file: "src/Setoid/Congruences/Simple.lagda.md"
title: "Setoid.Congruences.Simple module (The Agda Universal Algebra Library)"
date: "2026-08-31"
author: "the agda-algebras development team"
---

### Simple algebras

This is the [Setoid.Congruences.Simple][] module of the [Agda Universal Algebra Library][].

An algebra is **simple** when its congruence lattice has exactly two members: the
diagonal, which relates only the setoid-equal pairs, and the total congruence, which
relates everything.  This module states the notion at the congruence level, in the
implication form that concrete instances can inhabit, and develops the following:

+  `RelatesApart`{.AgdaFunction}: the positive data of a congruence relating a pair
   of provably distinct elements;
+  `IsSimple`{.AgdaFunction}, the implication definition of "simple algebra": a
   congruence relating a distinct pair relates every pair;
+  `trivial⇒simple`{.AgdaFunction}: the trivial algebra is simple vacuously;
+  `simple⇒total`{.AgdaFunction}: in a simple algebra, a congruence relating a
   distinct pair is the total congruence;
+  `nontrivial⇒𝟙-nonzero`{.AgdaFunction} and `simple⇒si`{.AgdaFunction}: a
   nontrivial simple algebra is subdirectly irreducible with the total congruence as
   its monolith, under a witness-extraction antecedent that the design note below
   explains.

The group-theoretic special case is `IsSimple`{.AgdaFunction} of
[Classical.Structures.Group.Simple][]; the identification of the two notions through
the normal-subgroup/congruence correspondence is proved in
[Classical.Structures.Group.Congruences][].

#### Design note: the implication form, at this level too

The textbook definition classifies every congruence as the diagonal or the total
congruence.  Stated over arbitrary congruences, that disjunction is oracle-strength
data, for exactly the reason recorded in [Classical.Structures.Group.Simple][] and
[Classical.Structures.Group.MaximalSubgroup][]: relatedness under a congruence can
encode an arbitrary proposition, so the classifier would decide it up to double
negation, and no concrete algebra could inhabit the disjunctive form in `--safe`
Agda.  The definition here is therefore the implication: a congruence that relates
some pair of provably distinct elements relates every pair.

Two further choices mirror the group module.

+  **The witnessed pair is positive data**.  The hypothesis is
   `RelatesApart`{.AgdaFunction}, a Σ-packaged pair carrying its relatedness and
   distinctness proofs, deliberately not `Nonzero`{.AgdaFunction} of
   [Setoid.Congruences.Monolith][], which is a negation and carries no witness.
   Consumers apply simplicity by producing the pair; the group-side equivalence of
   [Classical.Structures.Group.Congruences][] produces it from a non-identity member
   of a normal subgroup.
+  **Nontriviality stays out of the definition**.  The trivial algebra inhabits the
   implication form vacuously (`trivial⇒simple`{.AgdaFunction}); nontriviality
   witnesses live in bundles, exactly as `IsNonabelianSimple`{.AgdaRecord} handles
   the group side.

The implication form does not recover the disjunctive classification, at this level
or at the group level: deciding which disjunct holds would decide, for an arbitrary
congruence, whether it relates a distinct pair.  That the disjunctive readings are
unreachable from the notion concrete instances inhabit, on both sides at once, is
the strongest evidence that the implication form is the right primitive at both
levels; the group-side equivalence accordingly runs entirely at the implication
level, constructively in both directions.

#### A note on levels

`IsSimple`{.AgdaFunction} takes the congruence level `ℓ`{.AgdaBound} as a parameter
and quantifies over `Con 𝑨 ℓ`{.AgdaFunction} at exactly that level, the same
per-level discipline as the correspondence of
[Classical.Structures.Group.Congruences][].  The subdirect-irreducibility facts
below instantiate it at the algebra's own relation level `ρ`{.AgdaBound}, where the
monolith vocabulary of [Setoid.Congruences.Monolith][] lives; the group-side
equivalence instantiates it at the level `α ⊔ ρ ⊔ ℓ₀` of the group's subgroup
predicates.

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
open import Relation.Binary   using ( Setoid )
open import Relation.Nullary  using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                     using  ( 𝑆 )
open import Setoid.Algebras.Basic        using  ( ov ; Algebra ; 𝔻[_] )
open import Setoid.Congruences.Basic     using  ( Con ; 𝟙[_] )
open import Setoid.Congruences.Lattice   using  ( _≑_ )
open import Setoid.Congruences.Monolith  using  ( Nontrivial ; Trivial ; Nonzero
                                                ; IsSubdirectlyIrreducible )

private variable α ρ ℓ : Level
```
-->

#### Simplicity, in implication form

Fix an algebra `𝑨`.  The hypothesis a consumer supplies is a related pair together
with a proof that the setoid equality keeps the pair apart; it enters as positive
Σ-data, in the same shape as the non-identity member the group-side definition
consumes.

```agda
module _ (𝑨 : Algebra {𝑆 = 𝑆} α ρ) where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )

  -- The positive data: θ relates a pair of provably distinct elements.
  RelatesApart : Con 𝑨 ℓ → Type (α ⊔ ρ ⊔ ℓ)
  RelatesApart (θ , _) = ∃[ a ] ∃[ b ] θ a b × ¬ a ≈ b
```

**Simple algebra** (definition):  An algebra is **simple** provided every congruence
relating a pair of distinct elements relates every pair.  The trivial algebra
satisfies the definition vacuously.

```agda
  -- Simple algebra, implication form: a congruence relating a pair of
  -- provably distinct elements relates every pair.
  IsSimple : (ℓ : Level) → Type (α ⊔ ρ ⊔ ov {𝑆 = 𝑆} ℓ)
  IsSimple ℓ = (θ : Con 𝑨 ℓ) → RelatesApart θ → ∀ x y → proj₁ θ x y
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
  simple⇒total : IsSimple ℓ → (θ : Con 𝑨 ℓ) → RelatesApart θ → θ ≑ 𝟙[ 𝑨 ]
  simple⇒total simp θ wit = (λ _ → lift tt) , λ {x} {y} _ → simp θ wit x y
```

#### Relation to subdirect irreducibility

A nontrivial simple algebra is subdirectly irreducible, and its monolith is the
total congruence: every nonzero congruence is in fact total, so the total congruence
is the least nonzero one.  One step of this argument is not constructive.  The field
`mono-least`{.AgdaField} of `IsMonolith`{.AgdaRecord} consumes
`Nonzero`{.AgdaFunction}, which is a negation, while simplicity consumes the
positive `RelatesApart`{.AgdaFunction} data, and extracting the witness from the
negation is a double-negation elimination.  The statement below therefore isolates
that step as an antecedent, a witness-extraction principle for nonzero congruences,
exactly as `Stable-≈ε`{.AgdaFunction} isolates the classical step in
[Classical.Structures.Group.Simple][].  The antecedent is discharged wherever the
congruences concerned are pointwise decidable over a searchable carrier; the halves
that are constructive outright are stated separately, so a consumer holding positive
data never pays for the extraction.

```agda
  -- In a nontrivial algebra the total congruence is nonzero.
  nontrivial⇒𝟙-nonzero : Nontrivial 𝑨 → Nonzero 𝑨 (𝟙[ 𝑨 ] {ℓ})
  nontrivial⇒𝟙-nonzero (a , b , a≉b) 𝟙⊆Δ = a≉b (𝟙⊆Δ (lift tt))
```

```agda
  -- With a witness-extraction principle for nonzero congruences, a nontrivial
  -- simple algebra is subdirectly irreducible, with the total congruence as
  -- its monolith.
  simple⇒si : Nontrivial 𝑨 → IsSimple ρ
    →  ((θ : Con 𝑨 ρ) → Nonzero 𝑨 θ → RelatesApart θ)
    →  IsSubdirectlyIrreducible 𝑨
  simple⇒si nt simp extract = nt , 𝟙[ 𝑨 ] {ρ} , record
    { mono-nonzero  = nontrivial⇒𝟙-nonzero nt
    ; mono-least    = λ θ nz {x} {y} _ → simp θ (extract θ nz) x y }
```
