---
layout: default
file: "src/Classical/Structures/Group/NormalClosure.lagda.md"
title: "Classical.Structures.Group.NormalClosure module"
date: "2026-08-30"
author: "the agda-algebras development team"
---

### Normal-closure witness terms

This is the [Classical.Structures.Group.NormalClosure][] module of the [Agda Universal Algebra Library][].

The **normal closure** of a set of elements of a group is the least normal
subgroup containing them.  This module does not construct that subgroup; it
provides the *witness language* for membership claims about it: a term datatype
`ClosureTerm`{.AgdaDatatype} whose inhabitants denote elements built from given
seeds by the identity, inverses, products, and conjugates, together with the
soundness theorem `closure-sound`{.AgdaFunction}: whenever a normal subgroup
contains the seeds, it contains the value of every term.

The point of the language is finite certification.  A simplicity certificate in
the sense of [Classical.Structures.Group.Simple][] must show, for a given seed,
that the seed's normal closure is everything; a certificate does that by
exhibiting, for each target element, a closure term that evaluates to it, and the
evaluations are decidable equalities over a finite carrier.  Soundness then
replays the certificate against an *arbitrary* normal subgroup containing the
seed, with no completeness theorem needed: only the two directions actually
consumed are stated.

The term datatype is parameterized by the carrier type alone, not by a group,
so that generated certificate data can be written down before (and independent
of) the group structure it will be replayed against; evaluation and soundness
live in the group-parameterized module below.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.NormalClosure where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base    using  ( Fin )
open import Data.Nat.Base    using  ( ℕ )
open import Data.Product     using  ( _,_ )
open import Level            using  ( Level )
open import Relation.Unary   using  ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic        using ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation  using ( module Conjugate )
open import Classical.Structures.Group.Subgroups    using ( IsSubgroup )
open import Setoid.Algebras.Basic                   using ( 𝕌[_] )
```
-->

#### The witness terms

A closure term over a carrier `A` with `k` seeds denotes an element built from
the seeds by the four normal-subgroup closure operations.  The conjugating
element of `cnj`{.AgdaInductiveConstructor} is an arbitrary carrier element, not
a term: normality closes a subgroup under conjugation by *everything*.

```agda
data ClosureTerm {a : Level} (A : Type a) (k : ℕ) : Type a where
  one   : ClosureTerm A k
  seed  : Fin k → ClosureTerm A k
  inv   : ClosureTerm A k → ClosureTerm A k
  mul   : ClosureTerm A k → ClosureTerm A k → ClosureTerm A k
  cnj   : A → ClosureTerm A k → ClosureTerm A k
```

#### Evaluation and soundness

Evaluation interprets a term in a group, at an assignment of the seeds; the
conjugation case is exactly `conj`{.AgdaFunction} of
[Classical.Structures.Group.Conjugation][] (syntax: `_^ g`), so that soundness
can consume a normality proof with no conversion.

```agda
module NormalClosure {α ρ : Level} (𝒢@(𝑮 , _) : Group α ρ) where
  open Group-Op 𝒢   using  ( _∙_ ; ε ; _⁻¹ )
  open Conjugate 𝒢  using  ( conj-syntax ; IsNormal )

  -- Evaluate a closure term at an assignment of the seeds.
  ⟦_⟧ : {k : ℕ} → ClosureTerm 𝕌[ 𝑮 ] k → (Fin k → 𝕌[ 𝑮 ]) → 𝕌[ 𝑮 ]
  ⟦ one ⟧      σ = ε
  ⟦ seed i ⟧   σ = σ i
  ⟦ inv e ⟧    σ = ⟦ e ⟧ σ ⁻¹
  ⟦ mul e f ⟧  σ = ⟦ e ⟧ σ ∙ ⟦ f ⟧ σ
  ⟦ cnj g e ⟧  σ = ⟦ e ⟧ σ ^ g
```

**Soundness**.  A normal subgroup containing every seed contains the value of
every term.  The proof is structural, one closure property per constructor.

```agda
  -- A normal subgroup containing the seeds contains every term's value.
  closure-sound : {ℓ : Level} {N : Pred 𝕌[ 𝑮 ] ℓ}
    →  IsSubgroup 𝒢 N → IsNormal N
    →  {k : ℕ} {σ : Fin k → 𝕌[ 𝑮 ]} → (∀ i → σ i ∈ N)
    →  (e : ClosureTerm 𝕌[ 𝑮 ] k) → ⟦ e ⟧ σ ∈ N
  closure-sound sg nrm σ∈ one        = IsSubgroup.ε-closed sg
  closure-sound sg nrm σ∈ (seed i)   = σ∈ i
  closure-sound sg nrm σ∈ (inv e)    = IsSubgroup.⁻¹-closed sg (closure-sound sg nrm σ∈ e)
  closure-sound sg nrm σ∈ (mul e f)  = IsSubgroup.∙-closed sg  (closure-sound sg nrm σ∈ e)
                                                               (closure-sound sg nrm σ∈ f)
  closure-sound sg nrm σ∈ (cnj g e)  = nrm g (closure-sound sg nrm σ∈ e)
```
