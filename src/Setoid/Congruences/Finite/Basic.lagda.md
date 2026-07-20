---
layout: default
file: "src/Setoid/Congruences/Finite/Basic.lagda.md"
title: "Setoid.Congruences.Finite.Basic module (The Agda Universal Algebra Library)"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Finitely enumerable congruence lattices

This is the [Setoid.Congruences.Finite.Basic][] module of the [Agda Universal Algebra Library][].

While [Setoid.Algebras.Finite][] defines the finiteness interface for a setoid algebra
(decidable `≈` and a finite surjective enumeration of the carrier), this module
supplies the finiteness interface for congruences, that is, **decidable congruences**
(`DecCon`{.AgdaFunction}) and the record type `FiniteCongruences`{.AgdaRecord} `𝑨`.

`FiniteCongruences`{.AgdaRecord} `𝑨` packages a finite list `cons` of decidable
congruences of `𝑨` along with a proof that this list is *complete* in the sense that
every congruence of `𝑨` is, up to mutual containment `≑`, one of those in `cons`.

This provides a searchable congruence lattice that finite-algebra theorems run their
algorithms over; its first consumer is the finite Birkhoff theorem of
[Setoid.Subalgebras.Subdirect.Finite][].

#### Why carrier finiteness does not suffice

Crucially, the data packaged here is *strictly stronger* than a
`FiniteAlgebra`{.AgdaRecord} witness, which is why the two interfaces are separate
records.  Carrier-finiteness along with decidable setoid equality do not, by
themselves, admit a complete congruence enumeration constructively.

Indeed, a congruence is a `Type`-valued relation `𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ`, and an
arbitrary such relation on a finite carrier need not be decidable; e.g., on a bare
set of two elements, the relation that collapses the two points *iff* `P` holds is a
congruence for any proposition `P`, and it is `≑`-equal to a decidable congruence
only iff `P` is decidable.

Thus, a complete enumeration of congruences-up-to-`≑` is strictly stronger than
decidable equality on a finite set; it is exactly the classical content of "finite
algebra" for congruence-lattice purposes.  Classically every finite algebra furnishes
these data; constructively they must be supplied, and this record is the interface
through which they are.

The two interfaces are logically independent in the other direction as well: an
infinite algebra can perfectly well have a finitely enumerable congruence lattice
(consider an algebra that is constructively simple, with decidable equality — its
complete list is the diagonal and the total congruence), so
`FiniteCongruences`{.AgdaRecord} does not presuppose a finite carrier.

There is, however, one overlap, recorded as `≈-dec`{.AgdaFunction} below:
completeness forces the listed representative of the *diagonal* to decide setoid
equality, so the `_≟_`{.AgdaField} field of `FiniteAlgebra`{.AgdaRecord} is derivable
from a `FiniteCongruences`{.AgdaRecord} witness.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Congruences.Finite.Basic where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------------------------
open import Data.List.Base                         using  ( List ; [] ; _∷_ )
open import Data.List.Membership.Propositional     using  ( _∈_ )
open import Data.List.Relation.Unary.Any           using  ( here )
open import Data.Product                           using  ( _×_ ; _,_ ; Σ-syntax
                                                          ; proj₁ ; proj₂ )
open import Data.Unit.Base                         using  ( ⊤ ; tt )
open import Function                               using  ( _∘_ )
open import Level                                  using  ( Level ; _⊔_ ; Lift ; lift ; lower )
                                                   renaming ( suc to lsuc )
open import Relation.Binary                        using  ( Setoid )
                                                   renaming ( Rel to BinaryRel )
open import Relation.Binary.PropositionalEquality  using  ( refl )
open import Relation.Nullary                       using  ( Dec ; yes ; no )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                       using ( 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open import Setoid.Algebras.Basic          using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite         using ( 𝟏 )
open import Setoid.Congruences.Basic       using ( Con ; mkcon ; reflexive ; 𝟘[_] )
open import Setoid.Congruences.Lattice     using ( _≑_ )

private variable α ρ : Level
```
-->

#### Decidable congruences and the working level

A **decidable congruence** is a congruence whose membership relation is decidable.
The working congruence level is the absorbing level `𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ`, at
which the generated (principal) congruences used downstream (e.g. for the monolith
in the finite Birkhoff construction) stay put — the same level discipline as in
[Setoid.Congruences.CompleteLattice][].

```agda
-- A congruence together with a decision procedure for its membership.
DecCon : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra {𝑆 = 𝑆} α ρ)(ℓ : Level) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ lsuc ℓ)
DecCon 𝑨 ℓ = Σ[ (_θ_ , _) ∈ Con 𝑨 ℓ ] ∀ x y → Dec (x θ y)

-- The underlying relation of a decidable congruence.
ConRel : {𝑨 : Algebra {𝑆 = 𝑆} α ρ}{ℓ : Level} → DecCon 𝑨 ℓ → BinaryRel 𝕌[ 𝑨 ] ℓ
ConRel ((θ , _) , _) = θ
```

#### The congruence-side finiteness interface

The record bundles a finite list `cons`{.AgdaField} of decidable congruences and a
proof `complete`{.AgdaField} that the list exhausts the congruence lattice up to
`≑`.  The `witness*`{.AgdaFunction} helpers project, for any congruence, its listed
representative together with the membership and `≑`-equality proofs.[^1]

```agda
record FiniteCongruences {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra {𝑆 = 𝑆} α ρ) : Type (lsuc (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)) where
  field
    -- a finite list of decidable congruences of 𝑨 ...
    cons      : List (DecCon 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ))
    -- ... exhausting the congruence lattice of 𝑨, up to ≑
    complete  : ∀ φ → Σ[ d ∈ DecCon 𝑨 _ ] (d ∈ cons) × (φ ≑ proj₁ d)

  witness : ∀ φ → DecCon 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  witness = proj₁ ∘ complete

  witness∈ : ∀ φ → witness φ ∈ cons
  witness∈ = proj₁ ∘ proj₂ ∘ complete

  witness≑ : ∀ φ → φ ≑ proj₁ (witness φ)
  witness≑ = proj₂ ∘ proj₂ ∘ complete

```

As promised, a `FiniteCongruences`{.AgdaRecord} witness decides setoid equality:
the diagonal congruence `𝟘[ 𝑨 ]` has a listed representative whose decidable
membership coincides, up to the two containments of `≑`, with `≈`.

```agda
module _ {𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑪 : FiniteCongruences 𝑨) where
  open FiniteCongruences 𝑪
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

  private
    -- The diagonal congruence at the working level.
    Δ : Con 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
    Δ = 𝟘[ 𝑨 ] {𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ}

  -- Setoid equality is decidable whenever the congruence lattice is
  -- finitely enumerable: ask the diagonal's listed representative.
  ≈-dec : (x y : 𝕌[ 𝑨 ]) → Dec (x ≈ y)
  ≈-dec x y with proj₂ (witness Δ) x y
  ... | yes dxy  = yes (lower (proj₂ (witness≑ Δ) dxy))
  ... | no ¬dxy  = no λ x≈y → ¬dxy (proj₁ (witness≑ Δ) (lift x≈y))
```

#### Non-vacuity: the one-element algebra

The one-element algebra `𝟏`{.AgdaFunction} of [Setoid.Algebras.Finite][] has, up to
`≑`, exactly one congruence — the all-relation, which on a one-point carrier is
also the diagonal — so its complete list is a singleton.

```agda
-- The sole decidable congruence of 𝟏: the all-relation (= the diagonal on a point).
𝟏-Δ : {𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → DecCon (𝟏 {𝑆 = 𝑆}) (𝓞 ⊔ 𝓥)
𝟏-Δ {𝓞 = 𝓞}{𝓥 = 𝓥} = ((λ _ _ → Lift (𝓞 ⊔ 𝓥) ⊤)
      , mkcon  (λ _ → lift tt)
               (record { refl = lift tt ; sym = λ _ → lift tt ; trans = λ _ _ → lift tt })
               (λ _ _ → lift tt))
      , (λ _ _ → yes (lift tt))

-- The congruence lattice of 𝟏 is finitely enumerable.
open FiniteCongruences
𝟏-FiniteCongruences : FiniteCongruences (𝟏 {𝑆 = 𝑆})
𝟏-FiniteCongruences .cons = 𝟏-Δ ∷ []
𝟏-FiniteCongruences .complete ( _ , φcon ) =
  𝟏-Δ , here refl , (λ _ → lift tt) , λ x → reflexive φcon tt
```

--------------------------------------

[^1]: In the definition of `FiniteCongruences`, each occurrence of
      `∀ φ → ...` could be expressed more explicitly as `φ : Con 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) → ...`.
