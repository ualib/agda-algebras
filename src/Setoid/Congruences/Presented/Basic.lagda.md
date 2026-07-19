---
layout: default
file: "src/Setoid/Congruences/Presented/Basic.lagda.md"
title: "Setoid.Congruences.Presented.Basic module (The Agda Universal Algebra Library)"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Finitely presented congruences: reconstruction from generating pairs

This is the [Setoid.Congruences.Presented.Basic][] module of the [Agda Universal Algebra Library][].

A congruence in this library is a `Type`-valued relation, and on that semantic
layer even a two-element carrier has classically-loaded congruences.[^1]

We adopt a two-layer congruence discipline that builds a *decidable* layer, whose
defining property is **reconstructibility from generating pairs**:
a decidable congruence on a finite carrier is determined by the finite list of
enumerated pairs it relates; this module proves that property.[^2]

Concretely, for an algebra `𝑨` with the carrier-finiteness data of
[Setoid.Algebras.Finite][] and a decidable congruence `d : DecCon 𝑨 ℓ`
([Setoid.Congruences.Finite.Basic][]) we define

+  `fromPairs ps`{.AgdaFunction} — the binary relation *presented* by a pair list
   `ps`: two elements are related when `ps` lists a pair to which they are
   componentwise `≈`-equal;
+  `relatedPairs d`{.AgdaFunction} — the finite list of `d`-related pairs of
   enumerated elements, obtained by filtering all pairs of enumerated elements
   through `d`'s decision procedure;

We prove the following **reconstruction theorem**:

    proj₁ d ≑ Cg (fromPairs (relatedPairs d))

That is, `d` is, up to mutual containment, the congruence *generated* by its own
related-pairs list.

One inclusion is the `base`{.AgdaInductiveConstructor} rule of `Cg`{.AgdaFunction}
applied to completeness of the list; the other is `Cg-least`{.AgdaFunction} applied
to soundness of the list.[^3]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Congruences.Presented.Basic where

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Base                       using  ( Fin )
open import Data.List.Base                      using  ( List ; allFin ; filter
                                                       ; map ; cartesianProduct )
open import Data.List.Membership.Propositional  using  ( _∈_ ; lose )
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All        using  ( All ; lookupAny )
open import Data.List.Relation.Unary.All.Properties
                                                using  ( all-filter )
open import Data.List.Relation.Unary.Any        using  ( Any ; any? )
open import Data.Product                        using  ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                               using  ( Level ; _⊔_ )
open import Relation.Binary                     using  ( Setoid ; IsEquivalence )
                                                renaming ( Rel to BinaryRel )
open import Relation.Nullary.Decidable          using  ( Dec ; _×-dec_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                         using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic            using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite           using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic         using  ( Con ; reflexive ; is-equivalence )
open import Setoid.Congruences.Finite.Basic  using  ( DecCon ; ConRel )
open import Setoid.Congruences.Generation    using  ( Cg ; base ; Cg-least ; _⊑_ )
open import Setoid.Congruences.Lattice       using  ( _≑_ )

private variable α ρ ℓ : Level
```
-->

#### The relation presented by a list of pairs

Fix an algebra `𝑨`.  A pair list `ps` presents the relation that holds between
`x` and `y` exactly when some listed pair `(a , b)` has `x ≈ a` and `y ≈ b` —
membership in the list, up to `≈` componentwise.  Because the relation quantifies
existentially over the list (via `Any`{.AgdaDatatype}), it is decidable as soon
as `≈` is; no other structure is needed.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym )

  -- The relation presented by a pair list: componentwise ≈-membership.
  fromPairs : List (𝕌[ 𝑨 ] × 𝕌[ 𝑨 ]) → BinaryRel 𝕌[ 𝑨 ] (α ⊔ ρ)
  fromPairs ps x y = Any (λ p → x ≈ proj₁ p × y ≈ proj₂ p) ps

  -- The presented relation is decidable whenever ≈ is.
  fromPairs? : (∀ x y → Dec (x ≈ y)) → (ps : List (𝕌[ 𝑨 ] × 𝕌[ 𝑨 ]))
    → ∀ x y → Dec (fromPairs ps x y)
  fromPairs? _≟_ ps x y = any? (λ p → x ≟ proj₁ p ×-dec y ≟ proj₂ p) ps
```

A small helper used repeatedly below: a congruence relates `≈`-equal replacements
of related elements.  This is just reflexivity-over-`≈` composed with the equivalence
laws, but naming it keeps the proofs legible.

```agda
  -- From a θ b infer x θ y for any x ≈ a and y ≈ b.
  con-resp-≈ : ((_θ_ , _) : Con 𝑨 ℓ) {x y a b : 𝕌[ 𝑨 ]}
    → x ≈ a → y ≈ b → a θ b → x θ y

  con-resp-≈ (_ , θcon) x≈a y≈b aθb =
    θtrans (reflexive θcon x≈a) (θtrans aθb (θsym (reflexive θcon y≈b)))
    where
    open IsEquivalence (is-equivalence θcon) using ()
      renaming ( sym to θsym ; trans to θtrans )
```

#### The related-pairs list of a decidable congruence

Now fix carrier-finiteness data `𝑭` for `𝑨` (a nested module, so that
`fromPairs`{.AgdaFunction} and its consumers share the ambient algebra).  The
pairs of enumerated elements form a finite list, and a decidable congruence
filters it: `relatedPairs d` keeps exactly the pairs that `d`'s decision
procedure accepts.

```agda
  module _ (𝑭 : FiniteAlgebra 𝑨) where
    open FiniteAlgebra 𝑭 using ( card ; enum ; enum-sur )

    private
      -- A chosen enumeration index for each carrier element, and its correctness.
      idx : 𝕌[ 𝑨 ] → Fin card
      idx x = proj₁ (enum-sur x)

      idx-≈ : (x : 𝕌[ 𝑨 ]) → enum (idx x) ≈ x
      idx-≈ x = proj₂ (enum-sur x)

    -- All pairs of enumerated elements.
    enumPairs : List (𝕌[ 𝑨 ] × 𝕌[ 𝑨 ])
    enumPairs = map (λ p → enum (proj₁ p) , enum (proj₂ p))
                    (cartesianProduct (allFin card) (allFin card))

    -- The pairs of enumerated elements related by a decidable congruence.
    relatedPairs : DecCon 𝑨 ℓ → List (𝕌[ 𝑨 ] × 𝕌[ 𝑨 ])
    relatedPairs d = filter (λ p → proj₂ d (proj₁ p) (proj₂ p)) enumPairs
```

**Soundness**: every listed pair is `d`-related — immediately from the filter.
Consequently the relation presented by the list is contained in `d`, using
`con-resp-≈`{.AgdaFunction} to absorb the componentwise `≈`-steps.

```agda
    -- Every pair on the list is d-related.
    relatedPairs-related : (d : DecCon 𝑨 ℓ)
      →  All (λ p → ConRel d (proj₁ p) (proj₂ p)) (relatedPairs d)
    relatedPairs-related d =
      all-filter (λ p → proj₂ d (proj₁ p) (proj₂ p)) enumPairs

    -- Hence the presented relation of the list is contained in d.
    fromPairs-relatedPairs-⊆ : (d : DecCon 𝑨 ℓ) {x y : 𝕌[ 𝑨 ]}
      →  fromPairs (relatedPairs d) x y → ConRel d x y
    fromPairs-relatedPairs-⊆ d mem =
      let (aθb , x≈a , y≈b) = lookupAny (relatedPairs-related d) mem
      in  con-resp-≈ (proj₁ d) x≈a y≈b aθb
```

**Completeness**: every `d`-related pair is presented by the list.  Given
`x θ y`, pass to the enumerated representatives `enum (idx x)` and
`enum (idx y)`: they are `θ`-related by `con-resp-≈`{.AgdaFunction}, so the pair
survives the filter, and `x`, `y` are componentwise `≈`-equal to it.

```agda
    -- Every d-related pair is presented by the list.
    relatedPairs-complete : (d : DecCon 𝑨 ℓ) {x y : 𝕌[ 𝑨 ]}
      →  ConRel d x y → fromPairs (relatedPairs d) x y
    relatedPairs-complete d {x} {y} xθy =
      lose pair∈related (≈sym (idx-≈ x) , ≈sym (idx-≈ y))
      where
      eθe : ConRel d (enum (idx x)) (enum (idx y))
      eθe = con-resp-≈ (proj₁ d) (idx-≈ x) (idx-≈ y) xθy

      pair∈enum : (enum (idx x) , enum (idx y)) ∈ enumPairs
      pair∈enum = ∈-map⁺ (λ p → enum (proj₁ p) , enum (proj₂ p))
                         (∈-cartesianProduct⁺ (∈-allFin (idx x)) (∈-allFin (idx y)))

      pair∈related : (enum (idx x) , enum (idx y)) ∈ relatedPairs d
      pair∈related = ∈-filter⁺ (λ p → proj₂ d (proj₁ p) (proj₂ p)) pair∈enum eθe
```

#### The reconstruction theorem (L2)

The two containments between `d` and the congruence generated by its
related-pairs list, at any relation level; then, at the working level
`𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ`, their conjunction as an `_≑_`{.AgdaFunction}.  Note that
`Cg (fromPairs (relatedPairs d))` lands at level `𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` on the nose, because
the generation closure absorbs the operation, arity, and carrier levels.

```agda
    -- The generated congruence of the list is contained in d ... (via Cg-least)
    Cg-relatedPairs-⊑ : (d : DecCon 𝑨 ℓ) → Cg (fromPairs (relatedPairs d)) ⊑ proj₁ d
    Cg-relatedPairs-⊑ d = Cg-least (proj₁ d) (fromPairs-relatedPairs-⊆ d)

    -- ... and conversely d is contained in it (via the base rule).
    ⊑-Cg-relatedPairs : (d : DecCon 𝑨 ℓ) → proj₁ d ⊑ Cg (fromPairs (relatedPairs d))
    ⊑-Cg-relatedPairs d xθy = base (relatedPairs-complete d xθy)

    -- L2: a decidable congruence at the working level is ≑ to the congruence
    -- generated by its related-pairs list.
    reconstruction : (d : DecCon 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ))
      →  proj₁ d ≑ Cg (fromPairs (relatedPairs d))
    reconstruction d = ⊑-Cg-relatedPairs d , Cg-relatedPairs-⊑ d
```

--------------------------------------

[^1]: Recall the oracle congruences and the "no-go" theorem of [FLRP.Problem][].

[^2]: See [ADR-008][] and Lemma L2 of `docs/notes/flrp-two-layer-congruences.md` § 3.

[^3]: Two scope remarks.

      1.  Only **carrier** finiteness is used — in fact only the
          `card`{.AgdaField}/`enum`{.AgdaField}/`enum-sur`{.AgdaField} fields;
          not even the `_≟_`{.AgdaField} field is needed, since `d` carries its own
          decision procedure.  In particular no `FiniteSignature`{.AgdaRecord}
          hypothesis appears: signature finiteness enters only for the *converse*
          direction of the layer-D programme — that `Cg`{.AgdaFunction} of a finite
          pair list is again decidable (Lemma L1) — which is the business of
          [Setoid.Congruences.Presented.Decidable][].

      2.  The containments hold for a `DecCon`{.AgdaFunction} at *any*
          relation level and are stated heterogeneously via `_⊑_`{.AgdaFunction}; at
          the working congruence level `𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` of [Setoid.Congruences.Finite][] the
          two sides live at the same level and combine into an honest `_≑_`{.AgdaFunction}.
