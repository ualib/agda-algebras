---
layout: default
file: "src/FLRP/KurzweilNetter/Blocks.lagda.md"
title: "FLRP.KurzweilNetter.Blocks module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### Decidable equivalences of a finite carrier as partitions of its index set

This is the [FLRP.KurzweilNetter.Blocks][] module of the [Agda Universal Algebra Library][].

The Kurzweil–Netter construction (issue #502) represents the dual of
`Con 𝑨` on a power of a simple group *indexed by the carrier* of the finite
algebra `𝑨`{.AgdaBound}.  The traffic between the two sides runs through the
partition lattice `Eq(m)` of [Classical.Structures.Lattice.Partitions][]: a
decidable congruence of `𝑨`{.AgdaBound} must become a partition of
`Fin m`{.AgdaDatatype}, and a partition must become a decidable relation on the
carrier.  This module provides exactly that dictionary, *at the relation level*
— no operations of `𝑨`{.AgdaBound} appear, so everything here is about
decidable equivalences; the interaction with the operations (which partitions
arise from congruences) is the business of
[FLRP.KurzweilNetter.Translations][].

Throughout, the carrier is presented by an *irredundant* enumeration
([Setoid.Algebras.Finite.Irredundant][]): `ienum : Fin m → 𝕌[ 𝑨 ]` hits every
`≈`-class exactly once.  Irredundancy is not a convenience but a correctness
condition — with a redundant index the partitions of `Fin m` could separate two
copies of one carrier element, and the correspondence below would fail to be a
bijection.

The two directions:

+  **`pvOf`** sends a decidable congruence `d` to the partition of the index
   set by `d`-classes, presented as a `ParentVec`{.AgdaFunction}: index `i` is
   labelled by the *least* index `d`-related to it, computed by the bounded
   search `findLeast`{.AgdaFunction}.  Its kernel is exactly the restriction of
   `d` to enumerated values (`pvOf-sound`{.AgdaFunction} /
   `pvOf-complete`{.AgdaFunction}).

+  **`blockRel`** sends a partition `pv` to the relation identifying carrier
   elements whose indices share a block.  It is a decidable equivalence
   respecting `≈`{.AgdaFunction}, by irredundancy of the enumeration.

The module closes with the monotonicity of both maps and the two round trips,
each stated against an arbitrary relation-equivalent presentation so that the
downstream isomorphisms can consume them without definitional coincidences.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter.Blocks where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty          using ( ⊥-elim )
open import Data.Fin.Base       using ( Fin ) renaming ( _≤_ to _≤ᶠ_ )
open import Data.Fin.Properties using () renaming ( _≟_ to _≟ᶠ_ )
open import Data.Product        using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base       using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Vec.Base       using ( tabulate )
open import Level               using ( 0ℓ )
open import Relation.Binary     using ( Setoid ; IsEquivalence )
                                renaming ( Rel to BinaryRel )
open import Relation.Binary.PropositionalEquality
                                using ( _≡_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary    using ( ¬_ ; Dec )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Partitions
  using ( SameBlock ; _⊑_ ; _≈ᵖ_ ; parent-tab ; findLeast ; least-unique )
open import Overture                             using ( Signature )
open import Setoid.Algebras.Basic                using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite.Irredundant   using ( IrredundantEnumeration )
open import Setoid.Congruences.Basic             using ( reflexive ; is-equivalence )
open import Setoid.Congruences.Certificates.Schema  using ( ParentVec ; parent )
open import Setoid.Congruences.Finite.Basic      using ( DecCon ; ConRel )
```
-->

#### The dictionary module

`KNBlocks`{.AgdaModule} fixes the algebra and an irredundant enumeration of its
carrier.  Nothing here looks at the operations, but the ambient algebra is kept
(rather than a bare setoid) because the input and output of the dictionary are
`DecCon`{.AgdaFunction}s.

```agda
module KNBlocks {𝑆 : Signature 0ℓ 0ℓ} (𝑨 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ)
                (𝑬 : IrredundantEnumeration 𝑨) where

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
    renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open IrredundantEnumeration 𝑬 using ( ienum ; ienum-sur ; ienum-inj )
    renaming ( icard to m )
```

#### The index of a carrier element

Irredundancy makes "the index of `x`" a function of the `≈`-class of `x`: any
two `≈`-equal elements are sent to propositionally equal indices, and the index
of an enumerated value is its own position.

```agda
  -- The index of (the ≈-class of) a carrier element.
  eIdx : 𝕌[ 𝑨 ] → Fin m
  eIdx x = proj₁ (ienum-sur x)

  -- The enumerated value at the index of x is x, up to ≈.
  eIdx-≈ : ∀ x → ienum (eIdx x) ≈ x
  eIdx-≈ x = proj₂ (ienum-sur x)

  -- ≈-equal elements have equal indices (this is exactly irredundancy).
  eIdx-cong : ∀ {x y} → x ≈ y → eIdx x ≡ eIdx y
  eIdx-cong {x} {y} e = ienum-inj (≈trans (eIdx-≈ x) (≈trans e (≈sym (eIdx-≈ y))))

  -- The index of an enumerated value is its position.
  eIdx-ienum : ∀ i → eIdx (ienum i) ≡ i
  eIdx-ienum i = ienum-inj (eIdx-≈ (ienum i))
```

#### From a decidable congruence to a partition

Fix a decidable congruence `d`.  Each index `i` is relabelled by the least
index whose value is `d`-related to `ienum i`; the search cannot fail because
`i` itself qualifies, by reflexivity of `d` over `≈`.

```agda
  module _ (d : DecCon 𝑨 0ℓ) where

    private
      θ : BinaryRel 𝕌[ 𝑨 ] 0ℓ
      θ = ConRel d

      θ-refl≈ : ∀ {x y} → x ≈ y → θ x y
      θ-refl≈ = reflexive (proj₂ (proj₁ d))

      θ-sym : ∀ {x y} → θ x y → θ y x
      θ-sym = IsEquivalence.sym (is-equivalence (proj₂ (proj₁ d)))

      θ-trans : ∀ {x y z} → θ x y → θ y z → θ x z
      θ-trans = IsEquivalence.trans (is-equivalence (proj₂ (proj₁ d)))

      -- The least index of the d-class of ienum i, with its two certificates.
      found : (i : Fin m)
        → Σ[ j ∈ Fin m ] (θ (ienum j) (ienum i) × ((k : Fin m) → θ (ienum k) (ienum i) → j ≤ᶠ k))
      found i = extract (findLeast m (λ j → proj₂ d (ienum j) (ienum i)))
        where
        extract :
             (Σ[ j ∈ Fin m ] (θ (ienum j) (ienum i) × ((k : Fin m) → θ (ienum k) (ienum i) → j ≤ᶠ k)))
           ⊎ ((j : Fin m) → ¬ θ (ienum j) (ienum i))
          → Σ[ j ∈ Fin m ] (θ (ienum j) (ienum i) × ((k : Fin m) → θ (ienum k) (ienum i) → j ≤ᶠ k))
        extract (inj₁ w)     = w
        extract (inj₂ none)  = ⊥-elim (none i (θ-refl≈ ≈refl))

      -- The class representative (least related index).
      rep : Fin m → Fin m
      rep i = proj₁ (found i)

      rep-rel : (i : Fin m) → θ (ienum (rep i)) (ienum i)
      rep-rel i = proj₁ (proj₂ (found i))

      rep-least : (i k : Fin m) → θ (ienum k) (ienum i) → rep i ≤ᶠ k
      rep-least i = proj₂ (proj₂ (found i))

    -- The partition of the index set by d-classes.
    pvOf : ParentVec m
    pvOf = tabulate rep
```

The kernel of `pvOf`{.AgdaFunction} is the restriction of `d` to enumerated
values: same label means related through the shared representative, and related
values search pointwise-equivalent predicates, so their least representatives
coincide.

```agda
    -- Same pvOf-block implies d-related values.
    pvOf-sound : ∀ {i j} → SameBlock pvOf i j → θ (ienum i) (ienum j)
    pvOf-sound {i} {j} sb =
      θ-trans (θ-sym (rep-rel i)) (subst (λ k → θ (ienum k) (ienum j)) (sym rep≡) (rep-rel j))
      where
      rep≡ : rep i ≡ rep j
      rep≡ = trans (sym (parent-tab rep i)) (trans sb (parent-tab rep j))

    -- d-related values imply same pvOf-block.
    pvOf-complete : ∀ {i j} → θ (ienum i) (ienum j) → SameBlock pvOf i j
    pvOf-complete {i} {j} rel = trans (parent-tab rep i) (trans rep≡ (sym (parent-tab rep j)))
      where
      rep≡ : rep i ≡ rep j
      rep≡ = least-unique
        (λ k pk → θ-trans pk rel) (λ k qk → θ-trans qk (θ-sym rel))
        (rep i) (rep-rel i) (rep-least i)
        (rep j) (rep-rel j) (rep-least j)
```

#### From a partition to a decidable equivalence

`blockRel pv` identifies carrier elements whose indices share a `pv`-block.
Because `SameBlock`{.AgdaFunction} is a propositional equality of labels, the
equivalence laws are those of `_≡_`{.AgdaDatatype}; reflexivity over
`≈`{.AgdaFunction} and decidability come from irredundancy and the decidable
equality of `Fin`{.AgdaDatatype}.

```agda
  -- The relation on the carrier induced by a partition of the index set.
  blockRel : ParentVec m → BinaryRel 𝕌[ 𝑨 ] 0ℓ
  blockRel pv x y = SameBlock pv (eIdx x) (eIdx y)

  -- blockRel contains the setoid equality.
  blockRel-refl≈ : (pv : ParentVec m) → ∀ {x y} → x ≈ y → blockRel pv x y
  blockRel-refl≈ pv e = cong (parent pv) (eIdx-cong e)

  -- blockRel is an equivalence (label equality is propositional equality).
  blockRel-isEquivalence : (pv : ParentVec m) → IsEquivalence (blockRel pv)
  blockRel-isEquivalence pv = record { refl = refl ; sym = sym ; trans = trans }

  -- blockRel is decidable: compare the two labels.
  blockRel-dec : (pv : ParentVec m) → ∀ x y → Dec (blockRel pv x y)
  blockRel-dec pv x y = parent pv (eIdx x) ≟ᶠ parent pv (eIdx y)
```

#### Monotonicity

Both maps are monotone for containment: refinement of partitions is inclusion
of kernels, so `blockRel`{.AgdaFunction} forwards it verbatim, and
`pvOf`{.AgdaFunction} forwards a congruence containment through the two kernel
characterizations.

```agda
  -- Refinement of partitions gives containment of the induced relations.
  blockRel-mono : {pu pw : ParentVec m} → pu ⊑ pw
    → ∀ {x y} → blockRel pu x y → blockRel pw x y
  blockRel-mono h = h

  -- Containment of congruences gives refinement of the induced partitions.
  pvOf-mono : (d e : DecCon 𝑨 0ℓ) → (∀ {x y} → ConRel d x y → ConRel e x y)
    → pvOf d ⊑ pvOf e
  pvOf-mono d e sub sb = pvOf-complete e (sub (pvOf-sound d sb))
```

#### The round trips

Each round trip is stated against an arbitrary relation-equivalent
presentation.  On the partition side: if the relation of `d` is pointwise
equivalent to `blockRel pv`, then `pvOf d` and `pv` have the same kernel — the
step from index `i` to carrier element `ienum i` and back is repaired by
`eIdx-ienum`{.AgdaFunction}.

```agda
  -- Round trip on partitions: pvOf inverts blockRel, up to kernel equality.
  pvOf-blockRel : (d : DecCon 𝑨 0ℓ) (pv : ParentVec m)
    → (∀ {x y} → ConRel d x y → blockRel pv x y)
    → (∀ {x y} → blockRel pv x y → ConRel d x y)
    → pvOf d ≈ᵖ pv
  pvOf-blockRel d pv fwd bwd = to-pv , from-pv
    where
    to-pv : pvOf d ⊑ pv
    to-pv {i} {j} sb =
      subst₂ (SameBlock pv) (eIdx-ienum i) (eIdx-ienum j) (fwd (pvOf-sound d sb))

    from-pv : pv ⊑ pvOf d
    from-pv {i} {j} sb =
      pvOf-complete d (bwd (subst₂ (SameBlock pv) (sym (eIdx-ienum i)) (sym (eIdx-ienum j)) sb))
```

On the congruence side: the relation induced by the partition of a decidable
congruence is the congruence itself, the step from `x` to `ienum (eIdx x)` and
back repaired by reflexivity over `≈`{.AgdaFunction} and transitivity.

```agda
  -- Round trip on relations: blockRel inverts pvOf, up to mutual containment.
  blockRel-pvOf-out : (d : DecCon 𝑨 0ℓ) → ∀ {x y} → blockRel (pvOf d) x y → ConRel d x y
  blockRel-pvOf-out d {x} {y} sb = θ-trans (θ-sym (θ-refl≈ (eIdx-≈ x))) (θ-trans rel (θ-refl≈ (eIdx-≈ y)))
    where
    θ-refl≈  = reflexive (proj₂ (proj₁ d))
    θ-sym    = IsEquivalence.sym (is-equivalence (proj₂ (proj₁ d)))
    θ-trans  = IsEquivalence.trans (is-equivalence (proj₂ (proj₁ d)))

    rel : ConRel d (ienum (eIdx x)) (ienum (eIdx y))
    rel = pvOf-sound d sb

  blockRel-pvOf-in : (d : DecCon 𝑨 0ℓ) → ∀ {x y} → ConRel d x y → blockRel (pvOf d) x y
  blockRel-pvOf-in d {x} {y} rel =
    pvOf-complete d (θ-trans (θ-refl≈ (eIdx-≈ x)) (θ-trans rel (θ-sym (θ-refl≈ (eIdx-≈ y)))))
    where
    θ-refl≈  = reflexive (proj₂ (proj₁ d))
    θ-sym    = IsEquivalence.sym (is-equivalence (proj₂ (proj₁ d)))
    θ-trans  = IsEquivalence.trans (is-equivalence (proj₂ (proj₁ d)))
```

--------------------------------------
