---
layout: default
file: "src/Classical/Structures/Lattice/Product.lagda.md"
title: "Classical.Structures.Lattice.Product module"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### Binary products of lattices {#classical-structures-lattice-product}

This is the [Classical.Structures.Lattice.Product][] module of the [Agda Universal Algebra Library][].

Given lattices `𝑳₁`{.AgdaBound} and `𝑳₂`{.AgdaBound} over
[`Sig-Lattice`][Classical.Signatures.Lattice], this module constructs their
**binary direct product** `𝑳₁`{.AgdaBound}` ×ˡ `{.AgdaFunction}`𝑳₂`{.AgdaBound}:
the lattice on the product
setoid whose meet and join act componentwise.  The construction mirrors the group
case ([Classical.Structures.Group.Product][]) but is assembled through the
setoid-level builder `setoidEqsToLattice`{.AgdaFunction} of
[Classical.Structures.Lattice][], whose interpretation clauses reduce
definitionally; consequently each of the eight lattice equations for the product is
*literally* the pair of the component equations, and no term-induction lemma is
needed.

Besides the product itself, the module characterizes the induced meet order of
[Classical.Properties.Lattice][]: the product order is the componentwise order,
definitionally, and the three accessors `≤ₓ-fst`{.AgdaFunction},
`≤ₓ-snd`{.AgdaFunction}, `≤ₓ-pair`{.AgdaFunction} name the two projections and the
pairing.  The first consumer is the FLRP closure toolkit
([FLRP.Closure][]; roadmap § 3, work package WP-5), which represents
`𝑳₁ ×ˡ 𝑳₂`{.AgdaFunction} as a congruence lattice whenever its factors are so
representable.

Following the Cubical-port discipline, the underlying equivalence of the product is
isolated in `A×B`{.AgdaFunction} — the pointwise pair of the component
equivalences — so it can be mechanically substituted on the eventual port.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.Product where


-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product          using ( _,_ ; _×_ ; proj₁ ; proj₂ )
open import Level                 using ( Level ; _⊔_ )
open import Relation.Binary       using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using ( module Lattice-Order )
open import Classical.Structures.Lattice  using ( Lattice ; module Lattice-Op
                                                ; setoidEqsToLattice )
open import Setoid.Algebras.Basic         using ( 𝕌[_] ; 𝔻[_] )

private variable α ρ β σ : Level
```
-->

#### The product construction

`LatticeProduct`{.AgdaModule} `𝑳₁` `𝑳₂` packages the whole development for a fixed
pair of lattices; opening it provides the product setoid, the componentwise
operations with their congruences and equations, the product lattice, and the
characterization of its order.

```agda
module LatticeProduct (𝑳₁ : Lattice α ρ) (𝑳₂ : Lattice β σ) where
  private
    𝑨 = proj₁ 𝑳₁
    𝑩 = proj₁ 𝑳₂

  open Setoid 𝔻[ 𝑨 ] using ()
    renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑩 ] using ()
    renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  open Lattice-Op 𝑳₁ using ()
    renaming ( _∧_ to _∧₁_ ; _∨_ to _∨₁_ ; ∧-cong to ∧₁-cong ; ∨-cong to ∨₁-cong
             ; ∧-assoc-law to ∧₁-assoc ; ∧-comm-law to ∧₁-comm ; ∧-idem-law to ∧₁-idem
             ; ∨-assoc-law to ∨₁-assoc ; ∨-comm-law to ∨₁-comm ; ∨-idem-law to ∨₁-idem
             ; absorbˡ-law to absorbˡ₁ ; absorbʳ-law to absorbʳ₁ )
  open Lattice-Op 𝑳₂ using ()
    renaming ( _∧_ to _∧₂_ ; _∨_ to _∨₂_ ; ∧-cong to ∧₂-cong ; ∨-cong to ∨₂-cong
             ; ∧-assoc-law to ∧₂-assoc ; ∧-comm-law to ∧₂-comm ; ∧-idem-law to ∧₂-idem
             ; ∨-assoc-law to ∨₂-assoc ; ∨-comm-law to ∨₂-comm ; ∨-idem-law to ∨₂-idem
             ; absorbˡ-law to absorbˡ₂ ; absorbʳ-law to absorbʳ₂ )
```

The carrier of the product is the pair type, and its equivalence is the pointwise
pair of the component equivalences — the isolated-equality locus for the Cubical
port.

```agda
  A×B : Setoid (α ⊔ β) (ρ ⊔ σ)
  A×B = record
    { Carrier        = 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
    ; _≈_            = λ p q → (proj₁ p ≈₁ proj₁ q) × (proj₂ p ≈₂ proj₂ q)
    ; isEquivalence  = record
        { refl   = refl₁ , refl₂
        ; sym    = λ e → sym₁ (proj₁ e) , sym₂ (proj₂ e)
        ; trans  = λ (d₁ , d₂) (e₁ , e₂) → trans₁ d₁ e₁ , trans₂ d₂ e₂
        }
    }

  open Setoid A×B using () renaming ( _≈_ to _≈ₓ_ )
```

Meet and join act componentwise.  The operations project rather than pattern-match
their arguments, so they reduce on any pair expression, matched or not.

```agda
  _∧ₓ_ : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
  p ∧ₓ q = (proj₁ p ∧₁ proj₁ q) , (proj₂ p ∧₂ proj₂ q)

  _∨ₓ_ : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
  p ∨ₓ q = (proj₁ p ∨₁ proj₁ q) , (proj₂ p ∨₂ proj₂ q)
```

Congruence and the eight equations are all inherited componentwise: each proof is
the pair of the component proofs, applied at the projections.

```agda
  ∧ₓ-cong : ∀ {p q u v} → p ≈ₓ q → u ≈ₓ v → (p ∧ₓ u) ≈ₓ (q ∧ₓ v)
  ∧ₓ-cong e f = ∧₁-cong (proj₁ e) (proj₁ f) , ∧₂-cong (proj₂ e) (proj₂ f)

  ∨ₓ-cong : ∀ {p q u v} → p ≈ₓ q → u ≈ₓ v → (p ∨ₓ u) ≈ₓ (q ∨ₓ v)
  ∨ₓ-cong e f = ∨₁-cong (proj₁ e) (proj₁ f) , ∨₂-cong (proj₂ e) (proj₂ f)

  ∧ₓ-assoc : ∀ {p q r} → ((p ∧ₓ q) ∧ₓ r) ≈ₓ (p ∧ₓ (q ∧ₓ r))
  ∧ₓ-assoc = ∧₁-assoc , ∧₂-assoc

  ∧ₓ-comm : ∀ {p q} → (p ∧ₓ q) ≈ₓ (q ∧ₓ p)
  ∧ₓ-comm = ∧₁-comm , ∧₂-comm

  ∧ₓ-idem : ∀ {p} → (p ∧ₓ p) ≈ₓ p
  ∧ₓ-idem = ∧₁-idem , ∧₂-idem

  ∨ₓ-assoc : ∀ {p q r} → ((p ∨ₓ q) ∨ₓ r) ≈ₓ (p ∨ₓ (q ∨ₓ r))
  ∨ₓ-assoc = ∨₁-assoc , ∨₂-assoc

  ∨ₓ-comm : ∀ {p q} → (p ∨ₓ q) ≈ₓ (q ∨ₓ p)
  ∨ₓ-comm = ∨₁-comm , ∨₂-comm

  ∨ₓ-idem : ∀ {p} → (p ∨ₓ p) ≈ₓ p
  ∨ₓ-idem = ∨₁-idem , ∨₂-idem

  absorbˡₓ : ∀ {p q} → (p ∧ₓ (p ∨ₓ q)) ≈ₓ p
  absorbˡₓ = absorbˡ₁ , absorbˡ₂

  absorbʳₓ : ∀ {p q} → ((p ∧ₓ q) ∨ₓ p) ≈ₓ p
  absorbʳₓ = absorbʳ₁ , absorbʳ₂
```

Assembling through the setoid-level builder yields the product lattice.

```agda
  ×ˡ-Lattice : Lattice (α ⊔ β) (ρ ⊔ σ)
  ×ˡ-Lattice = setoidEqsToLattice A×B _∧ₓ_ _∨ₓ_ ∧ₓ-cong ∨ₓ-cong
    ∧ₓ-assoc ∧ₓ-comm ∧ₓ-idem ∨ₓ-assoc ∨ₓ-comm ∨ₓ-idem absorbˡₓ absorbʳₓ
```

#### The product order is the componentwise order

The meet order of `×ˡ-Lattice`{.AgdaFunction} at `(p , q)` unfolds definitionally
to the pair of the component meet orders, because the builder's interpretation
applies its argument tuple and the product setoid's equality is the pointwise pair.
The three accessors below are therefore projections and pairing, but we name them:
they are the interface through which consumers (the FLRP closure lemmas) read the
product order without unfolding the builder.

```agda
  open Lattice-Order ×ˡ-Lattice using () renaming ( _≤_ to _≤ₓ_ )
  open Lattice-Order 𝑳₁ using () renaming ( _≤_ to _≤₁_ )
  open Lattice-Order 𝑳₂ using () renaming ( _≤_ to _≤₂_ )

  -- The product order projects to the first factor's order.
  ≤ₓ-fst : ∀ {p q} → p ≤ₓ q → proj₁ p ≤₁ proj₁ q
  ≤ₓ-fst = proj₁

  -- The product order projects to the second factor's order.
  ≤ₓ-snd : ∀ {p q} → p ≤ₓ q → proj₂ p ≤₂ proj₂ q
  ≤ₓ-snd = proj₂

  -- Componentwise order proofs pair into a product order proof.
  ≤ₓ-pair : ∀ {p q} → proj₁ p ≤₁ proj₁ q → proj₂ p ≤₂ proj₂ q → p ≤ₓ q
  ≤ₓ-pair e f = e , f
```

#### The product operator

The standalone binary operator, for consumers that need only the lattice.

```agda
infixr 7 _×ˡ_

_×ˡ_ : Lattice α ρ → Lattice β σ → Lattice (α ⊔ β) (ρ ⊔ σ)
𝑳₁ ×ˡ 𝑳₂ = LatticeProduct.×ˡ-Lattice 𝑳₁ 𝑳₂
```

--------------------------------------
