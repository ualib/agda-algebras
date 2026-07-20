---
layout: default
file: "src/Classical/Structures/DistributiveLattice.lagda.md"
title: "Classical.Structures.DistributiveLattice module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Distributive lattices {#classical-structures-distributivelattice}

This is the [Classical.Structures.DistributiveLattice][] module of the [Agda Universal Algebra Library][].

A **distributive lattice** inhabits `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-DistributiveLattice`
over the *same* `Sig-Lattice` signature as [`Lattice`][Classical.Structures.Lattice].
It is an *equation-only* extension of `Lattice`: the forgetful
`distributiveLattice→lattice` is a pure theory-reindex (the two distributivity
equations are dropped, the remaining eight map across definitionally), and
`DistributiveLattice-Op` inherits `_∧_`, `_∨_`, both congruences, the node bridges,
and all eight lattice laws through it.  This is the two-operation analogue of how
[`CommutativeMonoid`][Classical.Structures.CommutativeMonoid] extends `Monoid`.

On top of the inherited laws this module adds four distributivity laws in curried
form: the two *left* laws `∧-distribˡ-law` and `∨-distribˡ-law` come straight from
the theory's two witnesses (the proof shape is `Ring`'s `rg-distribˡ`), and the two
*right* laws `∧-distribʳ-law` and `∨-distribʳ-law` are derived from them by
commutativity.  All four are what the bundle bridge feeds to the standard library's
`IsDistributiveLattice`, whose `∨-distrib-∧` and `∧-distrib-∨` fields each pair a
left and a right law.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.DistributiveLattice where

open import Agda.Primitive                using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Fin.Base                 using ( Fin )
open import Data.Fin.Patterns             using ( 0F ; 1F ; 2F )
open import Data.Product                  using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                      using ( Func )
open import Level                         using ( Level ; _⊔_ ; suc )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Operations          using  ( pair )
open import Classical.Signatures.Lattice  using  ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Classical.Structures.Lattice  using  ( Lattice ; module Lattice-Op
                                                 ; opsToBareLattice )
open import Classical.Theories.Lattice    using  ()
  renaming  ( ∧-assoc to ∧-assocˡᵃ ; ∧-comm to ∧-commˡᵃ ; ∧-idem to ∧-idemˡᵃ
            ; ∨-assoc to ∨-assocˡᵃ ; ∨-comm to ∨-commˡᵃ ; ∨-idem to ∨-idemˡᵃ
            ; absorbˡ to absorbˡˡᵃ ; absorbʳ to absorbʳˡᵃ )

open import Classical.Theories.DistributiveLattice
  using  ( Eq-DistributiveLattice ; Th-DistributiveLattice ; ∧-assoc ; ∧-comm ; ∧-idem
         ; ∨-assoc ; ∨-comm ; ∨-idem ; absorbˡ ; absorbʳ ; ∧-distribˡ ; ∨-distribˡ )

open import Overture.Terms {𝑆 = Sig-Lattice} using ( Term ; ℊ ; node )
open import Setoid.Algebras.Basic using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms using ( module Environment )
open import Setoid.Varieties.EquationalLogic using ( _⊧_≈_ )

private variable α ρ : Level
```
-->

#### The satisfaction predicate and the type of distributive lattices {#the-type}

```agda
infix 4 _⊨ᵈˡ_
_⊨ᵈˡ_ : (𝑨 : Algebra {𝑆 = Sig-Lattice} α ρ) (ℰ : Eq-DistributiveLattice → Term (Fin 3) × Term (Fin 3))
  → Type (α ⊔ ρ)

𝑨 ⊨ᵈˡ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

DistributiveLattice : (α ρ : Level) → Type (suc α ⊔ suc ρ)
DistributiveLattice α ρ = Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Lattice} α ρ ] 𝑨 ⊨ᵈˡ Th-DistributiveLattice
```

#### The forgetful projection to lattices {#forgetful-to-lattice}

The eight lattice equations are dropped from `Th-DistributiveLattice` to `Th-Lattice`.
Because each shared equation is built by the *same* `Classical.Equations` builder on
both sides, `Th-Lattice c` and `Th-DistributiveLattice c` are definitionally equal,
so the witnesses transport with no work — the two distributivity equations are simply
not requested.

```agda
distributiveLattice→lattice : DistributiveLattice α ρ → Lattice α ρ
distributiveLattice→lattice (𝑨 , mod) = 𝑨 ,
  λ { ∧-assocˡᵃ → mod ∧-assoc ; ∧-commˡᵃ → mod ∧-comm ; ∧-idemˡᵃ → mod ∧-idem
    ; ∨-assocˡᵃ → mod ∨-assoc ; ∨-commˡᵃ → mod ∨-comm ; ∨-idemˡᵃ → mod ∨-idem
    ; absorbˡˡᵃ → mod absorbˡ ; absorbʳˡᵃ → mod absorbʳ }
```

#### The `DistributiveLattice-Op` module {#distributivelattice-op}

`DistributiveLattice-Op` re-exports the meet/join operations, congruences, node
bridges, and eight lattice laws from the inherited `Lattice-Op`, and adds the four
distributivity laws.

```agda
module DistributiveLattice-Op {α ρ : Level} (𝑫 : DistributiveLattice α ρ) where
  private 𝑨 = proj₁ 𝑫
  open Setoid 𝔻[ 𝑨 ]
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  open Lattice-Op (distributiveLattice→lattice 𝑫) public
    using  ( _∧_ ; ∧-cong ; interp-node-∧ ; ∧-assoc-law ; ∧-comm-law ; ∧-idem-law
           ; _∨_ ; ∨-cong ; interp-node-∨ ; ∨-assoc-law ; ∨-comm-law ; ∨-idem-law
           ; absorbˡ-law ; absorbʳ-law )

  equations : 𝑨 ⊨ᵈˡ Th-DistributiveLattice
  equations = proj₂ 𝑫

  -- x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)   (meet distributes over join, on the left)
  ∧-distribˡ-law : ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
  ∧-distribˡ-law x y z = begin
    x ∧ (y ∨ z)                   ≈⟨ ∧-cong refl (sym (interp-node-∨ (ℊ 1F) (ℊ 2F) {η})) ⟩
    x ∧ ⟦ y∨z ⟧ ⟨$⟩ η             ≈⟨ sym (interp-node-∧ (ℊ 0F) y∨z {η}) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η                ≈⟨ equations ∧-distribˡ η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η                ≈⟨ interp-node-∨ xy xz {η} ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∨ ⟦ xz ⟧ ⟨$⟩ η   ≈⟨ ∨-cong (interp-node-∧ (ℊ 0F) (ℊ 1F) {η}) (interp-node-∧ (ℊ 0F) (ℊ 2F) {η}) ⟩
    (x ∧ y) ∨ (x ∧ z)             ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    y∨z xy xz lhsT rhsT : Term (Fin 3)
    y∨z  = node ∨-Op (pair (ℊ 1F) (ℊ 2F))
    xy   = node ∧-Op (pair (ℊ 0F) (ℊ 1F))
    xz   = node ∧-Op (pair (ℊ 0F) (ℊ 2F))
    lhsT = node ∧-Op (pair (ℊ 0F) y∨z)
    rhsT = node ∨-Op (pair xy xz)

  -- x ∨ (y ∧ z) ≈ (x ∨ y) ∧ (x ∨ z)   (join distributes over meet, on the left)
  ∨-distribˡ-law : ∀ x y z → x ∨ (y ∧ z) ≈ (x ∨ y) ∧ (x ∨ z)
  ∨-distribˡ-law x y z = begin
    x ∨ (y ∧ z)                   ≈⟨ ∨-cong refl (sym (interp-node-∧ (ℊ 1F) (ℊ 2F) {η})) ⟩
    x ∨ ⟦ y∧z ⟧ ⟨$⟩ η             ≈⟨ sym (interp-node-∨ (ℊ 0F) y∧z {η}) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η                ≈⟨ equations ∨-distribˡ η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η                ≈⟨ interp-node-∧ xy xz {η} ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∧ ⟦ xz ⟧ ⟨$⟩ η   ≈⟨ ∧-cong (interp-node-∨ (ℊ 0F) (ℊ 1F) {η}) (interp-node-∨ (ℊ 0F) (ℊ 2F) {η}) ⟩
    (x ∨ y) ∧ (x ∨ z)             ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    y∧z xy xz lhsT rhsT : Term (Fin 3)
    y∧z  = node ∧-Op (pair (ℊ 1F) (ℊ 2F))
    xy   = node ∨-Op (pair (ℊ 0F) (ℊ 1F))
    xz   = node ∨-Op (pair (ℊ 0F) (ℊ 2F))
    lhsT = node ∨-Op (pair (ℊ 0F) y∧z)
    rhsT = node ∧-Op (pair xy xz)

  -- (y ∨ z) ∧ x ≈ (y ∧ x) ∨ (z ∧ x)   (right form, by ∧-commutativity)
  ∧-distribʳ-law : ∀ x y z → (y ∨ z) ∧ x ≈ (y ∧ x) ∨ (z ∧ x)
  ∧-distribʳ-law x y z = begin
    (y ∨ z) ∧ x        ≈⟨ ∧-comm-law (y ∨ z) x ⟩
    x ∧ (y ∨ z)        ≈⟨ ∧-distribˡ-law x y z ⟩
    (x ∧ y) ∨ (x ∧ z)  ≈⟨ ∨-cong (∧-comm-law x y) (∧-comm-law x z) ⟩
    (y ∧ x) ∨ (z ∧ x)  ∎

  -- (y ∧ z) ∨ x ≈ (y ∨ x) ∧ (z ∨ x)   (right form, by ∨-commutativity)
  ∨-distribʳ-law : ∀ x y z → (y ∧ z) ∨ x ≈ (y ∨ x) ∧ (z ∨ x)
  ∨-distribʳ-law x y z = begin
    (y ∧ z) ∨ x        ≈⟨ ∨-comm-law (y ∧ z) x ⟩
    x ∨ (y ∧ z)        ≈⟨ ∨-distribˡ-law x y z ⟩
    (x ∨ y) ∧ (x ∨ z)  ≈⟨ ∧-cong (∨-comm-law x y) (∨-comm-law x z) ⟩
    (y ∨ x) ∧ (z ∨ x)  ∎
```

#### `eqsToDistributiveLattice` {#builders}

`eqsToDistributiveLattice` reuses `opsToBareLattice` to build the underlying
`Sig-Lattice`-algebra from a carrier and two operations, then attaches the ten
equation proofs.  The two distributivity arguments are taken in their *left* form
`a ∧' (b ∨' c) ≡ (a ∧' b) ∨' (a ∧' c)` and dually.

```agda
open Algebra
eqsToDistributiveLattice : (A : Type α) (_∧'_ _∨'_ : A → A → A)
  → (∧-assoc-≡    : ∀ a b c → (a ∧' b) ∧' c ≡ a ∧' (b ∧' c))
  → (∧-comm-≡     : ∀ a b → a ∧' b ≡ b ∧' a)
  → (∧-idem-≡     : ∀ a → a ∧' a ≡ a)
  → (∨-assoc-≡    : ∀ a b c → (a ∨' b) ∨' c ≡ a ∨' (b ∨' c))
  → (∨-comm-≡     : ∀ a b → a ∨' b ≡ b ∨' a)
  → (∨-idem-≡     : ∀ a → a ∨' a ≡ a)
  → (absorbˡ-≡    : ∀ a b → a ∧' (a ∨' b) ≡ a)
  → (absorbʳ-≡    : ∀ a b → (a ∧' b) ∨' a ≡ a)
  → (∧-distribˡ-≡ : ∀ a b c → a ∧' (b ∨' c) ≡ (a ∧' b) ∨' (a ∧' c))
  → (∨-distribˡ-≡ : ∀ a b c → a ∨' (b ∧' c) ≡ (a ∨' b) ∧' (a ∨' c))
  → DistributiveLattice α α
eqsToDistributiveLattice A _∧'_ _∨'_
  ∧-assoc-≡ ∧-comm-≡ ∧-idem-≡ ∨-assoc-≡ ∨-comm-≡ ∨-idem-≡ absorbˡ-≡ absorbʳ-≡ ∧-distribˡ-≡ ∨-distribˡ-≡ =
  opsToBareLattice A _∧'_ _∨'_ , proof
  where
  proof : opsToBareLattice A _∧'_ _∨'_ ⊨ᵈˡ Th-DistributiveLattice
  proof ∧-assoc    ρ = ∧-assoc-≡    (ρ 0F) (ρ 1F) (ρ 2F)
  proof ∧-comm     ρ = ∧-comm-≡     (ρ 0F) (ρ 1F)
  proof ∧-idem     ρ = ∧-idem-≡     (ρ 0F)
  proof ∨-assoc    ρ = ∨-assoc-≡    (ρ 0F) (ρ 1F) (ρ 2F)
  proof ∨-comm     ρ = ∨-comm-≡     (ρ 0F) (ρ 1F)
  proof ∨-idem     ρ = ∨-idem-≡     (ρ 0F)
  proof absorbˡ    ρ = absorbˡ-≡    (ρ 0F) (ρ 1F)
  proof absorbʳ    ρ = absorbʳ-≡    (ρ 0F) (ρ 1F)
  proof ∧-distribˡ ρ = ∧-distribˡ-≡ (ρ 0F) (ρ 1F) (ρ 2F)
  proof ∨-distribˡ ρ = ∨-distribˡ-≡ (ρ 0F) (ρ 1F) (ρ 2F)
```
