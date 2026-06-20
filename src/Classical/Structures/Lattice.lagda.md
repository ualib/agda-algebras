---
layout: default
file: "src/Classical/Structures/Lattice.lagda.md"
title: "Classical.Structures.Lattice module"
date: "2026-05-28"
author: "the agda-algebras development team"
---

### Lattices {#classical-structures-lattice}

This is the [Classical.Structures.Lattice][] module of the [Agda Universal Algebra Library][].

This module formalizes a lattice *as an equational algebra* (an algebra over
`Sig-Lattice` satisfying `Th-Lattice`).  For the complementary *order-theoretic* view —
a lattice as a poset with meets and joins, the form taken by the congruence and
subalgebra lattices — see [Order.CompleteLattice][] (the two presentations are
equivalent via a standard theorem).

A **lattice** inhabits the Σ-typed structure `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Lattice`
over `Sig-Lattice`.  Lattice is the first structure in the [`Classical/`][Classical]
tree with two *distinct* binary operation symbols (`∧-Op` and `∨-Op`); its
signature is parallel to `Sig-Magma`, not an extension of it, and so it has
*two* natural forgetful projections — one for each operation — both landing in
[`Semilattice`][Classical.Structures.Semilattice].

This module's prose adds the following conventions to the
two-binary-symbols-with-eight-equations case beyond the
[Monoid][Classical.Structures.Monoid] template:

+  **Two reducts, one per operation.**  `lattice→meetMagma` and
   `lattice→joinMagma` are the two container-morphism reducts
   `Sig-Magma ↪ Sig-Lattice` that send `∙-Op` to `∧-Op` and `∨-Op` respectively,
   with identity position maps.  Both are pure reducts (no laws needed); the
   downstream `lattice→meetSemilattice` and `lattice→joinSemilattice` add
   `Th-Semilattice` satisfaction on top via the curried-law pivot, exactly as
   `monoid→semigroup` does for the single-operation case.
+  **Eight standalone curried laws.**  Each of the eight equations in
   `Th-Lattice` is exposed as a standalone curried-form lemma
   (`lt-∧-assoc` through `lt-absorbʳ`) defined once in a
   `module _ (𝑳 : Lattice α ρ)` block above the forgetfuls, so that both
   `Lattice-Op` and each `lattice→<X>Semilattice` consume the same proof.
+  **Direct curried accessors.**  `Lattice-Op` defines `_∧_` and `_∨_` directly
   via `Curry₂ (∧-Op ^ 𝑨)` / `Curry₂ (∨-Op ^ 𝑨)` rather than inheriting through
   either semilattice reduct, for the same reason Monoid does: the reduct's
   position map re-indexes definitionally to the identity in both cases, but
   keeping the accessors direct keeps every downstream `refl` independent of
   that reduction.
+  **No two-symbol bridge primitive.**  The absorption laws involve terms
   nesting two operation symbols (e.g. `node ∧-Op (pair (ℊ 0F)
   (node ∨-Op (pair (ℊ 0F) (ℊ 1F))))`), but the term-to-curried bridge is two
   compositions of single-symbol `interp-cong` calls — one per operation —
   exactly as `Monoid-Op`'s `interp-node-∙` is reused.  No new primitive in
   `Classical.Structures.Interpret` is needed; the existing `interp-cong`
   composes through the nesting.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice where

open import Agda.Primitive                         using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Patterns                      using  ( 0F ; 1F ; 2F )
open import Data.Product                           using  ( Σ-syntax ; _×_ ; _,_
                                                          ; proj₁ ; proj₂ )
open import Function                               using  ( Func )
open import Level                                  using  ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl ; setoid; cong₂)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Operations              using  ( pair ; Curry₂ )
open import Classical.Signatures.Lattice      using  ( Sig-Lattice ; Op-Lattice
                                                     ; ∧-Op ; ∨-Op )
open import Classical.Signatures.Magma        using  ( Sig-Magma ; Op-Magma )
                                              renaming ( ∙-Op to ∙-Opᵐᵃ )
open import Classical.Structures.Interpret    using  ( interp-cong )
open import Classical.Structures.Semilattice  using  ( Semilattice ; _⊨ˢˡ_)
open import Classical.Theories.Lattice        using  ( Eq-Lattice ; Th-Lattice ; ∧-assoc
                                                     ; ∧-comm ; ∧-idem ; ∨-assoc ; ∨-comm
                                                     ; ∨-idem ; absorbˡ ; absorbʳ )
open import Classical.Theories.Semilattice    using  ( Th-Semilattice )
                                              renaming  ( assoc to assocˢˡ ; comm  to commˢˡ
                                                        ; idem  to idemˢˡ )
open import Overture.Terms                    using  ( Term ; ℊ ; node )
open import Overture.Signatures               using  ( ArityOf ; OperationSymbolsOf )
open import Setoid.Algebras.Basic             using  ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Reduct            using  ( reductBy )
open import Setoid.Signatures                 using  ( ⟨_⟩ )
open import Setoid.Terms                      using  ( module Environment )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Lattice} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### The local satisfaction predicate

```agda
infix 4 _⊨ˡᵃ_
_⊨ˡᵃ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-Lattice → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ˡᵃ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### The type of lattices

```agda
Lattice : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Lattice α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ˡᵃ Th-Lattice
```

#### The meet and join magma reducts

The two container morphisms `Sig-Magma ⟹ Sig-Lattice` send the magma's
`∙-Opᵐᵃ` to the lattice's `∧-Op` and `∨-Op` respectively; the position maps are
the identity (`Fin 2` to `Fin 2`).  `lattice→meetMagma` and `lattice→joinMagma`
are the induced reducts.

```agda
∧-incl : Op-Magma → Op-Lattice
∧-incl ∙-Opᵐᵃ = ∧-Op

∧-κ : (o : OperationSymbolsOf Sig-Magma)
  → ArityOf Sig-Lattice (∧-incl o) → ArityOf Sig-Magma o
∧-κ ∙-Opᵐᵃ = λ z → z

∨-incl : Op-Magma → Op-Lattice
∨-incl ∙-Opᵐᵃ = ∨-Op

∨-κ : (o : OperationSymbolsOf Sig-Magma)
  → ArityOf Sig-Lattice (∨-incl o) → ArityOf Sig-Magma o
∨-κ ∙-Opᵐᵃ = λ z → z

lattice→meetMagma : Lattice α ρ → Algebra {𝑆 = Sig-Magma} α ρ
lattice→meetMagma 𝑳 = reductBy ∧-incl ∧-κ (𝑳 .proj₁)

lattice→joinMagma : Lattice α ρ → Algebra {𝑆 = Sig-Magma} α ρ
lattice→joinMagma 𝑳 = reductBy ∨-incl ∨-κ (𝑳 .proj₁)
```

#### Curried laws, standalone

Each of the eight `Th-Lattice` equations is proved here in curried form once,
above the semilattice forgetfuls, so that `Lattice-Op` and each
`lattice→<X>Semilattice` consume the same proof.  The pattern is the same as
`Monoid-Op.mn-assoc`: bridge each `node` to curried form via `interp-cong`,
apply the satisfaction-witness equation, refold.

```agda
module _ (𝑳 : Lattice α ρ) where
  private 𝑨 = proj₁ 𝑳
  open Setoid 𝔻[ 𝑨 ] using (_≈_) renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans)
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  private
    _∧_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
    _∧_ = Curry₂ (∧-Op ^ 𝑨)

    _∨_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
    _∨_ = Curry₂ (∨-Op ^ 𝑨)

    infixr 7 _∧_
    infixr 6 _∨_

    interp-node-∧ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑨 ])
                  → ⟦ node ∧-Op (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∧ (⟦ t ⟧ ⟨$⟩ η)
    interp-node-∧ s t η = interp-cong 𝑨 ∧-Op (λ { 0F → ≈refl ; 1F → ≈refl })

    interp-node-∨ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑨 ])
                  → ⟦ node ∨-Op (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∨ (⟦ t ⟧ ⟨$⟩ η)
    interp-node-∨ s t η = interp-cong 𝑨 ∨-Op (λ { 0F → ≈refl ; 1F → ≈refl })

    ∧-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x ∧ u) ≈ (y ∧ v)
    ∧-cong x≈y u≈v = interp-cong 𝑨 ∧-Op (λ { 0F → x≈y ; 1F → u≈v })

    ∨-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x ∨ u) ≈ (y ∨ v)
    ∨-cong x≈y u≈v = interp-cong 𝑨 ∨-Op (λ { 0F → x≈y ; 1F → u≈v })

  lt-∧-assoc : ∀ x y z → (x ∧ y) ∧ z ≈ x ∧ (y ∧ z)
  lt-∧-assoc x y z = begin
    (x ∧ y) ∧ z       ≈⟨ ∧-cong (≈sym (interp-node-∧ (ℊ 0F) (ℊ 1F) η)) ≈refl ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∧ z  ≈⟨ ≈sym (interp-node-∧ xy (ℊ 2F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η    ≈⟨ proj₂ 𝑳 ∧-assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η    ≈⟨ interp-node-∧ (ℊ 0F) yz η ⟩
    x ∧ ⟦ yz ⟧ ⟨$⟩ η  ≈⟨ ∧-cong ≈refl (interp-node-∧ (ℊ 1F) (ℊ 2F) η) ⟩
    x ∧ (y ∧ z)       ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    xy yz lhsT rhsT : Term (Fin 3)
    xy   = node ∧-Op (pair (ℊ 0F) (ℊ 1F))
    yz   = node ∧-Op (pair (ℊ 1F) (ℊ 2F))
    lhsT = node ∧-Op (pair xy (ℊ 2F))
    rhsT = node ∧-Op (pair (ℊ 0F) yz)

  lt-∧-comm : ∀ x y → x ∧ y ≈ y ∧ x
  lt-∧-comm x y = ≈trans  (≈sym (interp-node-∧ (ℊ 0F) (ℊ 1F) η))
                          (≈trans (proj₂ 𝑳 ∧-comm η) (interp-node-∧ (ℊ 1F) (ℊ 0F) η))
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → y ; 2F → x }

  lt-∧-idem : ∀ x → x ∧ x ≈ x
  lt-∧-idem x = ≈trans (≈sym (interp-node-∧ (ℊ 0F) (ℊ 0F) η)) (proj₂ 𝑳 ∧-idem η)
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → x ; 2F → x }

  lt-∨-assoc : ∀ x y z → (x ∨ y) ∨ z ≈ x ∨ (y ∨ z)
  lt-∨-assoc x y z = begin
    (x ∨ y) ∨ z       ≈⟨ ∨-cong (≈sym (interp-node-∨ (ℊ 0F) (ℊ 1F) η)) ≈refl ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∨ z  ≈⟨ ≈sym (interp-node-∨ xy (ℊ 2F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η    ≈⟨ proj₂ 𝑳 ∨-assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η    ≈⟨ interp-node-∨ (ℊ 0F) yz η ⟩
    x ∨ ⟦ yz ⟧ ⟨$⟩ η  ≈⟨ ∨-cong ≈refl (interp-node-∨ (ℊ 1F) (ℊ 2F) η) ⟩
    x ∨ (y ∨ z)       ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    xy yz lhsT rhsT : Term (Fin 3)
    xy   = node ∨-Op (pair (ℊ 0F) (ℊ 1F))
    yz   = node ∨-Op (pair (ℊ 1F) (ℊ 2F))
    lhsT = node ∨-Op (pair xy (ℊ 2F))
    rhsT = node ∨-Op (pair (ℊ 0F) yz)

  lt-∨-comm : ∀ x y → x ∨ y ≈ y ∨ x
  lt-∨-comm x y = ≈trans  (≈sym (interp-node-∨ (ℊ 0F) (ℊ 1F) η))
                          (≈trans (proj₂ 𝑳 ∨-comm η) (interp-node-∨ (ℊ 1F) (ℊ 0F) η))
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → y ; 2F → x }

  lt-∨-idem : ∀ x → x ∨ x ≈ x
  lt-∨-idem x = ≈trans (≈sym (interp-node-∨ (ℊ 0F) (ℊ 0F) η)) (proj₂ 𝑳 ∨-idem η)
    where  η : Fin 3 → 𝕌[ 𝑨 ]
           η = λ { 0F → x ; 1F → x ; 2F → x }

  -- x ∧ (x ∨ y) ≈ x   (meet absorbs join)
  lt-absorbˡ : ∀ x y → x ∧ (x ∨ y) ≈ x
  lt-absorbˡ x y = begin
    x ∧ (x ∨ y)        ≈⟨ ∧-cong ≈refl (≈sym (interp-node-∨ (ℊ 0F) (ℊ 1F) η)) ⟩
    x ∧ ⟦ x∨y ⟧ ⟨$⟩ η  ≈⟨ ≈sym (interp-node-∧ (ℊ 0F) x∨y η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η     ≈⟨ proj₂ 𝑳 absorbˡ η ⟩
    x                  ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → x }
    x∨y lhsT : Term (Fin 3)
    x∨y  = node ∨-Op (pair (ℊ 0F) (ℊ 1F))
    lhsT = node ∧-Op (pair (ℊ 0F) x∨y)

  -- (x ∧ y) ∨ x ≈ x   (join absorbs meet, with x on the right of the outer ∨)
  lt-absorbʳ : ∀ x y → (x ∧ y) ∨ x ≈ x
  lt-absorbʳ x y = begin
    (x ∧ y) ∨ x        ≈⟨ ∨-cong (≈sym (interp-node-∧ (ℊ 0F) (ℊ 1F) η)) ≈refl ⟩
    ⟦ x∧y ⟧ ⟨$⟩ η ∨ x  ≈⟨ ≈sym (interp-node-∨ x∧y (ℊ 0F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η     ≈⟨ proj₂ 𝑳 absorbʳ η ⟩
    x                  ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → x }
    x∧y lhsT : Term (Fin 3)
    x∧y  = node ∧-Op (pair (ℊ 0F) (ℊ 1F))
    lhsT = node ∨-Op (pair x∧y (ℊ 0F))
```

#### The `Lattice-Op` module

`Lattice-Op` exposes `_∧_`, `_∨_`, their congruences, the term-to-curried node
bridges `interp-node-∧` / `interp-node-∨`, the eight curried laws (matching the
eight constructors of `Eq-Lattice`), and the satisfaction-witness `equations`
accessor.

```agda
module Lattice-Op {α ρ : Level} (𝑳 : Lattice α ρ) where
  private 𝑨 = proj₁ 𝑳
  open Setoid 𝔻[ 𝑨 ] using (_≈_) renaming (refl to ≈refl)
  open Environment 𝑨 using ( ⟦_⟧ )

  infixr 7 _∧_
  infixr 6 _∨_

  _∧_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _∧_ = Curry₂ (∧-Op ^ 𝑨)

  _∨_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _∨_ = Curry₂ (∨-Op ^ 𝑨)

  equations : 𝑨 ⊨ˡᵃ Th-Lattice
  equations = proj₂ 𝑳

  ∧-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x ∧ u ≈ y ∧ v
  ∧-cong x≈y u≈v = interp-cong 𝑨 ∧-Op λ { 0F → x≈y ; 1F → u≈v }

  ∨-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x ∨ u ≈ y ∨ v
  ∨-cong x≈y u≈v = interp-cong 𝑨 ∨-Op λ { 0F → x≈y ; 1F → u≈v }

  interp-node-∧ : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ∧-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∧ ⟦ t ⟧ ⟨$⟩ η
  interp-node-∧ s t = interp-cong 𝑨 ∧-Op λ { 0F → ≈refl ; 1F → ≈refl }

  interp-node-∨ : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ∨-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∨ ⟦ t ⟧ ⟨$⟩ η
  interp-node-∨ s t = interp-cong 𝑨 ∨-Op λ { 0F → ≈refl ; 1F → ≈refl }

  ∧-assoc-law : ∀ x y z → (x ∧ y) ∧ z ≈ x ∧ (y ∧ z)
  ∧-assoc-law = lt-∧-assoc 𝑳

  ∧-comm-law : ∀ x y → x ∧ y ≈ y ∧ x
  ∧-comm-law = lt-∧-comm 𝑳

  ∧-idem-law : ∀ x → x ∧ x ≈ x
  ∧-idem-law = lt-∧-idem 𝑳

  ∨-assoc-law : ∀ x y z → (x ∨ y) ∨ z ≈ x ∨ (y ∨ z)
  ∨-assoc-law = lt-∨-assoc 𝑳

  ∨-comm-law : ∀ x y → x ∨ y ≈ y ∨ x
  ∨-comm-law = lt-∨-comm 𝑳

  ∨-idem-law : ∀ x → x ∨ x ≈ x
  ∨-idem-law = lt-∨-idem 𝑳

  absorbˡ-law : ∀ x y → x ∧ (x ∨ y) ≈ x
  absorbˡ-law = lt-absorbˡ 𝑳

  absorbʳ-law : ∀ x y → (x ∧ y) ∨ x ≈ x
  absorbʳ-law = lt-absorbʳ 𝑳
```

#### The forgetful projections to semilattices

`lattice→meetSemilattice` and `lattice→joinSemilattice` each take a lattice to
the semilattice on its meet (resp. join) operation: the underlying algebra is
the corresponding magma reduct, and the `Th-Semilattice` satisfaction proof
pivots through `lt-∧-{assoc,comm,idem}` (resp. `lt-∨-{assoc,comm,idem}`) by
the curried-law-pivot pattern of `monoid→semigroup`.

```agda
lattice→meetSemilattice : Lattice α ρ → Semilattice α ρ
lattice→meetSemilattice ℒ@(𝑳 , _) = 𝑹 , thm
  where
  𝑹 : Algebra {𝑆 = Sig-Magma} _ _
  𝑹 = lattice→meetMagma ℒ
  open Setoid 𝔻[ 𝑳 ] using (_≈_) renaming (refl to ≈refl)
  open Environment 𝑹 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑳 ]
  open Lattice-Op ℒ using ( _∧_ ; ∧-assoc-law ; ∧-comm-law ; ∧-idem-law )

  interp-congᴿ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑳 ])
      → ⟦ node ∙-Opᵐᵃ (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∧ (⟦ t ⟧ ⟨$⟩ η)
  interp-congᴿ s t η = interp-cong 𝑹 ∙-Opᵐᵃ λ { 0F → ≈refl ; 1F → ≈refl }

  ∧-congᴿ : ∀ {a b c d} → a ≈ b → c ≈ d → a ∧ c ≈ b ∧ d
  ∧-congᴿ a≈b c≈d = interp-cong 𝑹 ∙-Opᵐᵃ λ { 0F → a≈b ; 1F → c≈d }

  thm : 𝑹 ⊨ˢˡ Th-Semilattice
  thm assocˢˡ η = let x = η 0F ; y = η 1F ; z = η 2F in begin
    ⟦ Th-Semilattice assocˢˡ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ xy (ℊ 2F) η ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∧ z                         ≈⟨ ∧-congᴿ (interp-congᴿ (ℊ 0F) (ℊ 1F) η) ≈refl ⟩
    (x ∧ y) ∧ z                              ≈⟨ ∧-assoc-law x y z ⟩
    x ∧ (y ∧ z)                              ≈˘⟨ ∧-congᴿ ≈refl (interp-congᴿ (ℊ 1F) (ℊ 2F) η) ⟩
    x ∧ ⟦ yz ⟧ ⟨$⟩ η                         ≈˘⟨ interp-congᴿ (ℊ 0F) yz η ⟩
    ⟦ Th-Semilattice assocˢˡ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    xy yz : Term (Fin 3)
    xy = node ∙-Opᵐᵃ (pair (ℊ 0F) (ℊ 1F))
    yz = node ∙-Opᵐᵃ (pair (ℊ 1F) (ℊ 2F))

  thm commˢˡ η = let x = η 0F ; y = η 1F in begin
    ⟦ Th-Semilattice commˢˡ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ (ℊ 0F) (ℊ 1F) η ⟩
    x ∧ y                                   ≈⟨ ∧-comm-law x y ⟩
    y ∧ x                                   ≈˘⟨ interp-congᴿ (ℊ 1F) (ℊ 0F) η ⟩
    ⟦ Th-Semilattice commˢˡ .proj₂ ⟧ ⟨$⟩ η  ∎

  thm idemˢˡ η = let x = η 0F in begin
    ⟦ Th-Semilattice idemˢˡ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ (ℊ 0F) (ℊ 0F) η ⟩
    x ∧ x                                   ≈⟨ ∧-idem-law x ⟩
    x                                       ∎

lattice→joinSemilattice : Lattice α ρ → Semilattice α ρ
lattice→joinSemilattice ℒ@(𝑳 , _) = 𝑹 , thm
  where
  𝑹 : Algebra {𝑆 = Sig-Magma} _ _
  𝑹 = lattice→joinMagma ℒ
  open Setoid 𝔻[ 𝑳 ] using (_≈_) renaming (refl to ≈refl)
  open Environment 𝑹 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑳 ]
  open Lattice-Op ℒ using ( _∨_ ; ∨-assoc-law ; ∨-comm-law ; ∨-idem-law )

  interp-congᴿ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑳 ])
      → ⟦ node ∙-Opᵐᵃ (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∨ ⟦ t ⟧ ⟨$⟩ η
  interp-congᴿ s t η = interp-cong 𝑹 ∙-Opᵐᵃ λ { 0F → ≈refl ; 1F → ≈refl }

  ∨-congᴿ : ∀ {a b c d} → a ≈ b → c ≈ d → a ∨ c ≈ b ∨ d
  ∨-congᴿ a≈b c≈d = interp-cong 𝑹 ∙-Opᵐᵃ λ { 0F → a≈b ; 1F → c≈d }

  thm : 𝑹 ⊨ˢˡ Th-Semilattice
  thm assocˢˡ η = let x = η 0F ; y = η 1F ; z = η 2F in begin
    ⟦ Th-Semilattice assocˢˡ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ xy (ℊ 2F) η ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∨ z                         ≈⟨ ∨-congᴿ (interp-congᴿ (ℊ 0F) (ℊ 1F) η) ≈refl ⟩
    (x ∨ y) ∨ z                              ≈⟨ ∨-assoc-law x y z ⟩
    x ∨ (y ∨ z)                              ≈˘⟨ ∨-congᴿ ≈refl (interp-congᴿ (ℊ 1F) (ℊ 2F) η) ⟩
    x ∨ ⟦ yz ⟧ ⟨$⟩ η                         ≈˘⟨ interp-congᴿ (ℊ 0F) yz η ⟩
    ⟦ Th-Semilattice assocˢˡ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    xy yz : Term (Fin 3)
    xy = node ∙-Opᵐᵃ (pair (ℊ 0F) (ℊ 1F))
    yz = node ∙-Opᵐᵃ (pair (ℊ 1F) (ℊ 2F))

  thm commˢˡ η = let x = η 0F ; y = η 1F in begin
    ⟦ Th-Semilattice commˢˡ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ (ℊ 0F) (ℊ 1F) η ⟩
    x ∨ y                                   ≈⟨ ∨-comm-law x y ⟩
    y ∨ x                                   ≈˘⟨ interp-congᴿ (ℊ 1F) (ℊ 0F) η ⟩
    ⟦ Th-Semilattice commˢˡ .proj₂ ⟧ ⟨$⟩ η  ∎

  thm idemˢˡ η = let x = η 0F in begin
    ⟦ Th-Semilattice idemˢˡ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ (ℊ 0F) (ℊ 0F) η ⟩
    x ∨ x                                   ≈⟨ ∨-idem-law x ⟩
    x                                       ∎
```

#### Lattice builders

`opsToBareLattice` builds a "raw" `Sig-Lattice`-algebra from a carrier and two
binary operations.  `eqsToLattice` adds the eight equation proofs and produces
a `Lattice α α`.

```agda
open Algebra
opsToBareLattice : (A : Type α) (_∧'_ _∨'_ : A → A → A) → Algebra {𝑆 = Sig-Lattice} α α
opsToBareLattice A _∧'_ _∨'_ .Domain = setoid A
opsToBareLattice A _∧'_ _∨'_ .Interp ⟨$⟩ (∧-Op , args) = args 0F ∧' args 1F
opsToBareLattice A _∧'_ _∨'_ .Interp ⟨$⟩ (∨-Op , args) = args 0F ∨' args 1F
opsToBareLattice A _∧'_ _∨'_ .Interp .cong {∧-Op , _} {.∧-Op , _} (refl , args≡) = cong₂ _∧'_ (args≡ 0F) (args≡ 1F)
opsToBareLattice A _∧'_ _∨'_ .Interp .cong {∨-Op , _} {.∨-Op , _} (refl , args≡) = cong₂ _∨'_ (args≡ 0F) (args≡ 1F)

eqsToLattice : (A : Type α) (_∧'_ _∨'_ : A → A → A)
  → (∧-assoc-≡ : ∀ a b c → (a ∧' b) ∧' c ≡ a ∧' (b ∧' c))
  → (∧-comm-≡  : ∀ a b → a ∧' b ≡ b ∧' a)
  → (∧-idem-≡  : ∀ a → a ∧' a ≡ a)
  → (∨-assoc-≡ : ∀ a b c → (a ∨' b) ∨' c ≡ a ∨' (b ∨' c))
  → (∨-comm-≡  : ∀ a b → a ∨' b ≡ b ∨' a)
  → (∨-idem-≡  : ∀ a → a ∨' a ≡ a)
  → (absorbˡ-≡ : ∀ a b → a ∧' (a ∨' b) ≡ a)
  → (absorbʳ-≡ : ∀ a b → (a ∧' b) ∨' a ≡ a)
  → Lattice α α
eqsToLattice A _∧'_ _∨'_ ∧-assoc-≡ ∧-comm-≡ ∧-idem-≡ ∨-assoc-≡ ∨-comm-≡ ∨-idem-≡ absorbˡ-≡ absorbʳ-≡ =
  opsToBareLattice A _∧'_ _∨'_ , proof
  where
  proof : opsToBareLattice A _∧'_ _∨'_ ⊨ˡᵃ Th-Lattice
  proof ∧-assoc ρ = ∧-assoc-≡ (ρ 0F) (ρ 1F) (ρ 2F)
  proof ∧-comm  ρ = ∧-comm-≡  (ρ 0F) (ρ 1F)
  proof ∧-idem  ρ = ∧-idem-≡  (ρ 0F)
  proof ∨-assoc ρ = ∨-assoc-≡ (ρ 0F) (ρ 1F) (ρ 2F)
  proof ∨-comm  ρ = ∨-comm-≡  (ρ 0F) (ρ 1F)
  proof ∨-idem  ρ = ∨-idem-≡  (ρ 0F)
  proof absorbˡ ρ = absorbˡ-≡ (ρ 0F) (ρ 1F)
  proof absorbʳ ρ = absorbʳ-≡ (ρ 0F) (ρ 1F)
```

--------------------------------------

{% include UALib.Links.md %}
