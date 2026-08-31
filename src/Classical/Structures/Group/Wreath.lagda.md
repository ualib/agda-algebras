---
layout: default
file: "src/Classical/Structures/Group/Wreath.lagda.md"
title: "Classical.Structures.Group.Wreath module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Wreath products

This is the [Classical.Structures.Group.Wreath][] module of the [Agda Universal Algebra Library][].

For a base group `S`, an index set `I`, and a group `G` acting on `I` on the right
([Classical.Structures.Group.IndexAction][]), the **permutational wreath product**
`S ≀ G` is the semidirect product `Sᴵ ⋊ G` consisting of pairs `(f , x)`, where
`f` is a tuple in `Sᴵ` and `x` is an element of `G`.  Such pairs are multiplied by
"twisting" the right factor's tuple with the action of the left factor's second
component,

    (s , x) (t , y) = (s₁ tₓ₁ , … , sₙ tₓₙ , x y).

Coordinate `i` of the product is `s i ∙ t (x i)`.[^1]

**Terminology**.  When referring to an element `(s , x)` of a wreath product,
we will call the tuple `s` the "first component" or "base tuple"; we will call `x`
the "second component" or "action element."

Associativity of this multiplication is exactly the contravariant compatibility
law of the right action, and the inverse twists by the action of the inverted
second component; no other property of the action is used, so the
construction is parameterized by a bare `RightAction`{.AgdaRecord}, with no
permutation-group or automorphism-group object in sight.

The module provides the following `Classical/` components:

+  the wreath product group `≀-Group`{.AgdaFunction} (group-level operator
   `_≀ᵍ_`{.AgdaFunction}), built by `setoidEqsToGroup`{.AgdaFunction} of
   [Classical.Structures.Group.Basic][] with each group law proved coordinatewise;
+  the subgroup `D Ḡ` of wreath elements with *diagonal* first component
   (`Diag≀`{.AgdaFunction}), the bottom of the interval `[D Ḡ , S ≀ G]` that
   Kurzweil's construction inhabits; its membership predicate is the diagonal
   predicate of [Classical.Structures.Group.Diagonal][] on the first component;
+  **the core-freeness preservation theorem** (`Diag≀-coreFree`{.AgdaFunction}):
   if the action is faithful, the index set has at least two points and decidable
   equality, and the base group is nontrivial with trivial center, then `D Ḡ` is
   core-free in `S ≀ G`.  This is the technical heart of the note's Lemma 3.3, the
   step its proof carries out in full rather than citing.

**On the hypotheses of the preservation theorem**.  The note's proof picks,
for a moved index `x(1) = j ≠ 1`, a third index `k ∉ {1 , j}`, justifying its
existence by `n = |G : H| > 2` "since otherwise `H ⊴ G`, contradicting
`Core_G(H) = 1`"; this justification fails for `H = 1`: the pair
`(H , G) = (1 , C₂)` is core-free with index `2`.  The formalization below
closes the gap by *removing the third index altogether*: probing the constraint
at the two indices `i₀` and `j = x i₀` with the tuple that is `a` at `j` and
identity elsewhere yields `d ∙ a ⁻¹ ≈ a ∙ d` for every `a`, which makes
conjugation by `d` an inversion, forces the base group to be abelian
(`inv-conj→comm`{.AgdaFunction}), and precludes a nontrivial base group with a
trivial center.  One uniform argument covers every index set with two points; the
theorem is *false* for a one-point index set, where `D Ḡ` is all of `S ≀ G`.[^2]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Wreath where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                         using  ( if_then_else_ )
open import Data.Empty                             using  ( ⊥-elim )
open import Data.Product                           using  ( Σ-syntax ; _×_ ; _,_
                                                          ; proj₁ ; proj₂ )
open import Level                                  using  ( Level ; _⊔_ )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl ; sym
                                                          ; trans ; cong )
open import Relation.Nullary                       using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable             using  ( does ; dec-true
                                                          ; dec-false )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group                 using  ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic        using  ( Group ; module Group-Op
                                                           ; setoidEqsToGroup )
open import Classical.Structures.Group.Conjugation  using  ( module Conjugate )
open import Classical.Structures.Group.Diagonal     using  ( module DiagonalSubgroup )
open import Classical.Structures.Group.IndexAction  using  ( RightAction )
open import Classical.Structures.Group.NormalCore   using  ( module Core )
open import Classical.Structures.Group.Subgroups    using  ( IsSubgroup
                                                           ; mkIsSubgroup
                                                           ; trivialSubgroup )
open import Setoid.Algebras.Basic                   using  ( 𝕌[_] ; 𝔻[_] )

private variable ι α ρ β σ : Level
```
-->

#### The construction

`WreathProduct`{.AgdaModule}` 𝒮 A` packages the wreath product of the base group
`𝒮`{.AgdaBound} by the right action `A`{.AgdaBound} of a group on an index set.

```agda
module WreathProduct (𝒮@(𝑺 , _) : Group α ρ) {I : Type ι} {𝒢@(𝑮 , _) : Group β σ}
  (A : RightAction I 𝒢)
  where

  open Setoid 𝔻[ 𝑺 ]  using (_≈_)
                      renaming  ( refl to reflˢ ; sym to symˢ ; trans to transˢ
                                ; reflexive to reflexiveˢ )
  open Group-Op 𝒮     using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; assoc-law
                              ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open Setoid 𝔻[ 𝑮 ]  using ()
                       renaming  ( _≈_ to _≈ᵍ_ ; refl to reflᵍ
                                 ; sym to symᵍ ; trans to transᵍ )
  open Group-Op 𝒢      using ()
                       renaming  ( _∙_ to _∙ᵍ_ ; ε to εᵍ ; _⁻¹ to _⁻¹ᵍ
                                 ; ∙-cong to ∙ᵍ-cong ; ⁻¹-cong to ⁻¹ᵍ-cong
                                 ; assoc-law to assoc-lawᵍ ; idˡ-law to idˡ-lawᵍ
                                 ; idʳ-law to idʳ-lawᵍ ; invˡ-law to invˡ-lawᵍ
                                 ; invʳ-law to invʳ-lawᵍ )
  open RightAction A
```

**The carrier**: pairs of a base tuple `I → S` and a group element, with pointwise
base equality and componentwise pair equality, the isolated-equality locus
for the Cubical port, as in [Classical.Structures.Group.Product][].

```agda
  -- Base tuples, and the wreath carrier.
  Base : Type (ι ⊔ α)
  Base = I → 𝕌[ 𝑺 ]

  W : Type (ι ⊔ α ⊔ β)
  W = Base × 𝕌[ 𝑮 ]

  ≀-setoid : Setoid (ι ⊔ α ⊔ β) (ι ⊔ ρ ⊔ σ)
  ≀-setoid = record
    { Carrier        = W
    ; _≈_            = λ (p₁ , p₂) (q₁ , q₂) → (∀ i → p₁ i ≈ q₁ i) × p₂ ≈ᵍ q₂
    ; isEquivalence  = record
        { refl   = (λ i → reflˢ) , reflᵍ
        ; sym    = λ (e₁ , e₂) → (λ i → symˢ (e₁ i)) , symᵍ e₂
        ; trans  = λ (d₁ , d₂) (e₁ , e₂) → (λ i → transˢ (d₁ i) (e₁ i)) , transᵍ d₂ e₂
        }
    }

  open Setoid ≀-setoid using () renaming ( _≈_ to _≈ᵂ_ )
```

**The three operations**.  Coordinate `i` of a product is `f i ∙ g (x i)`; the
left factor's tuple `f` is untwisted; the right factor's tuple is twisted by
permuting its indices by `x`, the left factors group element.  The inverse twists
by the action of the inverted group element; the two-sided inverse laws below
confirm that the choice works.

```agda
  -- The wreath multiplication.
  ≀-mul : W → W → W
  ≀-mul (f , x) (g , y) = (λ i → f i ∙ g (act x i)) , x ∙ᵍ y

  -- The identity: the constant-identity tuple over the group identity.
  ≀-one : W
  ≀-one = (λ _ → ε) , εᵍ

  -- The inverse: invert the tuple pointwise and untwist by the inverted group element.
  ≀-inv : W → W
  ≀-inv (f , x) = (λ i → f (act (x ⁻¹ᵍ) i) ⁻¹) , x ⁻¹ᵍ
```

**Congruence of the operations**.  The only nontrivial step is the index of the
twisted tuple, which moves by `act-cong`{.AgdaField} along the group equality
and re-enters the base equality through `reflexive`.

```agda
  ≀-mul-cong : ∀ {p q u v} → p ≈ᵂ q → u ≈ᵂ v → ≀-mul p u ≈ᵂ ≀-mul q v
  ≀-mul-cong {(_ , p₂)} {q} {u} {(v₁ , _)} (bf , tf) (bg , tg) =
    ( λ i → ∙-cong (bf i) (transˢ  (bg (act p₂ i))
                                  (reflexiveˢ (cong v₁ (act-cong tf i)))) )
    , ∙ᵍ-cong tf tg

  ≀-inv-cong : ∀ {p q} → p ≈ᵂ q → ≀-inv p ≈ᵂ ≀-inv q
  ≀-inv-cong {(_ , p₂)} {(q₁ , _)} (bf , tf) =
    (λ i → ⁻¹-cong (transˢ  (bf (act (p₂ ⁻¹ᵍ) i))
                            (reflexiveˢ (cong q₁ (act-cong (⁻¹ᵍ-cong tf) i)))))
    , ⁻¹ᵍ-cong tf
```

#### The group laws

Each law is a named lemma proved coordinatewise: the first component reduces to
the corresponding law of `𝒮` after rewriting the tuple indices along the
action laws, and the second component is the corresponding law of `𝒢`.
Associativity uses compatibility (`act-∙`{.AgdaField}), the left identity uses
the identity law (`act-ε`{.AgdaField}), and the right inverse uses the derived
round trip (`act-invˡ`{.AgdaFunction}); the right identity and left inverse
are index-free.

```agda
  ≀-assoc : ∀ p q r → ≀-mul (≀-mul p q) r ≈ᵂ ≀-mul p (≀-mul q r)
  ≀-assoc (f , x) (g , y) (h , z) = base , assoc-lawᵍ x y z
    where
    base : ∀ i → (f i ∙ g (act x i)) ∙ h (act (x ∙ᵍ y) i)
                 ≈ f i ∙ (g (act x i) ∙ h (act y (act x i)))
    base i = transˢ  (∙-cong reflˢ (reflexiveˢ (cong h (act-∙ x y i))))
                     (assoc-law (f i) (g (act x i)) (h (act y (act x i))))

  ≀-idˡ : ∀ p → ≀-mul ≀-one p ≈ᵂ p
  ≀-idˡ (f , x) = base , idˡ-lawᵍ x
    where
    base : ∀ i → ε ∙ f (act εᵍ i) ≈ f i
    base i = transˢ (idˡ-law (f (act εᵍ i))) (reflexiveˢ (cong f (act-ε i)))

  ≀-idʳ : ∀ p → ≀-mul p ≀-one ≈ᵂ p
  ≀-idʳ (f , x) = (λ i → idʳ-law (f i)) , idʳ-lawᵍ x

  ≀-invˡ : ∀ p → ≀-mul (≀-inv p) p ≈ᵂ ≀-one
  ≀-invˡ (f , x) = (λ i → invˡ-law (f (act (x ⁻¹ᵍ) i))) , invˡ-lawᵍ x

  ≀-invʳ : ∀ p → ≀-mul p (≀-inv p) ≈ᵂ ≀-one
  ≀-invʳ (f , x) = base , invʳ-lawᵍ x
    where
    base : ∀ i → f i ∙ (f (act (x ⁻¹ᵍ) (act x i))) ⁻¹ ≈ ε
    base i = transˢ  (∙-cong reflˢ (⁻¹-cong (reflexiveˢ (cong f (act-invˡ x i)))))
                     (invʳ-law (f i))
```

The wreath product group, assembled by the setoid-level builder.

```agda
  ≀-Group : Group (ι ⊔ α ⊔ β) (ι ⊔ ρ ⊔ σ)
  ≀-Group = setoidEqsToGroup ≀-setoid ≀-mul ≀-one ≀-inv ≀-mul-cong ≀-inv-cong
              ≀-assoc ≀-idˡ ≀-idʳ ≀-invˡ ≀-invʳ
```

#### The subgroup `D Ḡ`

The elements whose base tuple is *diagonal* (constant up to `≈`) form a
subgroup: the twist permutes the coordinates of a constant tuple invisibly, so
the product of two diagonal-based elements is diagonal-based.

The membership predicate is the canonical diagonal predicate of
[Classical.Structures.Group.Diagonal][] applied to the first component, so the
library keeps a single notion of "diagonal".  This subgroup is the `D Ḡ` of
Kurzweil's construction: the second component ranges over all of `G`, the first
over the diagonal copy of `S`.

```agda
  open DiagonalSubgroup I 𝒮 using ( Diag )

  -- Membership: the first component is diagonal (the second component is unconstrained).
  Diag≀ : Pred W (ι ⊔ ρ)
  Diag≀ (w , _) = w ∈ Diag

  -- (∙-c is applied through a wrapper binding both pairs explicitly: the
  -- closure's type never mentions the right factor's second component, so an
  -- implicit q would leave that component an unsolved metavariable.)
  Diag≀-isSubgroup : IsSubgroup ≀-Group Diag≀
  Diag≀-isSubgroup =
    mkIsSubgroup ≀-Group resp (λ {p} {q} dp dq → ∙-c p q dp dq) ε-c ⁻¹-c
    where
    resp : ∀ {p q} → p ≈ᵂ q → p ∈ Diag≀ → q ∈ Diag≀
    resp (be , _) d i j = transˢ (symˢ (be i)) (transˢ (d i j) (be j))

    ∙-c : ∀ p q → p ∈ Diag≀ → q ∈ Diag≀ → ≀-mul p q ∈ Diag≀
    ∙-c (_ , p₂) _ dp dq i j = ∙-cong (dp i j) (dq (act p₂ i) (act p₂ j))

    ε-c : ≀-one ∈ Diag≀
    ε-c i j = reflˢ

    ⁻¹-c : ∀ {p} → p ∈ Diag≀ → ≀-inv p ∈ Diag≀
    ⁻¹-c {(_ , p₂)} d i j = ⁻¹-cong (d (act (p₂ ⁻¹ᵍ) i) (act (p₂ ⁻¹ᵍ) j))
```

#### Core-freeness preservation

**The theorem for which this module exists**: with a faithful action on an index
set of at least two points with decidable equality, and a nontrivial base group
with trivial center, the subgroup `D Ḡ` is core-free in `S ≀ G`.

The hypotheses on `𝒮` are the two fragments of "finite nonabelian simple" the
argument actually consumes — a witness `s₀ ≉ ε` and triviality of the center —
stated directly, since the library does not yet define simplicity (issue
#512).  A nontrivial centerless group is automatically nonabelian, which is
where the repaired argument (see the module header) gets its contradiction.

`CoreFreeness`{.AgdaModule} fixes the hypotheses; its lemmas follow the
membership characterization of the constructive core
([Classical.Structures.Group.NormalCore][]): an element of the core has *all*
its conjugates inside `D Ḡ`, and we exploit conjugation by probe elements
`(t , ε)` whose tuple `t` is supported at a single index — the same
single-index probes as the block-indicator tuples of
[Classical.Structures.Group.PartitionSubgroup][].

```agda
  module CoreFreeness
    (_≟_         : (i j : I) → Dec (i ≡ j))
    (another     : ∀ i → Σ[ j ∈ I ] ¬ j ≡ i)
    (s₀          : 𝕌[ 𝑺 ])
    (s₀≉ε        : ¬ s₀ ≈ ε)
    (centerless  : ∀ d → (∀ t → t ∙ d ≈ d ∙ t) → d ≈ ε)
    (faithful    : Faithful)
    where

    open Core ≀-Group Diag≀ Diag≀-isSubgroup
                                  using ( core ; core-mem-conj ; core-⊆ )
    open Conjugate ≀-Group        using ( conj )
    open GroupProperties ⟨ 𝒮 ⟩ᵍᵖ  using (ε⁻¹≈ε ; ⁻¹-anti-homo-∙ )
    open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using () renaming ( ε⁻¹≈ε to ε⁻¹≈εᵍ )
    open Conjugate 𝒮             using ( conj-syntax ; conj-cong ; conj-∙-hom )
    open SetoidReasoning 𝔻[ 𝑺 ]
```

The probe tuples: value `a` at the index `j`, identity elsewhere.

```agda
    -- The tuple supported at j with value a.
    probe : I → 𝕌[ 𝑺 ] → I → 𝕌[ 𝑺 ]
    probe j a k = if does (k ≟ j) then a else ε

    -- The probe takes the value a at its support.
    probe-at : ∀ j a → probe j a j ≡ a
    probe-at j a = cong (λ b → if b then a else ε) (dec-true (j ≟ j) refl)

    -- The probe is the identity away from its support.
    probe-off : ∀ j a {k} → ¬ k ≡ j → probe j a k ≡ ε
    probe-off j a {k} k≢j = cong (λ b → if b then a else ε) (dec-false (k ≟ j) k≢j)
```

Conjugating `w = (f , x)` by the probe element `(t , ε)` produces, at
coordinate `i`, the note's expression `t i ∙ f i ∙ t (x(i)) ⁻¹` — the lemma
normalizes the raw composite along the action laws, so that everything after
it computes with the clean form.  Membership of the conjugate in `D Ḡ` then
reads as the note's constancy constraint on the conjugated coordinates.

```agda
    -- Coordinate i of the conjugate of (f , x) by (t , ε).
    conj-coord : (t f : Base) (x : 𝕌[ 𝑮 ]) (i : I)
      → conj (t , εᵍ) (f , x) .proj₁ i ≈ (t i ∙ f i) ∙ (t (act x i)) ⁻¹
    conj-coord t f x i =
      ∙-cong  (∙-cong reflˢ (reflexiveˢ (cong f (act-ε i))))
               (⁻¹-cong (reflexiveˢ (cong t index-eq)))
      where
      -- act (ε ⁻¹) (act (ε ∙ x) i) ≡ act x i, by three action-law rewrites.
      index-eq : act (εᵍ ⁻¹ᵍ) (act (εᵍ ∙ᵍ x) i) ≡ act x i
      index-eq = trans  (cong (act (εᵍ ⁻¹ᵍ)) (act-cong (idˡ-lawᵍ x) i))
                        (trans (act-cong ε⁻¹≈εᵍ (act x i)) (act-ε (act x i)))

    -- The core constraint: the conjugate's coordinates are pairwise equal.
    constraint : ∀ {f x} → (f , x) ∈ core .proj₁ → (t : Base) → ∀ i j
      →  (t i ∙ f i) ∙ t (act x i) ⁻¹
      ≈ (t j ∙ f j) ∙ t (act x j) ⁻¹
    constraint {f} {x} w∈core t i j =
      transˢ  (symˢ (conj-coord t f x i))
              (transˢ (core-mem-conj w∈core (t , εᵍ) i j) (conj-coord t f x j))
```

**The moved-index case**.  Suppose the group component `x` moves some index:
`x i₀ = j ≠ i₀`.  Probing the constraint at the pair `(i₀ , j)` with the tuple
supported at `j` with value `a` gives, writing `d = f i₀`: `d ∙ a ⁻¹ ≈ a ∙ d`; the
probe vanishes at `i₀` (which is off the support), and at the twisted index `x j`,
which avoids the support because `x` is injective and already sends `i₀` to `j`.
Since `a` is arbitrary, conjugation by `d` is an inversion, which forces any two
elements of the base group to commute (`inv-conj→comm`{.AgdaFunction} below).

This is where the formalization diverges from the note's proof: no third
index `k ∉ {i₀ , j}` is needed, so no lower bound on the index set beyond two
points, and the note's gap at index two closes.

```agda
    -- A moved index turns the constraint into the inversion relation.
    moved→inv-conj : ∀ {f x} → (f , x) ∈ proj₁ core
      → ∀ {i₀} → ¬ act x i₀ ≡ i₀
      → ∀ a → (f i₀) ∙ a ⁻¹ ≈ a ∙ (f i₀)
    moved→inv-conj {f} {x} w∈core {i₀} moved a =
      begin
      f i₀ ∙ a ⁻¹                 ≈˘⟨ ∙-cong  (idˡ-law (f i₀))
                                              (⁻¹-cong (reflexiveˢ (probe-at j a))) ⟩
      ε ∙ f i₀ ∙ t j ⁻¹           ≈˘⟨ ∙-cong  (∙-cong (reflexiveˢ (probe-off j a i₀≢j)) reflˢ)
                                              reflˢ ⟩
      t i₀ ∙ f i₀ ∙ t j ⁻¹        ≈⟨ constraint w∈core t i₀ j ⟩
      t j ∙ f j ∙ t (act x j) ⁻¹  ≈⟨ ∙-cong  (∙-cong (reflexiveˢ (probe-at j a)) (df j i₀))
                                             (⁻¹-cong (reflexiveˢ (probe-off j a xj≢j))) ⟩
      a ∙ f i₀ ∙ ε ⁻¹             ≈⟨ ∙-cong reflˢ ε⁻¹≈ε ⟩
      a ∙ f i₀ ∙ ε                ≈⟨ idʳ-law (a ∙ f i₀) ⟩
      a ∙ f i₀                    ∎
      where
      j : I
      j = act x i₀

      t : Base
      t = probe j a

      -- i₀ is off the support: x moves it to j.
      i₀≢j : ¬ i₀ ≡ j
      i₀≢j i₀≡j = moved (sym i₀≡j)

      -- x(j) is off the support: x is injective and already sends i₀ to j.
      xj≢j : ¬ act x j ≡ j
      xj≢j e = moved (act-injective x e)

      -- The base tuple of a core element is diagonal.
      df : ∀ p q → f p ≈ f q
      df = core-⊆ w∈core
```

The inversion relation collapses the base group: if conjugation by some `d`
inverts every element, then `a ↦ d ∙ a ⁻¹ ∙ d ⁻¹` is the identity, and reading a
product `p ∙ q` through it reverses the factors.

```agda
    -- Conjugation by d inverting every element forces commutativity.
    inv-conj→comm : ∀ {d} → (∀ a → d ∙ a ⁻¹ ≈ a ∙ d) → ∀ p q → p ∙ q ≈ q ∙ p
    inv-conj→comm {d} inv p q = begin
      p ∙ q                  ≈⟨ ∙-cong (fix p) (fix q) ⟩
      (p ⁻¹)^ d ∙ (q ⁻¹)^ d  ≈˘⟨ conj-∙-hom d (p ⁻¹) (q ⁻¹) ⟩
      (p ⁻¹ ∙ q ⁻¹)^ d       ≈˘⟨ conj-cong d (⁻¹-anti-homo-∙ q p) ⟩
      ((q ∙ p) ⁻¹)^ d        ≈˘⟨ fix (q ∙ p) ⟩
      q ∙ p                  ∎
      where
      -- Conjugating the inverse by d restores the element.
      fix : ∀ a → a ≈ (a ⁻¹)^ d
      fix a = symˢ (begin
        (a ⁻¹)^ d       ≈⟨ ∙-cong (inv a) reflˢ ⟩
        a ∙ d ∙ d ⁻¹    ≈⟨ assoc-law a d (d ⁻¹) ⟩
        a ∙ (d ∙ d ⁻¹)  ≈⟨ ∙-cong reflˢ (invʳ-law d) ⟩
        a ∙ ε           ≈⟨ idʳ-law a ⟩
        a               ∎)
```

**Assembling the theorem**.

+  **Step 1**: the group component of a core element fixes every index; the
   decision on `x i ≟ i` is passed to a named lemma, and the moved branch is
   killed by the inversion relation, commutativity, and the nontrivial centerless
   base.

+  **Step 2**: faithfulness collapses the group component to the identity.

+  **Step 3**: probing at a fixed index `i` (with a companion index supplied by
   the two-point hypothesis) shows the diagonal value is central, hence the
   identity.

```agda
    -- Step 1: the group component of a core element fixes every index.
    core-fixes : ∀ {f x} → (f , x) ∈ proj₁ core → ∀ i → act x i ≡ i
    core-fixes {f} {x} w∈core i = settle (act x i ≟ i)
      where
      -- The case split, as a lemma taking the decision as an argument.
      settle : Dec (act x i ≡ i) → act x i ≡ i
      settle (yes p)     = p
      settle (no moved)  = ⊥-elim (s₀≉ε (centerless s₀ commutes))
        where
        commutes : ∀ t → t ∙ s₀ ≈ s₀ ∙ t
        commutes t = inv-conj→comm (moved→inv-conj w∈core moved) t s₀

    -- Step 2: the group component of a core element is the identity.
    core-group : ∀ {f x} → (f , x) ∈ proj₁ core → x ≈ᵍ εᵍ
    core-group w∈core = faithful (core-fixes w∈core)
```

For step 3, we need one more small commutation lemma: an element whose conjugate
by `a` is itself commutes with `a`.

```agda
    -- A fixed conjugate commutes: b ^ a ≈ b gives a ∙ b ≈ b ∙ a.
    conj-fix→comm : ∀ {a b} → b ^ a ≈ b → a ∙ b ≈ b ∙ a
    conj-fix→comm {a} {b} h = begin
      a ∙ b               ≈˘⟨ idʳ-law (a ∙ b) ⟩
      a ∙ b ∙ ε           ≈˘⟨ ∙-cong reflˢ (invˡ-law a) ⟩
      a ∙ b ∙ (a ⁻¹ ∙ a)  ≈˘⟨ assoc-law (a ∙ b) (a ⁻¹) a ⟩
      b ^ a ∙ a           ≈⟨ ∙-cong h reflˢ ⟩
      b ∙ a               ∎

    -- Step 3: the base tuple of a core element is the identity tuple.
    core-base : ∀ {f x} → (f , x) ∈ core .proj₁ → ∀ i → f i ≈ ε
    core-base {f} {x} w∈core i = centerless (f i) commutes
      where
      i' : I
      i' = another i .proj₁

      i'≢i : ¬ i' ≡ i
      i'≢i = another i .proj₂

      df : ∀ p q → f p ≈ f q
      df = core-⊆ w∈core

      -- Probing at i with value a: the conjugate of f i by a is f i again.
      fixed : ∀ a → f i ^ a ≈ f i
      fixed a = begin
        f i ^ a                          ≈˘⟨ ∙-cong  (∙-cong (reflexiveˢ t-at-i) reflˢ)
                                                     (⁻¹-cong (reflexiveˢ t-at-xi)) ⟩
        (t i ∙ f i) ∙ t (act x i) ⁻¹     ≈⟨ constraint w∈core t i i' ⟩
        (t i' ∙ f i') ∙ t (act x i') ⁻¹  ≈⟨ ∙-cong  (∙-cong (reflexiveˢ t-at-i') (df i' i))
                                                            (⁻¹-cong (reflexiveˢ t-at-xi')) ⟩
        f i ^ ε                          ≈⟨ ∙-cong (idˡ-law (f i)) ε⁻¹≈ε ⟩
        f i ∙ ε                          ≈⟨ idʳ-law (f i) ⟩
        f i ∎
        where
        t : Base
        t = probe i a

        t-at-i : t i ≡ a
        t-at-i = probe-at i a

        t-at-xi : t (act x i) ≡ a
        t-at-xi = trans (cong t (core-fixes w∈core i)) (probe-at i a)

        t-at-i' : t i' ≡ ε
        t-at-i' = probe-off i a i'≢i

        t-at-xi' : t (act x i') ≡ ε
        t-at-xi' = trans (cong t (core-fixes w∈core i')) (probe-off i a i'≢i)

      commutes : ∀ a → a ∙ f i ≈ f i ∙ a
      commutes a = conj-fix→comm (fixed a)
```

**The theorem**.  The core of `D Ḡ` is contained in the identity class of the
wreath product, which is the exact shape into which `CoreFree`{.AgdaFunction} of
[FLRP.Enforceable][] unfolds, so FLRP consumers apply it directly.

```agda
    -- D Ḡ is core-free in S ≀ G.
    Diag≀-coreFree : proj₁ core ⊆ proj₁ (trivialSubgroup ≀-Group)
    Diag≀-coreFree w∈core = core-base w∈core , core-group w∈core
```

#### The wreath operator

The group-level form, for use at call sites: `𝒮 ≀ᵍ A` is the wreath product of the
base group `𝒮` by the right action `A` (whose index set and acting group stay implicit).

```agda
infixl 8 _≀ᵍ_

_≀ᵍ_ : (𝒮 : Group α ρ) {I : Type ι} {𝒢 : Group β σ}
  → RightAction I 𝒢 → Group (ι ⊔ α ⊔ β) (ι ⊔ ρ ⊔ σ)
𝒮 ≀ᵍ A = WreathProduct.≀-Group 𝒮 A
```

--------------------------------------

[^1]: arXiv:1205.1927, vendored at `docs/papers/flrp/ieprops/`; Lemma 3.3 and
      its proof.  The FLRP-side consumer is [FLRP.WreathNoGo][].

[^2]: See `docs/notes/flrp-rp4-wreath.md` § 4 for the full account.
