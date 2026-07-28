---
layout: default
file: "src/Classical/Structures/Group/Wreath.lagda.md"
title: "Classical.Structures.Group.Wreath module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Wreath products

This is the [Classical.Structures.Group.Wreath][] module of the [Agda Universal Algebra Library][].

For a base group `S`, an index set `I`, and a group `G` acting on `I` on the
right ([Classical.Structures.Group.IndexAction][]), the **permutational wreath
product** `S ≀ G` is the semidirect product `Sᴵ ⋊ G`: pairs `(f , x)` of a base
tuple and a top element, multiplied by twisting the right factor's tuple with
the action of the left factor's top component,

$$(s, x)\,(t, y) \;=\; (s_1\, t_{x(1)}, \dots, s_n\, t_{x(n)},\; x y),$$

which is the display in the proof of Lemma `lem:IE-must-have-wreaths` of the
interval-enforceable-properties note[^1] — coordinate `i` of the product is
`s i ∙ t (x(i))`.  Associativity of this multiplication is exactly the
contravariant compatibility law of the right action, and the inverse twists by
the action of the inverted top component; no other property of the action is
used, so the construction is parameterized by a bare
`RightAction`{.AgdaRecord}, with no permutation-group or automorphism-group
object in sight.

The module provides, over `Classical/` (this is reusable group theory, not
FLRP-specific content):

+  the wreath product group `≀-Group`{.AgdaFunction} (top-level operator
   `_≀ᵍ_`{.AgdaFunction}), built by `setoidEqsToGroup`{.AgdaFunction} of
   [Classical.Structures.Group.Basic][] with each group law proved
   coordinatewise;
+  the subgroup `D Ḡ` of wreath elements with *diagonal* base tuple
   (`Diag≀`{.AgdaFunction}), the bottom of the interval `[D Ḡ , S ≀ G]` that
   Kurzweil's construction inhabits — its membership predicate is the diagonal
   predicate of [Classical.Structures.Group.Diagonal][] on the base component;
+  **the core-freeness preservation theorem**
   (`Diag≀-coreFree`{.AgdaFunction}): if the action is faithful, the index set
   has at least two points and decidable equality, and the base group is
   nontrivial with trivial center, then `D Ḡ` is core-free in `S ≀ G`.  This
   is the technical heart of the note's Lemma 3.3, the step its proof carries
   out in full rather than citing.

**On the hypotheses of the preservation theorem.**  The note's proof picks,
for a moved index `x(1) = j ≠ 1`, a third index `k ∉ {1 , j}`, justifying its
existence by `n = |G : H| > 2` "since otherwise `H ⊴ G`, contradicting
`Core_G(H) = 1`" — a justification that fails for `H = 1`: the pair
`(H , G) = (1 , C₂)` is core-free with index `2`.  The formalization below
closes the gap by *removing the third index altogether*: probing the constraint
at the two indices `i₀` and `j = x(i₀)` with the tuple that is `a` at `j` and
identity elsewhere yields `d ∙ a ⁻¹ ≈ a ∙ d` for every `a`, which makes
conjugation by `d` an inversion, forces the base group abelian
(`inv-conj→comm`{.AgdaFunction}), and contradicts a nontrivial trivial-center
base.  One uniform argument covers every index set with two points; the
theorem is *false* for a one-point index set, where `D Ḡ` is all of `S ≀ G`.
See `docs/notes/flrp-rp4-wreath.md` § 4 for the full account.

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

`WreathProduct`{.AgdaModule} `𝒮` `A` packages the wreath product of the base
group `𝒮`{.AgdaBound} by the right action `A`{.AgdaBound} of a top group on an
index set.

```agda
module WreathProduct (𝒮 : Group α ρ) {I : Type ι} {𝒢 : Group β σ}
  (A : RightAction I 𝒢)
  where

  private
    𝑺 = proj₁ 𝒮
    𝑮 = proj₁ 𝒢
    S = 𝕌[ 𝑺 ]
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑺 ] using ()
    renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁
             ; reflexive to reflexive₁ )
  open Setoid 𝔻[ 𝑮 ] using ()
    renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )
  open Group-Op 𝒮 using ()
    renaming ( _∙_ to _∙₁_ ; ε to ε₁ ; _⁻¹ to _⁻¹₁ ; ∙-cong to ∙₁-cong
             ; ⁻¹-cong to ⁻¹₁-cong ; assoc-law to assoc₁ ; idˡ-law to idˡ₁
             ; idʳ-law to idʳ₁ ; invˡ-law to invˡ₁ ; invʳ-law to invʳ₁ )
  open Group-Op 𝒢 using ()
    renaming ( _∙_ to _∙₂_ ; ε to ε₂ ; _⁻¹ to _⁻¹₂ ; ∙-cong to ∙₂-cong
             ; ⁻¹-cong to ⁻¹₂-cong ; assoc-law to assoc₂ ; idˡ-law to idˡ₂
             ; idʳ-law to idʳ₂ ; invˡ-law to invˡ₂ ; invʳ-law to invʳ₂ )
  open RightAction A
```

The carrier: pairs of a base tuple `I → S` and a top element, with pointwise
base equality and componentwise pair equality — the isolated-equality locus
for the Cubical port, as in [Classical.Structures.Group.Product][].

```agda
  -- Base tuples, and the wreath carrier.
  Base : Type (ι ⊔ α)
  Base = I → S

  W : Type (ι ⊔ α ⊔ β)
  W = Base × G

  ≀-setoid : Setoid (ι ⊔ α ⊔ β) (ι ⊔ ρ ⊔ σ)
  ≀-setoid = record
    { Carrier        = W
    ; _≈_            = λ p q → (∀ i → proj₁ p i ≈₁ proj₁ q i) × (proj₂ p ≈₂ proj₂ q)
    ; isEquivalence  = record
        { refl   = (λ i → refl₁) , refl₂
        ; sym    = λ e → (λ i → sym₁ (proj₁ e i)) , sym₂ (proj₂ e)
        ; trans  = λ d e → (λ i → trans₁ (proj₁ d i) (proj₁ e i))
                         , trans₂ (proj₂ d) (proj₂ e)
        }
    }

  open Setoid ≀-setoid using () renaming ( _≈_ to _≈ᵂ_ )
```

The three operations.  Coordinate `i` of a product is `f i ∙ g (x(i))` — the
left factor's tuple untwisted, the right factor's tuple read through the
action of the left top component.  The inverse twists by the action of the
inverted top component; the two-sided inverse laws below confirm the choice.

```agda
  -- The wreath multiplication (the note's display, coordinatewise).
  ≀-mul : W → W → W
  ≀-mul (f , x) (g , y) = (λ i → f i ∙₁ g (act x i)) , x ∙₂ y

  -- The identity: the constant-identity tuple over the top identity.
  ≀-one : W
  ≀-one = (λ _ → ε₁) , ε₂

  -- The inverse: invert the tuple pointwise and untwist by the inverted top.
  ≀-inv : W → W
  ≀-inv (f , x) = (λ i → (f (act (x ⁻¹₂) i)) ⁻¹₁) , x ⁻¹₂
```

Congruence of the operations.  The only nontrivial step is the index of the
twisted tuple, which moves by `act-cong`{.AgdaField} along the top equality
and re-enters the base equality through `reflexive`.

```agda
  ≀-mul-cong : ∀ {p q u v} → p ≈ᵂ q → u ≈ᵂ v → ≀-mul p u ≈ᵂ ≀-mul q v
  ≀-mul-cong {p} {q} {u} {v} (bf , tf) (bg , tg) =
      (λ i → ∙₁-cong (bf i)
        (trans₁ (bg (act (proj₂ p) i))
                (reflexive₁ (cong (proj₁ v) (act-cong tf i)))))
    , ∙₂-cong tf tg

  ≀-inv-cong : ∀ {p q} → p ≈ᵂ q → ≀-inv p ≈ᵂ ≀-inv q
  ≀-inv-cong {p} {q} (bf , tf) =
      (λ i → ⁻¹₁-cong
        (trans₁ (bf (act (proj₂ p ⁻¹₂) i))
                (reflexive₁ (cong (proj₁ q) (act-cong (⁻¹₂-cong tf) i)))))
    , ⁻¹₂-cong tf
```

#### The group laws

Each law is a named lemma proved coordinatewise: the base component reduces to
the corresponding law of `𝒮` after rewriting the tuple indices along the
action laws, and the top component is the corresponding law of `𝒢`.
Associativity uses compatibility (`act-∙`{.AgdaField}), the left identity uses
the identity law (`act-ε`{.AgdaField}), and the right inverse uses the derived
round trip (`act-invˡ`{.AgdaFunction}); the right identity and left inverse
are index-free.

```agda
  ≀-assoc : ∀ p q r → ≀-mul (≀-mul p q) r ≈ᵂ ≀-mul p (≀-mul q r)
  ≀-assoc (f , x) (g , y) (h , z) = base , assoc₂ x y z
    where
    base : ∀ i → (f i ∙₁ g (act x i)) ∙₁ h (act (x ∙₂ y) i)
                 ≈₁ f i ∙₁ (g (act x i) ∙₁ h (act y (act x i)))
    base i = trans₁  (∙₁-cong refl₁ (reflexive₁ (cong h (act-∙ x y i))))
                     (assoc₁ (f i) (g (act x i)) (h (act y (act x i))))

  ≀-idˡ : ∀ p → ≀-mul ≀-one p ≈ᵂ p
  ≀-idˡ (f , x) = base , idˡ₂ x
    where
    base : ∀ i → ε₁ ∙₁ f (act ε₂ i) ≈₁ f i
    base i = trans₁ (idˡ₁ (f (act ε₂ i))) (reflexive₁ (cong f (act-ε i)))

  ≀-idʳ : ∀ p → ≀-mul p ≀-one ≈ᵂ p
  ≀-idʳ (f , x) = (λ i → idʳ₁ (f i)) , idʳ₂ x

  ≀-invˡ : ∀ p → ≀-mul (≀-inv p) p ≈ᵂ ≀-one
  ≀-invˡ (f , x) = (λ i → invˡ₁ (f (act (x ⁻¹₂) i))) , invˡ₂ x

  ≀-invʳ : ∀ p → ≀-mul p (≀-inv p) ≈ᵂ ≀-one
  ≀-invʳ (f , x) = base , invʳ₂ x
    where
    base : ∀ i → f i ∙₁ (f (act (x ⁻¹₂) (act x i))) ⁻¹₁ ≈₁ ε₁
    base i = trans₁  (∙₁-cong refl₁ (⁻¹₁-cong (reflexive₁ (cong f (act-invˡ x i)))))
                     (invʳ₁ (f i))
```

The wreath product group, assembled by the setoid-level builder.

```agda
  ≀-Group : Group (ι ⊔ α ⊔ β) (ι ⊔ ρ ⊔ σ)
  ≀-Group = setoidEqsToGroup ≀-setoid ≀-mul ≀-one ≀-inv ≀-mul-cong ≀-inv-cong
              ≀-assoc ≀-idˡ ≀-idʳ ≀-invˡ ≀-invʳ
```

#### The subgroup `D Ḡ`

The elements whose base tuple is *diagonal* — constant up to `≈` — form a
subgroup: the twist permutes the coordinates of a constant tuple invisibly, so
the product of two diagonal-based elements is diagonal-based.  The membership
predicate is the canonical diagonal predicate of
[Classical.Structures.Group.Diagonal][] applied to the base component, so the
library keeps a single notion of "diagonal".  This subgroup is the `D Ḡ` of
Kurzweil's construction: the top component ranges over all of `G`, the base
over the diagonal copy of `S`.

```agda
  open DiagonalSubgroup I 𝒮 using ( Diag )

  -- Membership: the base tuple is diagonal (the top component is unconstrained).
  Diag≀ : Pred W (ι ⊔ ρ)
  Diag≀ w = proj₁ w ∈ Diag

  -- (∙-c is applied through a wrapper binding both pairs explicitly: the
  -- closure's type never mentions the right factor's top component, so an
  -- implicit q would leave that component an unsolved metavariable.)
  Diag≀-isSubgroup : IsSubgroup ≀-Group Diag≀
  Diag≀-isSubgroup =
    mkIsSubgroup ≀-Group resp (λ {p} {q} dp dq → ∙-c p q dp dq) ε-c ⁻¹-c
    where
    resp : ∀ {p q} → p ≈ᵂ q → p ∈ Diag≀ → q ∈ Diag≀
    resp (be , _) d i j = trans₁ (sym₁ (be i)) (trans₁ (d i j) (be j))

    ∙-c : ∀ p q → p ∈ Diag≀ → q ∈ Diag≀ → ≀-mul p q ∈ Diag≀
    ∙-c p q dp dq i j =
      ∙₁-cong (dp i j) (dq (act (proj₂ p) i) (act (proj₂ p) j))

    ε-c : ≀-one ∈ Diag≀
    ε-c i j = refl₁

    ⁻¹-c : ∀ {p} → p ∈ Diag≀ → ≀-inv p ∈ Diag≀
    ⁻¹-c {p} d i j =
      ⁻¹₁-cong (d (act (proj₂ p ⁻¹₂) i) (act (proj₂ p ⁻¹₂) j))
```

#### Core-freeness preservation

The theorem this module exists for: with a faithful action on an index set of
at least two points with decidable equality, and a nontrivial base group with
trivial center, the subgroup `D Ḡ` is core-free in `S ≀ G`.

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
    (s₀          : S) (s₀≉ε : ¬ s₀ ≈₁ ε₁)
    (centerless  : ∀ d → (∀ t → t ∙₁ d ≈₁ d ∙₁ t) → d ≈₁ ε₁)
    (faithful    : Faithful)
    where

    open Conjugate ≀-Group using ( conj )
    open Core ≀-Group Diag≀ Diag≀-isSubgroup
      using ( core ; core-mem-conj ; core-⊆ )
    open GroupProperties ⟨ 𝒮 ⟩ᵍᵖ using ()
      renaming ( ε⁻¹≈ε to ε⁻¹≈ε₁ ; ⁻¹-anti-homo-∙ to ⁻¹-anti-homo-∙₁ )
    open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using ()
      renaming ( ε⁻¹≈ε to ε⁻¹≈ε₂ )
    open Conjugate 𝒮 using ()
      renaming ( conj to conj₁ ; conj-cong to conj₁-cong
               ; conj-∙-hom to conj₁-∙-hom )
    open SetoidReasoning 𝔻[ 𝑺 ]
```

The probe tuples: value `a` at the index `j`, identity elsewhere.

```agda
    -- The tuple supported at j with value a.
    probe : I → S → I → S
    probe j a k = if does (k ≟ j) then a else ε₁

    -- The probe takes the value a at its support.
    probe-at : ∀ j a → probe j a j ≡ a
    probe-at j a = cong (λ b → if b then a else ε₁) (dec-true (j ≟ j) refl)

    -- The probe is the identity away from its support.
    probe-off : ∀ j a {k} → ¬ k ≡ j → probe j a k ≡ ε₁
    probe-off j a {k} k≢j = cong (λ b → if b then a else ε₁) (dec-false (k ≟ j) k≢j)
```

Conjugating `w = (f , x)` by the probe element `(t , ε)` produces, at
coordinate `i`, the note's expression `t i ∙ f i ∙ t (x(i)) ⁻¹` — the lemma
normalizes the raw composite along the action laws, so that everything after
it computes with the clean form.  Membership of the conjugate in `D Ḡ` then
reads as the note's constancy constraint on the conjugated coordinates.

```agda
    -- Coordinate i of the conjugate of (f , x) by (t , ε).
    conj-coord : ∀ (t f : Base) (x : G) (i : I)
      → proj₁ (conj (t , ε₂) (f , x)) i ≈₁ (t i ∙₁ f i) ∙₁ (t (act x i)) ⁻¹₁
    conj-coord t f x i =
      ∙₁-cong  (∙₁-cong refl₁ (reflexive₁ (cong f (act-ε i))))
               (⁻¹₁-cong (reflexive₁ (cong t index-eq)))
      where
      -- act (ε ⁻¹) (act (ε ∙ x) i) ≡ act x i, by three action-law rewrites.
      index-eq : act (ε₂ ⁻¹₂) (act (ε₂ ∙₂ x) i) ≡ act x i
      index-eq = trans  (cong (act (ε₂ ⁻¹₂)) (act-cong (idˡ₂ x) i))
                        (trans (act-cong ε⁻¹≈ε₂ (act x i)) (act-ε (act x i)))

    -- The core constraint: the conjugate's coordinates are pairwise equal.
    constraint : ∀ {f x} → (f , x) ∈ proj₁ core → (t : Base) → ∀ i j
      →  (t i ∙₁ f i) ∙₁ (t (act x i)) ⁻¹₁
      ≈₁ (t j ∙₁ f j) ∙₁ (t (act x j)) ⁻¹₁
    constraint {f} {x} w∈core t i j =
      trans₁  (sym₁ (conj-coord t f x i))
              (trans₁ (core-mem-conj w∈core (t , ε₂) i j) (conj-coord t f x j))
```

**The moved-index case.**  Suppose the top component `x` moves some index:
`x(i₀) = j ≠ i₀`.  Probing the constraint at the pair `(i₀ , j)` with the
tuple supported at `j` with value `a` gives, writing `d = f i₀`:
`d ∙ a ⁻¹ ≈ a ∙ d` — the probe vanishes at `i₀` (which is off the support),
and at the twisted index `x(j)`, which avoids the support because `x` is
injective and already sends `i₀` to `j`.  Since `a` is arbitrary, conjugation
by `d` is an inversion, which forces any two elements of the base group to
commute (`inv-conj→comm`{.AgdaFunction} below).

This is where the formalization diverges from the note's proof: no third
index `k ∉ {i₀ , j}` is needed, so no lower bound on the index set beyond two
points, and the note's gap at index two closes.  See the module header.

```agda
    -- A moved index turns the constraint into the inversion relation.
    moved→inv-conj : ∀ {f x} → (f , x) ∈ proj₁ core
      → ∀ {i₀} → ¬ act x i₀ ≡ i₀
      → ∀ a → (f i₀) ∙₁ a ⁻¹₁ ≈₁ a ∙₁ (f i₀)
    moved→inv-conj {f} {x} w∈core {i₀} moved a = begin
      f i₀ ∙₁ a ⁻¹₁
        ≈˘⟨ ∙₁-cong (idˡ₁ (f i₀)) (⁻¹₁-cong (reflexive₁ (probe-at j a))) ⟩
      (ε₁ ∙₁ f i₀) ∙₁ (t j) ⁻¹₁
        ≈˘⟨ ∙₁-cong (∙₁-cong (reflexive₁ (probe-off j a i₀≢j)) refl₁) refl₁ ⟩
      (t i₀ ∙₁ f i₀) ∙₁ (t j) ⁻¹₁
        ≈⟨ constraint w∈core t i₀ j ⟩
      (t j ∙₁ f j) ∙₁ (t (act x j)) ⁻¹₁
        ≈⟨ ∙₁-cong  (∙₁-cong (reflexive₁ (probe-at j a)) (df j i₀))
                    (⁻¹₁-cong (reflexive₁ (probe-off j a xj≢j))) ⟩
      (a ∙₁ f i₀) ∙₁ ε₁ ⁻¹₁
        ≈⟨ ∙₁-cong refl₁ ε⁻¹≈ε₁ ⟩
      (a ∙₁ f i₀) ∙₁ ε₁
        ≈⟨ idʳ₁ (a ∙₁ f i₀) ⟩
      a ∙₁ f i₀ ∎
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
      df : ∀ p q → f p ≈₁ f q
      df = core-⊆ w∈core
```

The inversion relation collapses the base group: if conjugation by some `d`
inverts every element, then `a ↦ d ∙ a ⁻¹ ∙ d ⁻¹` is the identity, and
reading a product `p ∙ q` through it reverses the factors.

```agda
    -- Conjugation by d inverting every element forces commutativity.
    inv-conj→comm : ∀ {d} → (∀ a → d ∙₁ a ⁻¹₁ ≈₁ a ∙₁ d) → ∀ p q → p ∙₁ q ≈₁ q ∙₁ p
    inv-conj→comm {d} inv p q = begin
      p ∙₁ q                                 ≈⟨ ∙₁-cong (fix p) (fix q) ⟩
      conj₁ d (p ⁻¹₁) ∙₁ conj₁ d (q ⁻¹₁)     ≈˘⟨ conj₁-∙-hom d (p ⁻¹₁) (q ⁻¹₁) ⟩
      conj₁ d (p ⁻¹₁ ∙₁ q ⁻¹₁)               ≈˘⟨ conj₁-cong d (⁻¹-anti-homo-∙₁ q p) ⟩
      conj₁ d ((q ∙₁ p) ⁻¹₁)                 ≈˘⟨ fix (q ∙₁ p) ⟩
      q ∙₁ p                                 ∎
      where
      -- Conjugating the inverse by d restores the element.
      fix : ∀ a → a ≈₁ conj₁ d (a ⁻¹₁)
      fix a = sym₁ (begin
        (d ∙₁ a ⁻¹₁) ∙₁ d ⁻¹₁    ≈⟨ ∙₁-cong (inv a) refl₁ ⟩
        (a ∙₁ d) ∙₁ d ⁻¹₁        ≈⟨ assoc₁ a d (d ⁻¹₁) ⟩
        a ∙₁ (d ∙₁ d ⁻¹₁)        ≈⟨ ∙₁-cong refl₁ (invʳ₁ d) ⟩
        a ∙₁ ε₁                  ≈⟨ idʳ₁ a ⟩
        a                        ∎)
```

**Assembling the theorem.**  Step 1: the top component of a core element
fixes every index — the decision on `x(i) ≟ i` is passed to a named lemma,
and the moved branch is killed by the inversion relation, commutativity, and
the nontrivial centerless base.  Step 2: faithfulness collapses the top
component to the identity.  Step 3: probing at a fixed index `i` (with a
companion index supplied by the two-point hypothesis) shows the diagonal
value is central, hence the identity.

```agda
    -- Step 1: the top component of a core element fixes every index.
    core-fixes : ∀ {f x} → (f , x) ∈ proj₁ core → ∀ i → act x i ≡ i
    core-fixes {f} {x} w∈core i = settle (act x i ≟ i)
      where
      -- The case split, as a lemma taking the decision as an argument.
      settle : Dec (act x i ≡ i) → act x i ≡ i
      settle (yes p)     = p
      settle (no moved)  = ⊥-elim (s₀≉ε (centerless s₀ commutes))
        where
        commutes : ∀ t → t ∙₁ s₀ ≈₁ s₀ ∙₁ t
        commutes t = inv-conj→comm (moved→inv-conj w∈core moved) t s₀

    -- Step 2: the top component of a core element is the identity.
    core-top : ∀ {f x} → (f , x) ∈ proj₁ core → x ≈₂ ε₂
    core-top w∈core = faithful (core-fixes w∈core)
```

For step 3, one more small commutation lemma: an element whose conjugate by
`a` is itself commutes with `a`.

```agda
    -- A fixed conjugate commutes: (a ∙ b) ∙ a ⁻¹ ≈ b gives a ∙ b ≈ b ∙ a.
    conj-fix→comm : ∀ {a b} → (a ∙₁ b) ∙₁ a ⁻¹₁ ≈₁ b → a ∙₁ b ≈₁ b ∙₁ a
    conj-fix→comm {a} {b} h = begin
      a ∙₁ b                      ≈˘⟨ idʳ₁ (a ∙₁ b) ⟩
      (a ∙₁ b) ∙₁ ε₁              ≈˘⟨ ∙₁-cong refl₁ (invˡ₁ a) ⟩
      (a ∙₁ b) ∙₁ (a ⁻¹₁ ∙₁ a)    ≈˘⟨ assoc₁ (a ∙₁ b) (a ⁻¹₁) a ⟩
      ((a ∙₁ b) ∙₁ a ⁻¹₁) ∙₁ a    ≈⟨ ∙₁-cong h refl₁ ⟩
      b ∙₁ a                      ∎

    -- Step 3: the base tuple of a core element is the identity tuple.
    core-base : ∀ {f x} → (f , x) ∈ proj₁ core → ∀ i → f i ≈₁ ε₁
    core-base {f} {x} w∈core i = centerless (f i) commutes
      where
      i' : I
      i' = proj₁ (another i)

      i'≢i : ¬ i' ≡ i
      i'≢i = proj₂ (another i)

      df : ∀ p q → f p ≈₁ f q
      df = core-⊆ w∈core

      -- Probing at i with value a: the conjugate of f i by a is f i again.
      fixed : ∀ a → (a ∙₁ f i) ∙₁ a ⁻¹₁ ≈₁ f i
      fixed a = begin
        (a ∙₁ f i) ∙₁ a ⁻¹₁
          ≈˘⟨ ∙₁-cong  (∙₁-cong (reflexive₁ t-at-i) refl₁)
                       (⁻¹₁-cong (reflexive₁ t-at-xi)) ⟩
        (t i ∙₁ f i) ∙₁ (t (act x i)) ⁻¹₁
          ≈⟨ constraint w∈core t i i' ⟩
        (t i' ∙₁ f i') ∙₁ (t (act x i')) ⁻¹₁
          ≈⟨ ∙₁-cong  (∙₁-cong (reflexive₁ t-at-i') (df i' i))
                      (⁻¹₁-cong (reflexive₁ t-at-xi')) ⟩
        (ε₁ ∙₁ f i) ∙₁ ε₁ ⁻¹₁
          ≈⟨ ∙₁-cong (idˡ₁ (f i)) ε⁻¹≈ε₁ ⟩
        f i ∙₁ ε₁
          ≈⟨ idʳ₁ (f i) ⟩
        f i ∎
        where
        t : Base
        t = probe i a

        t-at-i : t i ≡ a
        t-at-i = probe-at i a

        t-at-xi : t (act x i) ≡ a
        t-at-xi = trans (cong t (core-fixes w∈core i)) (probe-at i a)

        t-at-i' : t i' ≡ ε₁
        t-at-i' = probe-off i a i'≢i

        t-at-xi' : t (act x i') ≡ ε₁
        t-at-xi' = trans (cong t (core-fixes w∈core i')) (probe-off i a i'≢i)

      commutes : ∀ a → a ∙₁ f i ≈₁ f i ∙₁ a
      commutes a = conj-fix→comm (fixed a)
```

The theorem: the core of `D Ḡ` is contained in the identity class of the
wreath product — the exact shape `CoreFree`{.AgdaFunction} of
[FLRP.Enforceable][] unfolds to, so FLRP consumers apply it directly.

```agda
    -- D Ḡ is core-free in S ≀ G.
    Diag≀-coreFree : proj₁ core ⊆ proj₁ (trivialSubgroup ≀-Group)
    Diag≀-coreFree w∈core = core-base w∈core , core-top w∈core
```

#### The wreath operator

The top-level form, for use at call sites: `𝒮 ≀ᵍ A` is the wreath product of
the base group `𝒮` by the right action `A` (whose index set and top group
stay implicit).

```agda
infixl 8 _≀ᵍ_

_≀ᵍ_ : (𝒮 : Group α ρ) {I : Type ι} {𝒢 : Group β σ}
  → RightAction I 𝒢 → Group (ι ⊔ α ⊔ β) (ι ⊔ ρ ⊔ σ)
𝒮 ≀ᵍ A = WreathProduct.≀-Group 𝒮 A
```

--------------------------------------

[^1]: arXiv:1205.1927, vendored at `docs/papers/flrp/ieprops/`; Lemma 3.3 and
      its proof.  The FLRP-side consumer is [FLRP.WreathNoGo][].
