---
layout: default
file: "src/Classical/Structures/Group/TableGroup.lagda.md"
title: "Classical.Structures.Group.TableGroup module"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Concrete groups from tables, with associativity via a faithful action

This is the [Classical.Structures.Group.TableGroup][] module of the [Agda Universal Algebra Library][].

The worked Cayley-table groups of [Examples.Classical.Groups][] discharge
associativity by brute decision, a cubic sweep involving `n³` equality tests.
At `n = 6` (the symmetric group `S₃`) that is 216 tests and instantaneous; at
`n = 60` (the alternating group `A₅` needed by the filter-ideal census entries[^1])
it is 216,000 tests, each through three table lookups, and the sweep dominates
type-checking.

This module removes the cubic sweep: when the group is presented *with a faithful
permutation action*, presenting each element `i` as the vector `elt i` of images
of a permutation of `Fin d`, then the associativity of the multiplication table
follows from two *quadratic* checks:

+  `elt`{.AgdaBound} is injective (the action is faithful), and
+  `elt`{.AgdaBound} sends table products to compositions
   (`elt (mul i j) ≡ (elt i) ⨁ (elt j)`).

Composition of functions is associative for free
(`⨁-assoc`{.AgdaFunction}, three `tabulate`/`lookup` steps), so the
table inherits associativity through injectivity.  Both hypotheses are
decidable (`elt-inj?`{.AgdaFunction}, `mul-hom?`{.AgdaFunction}), so a
concrete instance discharges them with `from-yes`{.AgdaFunction}: `n²`
vector comparisons instead of `n³` products.

The `Build`{.AgdaModule} submodule assembles the `Group`{.AgdaFunction} (via
`eqsToGroup`{.AgdaFunction}; the remaining unit and inverse laws are linear
sweeps the instance also discharges by decision), its carrier-finiteness
witness, and (because every concrete consumer immediately needs them)
**boolean subgroups**: a characteristic vector plus three decidable closure
checks yields a `DecSubgroup`{.AgdaFunction}.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.TableGroup where


-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base        using ( Bool ; T )
open import Data.Bool.Properties  using ( T? )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   renaming ( all? to allᶠ? ; _≟_ to _≟ᶠ_ )
                                  using ()
open import Data.Nat.Base         using ( ℕ )
open import Data.Product          using ( _,_ ; proj₁ )
open import Data.Vec.Base         using ( Vec ; lookup ; tabulate )
open import Data.Vec.Properties   using ( lookup∘tabulate ; tabulate-cong ; ≡-dec )
open import Level                 using ( 0ℓ )
open import Relation.Binary.Definitions            using ( _Respects_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans
                                                         ; cong ; subst )
open import Relation.Nullary                       using ( Dec )
open import Relation.Nullary.Decidable.Core        using ( _→-dec_ )
open import Relation.Unary                         using ( Pred )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic      using  ( Group ; eqsToGroup )
open import Classical.Structures.Group.Subgroups  using  ( IsSubgroup ; mkIsSubgroup
                                                         ; DecSubgroup )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
```
-->

#### Composition of image vectors

A permutation of `Fin d` is presented as its vector of images; composition is
`tabulate`{.AgdaFunction} of the composed lookups, and its associativity is
three applications of the `tabulate`/`lookup` round trip.

```agda
_⨁_ : {d : ℕ} → Vec (Fin d) d → Vec (Fin d) d → Vec (Fin d) d
u ⨁ v = tabulate (λ p → lookup u (lookup v p))

⨁-assoc :  {d : ℕ} (u v w : Vec (Fin d) d)
  →              (u ⨁ v) ⨁ w ≡ u ⨁ (v ⨁ w)
⨁-assoc u v w = trans
  (tabulate-cong (λ p → lookup∘tabulate (λ q → lookup u (lookup v q)) (lookup w p)))
  (sym (tabulate-cong (λ p → cong (lookup u) (lookup∘tabulate (λ q → lookup v (lookup w q)) p))))
```

#### The builder

The data of an instance: the action `elt`{.AgdaBound}, the multiplication
table (curried), the inverse table, and the identity index.

```agda
module TableGroupBuilder
  (n d    : ℕ)
  (elt    : Fin n → Vec (Fin d) d)
  (mul    : Fin n → Fin n → Fin n)
  (inv    : Fin n → Fin n)
  (e      : Fin n)
  where

  -- Faithfulness of the action, as a decidable statement.
  elt-inj? : Dec (∀ i j → elt i ≡ elt j → i ≡ j)
  elt-inj? = allᶠ? (λ i → allᶠ? (λ j → ≡-dec _≟ᶠ_ (elt i) (elt j) →-dec (i ≟ᶠ j)))

  -- The table computes composition, as a decidable statement.
  mul-hom? : Dec (∀ i j → elt (mul i j) ≡ elt i ⨁ elt j)
  mul-hom? = allᶠ? (λ i → allᶠ? (λ j → ≡-dec _≟ᶠ_ (elt (mul i j)) (elt i ⨁ elt j)))
```

Given the two action hypotheses and the four linear laws, the group is
assembled; associativity never runs the cubic sweep.

```agda
  module Build
    (inj   : ∀ i j → elt i ≡ elt j → i ≡ j)
    (hom   : ∀ i j → elt (mul i j) ≡ elt i ⨁ elt j)
    (idˡ   : ∀ a → mul e a ≡ a)
    (idʳ   : ∀ a → mul a e ≡ a)
    (invˡ  : ∀ a → mul (inv a) a ≡ e)
    (invʳ  : ∀ a → mul a (inv a) ≡ e)
    where

    -- Associativity of the table, through the faithful action.
    mul-assoc : ∀ i j k → mul (mul i j) k ≡ mul i (mul j k)
    mul-assoc i j k = inj _ _ (trans (hom (mul i j) k) (trans
      (cong (λ z → z ⨁ elt k) (hom i j)) (trans
      (⨁-assoc (elt i) (elt j) (elt k)) (trans
      (cong (elt i ⨁_) (sym (hom j k)))
      (sym (hom i (mul j k)))))))

    -- The group on carrier Fin n.
    theGroup : Group 0ℓ 0ℓ
    theGroup = eqsToGroup mul e inv mul-assoc idˡ idʳ invˡ invʳ

    -- Carrier finiteness: the identity enumeration.
    theGroup-FiniteAlgebra : FiniteAlgebra (proj₁ theGroup)
    theGroup-FiniteAlgebra = record
      { _≟_       = _≟ᶠ_
      ; card      = n
      ; enum      = λ i → i
      ; enum-sur  = λ x → x , refl
      }
```

#### Boolean subgroups

A subgroup of a table group is naturally presented by its characteristic
vector; the three closure conditions are decidable sweeps
(`chi-∙?`{.AgdaFunction} and companions), so instances discharge them with
`from-yes`{.AgdaFunction} and obtain a `DecSubgroup`{.AgdaFunction} whose
membership test is one vector lookup.

```agda
    module _ (chi : Vec Bool n) where

      -- Membership: the characteristic bit is true.
      chiPred : Pred (Fin n) 0ℓ
      chiPred x = T (lookup chi x)

      chi-∙? : Dec (∀ i j → chiPred i → chiPred j → chiPred (mul i j))
      chi-∙? = allᶠ? (λ i → allᶠ? (λ j →
        T? (lookup chi i) →-dec (T? (lookup chi j) →-dec T? (lookup chi (mul i j)))))

      chi-ε? : Dec (chiPred e)
      chi-ε? = T? (lookup chi e)

      chi-⁻¹? : Dec (∀ i → chiPred i → chiPred (inv i))
      chi-⁻¹? = allᶠ? (λ i → T? (lookup chi i) →-dec T? (lookup chi (inv i)))

      -- The subgroup *structure* is kept opaque, and this is load-bearing.
      -- It mentions the group bundle, whose law proofs are decision sweeps
      -- over the whole carrier; left transparent, every goal about a
      -- concrete subgroup (a containment of coset congruences, say)
      -- normalizes that tower, and the check diverges (measured on the A5
      -- instance: one containment exhausts a 32 GB heap).  Nothing needs a
      -- subgroup axiom to *compute*: the membership predicate and its
      -- decider, which the finite searches do run, stay transparent below.
      abstract
        boolIsSubgroup :  (∀ i j → chiPred i → chiPred j → chiPred (mul i j))
          →               chiPred e
          →               (∀ i → chiPred i → chiPred (inv i))
          →               IsSubgroup theGroup chiPred
        boolIsSubgroup c∙ cε c⁻¹ =
          mkIsSubgroup theGroup resp (λ {x} {y} → c∙ x y) cε (λ {x} → c⁻¹ x)
          where
          resp : chiPred Respects _≡_
          resp x≡y px = subst chiPred x≡y px

      -- The decidable subgroup cut out by the characteristic vector.
      boolSubgroup :  (∀ i j → chiPred i → chiPred j → chiPred (mul i j))
        →             chiPred e
        →             (∀ i → chiPred i → chiPred (inv i))
        →             DecSubgroup theGroup 0ℓ
      boolSubgroup c∙ cε c⁻¹ =
        (chiPred , boolIsSubgroup c∙ cε c⁻¹) , (λ x → T? (lookup chi x))
```

--------------------------------------

[^1]: See the filter-ideal design note, `docs/notes/flrp-530-filter-ideal.md`.
