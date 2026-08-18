---
layout: default
file: "src/Classical/Structures/Group/PartitionSubgroup.lagda.md"
title: "Classical.Structures.Group.PartitionSubgroup module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Partition subgroups of a finite power

This is the [Classical.Structures.Group.PartitionSubgroup][] module of the [Agda Universal Algebra Library][].

For the finite power `𝒢 ^ᵍ n` of [Classical.Structures.Group.Power][] and a
partition `π` of the index set, the **partition subgroup** is the set of tuples
constant on the blocks of `π`:

    Kπ = { y ∈ Gⁿ | ∀ i j → ker π ≤ ker y }
       = { y ∈ Gⁿ | ∀ i j → π i j → y i ≈ y j }.


This is an equality-respecting subgroup of the power, sandwiched between the diagonal
`D = K⊤` and the full power `Gⁿ = K⊥`, and the assignment `π ↦ Kπ` reverses the
refinement order — a finer partition imposes fewer constancy constraints, hence a
larger subgroup.

The delicate lemma is *order reflection*: if `Kρ ⊆ Kπ` then `π ⊑ ρ`.
Its proof is the one place the base group must be *nontrivial*.  Indeed, for indices
`i , j` in distinct `ρ`-blocks, the indicator tuple that is `s` on the `ρ`-block of
`i` and `ε` elsewhere lies in `Kρ`, so it lies in `Kπ`; if `π i j`, then the
indicator would identify `s` with `ε`.  The hypothesis enters as an explicit
witness `s` with `¬ s ≈ ε` — the constructive, positive form of nontriviality.[^1]
Membership in a `ρ`-block is decided by the parent lookups, so the reflection is
fully constructive.

Together, monotonicity and reflection make `π ↦ Kπ` a *dual order embedding* of the
partition lattice `Eq(n)` into the interval `[D , Gⁿ]` of the subgroup lattice.[^2]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.PartitionSubgroup where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base      using ( if_then_else_ )
open import Data.Empty          using ( ⊥-elim )
open import Data.Fin.Base       using ( Fin )
open import Data.Fin.Patterns   using ( 0F ; 1F )
open import Data.Fin.Properties using ( _≟_ )
open import Data.Nat.Base       using ( ℕ )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( id )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
open import Relation.Binary.Definitions           using ( _Respects_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans
                                                        ; cong )
open import Relation.Nullary            using ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable  using ( does ; dec-true ; dec-false )
open import Relation.Unary              using ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group             using  ( ∙-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic       using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Diagonal    using  ( module DiagonalSubgroup )
open import Classical.Structures.Group.Power       using  ( module GroupPower )
open import Classical.Structures.Group.Subgroups   using  ( IsSubgroup ; mkIsSubgroup )
open import Classical.Structures.Interpret         using  ( interp-cong )
open import Classical.Structures.Lattice.Partitions
  using  ( SameBlock ; _⊑_ ; _≈ᵖ_ ; ⊤ᵉ ; ⊤ᵉ-related ; ⊥ᵉ ; parent-tab )
open import Setoid.Congruences.Certificates.Schema using  ( ParentVec ; parent )
open import Setoid.Algebras.Basic                  using  ( 𝕌[_] ; 𝔻[_] )

private variable α ρ : Level
```
-->

#### The partition subgroup predicate

`PartitionSubgroups`{.AgdaModule}` n 𝒢` packages the family `K` for a fixed
power, together with the diagonal of [Classical.Structures.Group.Diagonal][].

```agda
module PartitionSubgroups (n : ℕ) (𝒢 : Group α ρ) where

  open GroupPower (Fin n) 𝒢 public
  open DiagonalSubgroup (Fin n) 𝒢 public

  private
    𝑮 = 𝒢 .proj₁
    Π𝑮 = ⨅ᵍ-Group .proj₁

  open Setoid 𝔻[ 𝑮 ] using (reflexive ; _≈_) renaming (sym to ≈sym ; trans to ≈trans)
  open Setoid 𝔻[ Π𝑮 ] using () renaming ( _≈_ to _≈ᴵ_ )
  open Group-Op 𝒢 using ( ε )

  -- Membership: the tuple is constant on every block of the partition.
  K : ParentVec n → Pred 𝕌[ Π𝑮 ] ρ
  K pv x = ∀ {i j} → SameBlock pv i j → x i ≈ x j
```

Every `K pv` is an equality-respecting subgroup, by the same coordinatewise
rewriting as for the diagonal.

```agda
  -- K pv respects the pointwise equality of the power.
  K-respects : (pv : ParentVec n) → K pv Respects _≈ᴵ_
  K-respects pv e k {i} {j} sb = ≈trans (≈sym (e i)) (≈trans (k sb) (e j))

  -- K pv is closed under the power operations, hence a respecting subgroup.
  K-isSubgroup : (pv : ParentVec n) → IsSubgroup ⨅ᵍ-Group (K pv)
  K-isSubgroup pv = mkIsSubgroup ⨅ᵍ-Group (K-respects pv) ∙-closed ε-closed ⁻¹-closed
    where
    open Group-Op ⨅ᵍ-Group  using () renaming ( _∙_ to _⊗_ ; ε to e ; _⁻¹ to inv )

    ∙-closed : ∀ {x y} → x ∈ K pv → y ∈ K pv → x ⊗ y ∈ K pv
    ∙-closed {x} {y} kx ky {i} {j} sb =
      ≈trans  (⊗-pointwise x y i)
              (≈trans  (interp-cong 𝑮 ∙-Op λ { 0F → kx sb ; 1F → ky sb })
                       (≈sym (⊗-pointwise x y j)))

    ε-closed : e ∈ K pv
    ε-closed {i} {j} _ = ≈trans (e-pointwise i) (≈sym (e-pointwise j))

    ⁻¹-closed : ∀ {x} → x ∈ K pv → inv x ∈ K pv
    ⁻¹-closed {x} kx {i} {j} sb =
      ≈trans  (inv-pointwise x i)
              (≈trans  (interp-cong 𝑮 ⁻¹-Op λ { 0F → kx sb })
                       (≈sym (inv-pointwise x j)))
```

#### The sandwich `D ≤ Kπ ≤ Sⁿ`

Diagonal tuples are constant outright, so they lie in every partition subgroup;
the one-block partition recovers the diagonal exactly, and the discrete
partition imposes no constraint at all.

```agda
  -- The diagonal lies in every partition subgroup.
  Diag⊆K : (pv : ParentVec n) → Diag ⊆ K pv
  Diag⊆K pv d {i} {j} _ = d i j

  -- The one-block partition carves out exactly the diagonal.
  K⊤⊆Diag : K (⊤ᵉ n) ⊆ Diag
  K⊤⊆Diag k i j = k (⊤ᵉ-related n i j)

  Diag⊆K⊤ : Diag ⊆ K (⊤ᵉ n)
  Diag⊆K⊤ = Diag⊆K (⊤ᵉ n)

  -- The discrete partition constrains nothing: K ⊥ᵉ is the full power.
  K⊥-full : (x : 𝕌[ Π𝑮 ]) → x ∈ K (⊥ᵉ n)
  K⊥-full x {i} {j} sb = reflexive (cong x discrete)
    where
    discrete : i ≡ j
    discrete = trans (sym (parent-tab id i)) (trans sb (parent-tab id j))
```

#### Order reversal

Refinement reverses under `K`: a finer partition has more blocks, fewer
constancy constraints, and a larger subgroup.

```agda
  -- Monotone contravariance: pu ⊑ pw implies K pw ⊆ K pu.
  K-antitone : {pu pw : ParentVec n} → pu ⊑ pw → K pw ⊆ K pu
  K-antitone h k sb = k (h sb)
```

Conversely, inclusion of partition subgroups reflects refinement, given a
witness that the base group is nontrivial.  For `π`-related `i , j`, either the
`ρ`-relation of `i , j` is already decided true, or the indicator of the
`ρ`-block of `i` — the tuple `s` on that block and `ε` off it — lies in
`K ρ ⊆ K π` yet takes the values `s` at `i` and `ε` at `j`, forcing the
contradiction `s ≈ ε`.

```agda
  -- Reflection: K pw ⊆ K pu implies pu ⊑ pw, for a nontrivial base group.
  K-reflects : (s : 𝕌[ 𝑮 ]) → ¬ (s ≈ ε) → {pu pw : ParentVec n}
    → K pw ⊆ K pu → pu ⊑ pw
  K-reflects s s≉ε {pu} {pw} incl {i} {j} sbu = decide (parent pw i ≟ parent pw j)
    where
    -- The indicator of the pw-block of i.
    ind : 𝕌[ Π𝑮 ]
    ind k = if does (parent pw k ≟ parent pw i) then s else ε

    -- The indicator is constant on pw-blocks, so it lies in K pw.
    ind∈Kpw : ind ∈ K pw
    ind∈Kpw {k} {l} sb =
      reflexive (cong (λ t → if does (t ≟ parent pw i) then s else ε) sb)

    decide : Dec (SameBlock pw i j) → SameBlock pw i j
    decide (yes e)   = e
    decide (no ¬e)   = ⊥-elim (s≉ε s≈ε)
      where
      ind-i : ind i ≡ s
      ind-i = cong (λ b → if b then s else ε) (dec-true (parent pw i ≟ parent pw i) refl)

      ind-j : ind j ≡ ε
      ind-j = cong  (λ b → if b then s else ε)
                    (dec-false (parent pw j ≟ parent pw i) (λ e → ¬e (sym e)))

      s≈ε : s ≈ ε
      s≈ε = ≈trans  (reflexive (sym ind-i))
                    (≈trans (incl ind∈Kpw sbu) (reflexive ind-j))
```

Reflection upgrades mutual inclusion of partition subgroups to equality of partitions
— the injectivity of `π ↦ Kπ`, in the setoid sense.

```agda
  -- Mutual inclusion of partition subgroups gives equal partitions.
  K-injective : (s : 𝕌[ 𝑮 ]) → ¬ s ≈ ε → {pu pw : ParentVec n}
    → K pw ⊆ K pu → K pu ⊆ K pw → pu ≈ᵖ pw
  K-injective s s≉ε {pu} {pw} wu uw =
    K-reflects s s≉ε {pu = pu} {pw = pw} wu , K-reflects s s≉ε {pu = pw} {pw = pu} uw
```

[^1]: The negative form `Nontrivial`{.AgdaFunction} of
      [Classical.Structures.Group.MinimalNormal][] supplies no witness to build the
      indicator from.

[^2]: `K` is also *onto* the interval if `G` is a nonabelian simple group; this is
      **Kurzweil's lemma**, registered as an explicit hypothesis where the FLRP
      program consumes it ([FLRP.KurzweilInterval][]).
