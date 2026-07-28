---
layout: default
file: "src/Classical/Structures/Group/NormalSubgroupLattice.lagda.md"
title: "Classical.Structures.Group.NormalSubgroupLattice module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### The lattice of normal subgroups

This is the [Classical.Structures.Group.NormalSubgroupLattice][] module of the [Agda Universal Algebra Library][].

[Classical.Structures.Group.Congruences][] proves that the congruences of a group and
its normal subgroups correspond, as an order isomorphism of *posets*.  This module
upgrades both sides to lattices and states the isomorphism at that level: the normal
subgroups of `𝒢`{.AgdaBound} *at the absorbing level `L`* form a bounded, complete
lattice, and it is order isomorphic to the congruence lattice
`Con-CompleteLattice`{.AgdaFunction} of [Setoid.Congruences.CompleteLattice][].  The
level restriction is not a technicality to be read past; the next section says where it
comes from and why it cannot be dropped.

It stands to [Classical.Structures.Group.Congruences][] exactly as
[Classical.Structures.Group.SubgroupLattice][] stands to
[Classical.Structures.Group.Subgroups][]: the predicate and its theory in one module,
the lattice they generate in the next.

#### Why this is a separate module, and where the levels come from

The correspondence of [Classical.Structures.Group.Congruences][] holds at *every*
relation level `ℓ`{.AgdaBound}.  A lattice cannot: its join is a **generated**
congruence, and `Cg`{.AgdaFunction} of [Setoid.Congruences.Generation][] raises the
relation level by `𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ`.  So the join is an operation only at the *absorbing*
level

    L = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ ℓ₀   —   for `Sig-Group`, where `𝓞 = 𝓥 = 0ℓ`, just `α ⊔ ρ ⊔ ℓ₀`

at which level join is idempotent, which is precisely the level
[Setoid.Congruences.CompleteLattice][] fixes.  Keeping the two modules apart therefore
keeps the correspondence at its full generality instead of narrowing it to the one
level the lattice happens to need.

#### What is proved, and how much of it is transported

Only the **joins** are obtained through the correspondence.  Everything else is built
directly on the subgroup side, where it has its familiar description:

+  the binary meet `_∩ⁿ_`{.AgdaFunction} and the infinitary meet `⋂ⁿ`{.AgdaFunction}
   are **intersections** of the underlying predicates — a normal subgroup, because
   each closure property holds componentwise;
+  the bottom `𝟘ⁿ`{.AgdaFunction} is the `≈`-class of the identity, i.e.
   `trivialSubgroup`{.AgdaFunction} of [Classical.Structures.Group.Subgroups][] at
   level `L`{.AgdaFunction} (`𝟘ⁿ-trivial`{.AgdaFunction},
   `trivial-𝟘ⁿ`{.AgdaFunction}), and the top `𝟙ⁿ`{.AgdaFunction} is the whole carrier;
+  the binary join `_∨ⁿ_`{.AgdaFunction} and the infinitary join
   `⋁ⁿ`{.AgdaFunction} are **defined** as the image under
   `normalOf`{.AgdaFunction} of the corresponding congruence join, their universal
   properties following from the correspondence's monotonicity and round trips.

That asymmetry is honest rather than incidental, and it is worth stating plainly: a
join of normal subgroups is *not* the union, so there is nothing on the subgroup side
to define it as without either a generation principle for normal subgroups or the
complex product.  The library has neither in the form this would need, so the
correspondence supplies it.  **Caveat**: consequently `𝑴 ∨ⁿ 𝑵`{.AgdaFunction} is
characterized here only by its universal property (least normal subgroup above both);
identifying it with the complex product `MN` of
[Classical.Structures.Group.Complexes][] is left to future work.

The maps are then shown to **preserve the lattice operations**, which is what
distinguishes an isomorphism of lattices from an isomorphism of the underlying posets:
`normalOf-∧`{.AgdaFunction}, `normalOf-⋀`{.AgdaFunction} (both hold *definitionally* —
the identity class of an intersection of congruences is the intersection of the
identity classes), and `normalOf-∨`{.AgdaFunction}, `normalOf-⋁`{.AgdaFunction}.  None
of these is logically necessary — the operations are determined by the order, as
greatest lower and least upper bounds, so any order isomorphism carries them across —
but stating them turns that argument into checked mathematics.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.NormalSubgroupLattice where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                  using  ( _,_ ; _×_ ; proj₁ ; proj₂ )
open import Data.Unit.Base                using  ( ⊤ ; tt )
open import Level                         using  ( Level ; _⊔_ ; suc ; lift ; lower )
open import Relation.Binary               using  ( Setoid )
open import Relation.Binary.Definitions   using  ( Maximum ; Minimum )
open import Relation.Binary.Lattice       using  ( Infimum ; Supremum ; IsLattice ; Lattice
                                                 ; IsBoundedLattice ; BoundedLattice )
open import Relation.Unary                using  ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic        using  ( Group )
open import Classical.Structures.Group.Congruences  using  ( module GroupCongruences )
open import Classical.Structures.Group.Conjugation  using  ( module Conj )
open import Classical.Structures.Group.Subgroups    using  ( IsSubgroup ; mkIsSubgroup
                                                           ; trivialSubgroup )
open import Order.CompleteLattice                   using  ( CompleteLattice )
open import Order.Iso                               using  ( OrderIso )
open import Setoid.Algebras.Basic                   using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Congruences.Basic                using  ( Con ; 𝟘[_] ; 𝟙[_] )
open import Setoid.Congruences.CompleteLattice      using  ( Con-CompleteLattice
                                                           ; ⋀ ; ⋁ ; ⋁-upper ; ⋁-least )
open import Setoid.Congruences.Generation           using  ( _∨_ ; ∨-upperˡ ; ∨-upperʳ
                                                           ; ∨-least )
open import Setoid.Congruences.Lattice              using  ( _∧_ ; _≑_ )
                                                    renaming ( _⊆_ to _⊑_ )
```
-->

#### The ambient group and the absorbing level

```agda
module NormalSubgroupLattice {α ρ : Level} (𝒢 : Group α ρ) (ℓ₀ : Level) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming ( sym to ≈sym )
  open Conj 𝒢         using ( IsNormal )
  open GroupCongruences 𝒢

  -- The absorbing level of the congruence lattice of the group algebra; the two
  -- signature levels of `Sig-Group` are zero, so this is the `L` of
  -- [Setoid.Congruences.CompleteLattice] on the nose.
  L : Level
  L = α ⊔ ρ ⊔ ℓ₀

  -- The carrier: normal subgroups whose predicates live at the absorbing level.
  Nrmᴸ : Type (α ⊔ ρ ⊔ suc L)
  Nrmᴸ = NormalSubgroup L
```

#### Meets are intersections

The intersection of two normal subgroups is a normal subgroup: every closure property
of `IsSubgroup`{.AgdaRecord}, and normality itself, holds componentwise.  It is the
greatest lower bound because inclusion of predicates is, pointwise, conjunction of
membership.

```agda
  infixr 7 _∩ⁿ_

  -- The binary meet: the intersection of the underlying predicates.
  _∩ⁿ_ : Nrmᴸ → Nrmᴸ → Nrmᴸ
  𝑴 ∩ⁿ 𝑵 = P , P-isSubgroup , P-normal
    where
    P : Pred G L
    P x = x ∈ set 𝑴 × x ∈ set 𝑵

    open IsSubgroup (set-isSubgroup 𝑴)  using ()
      renaming ( respects to Mresp ; ∙-closed to M∙ ; ε-closed to Mε ; ⁻¹-closed to M⁻¹ )
    open IsSubgroup (set-isSubgroup 𝑵)  using ()
      renaming ( respects to Nresp ; ∙-closed to N∙ ; ε-closed to Nε ; ⁻¹-closed to N⁻¹ )

    P-isSubgroup : IsSubgroup 𝒢 P
    P-isSubgroup = mkIsSubgroup 𝒢  (λ x≈y p → Mresp x≈y (proj₁ p) , Nresp x≈y (proj₂ p))
                                   (λ p q → M∙ (proj₁ p) (proj₁ q) , N∙ (proj₂ p) (proj₂ q))
                                   (Mε , Nε)
                                   (λ p → M⁻¹ (proj₁ p) , N⁻¹ (proj₂ p))

    P-normal : IsNormal P
    P-normal g p = set-normal 𝑴 g (proj₁ p) , set-normal 𝑵 g (proj₂ p)

  ∩ⁿ-infimum : Infimum (_≤ⁿ_ {L}) _∩ⁿ_
  ∩ⁿ-infimum 𝑴 𝑵 = proj₁ , proj₂ , λ 𝑷 𝑷≤𝑴 𝑷≤𝑵 p → 𝑷≤𝑴 p , 𝑷≤𝑵 p
```

The same argument, indexwise, gives the infinitary meet.  It stays at level
`L`{.AgdaFunction} because the index type is `ℓ₀`-small and `ℓ₀ ⊑ L`.

```agda
  -- The infinitary meet: the intersection of an ℓ₀-indexed family.
  ⋂ⁿ : {I : Type ℓ₀} → (I → Nrmᴸ) → Nrmᴸ
  ⋂ⁿ {I} 𝒩 = P , P-isSubgroup , P-normal
    where
    P : Pred G L
    P x = (i : I) → x ∈ set (𝒩 i)

    P-isSubgroup : IsSubgroup 𝒢 P
    P-isSubgroup = mkIsSubgroup 𝒢
      (λ x≈y p i  → IsSubgroup.respects   (set-isSubgroup (𝒩 i)) x≈y (p i))
      (λ p q i    → IsSubgroup.∙-closed   (set-isSubgroup (𝒩 i)) (p i) (q i))
      (λ i        → IsSubgroup.ε-closed   (set-isSubgroup (𝒩 i)))
      (λ p i      → IsSubgroup.⁻¹-closed  (set-isSubgroup (𝒩 i)) (p i))

    P-normal : IsNormal P
    P-normal g p i = set-normal (𝒩 i) g (p i)

  ⋂ⁿ-lower : {I : Type ℓ₀} (𝒩 : I → Nrmᴸ) (i : I) → ⋂ⁿ 𝒩 ≤ⁿ 𝒩 i
  ⋂ⁿ-lower 𝒩 i p = p i

  ⋂ⁿ-greatest : {I : Type ℓ₀} (𝒩 : I → Nrmᴸ) (𝑷 : Nrmᴸ)
    →  (∀ i → 𝑷 ≤ⁿ 𝒩 i) → 𝑷 ≤ⁿ ⋂ⁿ 𝒩
  ⋂ⁿ-greatest 𝒩 𝑷 h p i = h i p
```

#### The bounds

The bottom and top are the images of the diagonal and total congruences.  Taking them
this way is not a dodge: `normalOf`{.AgdaFunction} of the diagonal *unfolds* to the
`≈`-class of the identity (lifted to level `L`{.AgdaFunction}), and of the total
congruence to the whole carrier — so `𝟘ⁿ`{.AgdaFunction} is
`trivialSubgroup`{.AgdaFunction} of [Classical.Structures.Group.Subgroups][] and
`𝟙ⁿ`{.AgdaFunction} the full subgroup, with the subgroup and normality proofs already
discharged by the correspondence.  The two membership lemmas below record that
identification rather than leaving it to the reader to unfold.

Minimality is the one fact with content: every subgroup contains `ε`{.AgdaFunction},
and an equality-respecting one therefore contains its whole `≈`-class.

```agda
  -- The bottom: the ≈-class of the identity.
  𝟘ⁿ : Nrmᴸ
  𝟘ⁿ = normalOf (𝟘[ 𝑮 ] {L})

  -- The top: the whole carrier.
  𝟙ⁿ : Nrmᴸ
  𝟙ⁿ = normalOf (𝟙[ 𝑮 ] {L})

  -- 𝟘ⁿ is the trivial subgroup { x ∣ x ≈ ε }, up to the level lift.
  𝟘ⁿ-trivial : {x : G} → x ∈ set 𝟘ⁿ → x ∈ proj₁ (trivialSubgroup 𝒢)
  𝟘ⁿ-trivial = lower

  trivial-𝟘ⁿ : {x : G} → x ∈ proj₁ (trivialSubgroup 𝒢) → x ∈ set 𝟘ⁿ
  trivial-𝟘ⁿ = lift

  -- 𝟙ⁿ is the whole carrier.
  𝟙ⁿ-full : {x : G} → x ∈ set 𝟙ⁿ
  𝟙ⁿ-full = lift tt

  -- Every normal subgroup contains the ≈-class of the identity ...
  𝟘ⁿ-minimum : Minimum (_≤ⁿ_ {L}) 𝟘ⁿ
  𝟘ⁿ-minimum 𝑵 p = respects (≈sym (lower p)) ε-closed
    where open IsSubgroup (set-isSubgroup 𝑵) using ( respects ; ε-closed )

  -- ... and is contained in the whole carrier.
  𝟙ⁿ-maximum : Maximum (_≤ⁿ_ {L}) 𝟙ⁿ
  𝟙ⁿ-maximum 𝑵 _ = lift tt
```

#### Joins come from the correspondence

The join of two normal subgroups is the normal subgroup matching the join of the two
matching congruences.  Its universal property is the congruence-side one pushed across
the correspondence: each inclusion is one monotonicity step composed with one half of a
round trip.  (The endpoint implicits of `normalOf-mono`{.AgdaFunction} and
`congruenceOf-mono`{.AgdaFunction} are supplied by hand throughout, per the
non-injectivity discipline of [Setoid.Congruences.Lattice][].)

```agda
  infixr 6 _∨ⁿ_

  -- The binary join: the normal subgroup of the join of the corresponding congruences.
  _∨ⁿ_ : Nrmᴸ → Nrmᴸ → Nrmᴸ
  𝑴 ∨ⁿ 𝑵 = normalOf (congruenceOf 𝑴 ∨ congruenceOf 𝑵)

  ∨ⁿ-supremum : Supremum (_≤ⁿ_ {L}) _∨ⁿ_
  ∨ⁿ-supremum 𝑴 𝑵 = upperˡ , upperʳ , least
    where
    θ φ : Con 𝑮 L
    θ = congruenceOf 𝑴
    φ = congruenceOf 𝑵

    upperˡ : 𝑴 ≤ⁿ (𝑴 ∨ⁿ 𝑵)
    upperˡ p = normalOf-mono {L} {θ} {θ ∨ φ} (∨-upperˡ θ φ)
                 (proj₂ (normalOf∘congruenceOf 𝑴) p)

    upperʳ : 𝑵 ≤ⁿ (𝑴 ∨ⁿ 𝑵)
    upperʳ p = normalOf-mono {L} {φ} {θ ∨ φ} (∨-upperʳ θ φ)
                 (proj₂ (normalOf∘congruenceOf 𝑵) p)

    least : (𝑷 : Nrmᴸ) → 𝑴 ≤ⁿ 𝑷 → 𝑵 ≤ⁿ 𝑷 → (𝑴 ∨ⁿ 𝑵) ≤ⁿ 𝑷
    least 𝑷 𝑴≤𝑷 𝑵≤𝑷 p = proj₁ (normalOf∘congruenceOf 𝑷)
      (normalOf-mono {L} {θ ∨ φ} {congruenceOf 𝑷}
        (∨-least θ φ (congruenceOf 𝑷)  (congruenceOf-mono {L} {𝑴} {𝑷} 𝑴≤𝑷)
                                       (congruenceOf-mono {L} {𝑵} {𝑷} 𝑵≤𝑷))
        p)
```

The infinitary join is the same construction over an `ℓ₀`-indexed family, using the
congruence side's `⋁`{.AgdaFunction}.

```agda
  -- The infinitary join.
  ⋁ⁿ : {I : Type ℓ₀} → (I → Nrmᴸ) → Nrmᴸ
  ⋁ⁿ 𝒩 = normalOf (⋁ 𝑮 ℓ₀ (λ i → congruenceOf (𝒩 i)))

  ⋁ⁿ-upper : {I : Type ℓ₀} (𝒩 : I → Nrmᴸ) (i : I) → 𝒩 i ≤ⁿ ⋁ⁿ 𝒩
  ⋁ⁿ-upper 𝒩 i p =
    normalOf-mono  {L} {congruenceOf (𝒩 i)} {⋁ 𝑮 ℓ₀ (λ j → congruenceOf (𝒩 j))}
                   (⋁-upper 𝑮 ℓ₀ (λ j → congruenceOf (𝒩 j)) i)
                   (proj₂ (normalOf∘congruenceOf (𝒩 i)) p)

  ⋁ⁿ-least : {I : Type ℓ₀} (𝒩 : I → Nrmᴸ) (𝑷 : Nrmᴸ)
    →  (∀ i → 𝒩 i ≤ⁿ 𝑷) → ⋁ⁿ 𝒩 ≤ⁿ 𝑷
  ⋁ⁿ-least 𝒩 𝑷 h p = proj₁ (normalOf∘congruenceOf 𝑷)
    (normalOf-mono  {L} {⋁ 𝑮 ℓ₀ (λ j → congruenceOf (𝒩 j))} {congruenceOf 𝑷}
                    (⋁-least 𝑮 ℓ₀ (λ j → congruenceOf (𝒩 j)) (congruenceOf 𝑷)
                      (λ i → congruenceOf-mono {L} {𝒩 i} {𝑷} (h i)))
                    p)
```

#### The bundles

The partial order comes from [Classical.Structures.Group.Congruences][]; adding the
two binary operations gives a lattice, the two bounds a bounded lattice, and the two
infinitary operations a complete lattice — the same three bundles
[Setoid.Congruences.CompleteLattice][] assembles on the congruence side.

```agda
  Nrm-isLattice : IsLattice (_≈ⁿ_ {L}) _≤ⁿ_ _∨ⁿ_ _∩ⁿ_
  Nrm-isLattice = record  { isPartialOrder  = ≤ⁿ-isPartialOrder
                          ; supremum        = ∨ⁿ-supremum
                          ; infimum         = ∩ⁿ-infimum
                          }

  NormalSubgroup-Lattice : Lattice (α ⊔ ρ ⊔ suc L) (α ⊔ L) (α ⊔ L)
  NormalSubgroup-Lattice = record  { Carrier    = Nrmᴸ
                                   ; _≈_        = _≈ⁿ_
                                   ; _≤_        = _≤ⁿ_
                                   ; _∨_        = _∨ⁿ_
                                   ; _∧_        = _∩ⁿ_
                                   ; isLattice  = Nrm-isLattice
                                   }

  Nrm-isBoundedLattice : IsBoundedLattice (_≈ⁿ_ {L}) _≤ⁿ_ _∨ⁿ_ _∩ⁿ_ 𝟙ⁿ 𝟘ⁿ
  Nrm-isBoundedLattice = record  { isLattice  = Nrm-isLattice
                                 ; maximum    = 𝟙ⁿ-maximum
                                 ; minimum    = 𝟘ⁿ-minimum
                                 }

  NormalSubgroup-BoundedLattice : BoundedLattice (α ⊔ ρ ⊔ suc L) (α ⊔ L) (α ⊔ L)
  NormalSubgroup-BoundedLattice = record  { Carrier           = Nrmᴸ
                                          ; _≈_               = _≈ⁿ_
                                          ; _≤_               = _≤ⁿ_
                                          ; _∨_               = _∨ⁿ_
                                          ; _∧_               = _∩ⁿ_
                                          ; ⊤                 = 𝟙ⁿ
                                          ; ⊥                 = 𝟘ⁿ
                                          ; isBoundedLattice  = Nrm-isBoundedLattice
                                          }

  NormalSubgroup-CompleteLattice : CompleteLattice (α ⊔ ρ ⊔ suc L) (α ⊔ L) (α ⊔ L) ℓ₀
  NormalSubgroup-CompleteLattice = record
    { Carrier         = Nrmᴸ
    ; _≈_             = _≈ⁿ_
    ; _≤_             = _≤ⁿ_
    ; isPartialOrder  = ≤ⁿ-isPartialOrder
    ; ⨆               = ⋁ⁿ
    ; ⨅               = ⋂ⁿ
    ; ⨆-upper         = ⋁ⁿ-upper
    ; ⨆-least         = ⋁ⁿ-least
    ; ⨅-lower         = ⋂ⁿ-lower
    ; ⨅-greatest      = ⋂ⁿ-greatest
    }
```

#### The isomorphism of lattices

The two complete lattices have the *same* underlying orders as the two posets of
[Classical.Structures.Group.Congruences][], so the lattice isomorphism is that
module's `normal-congruence-iso`{.AgdaFunction}, instantiated at the absorbing level.
Stating it through the bundles' own `_≈_`{.AgdaField} and `_≤_`{.AgdaField} is the
point: it is what makes "these two *lattices* are isomorphic" a statement Agda has
checked, rather than a reading a human supplies.

```agda
  -- Con-CompleteLattice 𝑮 ℓ₀  ≅  NormalSubgroup-CompleteLattice.
  NormalCongruenceLatticeIso : Type (α ⊔ ρ ⊔ suc L)
  NormalCongruenceLatticeIso =
    OrderIso  (CompleteLattice._≈_ (Con-CompleteLattice 𝑮 ℓ₀))
              (CompleteLattice._≤_ (Con-CompleteLattice 𝑮 ℓ₀))
              (CompleteLattice._≈_ NormalSubgroup-CompleteLattice)
              (CompleteLattice._≤_ NormalSubgroup-CompleteLattice)

  normal-congruence-latticeIso : NormalCongruenceLatticeIso
  normal-congruence-latticeIso = normal-congruence-iso L
```

#### The maps preserve the lattice operations

An order isomorphism carries greatest lower bounds to greatest lower bounds and least
upper bounds to least upper bounds, so the preservation statements below are formal
consequences of the isomorphism.  They are nonetheless proved, because they are what a
reader means by "isomorphism of lattices" and because two of the four turn out to hold
*definitionally*: the identity class of an intersection of congruences **is**, on the
nose, the intersection of the identity classes.

```agda
  -- Meets are preserved, definitionally.
  normalOf-∧ : (θ φ : Con 𝑮 L) → normalOf (θ ∧ φ) ≈ⁿ (normalOf θ ∩ⁿ normalOf φ)
  normalOf-∧ θ φ = (λ p → p) , (λ p → p)

  normalOf-⋀ : {I : Type ℓ₀} (f : I → Con 𝑮 L)
    →  normalOf (⋀ 𝑮 ℓ₀ f) ≈ⁿ ⋂ⁿ (λ i → normalOf (f i))
  normalOf-⋀ f = (λ p → p) , (λ p → p)
```

Joins need the round trip, since `_∨ⁿ_`{.AgdaFunction} re-enters the congruence side
through `congruenceOf`{.AgdaFunction}.  The bridging step is monotonicity of the
congruence join in both arguments, which we prove here because
[Setoid.Congruences.Generation][] states only the three universal-property lemmas.

```agda
  private
    -- The congruence join is monotone in both arguments.
    ∨-mono : (θ φ θ' φ' : Con 𝑮 L) → θ ⊑ θ' → φ ⊑ φ' → (θ ∨ φ) ⊑ (θ' ∨ φ')
    ∨-mono θ φ θ' φ' θ⊑θ' φ⊑φ' =
      ∨-least θ φ (θ' ∨ φ')  (λ p → ∨-upperˡ θ' φ' (θ⊑θ' p))
                             (λ q → ∨-upperʳ θ' φ' (φ⊑φ' q))

    -- ... as is the infinitary one.
    ⋁-mono : {I : Type ℓ₀} (f g : I → Con 𝑮 L)
      →  (∀ i → f i ⊑ g i) → ⋁ 𝑮 ℓ₀ f ⊑ ⋁ 𝑮 ℓ₀ g
    ⋁-mono f g f⊑g =
      ⋁-least 𝑮 ℓ₀ f (⋁ 𝑮 ℓ₀ g) (λ i p → ⋁-upper 𝑮 ℓ₀ g i (f⊑g i p))

  -- Joins are preserved.
  normalOf-∨ : (θ φ : Con 𝑮 L) → normalOf (θ ∨ φ) ≈ⁿ (normalOf θ ∨ⁿ normalOf φ)
  normalOf-∨ θ φ = normalOf-cong {L} {θ ∨ φ} {θ' ∨ φ'}
    (  ∨-mono θ φ θ' φ'  (proj₂ (congruenceOf∘normalOf θ)) (proj₂ (congruenceOf∘normalOf φ))
    ,  ∨-mono θ' φ' θ φ  (proj₁ (congruenceOf∘normalOf θ)) (proj₁ (congruenceOf∘normalOf φ))
    )
    where
    θ' φ' : Con 𝑮 L
    θ' = congruenceOf (normalOf θ)
    φ' = congruenceOf (normalOf φ)

  normalOf-⋁ : {I : Type ℓ₀} (f : I → Con 𝑮 L)
    →  normalOf (⋁ 𝑮 ℓ₀ f) ≈ⁿ ⋁ⁿ (λ i → normalOf (f i))
  normalOf-⋁ f = normalOf-cong {L} {⋁ 𝑮 ℓ₀ f} {⋁ 𝑮 ℓ₀ f'}
    (  ⋁-mono f f'  (λ i → proj₂ (congruenceOf∘normalOf (f i)))
    ,  ⋁-mono f' f  (λ i → proj₁ (congruenceOf∘normalOf (f i)))
    )
    where
    f' : _ → Con 𝑮 L
    f' i = congruenceOf (normalOf (f i))
```

The other map preserves them too, and here *every* clause is free.  Meets again agree
on the nose — the relation "`x ∙ y ⁻¹` lies in both `M` and `N`" **is** the
intersection of the two relations — and each join and each bound is a round trip of the
correspondence at the congruence that defines it.  Together with the four lemmas above
this makes both directions checked lattice homomorphisms, so "isomorphism of lattices"
is discharged in the sense a reader expects and not merely in the sense that an order
isomorphism formally implies.

```agda
  -- Meets, definitionally.
  congruenceOf-∩ : (𝑴 𝑵 : Nrmᴸ)
    →  congruenceOf (𝑴 ∩ⁿ 𝑵) ≑ (congruenceOf 𝑴 ∧ congruenceOf 𝑵)
  congruenceOf-∩ 𝑴 𝑵 = (λ p → p) , (λ p → p)

  congruenceOf-⋂ : {I : Type ℓ₀} (𝒩 : I → Nrmᴸ)
    →  congruenceOf (⋂ⁿ 𝒩) ≑ ⋀ 𝑮 ℓ₀ (λ i → congruenceOf (𝒩 i))
  congruenceOf-⋂ 𝒩 = (λ p → p) , (λ p → p)

  -- Joins and bounds, each one round trip.
  congruenceOf-∨ : (𝑴 𝑵 : Nrmᴸ)
    →  congruenceOf (𝑴 ∨ⁿ 𝑵) ≑ (congruenceOf 𝑴 ∨ congruenceOf 𝑵)
  congruenceOf-∨ 𝑴 𝑵 = congruenceOf∘normalOf (congruenceOf 𝑴 ∨ congruenceOf 𝑵)

  congruenceOf-⋁ : {I : Type ℓ₀} (𝒩 : I → Nrmᴸ)
    →  congruenceOf (⋁ⁿ 𝒩) ≑ ⋁ 𝑮 ℓ₀ (λ i → congruenceOf (𝒩 i))
  congruenceOf-⋁ 𝒩 = congruenceOf∘normalOf (⋁ 𝑮 ℓ₀ (λ i → congruenceOf (𝒩 i)))

  congruenceOf-𝟘 : congruenceOf 𝟘ⁿ ≑ 𝟘[ 𝑮 ] {L}
  congruenceOf-𝟘 = congruenceOf∘normalOf (𝟘[ 𝑮 ] {L})

  congruenceOf-𝟙 : congruenceOf 𝟙ⁿ ≑ 𝟙[ 𝑮 ] {L}
  congruenceOf-𝟙 = congruenceOf∘normalOf (𝟙[ 𝑮 ] {L})
```
