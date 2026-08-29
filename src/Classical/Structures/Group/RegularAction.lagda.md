---
layout: default
file: "src/Classical/Structures/Group/RegularAction.lagda.md"
title: "Classical.Structures.Group.RegularAction module"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### The regular action and its congruence–subgroup correspondence

This is the [Classical.Structures.Group.RegularAction][] module of the [Agda Universal Algebra Library][].

Instantiating the coset G-set of [Classical.Structures.Group.GSet][] at the
**trivial subgroup** gives the (left-)regular action `G ↷ G`, packaged as a
unary algebra whose operations are the left translations `x ↦ g ∙ x`.  This
module records the classical correspondence for that instance:

+  **congruence ⟶ subgroup** (`Kθ`{.AgdaFunction}): the `θ`-class of the
   identity is a subgroup, decided — at Layer D — by `θ`'s own decision
   procedure at the pair `(ε , g)`;
+  **subgroup ⟶ congruence** (`cosetCon`{.AgdaFunction}): the left-coset
   relation `x ⁻¹ ∙ y ∈ K` of any equality-respecting subgroup `K` is a
   congruence of the regular action, decided by one group multiplication once
   membership in `K`{.AgdaBound} is decidable;
+  the two maps are mutually inverse (`cosetCon-Kθ`{.AgdaFunction},
   `Kθ-cosetCon`{.AgdaFunction}) and monotone in both directions
   (`cosetCon-mono`{.AgdaFunction}, `cosetCon-reflect`{.AgdaFunction}).

In words: **the congruence lattice of the regular action is the full subgroup
lattice `Sub(G)`**.  This is the `H = 1` instance of the Pálfy–Pudlák
correspondence `Con (G ↷ G/H) ≅ [H , G]`, whose general form — stated over the
respecting interval, at both layers — is the WP-3 bridge [FLRP.Bridge][]
(issue #454).  The instance is restated here, in the `Classical/` tree, for
two reasons.  First, layering: `Classical/` cannot import `FLRP/`, and the
consumers of the regular action are not FLRP-specific (any development
wanting `Sub(G)` as a concrete congruence lattice can use this module).
Second, the trivial-subgroup instance needs none of the interval apparatus:
"subgroup above the trivial subgroup" is no constraint at all — reflexivity of
the coset congruence over the carrier's coset equality is exactly
`ε`-closedness plus `respects`{.AgdaField} — so the statements simplify to
plain `Subgroup`{.AgdaFunction}s and `DecSubgroup`{.AgdaFunction}s.

The FLRP consumer of this module is the ambient-closedness step of Snow's
filter-ideal lemma (issue #530): both concrete filter-ideal instances present
their ambient lattice as `Sub(G) = Con (G ↷ G)`, with the translations as the
ambient operations, so "every congruence respecting the translations is a
coset partition" is `cosetCon-Kθ`{.AgdaFunction} — no unary-reduction theorem
(issue #501) is consumed.

#### A note on opacity

Several definitions below are sealed in `opaque`{.AgdaKeyword} blocks, and at
the scale this module is used for that is load-bearing rather than
stylistic.  A concrete instance — the alternating group `A5` on 60 points, in
the `L16` representation of issue #530 — carries group-law witnesses that are
`from-yes`{.AgdaFunction} of decision sweeps over the whole carrier.  Those
witnesses sit inside the group bundle that every type here mentions, so a
goal comparing the coset congruences of two *named* subgroups will, if
nothing blocks it, normalize the entire tower; measured, one such comparison
exhausted a 32 GB heap.  Sealing the proofs stops the unfolding at a name and
costs nothing, since no consumer needs a subgroup axiom or a round-trip proof
to *compute* — only to exist.  Two further consequences shape the code below:
the coset relation is written out directly instead of through a
`Coset`{.AgdaModule} module application (a module application at a concrete
subgroup re-instantiates that module, and `Algebra.Properties.Group` with
it), and every function taking a subgroup reads it through
`proj₁`{.AgdaFunction} / `proj₂`{.AgdaFunction} rather than a pattern match,
so its result reduces without forcing the argument open.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.RegularAction where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns             using ( 0F )
open import Data.Product                  using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                         using ( Level )
open import Relation.Binary               using ( Setoid ; IsEquivalence )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group               using  ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic      using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups  using  ( IsSubgroup ; mkIsSubgroup
                                                         ; Subgroup ; DecSubgroup
                                                         ; trivialSubgroup )
open import Classical.Structures.Group.Cosets     using  ( module Coset )
open import Classical.Structures.Group.GSet       using  ( module CosetAction )
open import Setoid.Algebras.Basic                 using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic              using  ( Con ; IsCongruence ; mkcon
                                                         ; _∣≈_ ; reflexive
                                                         ; is-equivalence
                                                         ; is-compatible )
open import Setoid.Congruences.Lattice            using  ( _≑_ )
                                                  renaming ( _⊆_ to _⊑_ )
open import Setoid.Congruences.Finite.Basic       using  ( DecCon )
```
-->

#### The regular action

The development is parameterized by a group; the coset machinery is
instantiated at the trivial subgroup, so the carrier's coset equality `_∼_`
identifies exactly the `≈`-equal elements (via one group computation), and the
`CosetAction`{.AgdaModule} exports below *are* the regular action.

```agda
module Regular {α ρ : Level} (𝒢 : Group α ρ) where

  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]            using ( _≈_ )
                                renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢               using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; idˡ-law
                                       ; idʳ-law ; invˡ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using  ( ε⁻¹≈ε ; \\-leftDividesˡ )

  -- The trivial subgroup (the ≈-class of ε) and its coset machinery.
  H₁ : Pred G ρ
  H₁ = proj₁ (trivialSubgroup 𝒢)

  H₁-sg : IsSubgroup 𝒢 H₁
  H₁-sg = proj₂ (trivialSubgroup 𝒢)

  open Coset 𝒢 H₁ H₁-sg               using ( _∼_ ; ≈⇒∼ ; ∼-dec )
  open CosetAction 𝒢 H₁ H₁-sg public  using ( cosetAlgebra ; cosetAlgebra-FiniteAlgebra )

  -- Membership in the trivial subgroup is decided by one equality test, so a
  -- finite group makes the regular action a finite algebra.
  regular-FiniteAlgebra : FiniteAlgebra 𝑮 → FiniteAlgebra cosetAlgebra
  regular-FiniteAlgebra fin =
    cosetAlgebra-FiniteAlgebra fin (∼-dec (λ x → FiniteAlgebra._≟_ fin x ε))
```

#### Elementary facts about a congruence of the regular action

As in the general bridge: a congruence is reflexive over the coset equality,
symmetric, transitive, and invariant under every left translation.  One
group-arithmetic fact (`ε⁻¹∙`{.AgdaFunction}) serves the round trips.

```agda
  module _ {ℓ : Level} where

    private
      module _ ((_θ_ , θcon) : Con cosetAlgebra ℓ) where

        θ-refl : {a b : G} → a ∼ b → a θ b
        θ-refl = reflexive θcon

        θ-sym : {a b : G} → a θ b → b θ a
        θ-sym = IsEquivalence.sym (is-equivalence θcon)

        θ-trans : {a b c : G} → a θ b → b θ c → a θ c
        θ-trans = IsEquivalence.trans (is-equivalence θcon)

        -- Compatibility of θ with the unary operation symbol g: left translation.
        θ-transl : (g : G) {a b : G} → a θ b → (g ∙ a) θ (g ∙ b)
        θ-transl g {a} {b} p = is-compatible θcon g {λ _ → a} {λ _ → b} (λ _ → p)

      ε⁻¹∙ : (a : G) → ε ⁻¹ ∙ a ≈ a
      ε⁻¹∙ a = ≈trans (∙-cong ε⁻¹≈ε ≈refl) (idˡ-law a)
```

#### Congruence to subgroup: the class of the identity

`Kθ θ`{.AgdaFunction} is the `θ`-class of `ε`, read as a predicate on the
carrier.  The subgroup obligations are the same short congruence computations
as in the general bridge, unchanged by the specialization.

```agda
    -- The θ-class of the identity.
    Kθ : Con cosetAlgebra ℓ → Pred G ℓ
    Kθ (_θ_ , _) g = ε θ g

    private
      Kθ-ε : (θ : Con cosetAlgebra ℓ) → ε ∈ Kθ θ
      Kθ-ε (_ , θcon) = IsEquivalence.refl (is-equivalence θcon)

      Kθ-∙ : (θ : Con cosetAlgebra ℓ) {x y : G} → x ∈ Kθ θ → y ∈ Kθ θ → x ∙ y ∈ Kθ θ
      Kθ-∙ θ {x} {y} εx εy =
        θ-trans θ εx (θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law x)))) (θ-transl θ x εy))

      Kθ-⁻¹ : (θ : Con cosetAlgebra ℓ) {x : G} → x ∈ Kθ θ → x ⁻¹ ∈ Kθ θ
      Kθ-⁻¹ θ {x} εx = θ-sym θ
        (θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law (x ⁻¹)))))
                   (θ-trans θ (θ-transl θ (x ⁻¹) εx) (θ-refl θ (≈⇒∼ (invˡ-law x)))))

      Kθ-resp : (θ : Con cosetAlgebra ℓ) → ∀ {x y} → x ≈ y → x ∈ Kθ θ → y ∈ Kθ θ
      Kθ-resp θ x≈y εx = θ-trans θ εx (θ-refl θ (≈⇒∼ x≈y))

    -- The θ-class of the identity is a subgroup; the axioms are sealed.
    opaque
      Kθ-isSubgroup : (θ : Con cosetAlgebra ℓ) → IsSubgroup 𝒢 (Kθ θ)
      Kθ-isSubgroup θ = mkIsSubgroup 𝒢 (Kθ-resp θ) (Kθ-∙ θ) (Kθ-ε θ) (Kθ-⁻¹ θ)

    Kθ-subgroup : Con cosetAlgebra ℓ → Subgroup 𝒢 ℓ
    Kθ-subgroup θ = Kθ θ , Kθ-isSubgroup θ

    -- At Layer D: a decidable congruence decides membership in its own
    -- ε-class, by running its decision procedure at (ε , g).
    Kθᵈ : DecCon cosetAlgebra ℓ → DecSubgroup 𝒢 ℓ
    Kθᵈ d = Kθ-subgroup (proj₁ d) , λ g → proj₂ d ε g
```

#### Subgroup to congruence: the coset partition

For any subgroup `K`, the left-coset relation of `K` is a congruence of the
regular action.  Reflexivity over the (trivial-subgroup) coset equality is
where "every subgroup lies above the trivial subgroup" enters: an element of
the trivial subgroup is `≈ ε`, hence in `K` by `respects`{.AgdaField} and
`ε`-closedness.  The equivalence and translation-compatibility are the stock
`Coset`{.AgdaModule} lemmas at `K` — consumed once, generically, inside the
opaque block, so that no call site re-instantiates them.

```agda
    -- The left-coset relation of K: x and y agree modulo K.
    cosetRel : Subgroup 𝒢 ℓ → G → G → Type ℓ
    cosetRel K x y = x ⁻¹ ∙ y ∈ proj₁ K

    opaque
      cosetIsCongruence : (K : Subgroup 𝒢 ℓ) → IsCongruence cosetAlgebra (cosetRel K)
      cosetIsCongruence K = mkcon reflx equivx compatx
        where
        K-sg : IsSubgroup 𝒢 (proj₁ K)
        K-sg = proj₂ K

        reflx : {a b : G} → a ∼ b → cosetRel K a b
        reflx a∼b = IsSubgroup.respects K-sg (≈sym a∼b) (IsSubgroup.ε-closed K-sg)

        equivx : IsEquivalence (cosetRel K)
        equivx = Coset.∼-isEquivalence 𝒢 (proj₁ K) K-sg

        compatx : cosetAlgebra ∣≈ cosetRel K
        compatx g h = Coset.∼-congˡ 𝒢 (proj₁ K) K-sg g (h 0F)

    cosetCon : Subgroup 𝒢 ℓ → Con cosetAlgebra ℓ
    cosetCon K = cosetRel K , cosetIsCongruence K

    -- At Layer D: the coset partition of a decidable subgroup is decided by
    -- one group multiplication and one membership test.
    cosetConᵈ : DecSubgroup 𝒢 ℓ → DecCon cosetAlgebra ℓ
    cosetConᵈ K = cosetCon (proj₁ K) , λ x y → proj₂ K (x ⁻¹ ∙ y)
```

#### Mutual inverseness and monotonicity

Every congruence of the regular action *is* the coset partition of its
`ε`-class (`cosetCon-Kθ`{.AgdaFunction}) — this is the ambient-closedness fact
the filter-ideal applications consume — and every subgroup is recovered from
its coset partition (`Kθ-cosetCon`{.AgdaFunction}).  Containment transfers
both ways, so the correspondence is an order isomorphism between
`Con (G ↷ G)` and `Sub(G)`.

```agda
    opaque
      -- Round trip on congruences: the coset partition of the ε-class is θ.
      cosetCon-Kθ : (θ : Con cosetAlgebra ℓ) → cosetCon (Kθ-subgroup θ) ≑ θ
      cosetCon-Kθ θ = fwd , bwd
        where
        fwd : cosetCon (Kθ-subgroup θ) ⊑ θ
        fwd {x} {y} q =
          θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law x))))
                    (θ-trans θ (θ-transl θ x q) (θ-refl θ (≈⇒∼ (\\-leftDividesˡ x y))))

        bwd : θ ⊑ cosetCon (Kθ-subgroup θ)
        bwd {x} {y} p =
          θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (invˡ-law x)))) (θ-transl θ (x ⁻¹) p)

      -- Round trip on subgroups: the ε-class of the coset partition is K.
      Kθ-cosetCon :  (K : Subgroup 𝒢 ℓ)
        →            (Kθ (cosetCon K) ⊆ proj₁ K) × (proj₁ K ⊆ Kθ (cosetCon K))
      Kθ-cosetCon K = fwd , bwd
        where
        fwd : Kθ (cosetCon K) ⊆ proj₁ K
        fwd {g} p = IsSubgroup.respects (proj₂ K) (ε⁻¹∙ g) p

        bwd : proj₁ K ⊆ Kθ (cosetCon K)
        bwd {g} p = IsSubgroup.respects (proj₂ K) (≈sym (ε⁻¹∙ g)) p

      -- Subgroup containment forwards to coset-partition containment ...
      cosetCon-mono :  (K L : Subgroup 𝒢 ℓ) → proj₁ K ⊆ proj₁ L
        →              cosetCon K ⊑ cosetCon L
      cosetCon-mono K L K⊆L p = K⊆L p

      -- ... and reflects back, through the ε-class.
      cosetCon-reflect :  (K L : Subgroup 𝒢 ℓ) → cosetCon K ⊑ cosetCon L
        →                 proj₁ K ⊆ proj₁ L
      cosetCon-reflect K L sub {x} x∈K =
        IsSubgroup.respects (proj₂ L) (ε⁻¹∙ x)
          (sub (IsSubgroup.respects (proj₂ K) (≈sym (ε⁻¹∙ x)) x∈K))
```

--------------------------------------
