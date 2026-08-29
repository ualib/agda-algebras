---
layout: default
file: "src/FLRP/Hunt.lagda.md"
title: "FLRP.Hunt module (The Agda Universal Algebra Library)"
date: "2026-08-29"
author: "the agda-algebras development team"
---

### The hunt for an empty intersection: the constraint dossier

This is the [FLRP.Hunt][] module of the [Agda Universal Algebra Library][].

This module is the formal face of research phase RP-3: the hunt, per Theorem 3.6
of the note[^1], for finitely many cf-IE classes whose intersection is empty,
which by the strategy meta-theorem of [FLRP.Parachute.Theorems][] would give the
FLRP a negative answer.  The hunt itself is open-ended; what this module records
is the **constraint dossier**: everything a candidate family is already known to
have to satisfy, each constraint either proved here (where it is a corollary of
existing formal artifacts) or pointed at its formal statement elsewhere.

**The dossier, in brief.**  A candidate family `𝒢₁ , … , 𝒢ₙ` of cf-IE classes
with empty intersection must satisfy all of the following.

+  **Every member is wreath-rich** (Lemma 3.3,
   `cfIE-must-have-wreaths`{.AgdaFunction} of [FLRP.WreathNoGo][]): over every
   admissible finite nonabelian simple `𝒮`, each class contains a wreath product
   `𝒮 ≀ Ū`.  Hence no member class can omit such wreath products; solvable,
   alternating-or-symmetric, and almost simple groups are all ruled out as member
   classes (`omits-wreaths→not-cfIE`{.AgdaFunction}).
+  **Every core-free parachute representation is structurally forced**
   (Lemma 3.7, Entries 1 through 3 of [FLRP.Reductions][]): a group realizing the
   candidate parachute is subdirectly irreducible with nonabelian minimal normal
   subgroup and trivial centralizers.  The joint tension of a candidate family
   must therefore live in invariants finer than wreath content: the structure of
   the unique minimal normal subgroup, its centralizer and complement behavior,
   and the permutation action on it.
+  **Not every enforcing lattice is a two-element chain**
   (`all-chain₂-family-intersects`{.AgdaFunction} below): classes enforced by
   two-element chains all contain every group with a core-free maximal subgroup,
   so any family living entirely on two-element chains has *inhabited*
   intersection as soon as one enforcing chain has a core-free representation.
   A candidate family therefore needs canopies with at least three elements,
   which is exactly the regime where statement (C) applies.
+  **The family cannot be a property and its negation on classified lattices,
   modulo statement (C)**
   (`statement-C→pair-question-classified`{.AgdaFunction} below): with each
   enforcing lattice classified as a two-element chain or as three-element-rich,
   statement (C) leaves no contradictory pair at all.  This closes the
   two-element corner that the RP-4 reduction
   (`statement-C→no-contradictory-pair`{.AgdaFunction} of [FLRP.WreathNoGo][])
   left open, using catalog Entry 9.

**A repair to the pair question's statement.**  The RP-4 statement type
`cfIE-no-contradictory-Statement`{.AgdaFunction} carries *no* nontriviality
hypothesis on the two lattices, and that unrestricted form is simply false: the
one-element chain core-free enforces the property "is trivial" (its only
core-free representation is the trivial subgroup of the trivial group), while
*every* lattice with two distinct elements enforces "is nontrivial", with no
core-freeness needed.  Both enforcements are proved below, together with a
concrete core-free representation of the one-element chain, so the unrestricted
statement is refuted outright from any core-free representation of any lattice
with two distinct elements (`unrestricted-question-refuted`{.AgdaFunction}).
The honest form of the dead-end question, `PairQuestion`{.AgdaFunction} below,
carries `HasTwoDistinct`{.AgdaFunction} on both lattices; everything RP-4 proved
about the question applies to this form verbatim.

**Constructive status.**  As everywhere in the catalog, the theorems here are
statements *about* representations and maximality data, whose witnesses are
supplied classically; the one concrete witness constructed
(`chain₁-coreFreeRep`{.AgdaFunction}) is possible precisely because the
one-element chain forces no properness anywhere, so the oracle obstruction of
[FLRP.Problem][] does not bite.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Hunt where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty          using  ( ⊥ )
open import Data.Fin.Base       using  ( Fin )
open import Data.Fin.Patterns   using  ( 0F ; 1F ; 2F )
open import Data.Nat.Base       using  ( ℕ ; _+_ )
open import Data.Product        using  ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base       using  ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base      using  ( ⊤ ; tt )
open import Level               using  ( Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower )
                                renaming ( suc to lsuc )
open import Relation.Binary     using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( refl )
open import Relation.Nullary    using  ( ¬_ )
open import Relation.Unary      using  ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice       using  ( module Lattice-Order )
open import Classical.Small.Structures         using  ( Lattice )
open import Classical.Small.Structures.Group   using  ( eqsToGroup )
open import Classical.Structures.Group         using  ( Group ; IsSubgroup
                                                      ; module Core
                                                      ; module MaximalSubgroup
                                                      ; trivialSubgroup
                                                      ; fullSubgroup )
open import Classical.Structures.Group.Basic   using  ( module Group-Op )
open import Classical.Structures.Group.IndexAction  using  ( RightAction )
open import Classical.Structures.Group.Wreath  using  ( _≀ᵍ_ )
open import FLRP.Enforceable   using  ( CoreFree ; GroupProperty
                                      ; GroupRepresentable ; IE ; IntervalIso
                                      ; Statement-C ; TwoBigCanopies
                                      ; HasThreeDistinct ; cfIE
                                      ; module UpperInterval )
open import FLRP.Problem       using  ( FiniteLattice ; toLattice
                                      ; chain₁-lattice ; OrderIso )
open import FLRP.Reductions    using  ( IsChain₂ ; module Chain₂Interval )
open import FLRP.WreathNoGo    using  ( HasTwoDistinct ; NontrivialCenterless
                                      ; KurzweilWreathInterval
                                      ; cfIE-must-have-wreaths
                                      ; cfIE-no-contradictory-Statement )
open import Overture           using  ( ∃-syntax )
open import Setoid.Algebras    using  ( 𝕌[_] ; 𝔻[_] ; FiniteAlgebra )

open GroupRepresentable
```
-->

#### The degenerate classes

The two group properties that make the one- and two-element chains degenerate as
enforcing lattices: being trivial, and not being trivial.

```agda
-- The trivial groups: every element is the identity.
IsTrivialᵍ : GroupProperty 0ℓ
IsTrivialᵍ 𝒢 = ∀ x → x ≈ ε
  where
  open Setoid 𝔻[ proj₁ 𝒢 ]  using  ( _≈_ )
  open Group-Op 𝒢           using  ( ε )
```

**The one-element chain core-free enforces triviality.**  A representation
`[H , G] ≅ 𝟙` collapses the interval, so `H` is all of `G`; then the normal core
of `H` is also all of `G`, and core-freeness makes every element the identity.
Note that plain IE fails here: without core-freeness, `[G , G]` realizes the
one-element chain over every group.

```agda
trivial-cfIE-chain₁ : cfIE IsTrivialᵍ chain₁-lattice
trivial-cfIE-chain₁ 𝒢 H H-sg cf iso x =
  cf (Core.conj-mem-core 𝒢 H H-sg (λ g → allH _))
  where
  open UpperInterval 𝒢 H H-sg  using  ( Interval≈ ; mk ; set ; above )
  module I = OrderIso iso

  H↑ᵉ G↑ᵉ : Interval≈
  H↑ᵉ = mk H H-sg (λ h → h)
  G↑ᵉ = mk (proj₁ (fullSubgroup 𝒢 0ℓ)) (proj₂ (fullSubgroup 𝒢 0ℓ)) (λ _ → lift tt)

  -- Any two elements of the one-element chain are related.
  ≤₁ : ∀ u v → Lattice-Order._≤_ chain₁-lattice u v
  ≤₁ 0F 0F = refl

  -- The full subgroup collapses onto H through the isomorphism.
  allH : ∀ y → y ∈ H
  allH y = proj₁ (I.from∘to H↑ᵉ)
    (I.from-mono {I.to G↑ᵉ} {I.to H↑ᵉ} (≤₁ (I.to G↑ᵉ) (I.to H↑ᵉ))
      (proj₂ (I.from∘to G↑ᵉ) (lift tt)))
```

**Every lattice with two distinct elements enforces nontriviality**, and at the
plain IE level: over a trivial group all interval elements coincide (each
contains the identity's class, which is everything), so the isomorphism would
collapse the two distinct lattice elements.

```agda
nontrivial-IE : (𝑳 : Lattice) → HasTwoDistinct 𝑳 → IE (λ 𝒢 → ¬ IsTrivialᵍ 𝒢) 𝑳
nontrivial-IE 𝑳 (x , y , x≉y) 𝒢 H H-sg iso triv = x≉y x≈y
  where
  open Setoid 𝔻[ proj₁ 𝑳 ]  using  ()
    renaming ( _≈_ to _≈ᴸ_ ; sym to ≈ᴸ-sym ; trans to ≈ᴸ-trans )
  open Setoid 𝔻[ proj₁ 𝒢 ]  using  ()  renaming ( sym to ≈ᵍ-sym )
  open Lattice-Order 𝑳      using  ( ≤-antisym )
  open UpperInterval 𝒢 H H-sg
    using  ( Interval≈ ; set ; element-isSubgroup ; _≈ᵢ_ )
  open IsSubgroup
  module I = OrderIso iso

  -- Over a trivial group, every interval element contains every element.
  every : (B : Interval≈) → ∀ z → z ∈ set B
  every B z = respects (element-isSubgroup B) (≈ᵍ-sym (triv z))
                       (ε-closed (element-isSubgroup B))

  -- Hence any two interval elements are equal ...
  same : (A B : Interval≈) → A ≈ᵢ B
  same A B = (λ {z} _ → every B z) , (λ {z} _ → every A z)

  -- ... and the two distinct lattice elements collapse.
  x≈y : x ≈ᴸ y
  x≈y = ≈ᴸ-trans (≈ᴸ-sym (I.to∘from x))
        (≈ᴸ-trans (≤-antisym  (I.to-mono (proj₁ (same (I.from x) (I.from y))))
                              (I.to-mono (proj₂ (same (I.from x) (I.from y)))))
                  (I.to∘from y))
```

#### A concrete core-free representation of the one-element chain

The trivial group, on the unit carrier; every group law is `refl` by eta.

```agda
𝟙ᵍ : Group 0ℓ 0ℓ
𝟙ᵍ = eqsToGroup ⊤ (λ _ _ → tt) tt (λ _ → tt)
       (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl)

private
  𝟙-sub : Pred 𝕌[ proj₁ 𝟙ᵍ ] 0ℓ
  𝟙-sub = proj₁ (trivialSubgroup 𝟙ᵍ)

  𝟙-sub-sg : IsSubgroup 𝟙ᵍ 𝟙-sub
  𝟙-sub-sg = proj₂ (trivialSubgroup 𝟙ᵍ)
```

The interval `[1 , 𝟙]` is a one-element poset and the isomorphism is by constant
maps; every obligation is `refl` or an inclusion between predicates that both
contain everything.  This witness is constructible precisely because no
properness is involved: contrast the WP-1 no-go of [FLRP.Problem][], which rules
out concrete representations of the *two*-element chain.

```agda
chain₁-coreFreeRep : GroupRepresentable chain₁-lattice
chain₁-coreFreeRep = record
  { grp           = 𝟙ᵍ
  ; sub           = 𝟙-sub
  ; isSubgroup    = 𝟙-sub-sg
  ; interval-iso  = iso
  }
  where
  open UpperInterval 𝟙ᵍ 𝟙-sub 𝟙-sub-sg  using  ( Interval≈ ; mk ; above )

  H↑ᵉ : Interval≈
  H↑ᵉ = mk 𝟙-sub 𝟙-sub-sg (λ h → h)

  iso : IntervalIso 𝟙ᵍ 𝟙-sub 𝟙-sub-sg chain₁-lattice
  iso = record
    { to         = λ _ → 0F
    ; from       = λ _ → H↑ᵉ
    ; to-mono    = λ _ → refl
    ; from-mono  = λ _ z → z
    ; to∘from    = λ { 0F → refl }
    ; from∘to    = λ K → above K , (λ _ → refl)
    }

-- The trivial subgroup of the trivial group is core-free.
chain₁-coreFree : CoreFree 𝟙ᵍ 𝟙-sub 𝟙-sub-sg
chain₁-coreFree _ = refl
```

#### The unrestricted pair question is refutable

`cfIE-no-contradictory-Statement`{.AgdaFunction} of [FLRP.WreathNoGo][] asks that
no property and its negation both be cf-IE via lattices with core-free
representations, with no size condition on the lattices.  The degenerate pair
(`IsTrivialᵍ`{.AgdaFunction} via the one-element chain, its negation via any
two-distinct lattice) refutes it, from any core-free representation of any
lattice with two distinct elements; classically such a representation exists
(`[1 , C₂]`), so the unrestricted statement is classically false and the
two-distinct hypotheses of `PairQuestion`{.AgdaFunction} below are not optional
bookkeeping but part of the question's content.

```agda
unrestricted-question-refuted : {ℓP : Level}
  (𝑳 : Lattice) (r : GroupRepresentable 𝑳)
  → CoreFree (r .grp) (r .sub) (r .isSubgroup)
  → HasTwoDistinct 𝑳
  → ¬ cfIE-no-contradictory-Statement ℓP
unrestricted-question-refuted {ℓP} 𝑳 r cf two stmt =
  stmt P chain₁-lattice 𝑳 chain₁-coreFreeRep chain₁-coreFree cfP r cf cf¬P
  where
  P : GroupProperty ℓP
  P 𝒢 = Lift ℓP (IsTrivialᵍ 𝒢)

  cfP : cfIE P chain₁-lattice
  cfP 𝒢 H H-sg c i = lift (trivial-cfIE-chain₁ 𝒢 H H-sg c i)

  cf¬P : cfIE (λ 𝒢 → ¬ P 𝒢) 𝑳
  cf¬P 𝒢 H H-sg c i l = nontrivial-IE 𝑳 two 𝒢 H H-sg i (lower l)
```

#### The pair question, repaired

The honest statement of RP-4's dead-end question: both lattices carry core-free
representations *and* two distinct elements.  As before this is a statement type
only; no inhabitant is claimed in either direction.

```agda
PairQuestion : (ℓP : Level) → Type (lsuc 0ℓ ⊔ lsuc ℓP)
PairQuestion ℓP =
  ∀ (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : Lattice)
  → (r₁ : GroupRepresentable 𝑳₁) → CoreFree (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup)
  → HasTwoDistinct 𝑳₁ → cfIE P 𝑳₁
  → (r₂ : GroupRepresentable 𝑳₂) → CoreFree (r₂ .grp) (r₂ .sub) (r₂ .isSubgroup)
  → HasTwoDistinct 𝑳₂ → cfIE (λ 𝒢 → ¬ P 𝒢) 𝑳₂
  → ⊥
```

#### The two-element corner, closed

First: a contradictory pair cannot live on two-element chains at all, with no
appeal to statement (C).  The given core-free representation of the first chain
supplies a group with a core-free maximal subgroup (Entry 9's backward
direction), and that same subgroup carries the second chain (the forward
direction), so the one group would satisfy the property and its negation.

```agda
pair-on-chains-impossible : {ℓP : Level}
  (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : Lattice)
  → IsChain₂ 𝑳₁ → IsChain₂ 𝑳₂
  → (r₁ : GroupRepresentable 𝑳₁) → CoreFree (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup)
  → cfIE P 𝑳₁ → cfIE (λ 𝒢 → ¬ P 𝒢) 𝑳₂
  → ⊥
pair-on-chains-impossible P 𝑳₁ 𝑳₂ c₁ c₂ r₁ cf₁ enfP enf¬P = ¬P-holds P-holds
  where
  P-holds : P (r₁ .grp)
  P-holds = enfP (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup) cf₁ (r₁ .interval-iso)

  H-max = Chain₂Interval.intervalIso→maximal 𝑳₁ c₁
            (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup) (r₁ .interval-iso)

  ¬P-holds : ¬ P (r₁ .grp)
  ¬P-holds = enf¬P (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup) cf₁
    (Chain₂Interval.maximal→intervalIso 𝑳₂ c₂
      (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup) H-max)
```

Second: statement (C) kills any pair in which at least one lattice has three
distinct elements, with **no hypothesis at all on the other lattice**.  The
trick is padding: instantiate (C) at the three-member family that repeats the
big lattice, so the two-big-canopies side condition is met by the two copies.
This strengthens `statement-C→no-contradictory-pair`{.AgdaFunction} of
[FLRP.WreathNoGo][], which needed three distinct elements on *both* sides.

```agda
statement-C→no-pair-with-big : {ℓP : Level} → Statement-C ℓP
  → (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : FiniteLattice)
  → HasThreeDistinct (toLattice 𝑳₁) ⊎ HasThreeDistinct (toLattice 𝑳₂)
  → cfIE P (toLattice 𝑳₁) → cfIE (λ 𝒢 → ¬ P 𝒢) (toLattice 𝑳₂)
  → ⊥
statement-C→no-pair-with-big stC P 𝑳₁ 𝑳₂ (inj₁ three₁) cf-ie₁ cf-ie₂ =
  (Ps-hold 2F) (Ps-hold 0F)
  where
  family : Fin 3 → FiniteLattice
  family 0F = 𝑳₁
  family 1F = 𝑳₁
  family 2F = 𝑳₂

  Ps : Fin 3 → GroupProperty _
  Ps 0F = P
  Ps 1F = P
  Ps 2F = λ 𝒢 → ¬ P 𝒢

  two-big : TwoBigCanopies family
  two-big = 0F , 1F , (λ ()) , three₁ , three₁

  cfs : ∀ i → cfIE (Ps i) (toLattice (family i))
  cfs 0F = cf-ie₁
  cfs 1F = cf-ie₁
  cfs 2F = cf-ie₂

  joint = stC 1 family Ps two-big cfs

  Ps-hold : ∀ i → Ps i (joint .proj₁)
  Ps-hold = joint .proj₂ .proj₁
statement-C→no-pair-with-big stC P 𝑳₁ 𝑳₂ (inj₂ three₂) cf-ie₁ cf-ie₂ =
  (Ps-hold 0F) (Ps-hold 2F)
  where
  family : Fin 3 → FiniteLattice
  family 0F = 𝑳₂
  family 1F = 𝑳₂
  family 2F = 𝑳₁

  Ps : Fin 3 → GroupProperty _
  Ps 0F = λ 𝒢 → ¬ P 𝒢
  Ps 1F = λ 𝒢 → ¬ P 𝒢
  Ps 2F = P

  two-big : TwoBigCanopies family
  two-big = 0F , 1F , (λ ()) , three₂ , three₂

  cfs : ∀ i → cfIE (Ps i) (toLattice (family i))
  cfs 0F = cf-ie₂
  cfs 1F = cf-ie₂
  cfs 2F = cf-ie₁

  joint = stC 1 family Ps two-big cfs

  Ps-hold : ∀ i → Ps i (joint .proj₁)
  Ps-hold = joint .proj₂ .proj₁
```

The corner assembled: once each enforcing lattice is classified as a two-element
chain or as three-element-rich, statement (C) leaves no room for a contradictory
pair whatsoever.  Classically the classification is trivial for a finite
lattice, so this says: modulo statement (C), the repaired pair question has a
positive answer on classified finite lattices, and the two-element mismatch of
the RP-4 reduction is closed.

```agda
statement-C→pair-question-classified : {ℓP : Level} → Statement-C ℓP
  → (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : FiniteLattice)
  → IsChain₂ (toLattice 𝑳₁) ⊎ HasThreeDistinct (toLattice 𝑳₁)
  → IsChain₂ (toLattice 𝑳₂) ⊎ HasThreeDistinct (toLattice 𝑳₂)
  → (r₁ : GroupRepresentable (toLattice 𝑳₁))
  → CoreFree (r₁ .grp) (r₁ .sub) (r₁ .isSubgroup)
  → cfIE P (toLattice 𝑳₁) → cfIE (λ 𝒢 → ¬ P 𝒢) (toLattice 𝑳₂)
  → ⊥
statement-C→pair-question-classified stC P 𝑳₁ 𝑳₂ (inj₁ c₁) (inj₁ c₂) r₁ cf₁ =
  pair-on-chains-impossible P (toLattice 𝑳₁) (toLattice 𝑳₂) c₁ c₂ r₁ cf₁
statement-C→pair-question-classified stC P 𝑳₁ 𝑳₂ (inj₁ c₁) (inj₂ three₂) _ _ =
  statement-C→no-pair-with-big stC P 𝑳₁ 𝑳₂ (inj₂ three₂)
statement-C→pair-question-classified stC P 𝑳₁ 𝑳₂ (inj₂ three₁) (inj₁ c₂) _ _ =
  statement-C→no-pair-with-big stC P 𝑳₁ 𝑳₂ (inj₁ three₁)
statement-C→pair-question-classified stC P 𝑳₁ 𝑳₂ (inj₂ three₁) (inj₂ _) _ _ =
  statement-C→no-pair-with-big stC P 𝑳₁ 𝑳₂ (inj₁ three₁)
```

#### Families on two-element chains intersect

The family-level face of the corner, and a genuine structure constraint on the
hunt: a family of cf-IE classes whose enforcing lattices are *all* two-element
chains has inhabited intersection, witnessed by the group of any one core-free
representation.  Contrapositively, an empty-intersection family must contain an
enforcing lattice that is not a two-element chain.

```agda
module _ {n : ℕ} {ℓP : Level}
  (𝑳s      : Fin n → Lattice)
  (chains  : ∀ i → IsChain₂ (𝑳s i))
  (Ps      : Fin n → GroupProperty ℓP)
  (cfs     : ∀ i → cfIE (Ps i) (𝑳s i))
  where

  all-chain₂-family-intersects :
    (i₀ : Fin n) (r : GroupRepresentable (𝑳s i₀))
    → CoreFree (r .grp) (r .sub) (r .isSubgroup)
    → Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ] (∀ i → Ps i 𝒢)
  all-chain₂-family-intersects i₀ r cf =
    r .grp , λ i →
      cfs i (r .grp) (r .sub) (r .isSubgroup) cf
        (Chain₂Interval.maximal→intervalIso (𝑳s i) (chains i)
          (r .grp) (r .sub) (r .isSubgroup)
          (Chain₂Interval.intervalIso→maximal (𝑳s i₀) (chains i₀)
            (r .grp) (r .sub) (r .isSubgroup) (r .interval-iso)))
```

#### Two-element-chain classes are wreath-rich

The second half of Entry 9, as the RP-4 design note requested: a class that is
cf-IE via a two-element chain contains wreath products over every admissible
`𝒮`, by Lemma 3.3 instantiated at the chain.  The representation the lemma
consumes is packaged from any group with a core-free maximal subgroup through
Entry 9's forward direction.

```agda
isChain₂→hasTwoDistinct : (𝑳 : Lattice) → IsChain₂ 𝑳 → HasTwoDistinct 𝑳
isChain₂→hasTwoDistinct 𝑳 c₂ =
  proj₁ (IsChain₂.bot c₂) , proj₁ (IsChain₂.top c₂) , IsChain₂.distinct c₂

chain₂-classes-wreath-rich : {ℓP : Level}
  (P : GroupProperty ℓP) (𝑳 : Lattice) (c₂ : IsChain₂ 𝑳) → cfIE P 𝑳
  → (𝒮 : Group 0ℓ 0ℓ) → NontrivialCenterless 𝒮 → KurzweilWreathInterval 𝒮
  → (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → FiniteAlgebra (proj₁ 𝒢) → CoreFree 𝒢 H H-sg
  → MaximalSubgroup.IsMaximalSubgroup 𝒢 0ℓ H
  → ∃[ 𝒰 ∈ Group 0ℓ 0ℓ ] ∃[ m ∈ ℕ ]
      Σ[ A ∈ RightAction (Fin (2 + m)) 𝒰 ] P (𝒮 ≀ᵍ A)
chain₂-classes-wreath-rich P 𝑳 c₂ enf 𝒮 nc kwi 𝒢 H H-sg fin cf H-max =
  cfIE-must-have-wreaths P 𝑳 𝒮 nc kwi enf rep fin cf
    (isChain₂→hasTwoDistinct 𝑳 c₂)
  where
  rep : GroupRepresentable 𝑳
  rep = record
    { grp           = 𝒢
    ; sub           = H
    ; isSubgroup    = H-sg
    ; interval-iso  = Chain₂Interval.maximal→intervalIso 𝑳 c₂ 𝒢 H H-sg H-max
    }
```

--------------------------------------

[^1]: arXiv:1205.1927 ("the note"), vendored at `docs/papers/flrp/ieprops/`;
      Theorem 3.6 (`thm-wjd-1`) and its Remark.  The survey note for this phase
      is `docs/notes/flrp-rp3-hunt.md`, and the design notes it builds on are
      `docs/notes/flrp-rp2-catalog.md` and `docs/notes/flrp-rp4-wreath.md`.
