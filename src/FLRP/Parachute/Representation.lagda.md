---
layout: default
file: "src/FLRP/Parachute/Representation.lagda.md"
title: "FLRP.Parachute.Representation module (The Agda Universal Algebra Library)"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Reading a parachute representation

This is the [FLRP.Parachute.Representation][] module of the [Agda Universal Algebra Library][].

[FLRP.Parachute][] proves that core-freeness propagates in a group whose interval
`[H , G]` *has the shape of* a parachute (`ParachuteConfig`{.AgdaRecord}).  This
module supplies the shape: from an isomorphism between `[H , G]` and the parachute
lattice `𝒫(L₁ , … , Lₙ)` of [Classical.Structures.Lattice.Parachute][] it reads off

+  the configuration itself (`config`{.AgdaFunction}) — the atoms and their meet,
   join, and covering properties;
+  for each `i`, an isomorphism `[Kᵢ , G] ≅ Lᵢ` (`canopyIso`{.AgdaFunction}) — the
   sense in which `Lᵢ` is a canopy of the representation, and the step that lets a
   property core-free enforceable by `Lᵢ` speak about `G`;
+  the translation of "`|Lᵢ| > 2`" into the `BigCanopy`{.AgdaRecord} datum the
   propagation theorem consumes (`bigCanopy`{.AgdaFunction}).

Everything here is transport along an order isomorphism, so the module opens with
the small toolkit that makes such transport routine: an order isomorphism preserves
and *reflects* the order, and preserves equality.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Parachute.Representation where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base    using  ( Fin )
open import Data.Nat.Base    using  ( ℕ )
open import Data.Product     using  ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Data.Sum.Base    using  ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base   using  ( tt )
open import Level            using  ( Level ; 0ℓ ; lift ) renaming ( suc to lsuc )
open import Relation.Binary  using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ )
open import Relation.Nullary using  ( ¬_ ; Dec )
open import Relation.Unary   using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using  ( module Lattice-Order ; TopOf ; BotOf )
open import Classical.Small.Structures    using  ( Lattice )
open import Classical.Structures.Group    using  ( Group ; IsSubgroup )
open import Classical.Structures.Lattice.Parachute  using  ( module ParachuteAtoms )
open import FLRP.Enforceable  using  ( module UpperInterval ; IntervalIso )
open import FLRP.Parachute    using  ( module GroupParachute )
open import FLRP.Problem      using  ( OrderIso )
open import Setoid.Algebras   using  ( 𝕌[_] ; 𝔻[_] )
```
-->

#### Transport along an interval isomorphism

An `IntervalIso`{.AgdaFunction} is an order isomorphism, so it preserves equality
(two elements comparable both ways map to comparable images) and *reflects* the
order (transport back and repair the round trip).  Both directions are needed
below, because the parachute's structure is stated in the lattice and consumed in
the interval.

```agda
module IntervalIsoTools
  (𝒢     : Group 0ℓ 0ℓ)
  (H     : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
  (H-sg  : IsSubgroup 𝒢 H)
  (𝑳     : Lattice)
  (iso   : IntervalIso 𝒢 H H-sg 𝑳)
  where

  open UpperInterval 𝒢 H H-sg
  open GroupParachute 𝒢 H H-sg  using  ( IsAll ; Hᵢ ; Gᵢ ; ⊇→IsAll )
  open OrderIso iso
  open Lattice-Order 𝑳         using  ( _≤_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ≤-reflexive )
  open Setoid 𝔻[ proj₁ 𝑳 ]     using  () renaming ( _≈_ to _≈ᴸ_ ; sym to ≈ᴸ-sym )

  -- Monotonicity with the endpoints explicit.  Neither `to`, `from`, nor `set`
  -- is injective, so an implicit endpoint under any of them is never inferred;
  -- every consumer below passes them.
  to-mono′ : (M N : Interval≈) → M ≤ᵢ N → to M ≤ to N
  to-mono′ M N le = to-mono {M} {N} le

  from-mono′ : (u v : 𝕌[ proj₁ 𝑳 ]) → u ≤ v → from u ≤ᵢ from v
  from-mono′ u v le = from-mono {u} {v} le

  -- An order isomorphism preserves equality ...
  to-≈ : (M N : Interval≈) → M ≈ᵢ N → to M ≈ᴸ to N
  to-≈ M N (M⊆N , N⊆M) = ≤-antisym (to-mono′ M N M⊆N) (to-mono′ N M N⊆M)

  from-≈ : (u v : 𝕌[ proj₁ 𝑳 ]) → u ≈ᴸ v → from u ≈ᵢ from v
  from-≈ u v e = from-mono′ u v (≤-reflexive e) , from-mono′ v u (≤-reflexive (≈ᴸ-sym e))

  -- ... and reflects the order: transport back and repair both round trips.
  reflect : (M N : Interval≈) → to M ≤ to N → M ≤ᵢ N
  reflect M N le z = proj₁ (from∘to N) (from-mono′ (to M) (to N) le (proj₂ (from∘to M) z))

  -- The two ends of the interval, transported.  A member whose image is below a
  -- bottom of `𝑳` collapses to `H`; a member whose image is above a top is all
  -- of `G`.
  module Ends (⊥ᴸ : BotOf 𝑳) (⊤ᴸ : TopOf 𝑳) where

    -- The image of the interval's top is a top of `𝑳`, and dually at the bottom.
    top-≤ : proj₁ ⊤ᴸ ≤ to Gᵢ
    top-≤ = ≤-trans  (≤-reflexive (≈ᴸ-sym (to∘from (proj₁ ⊤ᴸ))))
                     (to-mono′ (from (proj₁ ⊤ᴸ)) Gᵢ (λ _ → lift tt))

    ≤-bot : to Hᵢ ≤ proj₁ ⊥ᴸ
    ≤-bot = ≤-trans  (to-mono′ Hᵢ (from (proj₁ ⊥ᴸ)) (above (from (proj₁ ⊥ᴸ))))
                     (≤-reflexive (to∘from (proj₁ ⊥ᴸ)))

    below-bot : (M : Interval≈) → to M ≤ proj₁ ⊥ᴸ → set M ⊆ H
    below-bot M le = reflect M Hᵢ (≤-trans le (proj₂ ⊥ᴸ (to Hᵢ)))

    above-top : (C : Interval≈) → proj₁ ⊤ᴸ ≤ to C → IsAll C
    above-top C le = ⊇→IsAll C (reflect Gᵢ C (≤-trans (proj₂ ⊤ᴸ (to Gᵢ)) le))
```

#### Composing with a lattice isomorphism

An interval isomorphism composes on the *right* with an isomorphism of lattices, so
group representability transports along lattice isomorphisms.  (Its mirror,
composition on the interval side, is `compose-IntervalIso`{.AgdaFunction} of
[FLRP.Enforceable][].)

```agda
-- An isomorphism of (the meet orders of) two lattices.
LatticeIso : Lattice → Lattice → Type 0ℓ
LatticeIso 𝑴 𝑳 = OrderIso  (Setoid._≈_ 𝔻[ proj₁ 𝑴 ]) (Lattice-Order._≤_ 𝑴)
                           (Setoid._≈_ 𝔻[ proj₁ 𝑳 ]) (Lattice-Order._≤_ 𝑳)

compose-IntervalIsoʳ :
     (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
     (𝑴 𝑳 : Lattice)
  →  IntervalIso 𝒢 H H-sg 𝑴 → LatticeIso 𝑴 𝑳 → IntervalIso 𝒢 H H-sg 𝑳
compose-IntervalIsoʳ 𝒢 H H-sg 𝑴 𝑳 I J = record
  { to         = λ M → J.to (I.to M)
  ; from       = λ u → I.from (J.from u)
  ; to-mono    = λ {M} {N} le → J.to-mono (I.to-mono {M} {N} le)
  ; from-mono  = λ {u} {v} le → I.from-mono (J.from-mono {u} {v} le)
  ; to∘from    = λ u → ≈ᴸ-trans (to-≈ᴶ (I.to∘from (J.from u))) (J.to∘from u)
  ; from∘to    = λ M → ≈ᵢ-trans  { I.from (J.from (J.to (I.to M))) }
                                 { I.from (I.to M) } { M }
                                 (from-≈ᴵ (J.from∘to (I.to M))) (I.from∘to M)
  }
  where
  module I = OrderIso I
  module J = OrderIso J
  open GroupParachute 𝒢 H H-sg using ( ≈ᵢ-trans )
  open Lattice-Order 𝑴 using () renaming ( ≤-reflexive to ≤ᴹ-reflexive )
  open Lattice-Order 𝑳 using () renaming ( ≤-antisym to ≤ᴸ-antisym )
  open Setoid 𝔻[ proj₁ 𝑴 ] using () renaming ( sym to ≈ᴹ-sym )
  open Setoid 𝔻[ proj₁ 𝑳 ] using () renaming ( trans to ≈ᴸ-trans )

  to-≈ᴶ : {x y : 𝕌[ proj₁ 𝑴 ]} → Setoid._≈_ 𝔻[ proj₁ 𝑴 ] x y
        → Setoid._≈_ 𝔻[ proj₁ 𝑳 ] (J.to x) (J.to y)
  to-≈ᴶ {x} {y} e = ≤ᴸ-antisym  (J.to-mono {x} {y} (≤ᴹ-reflexive e))
                                (J.to-mono {y} {x} (≤ᴹ-reflexive (≈ᴹ-sym e)))

  from-≈ᴵ : {x y : 𝕌[ proj₁ 𝑴 ]} → Setoid._≈_ 𝔻[ proj₁ 𝑴 ] x y
          → UpperInterval._≈ᵢ_ 𝒢 H H-sg (I.from x) (I.from y)
  from-≈ᴵ {x} {y} e =  I.from-mono {x} {y} (≤ᴹ-reflexive e)
                    ,  I.from-mono {y} {x} (≤ᴹ-reflexive (≈ᴹ-sym e))
```

#### The configuration of a parachute representation

Fix a family of canopies with their extrema and the decision procedure the
parachute construction needs, and a group representation of the resulting
parachute lattice.

```agda
module ParachuteRep {m : ℕ}
  (𝑳s      : Fin (ℕ.suc m) → Lattice)
  (𝒕       : ∀ i → TopOf (𝑳s i))
  (top?    : ∀ i (x : 𝕌[ proj₁ (𝑳s i) ])
           → Dec (Setoid._≈_ 𝔻[ proj₁ (𝑳s i) ] x (proj₁ (𝒕 i))))
  (𝒃       : ∀ i → BotOf (𝑳s i))
  (nondeg  : ∀ i → ¬ (Setoid._≈_ 𝔻[ proj₁ (𝑳s i) ] (proj₁ (𝒃 i)) (proj₁ (𝒕 i))))
  where

  open ParachuteAtoms 𝑳s 𝒕 top? 𝒃 nondeg public

  -- "|Lᵢ| > 2": the i-th canopy has an element strictly between its two ends.
  record BigCanopyᴸ (i : Fin (ℕ.suc m)) : Type 0ℓ where
    field
      elt          : 𝕌[ proj₁ (𝑳s i) ]
      elt-not-bot  : ¬ ([ i ] elt ≤ bot i)
      elt-not-top  : NonTop i elt

  module Over
    (𝒢     : Group 0ℓ 0ℓ)
    (H     : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
    (H-sg  : IsSubgroup 𝒢 H)
    (iso   : IntervalIso 𝒢 H H-sg ⊕ᵖ-Lattice)
    where

    open UpperInterval 𝒢 H H-sg
    open GroupParachute 𝒢 H H-sg
    open IntervalIsoTools 𝒢 H H-sg ⊕ᵖ-Lattice iso
    open Ends ⊥ᵖ-isBot ⊤ᵖ-isTop
    open OrderIso iso using ( to ; from ; to∘from ; from∘to )
    open Lattice-Order ⊕ᵖ-Lattice  using  () renaming ( _≤_ to _≤ᴸ_ ; ≤-trans to ≤ᴸ-trans
                                                      ; ≤-respˡ-≈ to ≤ᴸ-respˡ ; ≤-respʳ-≈ to ≤ᴸ-respʳ
                                                      ; ∧-greatest to ∧ᴸ-greatest
                                                      ; ∨-least to ∨ᴸ-least
                                                      ; ∧-lowerˡ to ∧ᴸ-lowerˡ
                                                      ; ∧-lowerʳ to ∧ᴸ-lowerʳ )
```

The `i`-th atom of the representation is the subgroup corresponding to the `i`-th
atom of the parachute, and its image is that atom back again.

```agda
    -- The subgroup Kᵢ at the bottom of the i-th canopy.
    K : Fin (ℕ.suc m) → Interval≈
    K i = from (atom i)

    K-image : (i : Fin (ℕ.suc m)) → atom i ≈ᵖ to (K i)
    K-image i = ≈ᵖ-sym (to∘from (atom i))
```

The three fields of the configuration, in turn.  Distinct atoms meet at the
bottom: their intersection maps below `atom i ∧ atom j`, which is the parachute's
bottom.  They join to the top: a member containing both maps above
`atom i ∨ atom j`, which is the parachute's top.  And the covering property is the
parachute's own, transported.

```agda
    atoms-meet′ : (i j : Fin (ℕ.suc m)) → ¬ (i ≡ j) → (set (K i) ∩ set (K j)) ⊆ H
    atoms-meet′ i j i≢j = below-bot (K i ∧ᵢ K j) meet-below
      where
      meet-below : to (K i ∧ᵢ K j) ≤ᴸ ⊥ᵖ
      meet-below = ≤ᴸ-trans
        (∧ᴸ-greatest  (≤ᴸ-respʳ (≈ᵖ-sym (K-image i))
                                (to-mono′ (K i ∧ᵢ K j) (K i) (λ z → proj₁ z)))
                      (≤ᴸ-respʳ (≈ᵖ-sym (K-image j))
                                (to-mono′ (K i ∧ᵢ K j) (K j) (λ z → proj₂ z))))
        (≤ᵖ-sound (atoms-meet i j i≢j))

    atoms-join′ : (i j : Fin (ℕ.suc m)) → ¬ (i ≡ j) → (C : Interval≈)
                → set (K i) ⊆ set C → set (K j) ⊆ set C → IsAll C
    atoms-join′ i j i≢j C Ki⊆C Kj⊆C = above-top C
      (≤ᴸ-trans  (≤ᵖ-sound (atoms-join i j i≢j))
                 (∨ᴸ-least  (≤ᴸ-respˡ (≈ᵖ-sym (K-image i)) (to-mono′ (K i) C Ki⊆C))
                            (≤ᴸ-respˡ (≈ᵖ-sym (K-image j)) (to-mono′ (K j) C Kj⊆C))))

    covered′ : (M : Interval≈)
             → (set M ⊆ H) ⊎ (Σ[ i ∈ Fin (ℕ.suc m) ] (set (K i) ⊆ set M))
    covered′ M with covered (to M)
    ... | inj₁ below     = inj₁ (below-bot M (≤ᵖ-sound below))
    ... | inj₂ (i , le)  =
          inj₂ (i , λ z → proj₁ (from∘to M) (from-mono′ (atom i) (to M) (≤ᵖ-sound le) z))

    -- The parachute shape of [H , G], as the propagation theorem consumes it.
    config : ParachuteConfig (ℕ.suc m)
    config = record  { atom        = K
                     ; atoms-meet  = atoms-meet′
                     ; atoms-join  = atoms-join′
                     ; covered     = covered′
                     }

    -- No atom subgroup collapses to `H` — the atoms of the parachute are not its
    -- bottom — so an atom is proper as soon as there is a second one to meet it.
    K-⊄H : (i : Fin (ℕ.suc m)) → ¬ (set (K i) ⊆ H)
    K-⊄H i sub = atom-≢⊥ i
      (≤ᵖ-complete (≤ᴸ-respˡ  (≈ᵖ-sym (K-image i))
                              (≤ᴸ-trans (to-mono′ (K i) Hᵢ sub) ≤-bot)))

    K-proper : (i j : Fin (ℕ.suc m)) → ¬ (i ≡ j) → Proper (K i)
    K-proper i j i≢j all = K-⊄H j (λ {x} z → atoms-meet′ i j i≢j (all x , z))
```

#### The canopies are represented

`[Kᵢ , G] ≅ Lᵢ`.  The maps are the parachute's own canopy retraction `π i` and its
section `↑ i` ([Classical.Structures.Lattice.Parachute][]), conjugated by the
interval isomorphism.  The only bookkeeping is that a member of `[Kᵢ , G]` is also
a member of `[H , G]` (`widen`{.AgdaFunction}), since `H ⊆ Kᵢ`.

```agda
    module Canopy (i : Fin (ℕ.suc m)) where

      Kᵢ-sg : IsSubgroup 𝒢 (set (K i))
      Kᵢ-sg = element-isSubgroup (K i)

      private module IK = UpperInterval 𝒢 (set (K i)) Kᵢ-sg

      -- A subgroup above Kᵢ is a subgroup above H.
      widen : IK.Interval≈ → Interval≈
      widen M = mk (IK.set M) (IK.element-isSubgroup M) (λ h → IK.above M (above (K i) h))

      -- The i-th canopy coordinate of a member of [Kᵢ , G] ...
      toᶜ : IK.Interval≈ → 𝕌[ proj₁ (𝑳s i) ]
      toᶜ M = π i (to (widen M))

      -- ... and the member of [Kᵢ , G] a canopy element names.
      fromᶜ : 𝕌[ proj₁ (𝑳s i) ] → IK.Interval≈
      fromᶜ x = IK.mk  (set (from (↑ i x)))
                       (element-isSubgroup (from (↑ i x)))
                       (from-mono′ (atom i) (↑ i x) (≤ᵖ-sound (atom-≤-↑ i x)))

      toᶜ-mono : (M N : IK.Interval≈) → IK._≤ᵢ_ M N → [ i ] toᶜ M ≤ toᶜ N
      toᶜ-mono M N le = π-mono i (≤ᵖ-complete (to-mono′ (widen M) (widen N) le))

      fromᶜ-mono : (x y : 𝕌[ proj₁ (𝑳s i) ]) → [ i ] x ≤ y → IK._≤ᵢ_ (fromᶜ x) (fromᶜ y)
      fromᶜ-mono x y e = from-mono′ (↑ i x) (↑ i y) (≤ᵖ-sound (↑-mono i e))

      -- Round trip through the canopy: π i undoes ↑ i.
      toᶜ∘fromᶜ : (x : 𝕌[ proj₁ (𝑳s i) ]) → [ i ] toᶜ (fromᶜ x) ≈ x
      toᶜ∘fromᶜ x = ≈trans i (π-cong i step) (π∘↑ i x)
        where
        step : to (widen (fromᶜ x)) ≈ᵖ ↑ i x
        step = ≈ᵖ-trans (to-≈ (widen (fromᶜ x)) (from (↑ i x)) ((λ z → z) , (λ z → z)))
                        (to∘from (↑ i x))

      -- Round trip through the interval: ↑ i undoes π i above the i-th atom.
      fromᶜ∘toᶜ : (M : IK.Interval≈) → IK._≈ᵢ_ (fromᶜ (toᶜ M)) M
      fromᶜ∘toᶜ M = (λ z → proj₁ round z) , (λ z → proj₂ round z)
        where
        atom≤ : atom i ≤ᵖ to (widen M)
        atom≤ = ≤ᵖ-complete
          (≤ᴸ-respˡ (≈ᵖ-sym (K-image i)) (to-mono′ (K i) (widen M) (λ z → IK.above M z)))

        round : from (↑ i (π i (to (widen M)))) ≈ᵢ widen M
        round = ≈ᵢ-trans  { from (↑ i (π i (to (widen M)))) }
                          { from (to (widen M)) } { widen M }
                          (from-≈ (↑ i (π i (to (widen M)))) (to (widen M))
                                  (↑∘π i (to (widen M)) atom≤))
                          (from∘to (widen M))

      -- The canopy isomorphism [Kᵢ , G] ≅ Lᵢ.
      canopy-iso : IntervalIso 𝒢 (set (K i)) Kᵢ-sg (𝑳s i)
      canopy-iso = record
        { to         = toᶜ
        ; from       = fromᶜ
        ; to-mono    = λ {M} {N} le → toᶜ-mono M N le
        ; from-mono  = λ {x} {y} e → fromᶜ-mono x y e
        ; to∘from    = toᶜ∘fromᶜ
        ; from∘to    = fromᶜ∘toᶜ
        }

    canopyIso : (i : Fin (ℕ.suc m))
              → IntervalIso 𝒢 (set (K i)) (element-isSubgroup (K i)) (𝑳s i)
    canopyIso i = Canopy.canopy-iso i
```

#### Big canopies

"`|Lᵢ| > 2`" says `Lᵢ` has an element strictly between its bottom and its top.
Such an element names a member of `[Kᵢ , G]` strictly between `Kᵢ` and `G`, which
is precisely the `BigCanopy`{.AgdaRecord} datum of [FLRP.Parachute][].

```agda
    bigCanopy : (i : Fin (ℕ.suc m)) → BigCanopyᴸ i → BigCanopy (K i)
    bigCanopy i big = record
      { mid         = from (↑ i elt)
      ; atom-⊆-mid  = from-mono′ (atom i) (↑ i elt) (≤ᵖ-sound (atom-≤-↑ i elt))
      ; mid-⊄-atom  = not-below
      ; mid-proper  = not-all
      }
      where
      open BigCanopyᴸ big

      -- The canopy coordinate of the member named by `elt` is `elt` again ...
      coordinate : [ i ] π i (to (from (↑ i elt))) ≈ elt
      coordinate = ≈trans i (π-cong i (to∘from (↑ i elt))) (π∘↑ i elt)

      -- ... and the canopy coordinate of the atom is the canopy's bottom.
      atom-coordinate : [ i ] π i (to (K i)) ≈ bot i
      atom-coordinate = ≈trans i (π-cong i (≈ᵖ-sym (K-image i))) (π-atom i)

      -- Were the middle element below the atom, its canopy coordinate would be
      -- below the canopy's bottom.
      not-below : ¬ (set (from (↑ i elt)) ⊆ set (K i))
      not-below sub = elt-not-bot
        (≤trans i  (≤reflexive i (≈sym i coordinate))
                   (≤trans i  (π-mono i (≤ᵖ-complete
                                (to-mono′ (from (↑ i elt)) (K i) sub)))
                              (≤reflexive i atom-coordinate)))

      -- Were it everything, its canopy coordinate would be the canopy's top.
      not-all : Proper (from (↑ i elt))
      not-all all = elt-not-top
        (≤antisym i  (≤top i elt)
                     (≤trans i  (π-mono i (≤ᵖ-complete
                                  (≤ᴸ-trans top-≤
                                            (to-mono′ Gᵢ (from (↑ i elt))
                                                      (λ {x} _ → all x)))))
                                (≤reflexive i coordinate)))
```

---

The three outputs of this module — `config`{.AgdaFunction}, `canopyIso`{.AgdaFunction},
and `bigCanopy`{.AgdaFunction} — are exactly the inputs of the parachute theorems
of [FLRP.Parachute.Theorems][].
