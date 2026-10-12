---
layout: default
file: "src/Classical/Structures/Lattice/Free/Canonical/Joinands.lagda.md"
title: "Classical.Structures.Lattice.Free.Canonical.Joinands module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Canonical joinands

This is the [Classical.Structures.Lattice.Free.Canonical.Joinands][] module of the [Agda Universal Algebra Library][].

Let `w` be an element of the free lattice.  If the canonical form of `w` is a join
`t₁ ∨ ⋯ ∨ tₙ`, the elements the `tᵢ` represent are the *canonical joinands* of
`w`; otherwise (`w` is join irreducible) its only canonical joinand is `w` itself
([Freese, Ježek, and Nation (1995)][], Section I.3).  The canonical meetands are
dual.  Theorem 1.19 says that the canonical joinands refine every join
representation of `w`: if `w = u₁ ∨ ⋯ ∨ uₘ`, then every canonical joinand of `w`
lies below some `uⱼ`.  In this sense the canonical join representation is the
best way to write `w` as a join, and the theorem is the form in which canonical
forms are used: semidistributivity of free lattices is a short consequence, and
so are the later arithmetic of free lattices and the theory of their
sublattices.

Here `canonicalJoinands w`{.AgdaFunction} is the list of the lattice terms
embedded from the joinands of the canonical form computed by
[Classical.Structures.Lattice.Free.Canonical.Algorithm][], and Theorem 1.19
(`canonicalJoinands-refine`{.AgdaFunction}) is Lemma 1.16 of
[Classical.Structures.Lattice.Free.Canonical.Uniqueness][] read for that list.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Canonical.Joinands where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.Any           using ( Any ; here )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( inj₁ ; inj₂ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( refl ; sym ; subst )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Canonical.Algorithm
  using  ( module Canonicalization )
open import Classical.Structures.Lattice.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; CMand ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ≈ʷ-trans
         ; ⋁⁺ ; ⋀⁺ ; gen-⋁⁺-prime ; ⋀⁺-gen-below ; ⋁ᴶ-upper ; ⋁ᴶ-least ; ⋀ᴹ-lower
         ; ⋀ᴹ-greatest ; W-list-ᴹ⁺ ; W-list-⁺ᴶ ; IsCanonical ; cjoin ; cmeet ; asListJ
         ; asListM ; joinandsOf ; meetandsOf ; joinandsOf-sound ; meetandsOf-sound )
open import Classical.Structures.Lattice.Free.Canonical.Uniqueness
  using  ( ⋁ᴶ-refines ; ⋀ᴹ-refines ; module Antichains )
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm )
open import Classical.Structures.Lattice.Free.Whitman  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans )

private variable
  χ : Level
  X : Type χ
```
-->

#### Refinement for a canonical term

Theorem 1.19 is first proved for an arbitrary canonical term `C` and a join
representation of the element it represents (`joinands-refine`{.AgdaFunction}),
by cases on the shape of `C`.  The joinand of a generator is the generator, which
is join prime.  The joinands of a canonical join are covered by Lemma 1.16.  The
joinand of a canonical meet `⋀ⱼ tⱼ` is the meet itself: by Whitman's condition it
lies below some `uⱼ`, or some meetand `tⱼ` lies below the join of the `uⱼ`,
which is the meet itself, hence below every meetand; and no member of an
antichain of two or more lies below all the others.  `meetands-refine`{.AgdaFunction}
is the dual.

```agda
module _ {X : Type χ} where
  open Antichains {A = CJand X} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans
    using () renaming ( antichain-no-max to no-maxᴶ )
  open Antichains {A = CMand X} (λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ) ≤ʷ-trans
    using () renaming ( antichain-no-min to no-minᴹ )

  joinands-refine : (C : CTerm X) → IsCanonical C → {u : LatTerm X} {us : List (LatTerm X)}
                  → ⌊ C ⌋ ≈ʷ ⋁⁺ u us
                  → ∀ {a} → a ∈ asListJ (joinandsOf C) → Any (⌊ a ⌋ᴶ ≤ʷ_) (u ∷ us)
  joinands-refine (genᶜ _)     _                  (p , _)  (here refl)  = gen-⋁⁺-prime p
  joinands-refine (joinᶜ _ _)  (cjoin _ _ _ c4)   e        a∈           = ⋁ᴶ-refines c4 e a∈
  joinands-refine (meetᶜ _ _)  (cmeet ne _ ac _)  (p , q)  (here refl)  with W-list-ᴹ⁺ p
  ... | inj₁ r = let (_ , m∈ , m≤) = find r
                 in ⊥-elim (no-minᴹ ac ne m∈ (λ v∈ → ≤ʷ-trans m≤ (≤ʷ-trans q (⋀ᴹ-lower v∈))))
  ... | inj₂ r = r

  meetands-refine : (C : CTerm X) → IsCanonical C → {u : LatTerm X} {us : List (LatTerm X)}
                  → ⌊ C ⌋ ≈ʷ ⋀⁺ u us
                  → ∀ {a} → a ∈ asListM (meetandsOf C) → Any (_≤ʷ ⌊ a ⌋ᴹ) (u ∷ us)
  meetands-refine (genᶜ _)     _                  (_ , q)  (here refl)  = ⋀⁺-gen-below q
  meetands-refine (meetᶜ _ _)  (cmeet _ _ _ c4)   e        a∈           = ⋀ᴹ-refines c4 e a∈
  meetands-refine (joinᶜ _ _)  (cjoin ne _ ac _)  (p , q)  (here refl)  with W-list-⁺ᴶ q
  ... | inj₁ r = r
  ... | inj₂ r = let (_ , j∈ , ≤j) = find r
                 in ⊥-elim (no-maxᴶ ac ne j∈ (λ v∈ → ≤ʷ-trans (⋁ᴶ-upper v∈) (≤ʷ-trans p ≤j)))
```

#### Theorem 1.19

`canonicalJoinands w`{.AgdaFunction} and `canonicalMeetands w`{.AgdaFunction} are the
lattice terms of the joinands and meetands of the canonical form of `w`.  Each
canonical joinand lies below `w` (`canonicalJoinands-upper`{.AgdaFunction}), and
`w` lies below every common upper bound of them
(`canonicalJoinands-least`{.AgdaFunction}), so `w` is their join; dually for the
canonical meetands.  Theorem 1.19 (`canonicalJoinands-refine`{.AgdaFunction}) and
its dual (`canonicalMeetands-refine`{.AgdaFunction}) are the refinement lemmas
above, applied to the canonical form of `w`, which is canonical and represents `w`.

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  canonicalJoinands : LatTerm X → List (LatTerm X)
  canonicalJoinands w = map ⌊_⌋ᴶ (asListJ (joinandsOf (canonical w)))

  canonicalMeetands : LatTerm X → List (LatTerm X)
  canonicalMeetands w = map ⌊_⌋ᴹ (asListM (meetandsOf (canonical w)))

  canonicalJoinands-upper : {w c : LatTerm X} → c ∈ canonicalJoinands w → c ≤ʷ w
  canonicalJoinands-upper {w} c∈ with ∈-map⁻ ⌊_⌋ᴶ c∈
  ... | _ , a∈ , refl =
    ≤ʷ-trans (⋁ᴶ-upper a∈)
             (subst (_≤ʷ w) (sym (joinandsOf-sound (canonical w))) (proj₁ (canonical-sound w)))

  canonicalJoinands-least : {w z : LatTerm X} → (∀ {c} → c ∈ canonicalJoinands w → c ≤ʷ z) → w ≤ʷ z
  canonicalJoinands-least {w} f =
    ≤ʷ-trans (proj₂ (canonical-sound w))
             (subst (_≤ʷ _) (joinandsOf-sound (canonical w)) (⋁ᴶ-least λ a∈ → f (∈-map⁺ ⌊_⌋ᴶ a∈)))

  canonicalMeetands-lower : {w c : LatTerm X} → c ∈ canonicalMeetands w → w ≤ʷ c
  canonicalMeetands-lower {w} c∈ with ∈-map⁻ ⌊_⌋ᴹ c∈
  ... | _ , a∈ , refl =
    ≤ʷ-trans (proj₂ (canonical-sound w))
             (subst (_≤ʷ _) (meetandsOf-sound (canonical w)) (⋀ᴹ-lower a∈))

  canonicalMeetands-greatest : {w z : LatTerm X} → (∀ {c} → c ∈ canonicalMeetands w → z ≤ʷ c)
                             → z ≤ʷ w
  canonicalMeetands-greatest {w} f =
    ≤ʷ-trans (subst (_ ≤ʷ_) (meetandsOf-sound (canonical w)) (⋀ᴹ-greatest λ a∈ → f (∈-map⁺ ⌊_⌋ᴹ a∈)))
             (proj₁ (canonical-sound w))

  canonicalJoinands-refine : {w u : LatTerm X} {us : List (LatTerm X)} → w ≈ʷ ⋁⁺ u us
                           → ∀ {c} → c ∈ canonicalJoinands w → Any (c ≤ʷ_) (u ∷ us)
  canonicalJoinands-refine {w} e c∈ with ∈-map⁻ ⌊_⌋ᴶ c∈
  ... | _ , a∈ , refl =
    joinands-refine (canonical w) (canonical-isCanonical w) (≈ʷ-trans (canonical-sound w) e) a∈

  canonicalMeetands-refine : {w u : LatTerm X} {us : List (LatTerm X)} → w ≈ʷ ⋀⁺ u us
                           → ∀ {c} → c ∈ canonicalMeetands w → Any (_≤ʷ c) (u ∷ us)
  canonicalMeetands-refine {w} e c∈ with ∈-map⁻ ⌊_⌋ᴹ c∈
  ... | _ , a∈ , refl =
    meetands-refine (canonical w) (canonical-isCanonical w) (≈ʷ-trans (canonical-sound w) e) a∈
```
