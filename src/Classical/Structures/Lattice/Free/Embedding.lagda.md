---
layout: default
file: "src/Classical/Structures/Lattice/Free/Embedding.lagda.md"
title: "Classical.Structures.Lattice.Free.Embedding module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Embeddings of free lattices and canonical joinands

This is the [Classical.Structures.Lattice.Free.Embedding][] module of the [Agda Universal Algebra Library][].

A lattice embedding `σ : FL(X) ↣ FL(Y)` need not send the canonical form of an
element to the canonical form of its image: a generator `x` may go to an element
that the other images refine.  But a canonical joinand that is *not* a generator
survives.  [Freese, Ježek, and Nation (1995)][], Lemma 9.13: if `w₁` is a
canonical joinand of `w` and `w₁` is not a generator, then `σ(w₁)` is a canonical
joinand of `σ(w)`.  The lemma is the first step of Freese's analysis of Dean's
problem ("Notes on Dean's problem", 1997, where it is Lemma 1), and through it the
term expressing an element in the generators of a free sublattice is a
*truncation* of the element's canonical form.

The book's proof runs as follows.  Write `w = w₁ ∨ ⋯ ∨ wₙ` and
`w₁ = w₁₁ ∧ ⋯ ∧ w₁ₖ` canonically, and `σ(w) = u₁ ∨ ⋯ ∨ uᵣ` canonically.  Since
`σ(w₁) = ⋀ σ(w₁ⱼ) ≤ σ(w) = ⋁ uᵢ`, Whitman's condition gives `σ(w₁ⱼ) ≤ σ(w)` for
some `j`, which the canonicity of `w` (no meetand of a joinand lies below `w`) and
the injectivity of `σ` rule out, or `σ(w₁) ≤ uᵢ` for some `i`.  The canonical
joinands of `σ(w)` refine its representation `⋁ σ(wⱼ)` (Theorem 1.19), so
`uᵢ ≤ σ(wⱼ)` for some `j`, whence `w₁ ≤ wⱼ`, and since the canonical joinands of
`w` form an antichain, `wⱼ = w₁`.  So `uᵢ = σ(w₁)`.  (The book picks the joinand
`uᵢ` first, as the one not refined by the other `σ(wⱼ)`; starting from Whitman's
condition, as here, needs no case on `n` and also covers a join irreducible `w`.)

This module formalizes the argument for substitutions whose induced homomorphism
is injective ([Classical.Structures.Lattice.Free.Substitution][] shows every
homomorphism between free lattices is one), with membership among canonical
joinands read up to equality in the free lattice, since canonical forms are
unique only up to commutativity.  It then proves the dual for canonical meetands
and the two one-step forms of the truncation property.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Embedding where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; lookup ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ )

import Data.List.Relation.Unary.All.Properties       as All
import Data.List.Relation.Unary.AllPairs.Properties  as AllPairs

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Canonical.Algorithm
                                                    using ( module Canonicalization )
open import Classical.Structures.Lattice.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋
         ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁⁺ ; ⋀⁺ ; ⋁⁺-upper ; ⋁⁺-least ; ⋀⁺-lower ; ⋀⁺-greatest ; ⋁ᴶ-upper
         ; ⋀ᴹ-lower ; ⋁ᴶ≡⋁⁺ ; ⋀ᴹ≡⋀⁺ ; W-list ; ≈ʷ-refl ; ≈ʷ-sym ; _≰ʷ_ ; AntichainJ ; AntichainM
         ; IsCanonical ; cgen ; cjoin ; cmeet ; cjmeet ; cmjoin ; asListJ ; asListM ; joinandsOf
         ; meetandsOf ; joinandsOf-canonical ; meetandsOf-canonical )
open import Classical.Structures.Lattice.Free.Canonical.Joinands
  using  ( canonicalJoinands ; canonicalMeetands ; canonicalJoinands-upper
         ; canonicalJoinands-least ; canonicalJoinands-refine ; canonicalMeetands-lower
         ; canonicalMeetands-greatest ; canonicalMeetands-refine )
open import Classical.Structures.Lattice.Free.Canonical.Uniqueness
                                                    using ( module Antichains ; gen≉join ; gen≉meet )
open import Classical.Structures.Lattice.Free.Substitution
                                                    using ( Sub ; _[_] ; []-mono ; []-cong ; ⋁⁺-[]
                                                          ; ⋀⁺-[] ; subst-hom ; injective→reflects )
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm ; ℊ )
open import Classical.Structures.Lattice.Free.Whitman  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans )
open import Setoid.Functions                           using ( IsInjective )

private variable
  χ υ ℓ : Level
  A : Type ℓ
```
-->

#### Antichains

If a list is an antichain for a reflexive relation, a member below another member
is that member, so the second lies below the first as well
(`antichain-≤`{.AgdaFunction}).  This is the step "`w₁ ≤ wⱼ` forces `wⱼ = w₁`" of
the proof.

```agda
antichain-≤ : {R : A → A → Type ℓ} → (∀ {x} → R x x)
            → {xs : List A} → AllPairs (λ x y → ¬ R x y × ¬ R y x) xs
            → {x y : A} → x ∈ xs → y ∈ xs → R x y → R y x
antichain-≤ R-refl (_ ∷ _)   (here refl)  (here refl)  _  = R-refl
antichain-≤ R-refl (Ix ∷ _)  (here refl)  (there y∈)   p  = ⊥-elim (proj₁ (lookup Ix y∈) p)
antichain-≤ R-refl (Iy ∷ _)  (there x∈)   (here refl)  p  = ⊥-elim (proj₂ (lookup Iy x∈) p)
antichain-≤ R-refl (_ ∷ I)   (there x∈)   (there y∈)   p  = antichain-≤ R-refl I x∈ y∈ p
```

#### Two facts about canonical forms

The joinands of a canonical term form an antichain (`joinandsOf-antichain`{.AgdaFunction}):
for a join this is condition 3 of Theorem 1.18, and a generator or a meet is its
only joinand.  And no meetand of a joinand lies below the term
(`joinand-meetands-≰`{.AgdaFunction}): for a join this is condition 4, and for a
meet, whose only joinand is itself, a meetand below the meet would lie below all
the meetands, which an antichain of two or more forbids.  These are the two "basic
properties of canonical forms" the book's proof cites.  The duals hold for
meetands (`meetandsOf-antichain`{.AgdaFunction},
`meetand-joinands-≱`{.AgdaFunction}).

```agda
module _ {X : Type χ} where
  open Antichains {A = CJand X} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans
    using () renaming ( antichain-no-max to no-maxᴶ )
  open Antichains {A = CMand X} (λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ) ≤ʷ-trans
    using () renaming ( antichain-no-min to no-minᴹ )

  joinandsOf-antichain : {C : CTerm X} → IsCanonical C → AntichainJ (asListJ (joinandsOf C))
  joinandsOf-antichain cgen              = [] ∷ []
  joinandsOf-antichain (cjoin _ _ ac _)  = ac
  joinandsOf-antichain (cmeet _ _ _ _)   = [] ∷ []

  meetandsOf-antichain : {C : CTerm X} → IsCanonical C → AntichainM (asListM (meetandsOf C))
  meetandsOf-antichain cgen              = [] ∷ []
  meetandsOf-antichain (cjoin _ _ _ _)   = [] ∷ []
  meetandsOf-antichain (cmeet _ _ ac _)  = ac

  joinand-meetands-≰ : (C : CTerm X) → IsCanonical C → {mh : CMand X} {mt : List (CMand X)}
                     → jmeet mh mt ∈ asListJ (joinandsOf C) → ∀ {m} → m ∈ mh ∷ mt → ⌊ m ⌋ᴹ ≰ʷ ⌊ C ⌋
  joinand-meetands-≰ (genᶜ _)     _                  (here ())
  joinand-meetands-≰ (genᶜ _)     _                  (there ())
  joinand-meetands-≰ (joinᶜ _ _)  (cjoin _ _ _ c4)   a∈           m∈     = c4 a∈ m∈
  joinand-meetands-≰ (meetᶜ _ _)  (cmeet ne _ ac _)  (here refl)  m∈ m≤  =
    no-minᴹ ac ne m∈ (λ v∈ → ≤ʷ-trans m≤ (⋀ᴹ-lower v∈))
  joinand-meetands-≰ (meetᶜ _ _)  _                  (there ())

  meetand-joinands-≱ : (C : CTerm X) → IsCanonical C → {jh : CJand X} {jt : List (CJand X)}
                     → mjoin jh jt ∈ asListM (meetandsOf C) → ∀ {j} → j ∈ jh ∷ jt → ⌊ C ⌋ ≰ʷ ⌊ j ⌋ᴶ
  meetand-joinands-≱ (genᶜ _)     _                  (here ())
  meetand-joinands-≱ (genᶜ _)     _                  (there ())
  meetand-joinands-≱ (joinᶜ _ _)  (cjoin ne _ ac _)  (here refl)  j∈ ≤j  =
    no-maxᴶ ac ne j∈ (λ v∈ → ≤ʷ-trans (⋁ᴶ-upper v∈) ≤j)
  meetand-joinands-≱ (joinᶜ _ _)  _                  (there ())
  meetand-joinands-≱ (meetᶜ _ _)  (cmeet _ _ _ c4)   a∈           j∈     = c4 a∈ j∈
```

Read for the computed canonical form, the first fact says that the canonical
joinands of `w` form an antichain in the free lattice
(`canonicalJoinands-antichain`{.AgdaFunction}), and dually for the canonical
meetands (`canonicalMeetands-antichain`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-isCanonical )

  canonicalJoinands-antichain : (w : LatTerm X)
                              → AllPairs (λ u v → u ≰ʷ v × v ≰ʷ u) (canonicalJoinands _≟_ w)
  canonicalJoinands-antichain w = AllPairs.map⁺ (joinandsOf-antichain (canonical-isCanonical w))

  canonicalMeetands-antichain : (w : LatTerm X)
                              → AllPairs (λ u v → u ≰ʷ v × v ≰ʷ u) (canonicalMeetands _≟_ w)
  canonicalMeetands-antichain w = AllPairs.map⁺ (meetandsOf-antichain (canonical-isCanonical w))
```

The list of canonical joinands is never empty: it is the first joinand
`joinand₀ w`{.AgdaFunction} followed by `joinands₊ w`{.AgdaFunction}, by
definition, and `w` is their join (`joinand-representation`{.AgdaFunction}), by
`canonicalJoinands-upper`{.AgdaFunction} and `canonicalJoinands-least`{.AgdaFunction}
of [Classical.Structures.Lattice.Free.Canonical.Joinands][].  Dually for meetands.

```agda
  joinand₀ : LatTerm X → LatTerm X
  joinand₀ w = ⌊ proj₁ (joinandsOf (canonical w)) ⌋ᴶ

  joinands₊ : LatTerm X → List (LatTerm X)
  joinands₊ w = map ⌊_⌋ᴶ (proj₂ (joinandsOf (canonical w)))

  meetand₀ : LatTerm X → LatTerm X
  meetand₀ w = ⌊ proj₁ (meetandsOf (canonical w)) ⌋ᴹ

  meetands₊ : LatTerm X → List (LatTerm X)
  meetands₊ w = map ⌊_⌋ᴹ (proj₂ (meetandsOf (canonical w)))

  joinand-representation : (w : LatTerm X) → w ≈ʷ ⋁⁺ (joinand₀ w) (joinands₊ w)
  joinand-representation w =
    canonicalJoinands-least _≟_ ⋁⁺-upper , ⋁⁺-least (canonicalJoinands-upper _≟_)

  meetand-representation : (w : LatTerm X) → w ≈ʷ ⋀⁺ (meetand₀ w) (meetands₊ w)
  meetand-representation w =
    ⋀⁺-greatest (canonicalMeetands-lower _≟_) , canonicalMeetands-greatest _≟_ ⋀⁺-lower
```

#### The argument, for lists

The proof of Lemma 9.13 uses only a handful of facts about the canonical form of
`w` and that of `σ(w)`, and it is cleanest stated for lists of lattice terms with
those facts as hypotheses (`joinand-image`{.AgdaFunction}).  The joinand is the
meet `⋀⁺ m₀ ms` of its meetands; it is a member of the joinands `j₀ ∷ js` of `W`,
which form an antichain and whose join is `W`; no meetand lies below `W`; and the
list `u₀ ∷ us`, playing the canonical joinands of `W [ σ ]`, lies below
`W [ σ ]`, has `W [ σ ]` below its join, and refines the representation of
`W [ σ ]` as the join of the images of `j₀ ∷ js`.

```agda
module _ {X : Type χ} {Y : Type υ} (σ : Sub X Y) (inj : IsInjective (proj₁ (subst-hom σ))) where
  private
    reflect : {s t : LatTerm X} → s [ σ ] ≤ʷ t [ σ ] → s ≤ʷ t
    reflect {s} {t} = injective→reflects σ {s = s} {t = t} inj

  joinand-image : {W m₀ j₀ : LatTerm X} {ms js : List (LatTerm X)}
                  {u₀ : LatTerm Y} {us : List (LatTerm Y)}
                → ⋀⁺ m₀ ms ∈ j₀ ∷ js
                → AllPairs (λ u v → u ≰ʷ v × v ≰ʷ u) (j₀ ∷ js)
                → W ≈ʷ ⋁⁺ j₀ js
                → All (_≰ʷ W) (m₀ ∷ ms)
                → (∀ {u} → u ∈ u₀ ∷ us → u ≤ʷ W [ σ ])
                → W [ σ ] ≤ʷ ⋁⁺ u₀ us
                → (∀ {u} → u ∈ u₀ ∷ us → Any (u ≤ʷ_) (map (_[ σ ]) (j₀ ∷ js)))
                → Any (⋀⁺ m₀ ms [ σ ] ≈ʷ_) (u₀ ∷ us)
  joinand-image {W} {m₀} {j₀} {ms} {js} {u₀} {us} c∈ ac e c4 upper least refine =
    [ (λ r → ⊥-elim (no-meetand-below r)) , matched ]′ (W-list (map (_[ σ ]) ms) us image≤)
    where
    c : LatTerm X
    c = ⋀⁺ m₀ ms

    c≤W : c ≤ʷ W
    c≤W = ≤ʷ-trans (⋁⁺-upper c∈) (proj₂ e)

    image≡ : c [ σ ] ≡ ⋀⁺ (m₀ [ σ ]) (map (_[ σ ]) ms)
    image≡ = ⋀⁺-[] σ m₀ ms

    image≤ : ⋀⁺ (m₀ [ σ ]) (map (_[ σ ]) ms) ≤ʷ ⋁⁺ u₀ us
    image≤ = ≤ʷ-trans (subst (_≤ʷ W [ σ ]) image≡ ([]-mono σ c≤W)) least

    -- First case of Whitman's condition: a meetand's image below the join of the uᵢ.
    no-meetand-below : Any (_≤ʷ ⋁⁺ u₀ us) (m₀ [ σ ] ∷ map (_[ σ ]) ms) → ⊥
    no-meetand-below r =
      let (_ , m'∈ , m'≤) = find r
          (m , m∈ , m'≡) = ∈-map⁻ (_[ σ ]) {xs = m₀ ∷ ms} m'∈
      in lookup c4 m∈ (reflect (≤ʷ-trans (subst (_≤ʷ ⋁⁺ u₀ us) m'≡ m'≤) (⋁⁺-least upper)))

    -- Second case: the image of the joinand lies below some uᵢ, which then equals it.
    matched : Any (⋀⁺ (m₀ [ σ ]) (map (_[ σ ]) ms) ≤ʷ_) (u₀ ∷ us) → Any (c [ σ ] ≈ʷ_) (u₀ ∷ us)
    matched r =
      let (u , u∈ , c'≤u) = find r
          c≤u = subst (_≤ʷ u) (sym image≡) c'≤u
          (j' , j'∈ , u≤j') = find (refine u∈)
          (j , j∈ , j'≡) = ∈-map⁻ (_[ σ ]) {xs = j₀ ∷ js} j'∈
          u≤j = subst (u ≤ʷ_) j'≡ u≤j'
          j≤c = antichain-≤ ≤ʷ-refl ac c∈ j∈ (reflect (≤ʷ-trans c≤u u≤j))
      in lose u∈ (c≤u , ≤ʷ-trans u≤j ([]-mono σ j≤c))
```

The dual, for a canonical meetand `⋁⁺ j₀ js` that is a join of its joinands
(`meetand-image`{.AgdaFunction}), runs the same way with the order reversed.

```agda
  meetand-image : {W j₀ m₀ : LatTerm X} {js ms : List (LatTerm X)}
                  {u₀ : LatTerm Y} {us : List (LatTerm Y)}
                → ⋁⁺ j₀ js ∈ m₀ ∷ ms
                → AllPairs (λ u v → u ≰ʷ v × v ≰ʷ u) (m₀ ∷ ms)
                → W ≈ʷ ⋀⁺ m₀ ms
                → All (W ≰ʷ_) (j₀ ∷ js)
                → (∀ {u} → u ∈ u₀ ∷ us → W [ σ ] ≤ʷ u)
                → ⋀⁺ u₀ us ≤ʷ W [ σ ]
                → (∀ {u} → u ∈ u₀ ∷ us → Any (_≤ʷ u) (map (_[ σ ]) (m₀ ∷ ms)))
                → Any (⋁⁺ j₀ js [ σ ] ≈ʷ_) (u₀ ∷ us)
  meetand-image {W} {j₀} {m₀} {js} {ms} {u₀} {us} c∈ ac e c4 lower greatest refine =
    [ matched , (λ r → ⊥-elim (no-joinand-above r)) ]′ (W-list us (map (_[ σ ]) js) image≤)
    where
    c : LatTerm X
    c = ⋁⁺ j₀ js

    W≤c : W ≤ʷ c
    W≤c = ≤ʷ-trans (proj₁ e) (⋀⁺-lower c∈)

    image≡ : c [ σ ] ≡ ⋁⁺ (j₀ [ σ ]) (map (_[ σ ]) js)
    image≡ = ⋁⁺-[] σ j₀ js

    image≤ : ⋀⁺ u₀ us ≤ʷ ⋁⁺ (j₀ [ σ ]) (map (_[ σ ]) js)
    image≤ = ≤ʷ-trans greatest (subst (W [ σ ] ≤ʷ_) image≡ ([]-mono σ W≤c))

    -- Second case of Whitman's condition: the meet of the uᵢ below a joinand's image.
    no-joinand-above : Any (⋀⁺ u₀ us ≤ʷ_) (j₀ [ σ ] ∷ map (_[ σ ]) js) → ⊥
    no-joinand-above r =
      let (_ , j'∈ , ≤j') = find r
          (j , j∈ , j'≡) = ∈-map⁻ (_[ σ ]) {xs = j₀ ∷ js} j'∈
      in lookup c4 j∈ (reflect (≤ʷ-trans (⋀⁺-greatest lower) (subst (⋀⁺ u₀ us ≤ʷ_) j'≡ ≤j')))

    -- First case: some uᵢ lies below the image of the meetand, and then equals it.
    matched : Any (_≤ʷ ⋁⁺ (j₀ [ σ ]) (map (_[ σ ]) js)) (u₀ ∷ us) → Any (c [ σ ] ≈ʷ_) (u₀ ∷ us)
    matched r =
      let (u , u∈ , u≤c') = find r
          u≤c = subst (u ≤ʷ_) (sym image≡) u≤c'
          (m' , m'∈ , m'≤u) = find (refine u∈)
          (m , m∈ , m'≡) = ∈-map⁻ (_[ σ ]) {xs = m₀ ∷ ms} m'∈
          m≤u = subst (_≤ʷ u) m'≡ m'≤u
          c≤m = antichain-≤ ≤ʷ-refl ac m∈ c∈ (reflect (≤ʷ-trans m≤u u≤c))
      in lose u∈ (≤ʷ-trans ([]-mono σ c≤m) m≤u , u≤c)
```

#### Lemma 9.13

Now let `σ` be injective, with decidable equality of both sets of generators so
that canonical forms are computed.  If `c` is a canonical joinand of `w` that is
not a generator, then `c [ σ ]` is a canonical joinand of `w [ σ ]`, up to
equality in the free lattice (`embedding-canonicalJoinand`{.AgdaFunction}).  The
joinand of the computed canonical form behind `c` is a meet, whose meetands
`⌊ mh ⌋ᴹ ∷ map ⌊_⌋ᴹ mt` feed `joinand-image`{.AgdaFunction}; the canonical joinands
of `w` and of `w [ σ ]` supply the other hypotheses, by Theorem 1.19 and the facts
above.  The dual is `embedding-canonicalMeetand`{.AgdaFunction}.

```agda
module _ {X : Type χ} {Y : Type υ} (_≟ˣ_ : DecidableEquality X) (_≟ʸ_ : DecidableEquality Y)
         (σ : Sub X Y) (inj : IsInjective (proj₁ (subst-hom σ))) where
  open Canonicalization _≟ˣ_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  joinand-image-representation : (w : LatTerm X)
    → w [ σ ] ≈ʷ ⋁⁺ (joinand₀ _≟ˣ_ w [ σ ]) (map (_[ σ ]) (joinands₊ _≟ˣ_ w))
  joinand-image-representation w =
    subst (w [ σ ] ≈ʷ_) (⋁⁺-[] σ (joinand₀ _≟ˣ_ w) (joinands₊ _≟ˣ_ w))
          ([]-cong σ (joinand-representation _≟ˣ_ w))

  meetand-image-representation : (w : LatTerm X)
    → w [ σ ] ≈ʷ ⋀⁺ (meetand₀ _≟ˣ_ w [ σ ]) (map (_[ σ ]) (meetands₊ _≟ˣ_ w))
  meetand-image-representation w =
    subst (w [ σ ] ≈ʷ_) (⋀⁺-[] σ (meetand₀ _≟ˣ_ w) (meetands₊ _≟ˣ_ w))
          ([]-cong σ (meetand-representation _≟ˣ_ w))

  embedding-canonicalJoinand : (w : LatTerm X) {c : LatTerm X} → c ∈ canonicalJoinands _≟ˣ_ w
                             → (∀ x → ¬ (c ≈ʷ ℊ x))
                             → Any (c [ σ ] ≈ʷ_) (canonicalJoinands _≟ʸ_ (w [ σ ]))
  embedding-canonicalJoinand w c∈ not-gen with ∈-map⁻ ⌊_⌋ᴶ c∈
  ... | jgen x , _ , refl = ⊥-elim (not-gen x ≈ʷ-refl)
  ... | jmeet mh mt , a∈ , refl =
    subst (λ v → Any (v [ σ ] ≈ʷ_) (canonicalJoinands _≟ʸ_ (w [ σ ]))) (sym (⋀ᴹ≡⋀⁺ mh mt))
      (joinand-image σ inj {W = w} {m₀ = ⌊ mh ⌋ᴹ} {ms = map ⌊_⌋ᴹ mt}
        (subst (_∈ canonicalJoinands _≟ˣ_ w) (⋀ᴹ≡⋀⁺ mh mt) c∈)
        (canonicalJoinands-antichain _≟ˣ_ w)
        (joinand-representation _≟ˣ_ w)
        (All.map⁺ (tabulate λ m∈ m≤w →
          joinand-meetands-≰ (canonical w) (canonical-isCanonical w) a∈ m∈
                             (≤ʷ-trans m≤w (proj₂ (canonical-sound w)))))
        (canonicalJoinands-upper _≟ʸ_)
        (canonicalJoinands-least _≟ʸ_ ⋁⁺-upper)
        (canonicalJoinands-refine _≟ʸ_ (joinand-image-representation w)))

  embedding-canonicalMeetand : (w : LatTerm X) {c : LatTerm X} → c ∈ canonicalMeetands _≟ˣ_ w
                             → (∀ x → ¬ (c ≈ʷ ℊ x))
                             → Any (c [ σ ] ≈ʷ_) (canonicalMeetands _≟ʸ_ (w [ σ ]))
  embedding-canonicalMeetand w c∈ not-gen with ∈-map⁻ ⌊_⌋ᴹ c∈
  ... | mgen x , _ , refl = ⊥-elim (not-gen x ≈ʷ-refl)
  ... | mjoin jh jt , a∈ , refl =
    subst (λ v → Any (v [ σ ] ≈ʷ_) (canonicalMeetands _≟ʸ_ (w [ σ ]))) (sym (⋁ᴶ≡⋁⁺ jh jt))
      (meetand-image σ inj {W = w} {j₀ = ⌊ jh ⌋ᴶ} {js = map ⌊_⌋ᴶ jt}
        (subst (_∈ canonicalMeetands _≟ˣ_ w) (⋁ᴶ≡⋁⁺ jh jt) c∈)
        (canonicalMeetands-antichain _≟ˣ_ w)
        (meetand-representation _≟ˣ_ w)
        (All.map⁺ (tabulate λ j∈ w≤j →
          meetand-joinands-≱ (canonical w) (canonical-isCanonical w) a∈ j∈
                             (≤ʷ-trans (proj₁ (canonical-sound w)) w≤j)))
        (canonicalMeetands-lower _≟ʸ_)
        (canonicalMeetands-greatest _≟ʸ_ ⋀⁺-lower)
        (canonicalMeetands-refine _≟ʸ_ (meetand-image-representation w)))
```

#### Truncation

Freese draws the following consequence.  If `w` lies in the sublattice freely
generated by the images `σ i`, the term `t` expressing it in those generators is
a truncation of the canonical form of `w`: every path from the root of the
canonical form to a leaf passes between an element and an immediate subelement
with one of the `σ i` in between.  One level of that statement is
`joinands-of-image`{.AgdaFunction}: each canonical joinand `u` of `t [ σ ]` is
either the image of a canonical joinand of `t` that is not a generator, or lies
below a generator `σ i` whose generator `ℊ i` is a canonical joinand of `t`.  The
first case is Lemma 9.13 read backward, through the refinement of Theorem 1.19 and
the antichain of canonical joinands; in the second case `σ i` lies between `w`
and the joinand `u`.  `meetands-of-image`{.AgdaFunction} is the dual.

Iterating the two lemmas down a path through the canonical form of `t`, from
joinands to meetands and back, is the induction behind Freese's statement for each
path.  The induction itself is not formalized here: at each level it passes from
`a [ σ ]` to the canonical joinand of `w` that equals it, and so needs the
canonical joinands (or meetands) of two equal elements to agree up to equality,
which is Theorem 1.17 (`≈ʷ⇒≈ᶜ`{.AgdaFunction} of
[Classical.Structures.Lattice.Free.Canonical.Uniqueness][]) read through the
lists.

Freese uses the truncation in an "almost proof" that no ascending chain exists.
There are finitely many truncation patterns of the canonical forms of the three
generators `a`, `b`, `c` of the bottom of a chain, so along an infinite chain one
pattern recurs, and the generators of the later sublattices then lie in fixed
intervals `[a⁻, a⁺]`, `[b⁻, b⁺]`, `[c⁻, c⁺]`.  His Lemma 2 says that if these
intervals are strongly join and meet irredundant (`a⁻ ≰ b⁺ ∨ c⁺`, and
symmetrically and dually), the only element of a freely generated sublattice in
`[a⁻, a⁺]` is its own generator, which would force the chain to be constant.  As
we read the notes, what the argument still needs is that a recurring truncation
pattern yields intervals with that irredundancy; nothing in the truncation lemma
provides it, and the notes leave it open.

```agda
  private
    meet-not-gen : (t : LatTerm X) {mh : CMand X} {mt : List (CMand X)}
                 → jmeet mh mt ∈ asListJ (joinandsOf (canonical t)) → ∀ x → ¬ (⌊ jmeet mh mt ⌋ᴶ ≈ʷ ℊ x)
    meet-not-gen t a∈ x e with lookup (joinandsOf-canonical (canonical-isCanonical t)) a∈
    ... | cjmeet ic = gen≉meet ic (≈ʷ-sym e)

    join-not-gen : (t : LatTerm X) {jh : CJand X} {jt : List (CJand X)}
                 → mjoin jh jt ∈ asListM (meetandsOf (canonical t)) → ∀ x → ¬ (⌊ mjoin jh jt ⌋ᴹ ≈ʷ ℊ x)
    join-not-gen t a∈ x e with lookup (meetandsOf-canonical (canonical-isCanonical t)) a∈
    ... | cmjoin ic = gen≉join ic (≈ʷ-sym e)

  joinands-of-image : (t : LatTerm X) {u : LatTerm Y} → u ∈ canonicalJoinands _≟ʸ_ (t [ σ ])
                    → (Σ[ a ∈ LatTerm X ] a ∈ canonicalJoinands _≟ˣ_ t × (∀ x → ¬ (a ≈ʷ ℊ x))
                                          × u ≈ʷ a [ σ ])
                    ⊎ (Σ[ x ∈ X ] ℊ x ∈ canonicalJoinands _≟ˣ_ t × u ≤ʷ σ x)
  joinands-of-image t {u} u∈
    with find (canonicalJoinands-refine _≟ʸ_ (joinand-image-representation t) u∈)
  ... | a' , a'∈ , u≤a' with ∈-map⁻ (_[ σ ]) {xs = canonicalJoinands _≟ˣ_ t} a'∈
  ...   | a , a∈ , refl with ∈-map⁻ ⌊_⌋ᴶ a∈
  ...     | jgen x , _ , refl = inj₂ (x , a∈ , u≤a')
  ...     | jmeet mh mt , b∈ , refl =
    let not-gen = meet-not-gen t b∈
        (u' , u'∈ , a≈u') = find (embedding-canonicalJoinand t a∈ not-gen)
        u'≤u = antichain-≤ ≤ʷ-refl (canonicalJoinands-antichain _≟ʸ_ (t [ σ ])) u∈ u'∈
                           (≤ʷ-trans u≤a' (proj₁ a≈u'))
    in inj₁ (_ , a∈ , not-gen , u≤a' , ≤ʷ-trans (proj₁ a≈u') u'≤u)
```

For meetands the roles of the two inequalities trade places: a canonical meetand
of `t [ σ ]` is the image of a canonical meetand of `t` that is not a generator,
or lies above a generator `σ i` whose generator is a canonical meetand of `t`.

```agda
  meetands-of-image : (t : LatTerm X) {u : LatTerm Y} → u ∈ canonicalMeetands _≟ʸ_ (t [ σ ])
                    → (Σ[ a ∈ LatTerm X ] a ∈ canonicalMeetands _≟ˣ_ t × (∀ x → ¬ (a ≈ʷ ℊ x))
                                          × u ≈ʷ a [ σ ])
                    ⊎ (Σ[ x ∈ X ] ℊ x ∈ canonicalMeetands _≟ˣ_ t × σ x ≤ʷ u)
  meetands-of-image t {u} u∈
    with find (canonicalMeetands-refine _≟ʸ_ (meetand-image-representation t) u∈)
  ... | a' , a'∈ , a'≤u with ∈-map⁻ (_[ σ ]) {xs = canonicalMeetands _≟ˣ_ t} a'∈
  ...   | a , a∈ , refl with ∈-map⁻ ⌊_⌋ᴹ a∈
  ...     | mgen x , _ , refl = inj₂ (x , a∈ , a'≤u)
  ...     | mjoin jh jt , b∈ , refl =
    let not-gen = join-not-gen t b∈
        (u' , u'∈ , a≈u') = find (embedding-canonicalMeetand t a∈ not-gen)
        u≤u' = antichain-≤ ≤ʷ-refl (canonicalMeetands-antichain _≟ʸ_ (t [ σ ])) u'∈ u∈
                           (≤ʷ-trans (proj₂ a≈u') a'≤u)
    in inj₁ (_ , a∈ , not-gen , ≤ʷ-trans u≤u' (proj₂ a≈u') , a'≤u)
```
