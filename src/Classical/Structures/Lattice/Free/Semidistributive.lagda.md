---
layout: default
file: "src/Classical/Structures/Lattice/Free/Semidistributive.lagda.md"
title: "Classical.Structures.Lattice.Free.Semidistributive module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Free lattices satisfy (W) and are semidistributive

This is the [Classical.Structures.Lattice.Free.Semidistributive][] module of the [Agda Universal Algebra Library][].

The free lattice `FL X`{.AgdaFunction} satisfies Whitman's condition (W) and both
semidistributive laws, the three conditions defined in
[Classical.Properties.Lattice.Semidistributive][].  Since the conditions pass to
sublattices, so does every sublattice of a free lattice, and for a *finite*
lattice the converse is Nation's theorem ([Freese, Ježek, and Nation (1995)][],
Theorem 5.55), which is not formalized.

The two results have proofs of very different depth, and so different hypotheses.

+  **(W)** is Theorem 1.8 of the book, which proves it by Day's doubling
   construction.  In the syntactic development of
   [Classical.Structures.Lattice.Free.Whitman][], (W) is the sixth of the rules
   that *define* the order of `FL X`{.AgdaFunction}, so the theorem is the
   inversion of that rule read through the meet order.  It holds for every type
   of generators.
+  **Semidistributivity** is Theorem 1.21, due to Jónsson and Kiefer.  Its proof
   in the free-lattice case is three lines from Theorem 1.19, the refinement
   property of canonical joinands
   ([Classical.Structures.Lattice.Free.Canonical.Joinands][]).  Canonical forms
   are computed by an algorithm that compares generators, so this half assumes
   that equality of generators is decidable.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Semidistributive where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; _++_
                                                         ; cartesianProductWith )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-cartesianProductWith⁺
                                                         ; ∈-cartesianProductWith⁻ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( _,_ ; proj₂ )
open import Data.Sum.Base                          using () renaming ( map to ⊎-map )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( refl ; sym ; subst )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice.Semidistributive
  using  ( IsJoinSemidistributive ; IsMeetSemidistributive ; IsSemidistributive
         ; SatisfiesW )
open import Classical.Structures.Lattice.Free.Canonical.Basic
  using  ( ⋁⁺ ; ⋁⁺-upper ; ⋁⁺-least ; ≈ʷ-refl )
open import Classical.Structures.Lattice.Free.Canonical.Joinands
  using  ( canonicalJoinands-least ; canonicalJoinands-refine )
open import Classical.Structures.Lattice.Free.Duality  using ( dual ; dual-cong ; dual-reflects-≈ )
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm ; _∧̇_ ; _∨̇_ )
open import Classical.Structures.Lattice.Free.Universal  using ( FL ; ≤ʷ→≤ ; ≤→≤ʷ )
open import Classical.Structures.Lattice.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∧≤∨-inv ; ∨≤ ; ≤∧ ; ≤ʷ-trans ; ∨̇-upperˡ ; ∨̇-upperʳ
         ; ∧̇-lowerˡ ; ∧̇-lowerʳ )

private variable
  χ : Level
  X : Type χ
  a b c u v w z : LatTerm X
  as bs us vs : List (LatTerm X)
```
-->

#### Whitman's condition

An element of `FL X`{.AgdaFunction} is a lattice term, the curried meet and join
of `FL X`{.AgdaFunction} are the formal ones, and its meet order is Whitman's order
`_≤ʷ_`{.AgdaDatatype} (`≤→≤ʷ`{.AgdaFunction} and `≤ʷ→≤`{.AgdaFunction} of
[Classical.Structures.Lattice.Free.Universal][]).  So the hypothesis of (W) in
`FL X`{.AgdaFunction}, `s₁ ∧ s₂ ≤ t₁ ∨ t₂` for elements `s₁`, `s₂`, `t₁`, `t₂`,
is a derivation of `s₁ ∧̇ s₂ ≤ʷ t₁ ∨̇ t₂`: a formal meet below a formal join.  Such
a derivation ends in one of the four constructors of the sixth rule, and its
inversion `∧≤∨-inv`{.AgdaFunction} returns the disjunct, in the order in which
`SatisfiesW`{.AgdaFunction} lists them.  `FL-satisfiesW`{.AgdaFunction} is that
inversion, with each disjunct read back through the meet order.

```agda
FL-satisfiesW : SatisfiesW (FL X)
FL-satisfiesW s₁ s₂ t₁ t₂ p =
  ⊎-map (⊎-map ≤ʷ→≤ ≤ʷ→≤) (⊎-map ≤ʷ→≤ ≤ʷ→≤) (∧≤∨-inv (≤→≤ʷ p))
```

#### Joins of pairwise meets

Theorem 1.21 of [Freese, Ježek, and Nation (1995)][] says more than SD∨: in a free
lattice, if `w = ⋁ᵢ aᵢ = ⋁ⱼ bⱼ` for finite nonempty families, then
`w = ⋁ᵢⱼ (aᵢ ∧ bⱼ)`.  The join of the pairwise meets of the members of two
nonempty lists `a ∷ as` and `b ∷ bs` is `⋁-meets a as b bs`{.AgdaFunction}: the
standard library's `cartesianProductWith`{.AgdaFunction} lists the meets
`u ∧̇ v`, one for each `u` in the first list and `v` in the second, and the list
begins with `a ∧̇ b`, so its join is defined.  Each pairwise meet lies below the
join (`⋁-meets-upper`{.AgdaFunction}).  Conversely the join lies below every `w`
that is the join of the first list (`⋁-meets-below`{.AgdaFunction}), since each
pairwise meet lies below its first meetand; this is the inequality the book
calls obvious.

```agda
⋁-meets : LatTerm X → List (LatTerm X) → LatTerm X → List (LatTerm X) → LatTerm X
⋁-meets a as b bs = ⋁⁺ (a ∧̇ b) (map (a ∧̇_) bs ++ cartesianProductWith _∧̇_ as (b ∷ bs))

⋁-meets-upper : u ∈ a ∷ as → v ∈ b ∷ bs → u ∧̇ v ≤ʷ ⋁-meets a as b bs
⋁-meets-upper u∈ v∈ = ⋁⁺-upper (∈-cartesianProductWith⁺ _∧̇_ u∈ v∈)

⋁-meets-below : w ≈ʷ ⋁⁺ a as → ⋁-meets a as b bs ≤ʷ w
⋁-meets-below {w = w} {a = a} {as = as} {b = b} {bs = bs} ea = ⋁⁺-least below
  where
  below : ∀ {m} → m ∈ cartesianProductWith _∧̇_ (a ∷ as) (b ∷ bs) → m ≤ʷ w
  below m∈ =
    let (u , _ , u∈ , _ , m≡u∧v) = ∈-cartesianProductWith⁻ _∧̇_ (a ∷ as) (b ∷ bs) m∈
    in subst (_≤ʷ w) (sym m≡u∧v) (≤ʷ-trans ∧̇-lowerˡ (≤ʷ-trans (⋁⁺-upper u∈) (proj₂ ea)))
```

#### Theorem 1.21: free lattices are semidistributive

The proof in the book is the following.  Let `w = ⋁ᵢ aᵢ = ⋁ⱼ bⱼ`, and let
`w = w₁ ∨ ⋯ ∨ wₙ` canonically.  By Theorem 1.19 each canonical joinand `wₖ` lies
below some `aᵢ` and below some `bⱼ`, hence below `aᵢ ∧ bⱼ`; so `w`, the join of
its canonical joinands, lies below `⋁ᵢⱼ (aᵢ ∧ bⱼ)`.  The step for one canonical
joinand needs no canonical forms and is `joinand-below`{.AgdaFunction}: an element
below a member of each of two lists lies below any common upper bound of their
pairwise meets.

```agda
joinand-below : (∀ {u v} → u ∈ us → v ∈ vs → u ∧̇ v ≤ʷ z)
  → Any (c ≤ʷ_) us → Any (c ≤ʷ_) vs → c ≤ʷ z
joinand-below f p q =
  let (u , u∈ , c≤u) = find p ; (v , v∈ , c≤v) = find q
  in ≤ʷ-trans (≤∧ c≤u c≤v) (f u∈ v∈)
```

The canonical joinands are those of [Classical.Structures.Lattice.Free.Canonical.Joinands][],
whose module takes the decision procedure `_≟_`{.AgdaBound} for equality of
generators as its parameter, and so does the rest of this module.
`FL-below-meets`{.AgdaFunction} is the theorem in the form the proof gives it:
`w` lies below every common upper bound of the pairwise meets, by
`canonicalJoinands-least`{.AgdaFunction} (an element lies below every common
upper bound of its canonical joinands), with Theorem 1.19,
`canonicalJoinands-refine`{.AgdaFunction}, applied to the two join
representations of `w`.  Taking the join of the pairwise meets as the upper
bound and adding the obvious inequality gives the statement of the book,
`FL-⋁-meets`{.AgdaFunction}.

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where

  FL-below-meets : {w a b z : LatTerm X} {as bs : List (LatTerm X)}
    → w ≈ʷ ⋁⁺ a as → w ≈ʷ ⋁⁺ b bs
    → (∀ {u v} → u ∈ a ∷ as → v ∈ b ∷ bs → u ∧̇ v ≤ʷ z) → w ≤ʷ z
  FL-below-meets ea eb f =
    canonicalJoinands-least _≟_ λ c∈ →
      joinand-below f (canonicalJoinands-refine _≟_ ea c∈) (canonicalJoinands-refine _≟_ eb c∈)

  FL-⋁-meets : {w a b : LatTerm X} {as bs : List (LatTerm X)}
    → w ≈ʷ ⋁⁺ a as → w ≈ʷ ⋁⁺ b bs → w ≈ʷ ⋁-meets a as b bs
  FL-⋁-meets ea eb = FL-below-meets ea eb ⋁-meets-upper , ⋁-meets-below ea
```

The join semidistributive law is the instance `w = a ∨ b = a ∨ c`, with the
two-element lists `a ∷ b ∷ []` and `a ∷ c ∷ []`, whose joins are
`a ∨̇ b` and `a ∨̇ c` by definition.  Of the four pairwise meets, the three that
involve `a` lie below `a`, and the fourth is `b ∧ c`, so all four lie below
`a ∨ (b ∧ c)` (`SD∨-pairs`{.AgdaFunction}); `FL-below-meets`{.AgdaFunction} then
gives `a ∨ b ≤ a ∨ (b ∧ c)`, and the other inequality holds in every lattice.
The book's form `w = ⋁ᵢⱼ (aᵢ ∧ bⱼ)` is not needed for this instance, since the
upper bound `a ∨ (b ∧ c)` can be used directly; and the harder half of Theorem
1.21, that the general form holds in *every* join semidistributive lattice (an
induction on the lengths of the two joins), is not needed for free lattices and
is not formalized.

```agda
SD∨-pairs : u ∈ a ∷ b ∷ [] → v ∈ a ∷ c ∷ [] → u ∧̇ v ≤ʷ a ∨̇ (b ∧̇ c)
SD∨-pairs (here refl)          _                    = ≤ʷ-trans ∧̇-lowerˡ ∨̇-upperˡ
SD∨-pairs (there (here refl))  (here refl)          = ≤ʷ-trans ∧̇-lowerʳ ∨̇-upperˡ
SD∨-pairs (there (here refl))  (there (here refl))  = ∨̇-upperʳ
SD∨-pairs (there (here refl))  (there (there ()))
SD∨-pairs (there (there ()))   _

module _ {X : Type χ} (_≟_ : DecidableEquality X) where

  FL-isJoinSemidistributive : IsJoinSemidistributive (FL X)
  FL-isJoinSemidistributive a b c e =
    FL-below-meets _≟_ {as = b ∷ []} {bs = c ∷ []} ≈ʷ-refl e SD∨-pairs ,
    ∨≤ ∨̇-upperˡ (≤ʷ-trans ∧̇-lowerˡ ∨̇-upperʳ)
```

The meet semidistributive law follows by duality, as the book says.  The dual of
the hypothesis `a ∧ b ≈ a ∧ c` is `dual a ∨ dual b ≈ dual a ∨ dual c`, the dual
of the join semidistributive law applied to `dual a`, `dual b`, `dual c` is the
conclusion `a ∧ b ≈ a ∧ (b ∨ c)`, up to `dual`{.AgdaFunction}, and
`dual-reflects-≈`{.AgdaFunction} of [Classical.Structures.Lattice.Free.Duality][]
removes the duals.

```agda
  FL-isMeetSemidistributive : IsMeetSemidistributive (FL X)
  FL-isMeetSemidistributive a b c e =
    dual-reflects-≈ (FL-isJoinSemidistributive (dual a) (dual b) (dual c) (dual-cong e))

  FL-isSemidistributive : IsSemidistributive (FL X)
  FL-isSemidistributive = FL-isJoinSemidistributive , FL-isMeetSemidistributive
```
