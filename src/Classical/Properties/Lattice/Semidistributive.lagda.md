---
layout: default
file: "src/Classical/Properties/Lattice/Semidistributive.lagda.md"
title: "Classical.Properties.Lattice.Semidistributive module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Semidistributivity and Whitman's condition

This is the [Classical.Properties.Lattice.Semidistributive][] module of the [Agda Universal Algebra Library][].

A lattice is *join semidistributive* (SD∨) if `a ∨ b = a ∨ c` implies
`a ∨ b = a ∨ (b ∧ c)`, *meet semidistributive* (SD∧) if the dual implication
holds, and *semidistributive* if it is both.  It satisfies *Whitman's condition*
(W) if `s₁ ∧ s₂ ≤ t₁ ∨ t₂` implies `s₁ ≤ t₁ ∨ t₂`, or `s₂ ≤ t₁ ∨ t₂`, or
`s₁ ∧ s₂ ≤ t₁`, or `s₁ ∧ s₂ ≤ t₂`.  The conditions are independent of
distributivity and of each other.  Every distributive lattice is
semidistributive, yet the product of two three-element chains fails (W), since its
middle element is both a join of two smaller elements and a meet of two larger
ones (see `W-irreducible`{.AgdaFunction} below); and the five-element modular
lattice `M₃` satisfies (W) and neither semidistributive law.  What ties the three
together is the free lattice.  Free lattices satisfy (W) ([Freese, Ježek, and Nation
(1995)][], Theorem 1.8) and are semidistributive (Theorem 1.21, due to Jónsson and
Kiefer), and all three conditions are universal sentences, so every sublattice of
a free lattice satisfies them too.  Conversely, Nation's theorem (Theorem 5.55)
says that a *finite* lattice is a sublattice of a free lattice if and only if it
is semidistributive and satisfies (W).  Nation's proof is deep and is not
formalized here; this module supplies the three conditions it speaks of.

The module defines the predicates `IsJoinSemidistributive`{.AgdaFunction},
`IsMeetSemidistributive`{.AgdaFunction}, `IsSemidistributive`{.AgdaFunction},
and `SatisfiesW`{.AgdaFunction} on an arbitrary `Lattice`{.AgdaFunction}, stated
with the meet order of [Classical.Properties.Lattice][]; proves the second half
of Corollary 1.9 of the book (in a lattice satisfying (W) every element is join
irreducible or meet irreducible); and proves that each condition passes to
sublattices and along isomorphisms.  The free lattice `FL X`{.AgdaFunction} is
shown to satisfy the conditions in
[Classical.Structures.Lattice.Free.Semidistributive][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Properties.Lattice.Semidistributive where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Patterns                using ( 0F ; 1F )
open import Data.Product                     using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                    using ( _⊎_ ) renaming ( map to ⊎-map )
open import Function                         using ( Func )
open import Level                            using ( Level ; _⊔_ )
open import Relation.Binary                  using ( Setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Operations                using ( pair )
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret      using ( interp-cong )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsInjective )
open import Setoid.Homomorphisms.Basic          using ( hom ; IsHom )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; ≅-sym )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )
open import Setoid.Subalgebras.Properties       using ( ≅→≤ )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ β ρᵃ ρᵇ : Level
```
-->

#### The three conditions

Fix a lattice `𝑳`{.AgdaBound}, with the curried operations of
`Lattice-Op`{.AgdaModule} and the meet order `a ≤ b`, meaning `a ∧ b ≈ a`, of
`Lattice-Order`{.AgdaModule}.  The two semidistributive laws are stated as
implications between equations, exactly as in [Freese, Ježek, and Nation
(1995)][], Section I.3, and their conjunction is semidistributivity.  Whitman's
condition is stated for binary meets and joins, with its four disjuncts grouped
in the order of `∧≤∨-inv`{.AgdaFunction}, the inversion of the sixth of Whitman's
rules in [Classical.Structures.Lattice.Free.Whitman][]: first the two meetands
below the join, then the meet below the two joinands.  The book states (W) for
meets and joins of any finite number of elements; the binary form implies the
general one by induction on the numbers of meetands and joinands, and the two are
equivalent.  All four predicates quantify their variables explicitly, so that a
proof can be applied to the elements it is about, and a decision procedure can
sweep them.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( _≤_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ )

  IsJoinSemidistributive : Type (α ⊔ ρ)
  IsJoinSemidistributive = ∀ a b c → a ∨ b ≈ a ∨ c → a ∨ b ≈ a ∨ (b ∧ c)

  IsMeetSemidistributive : Type (α ⊔ ρ)
  IsMeetSemidistributive = ∀ a b c → a ∧ b ≈ a ∧ c → a ∧ b ≈ a ∧ (b ∨ c)

  IsSemidistributive : Type (α ⊔ ρ)
  IsSemidistributive = IsJoinSemidistributive × IsMeetSemidistributive

  SatisfiesW : Type (α ⊔ ρ)
  SatisfiesW = ∀ s₁ s₂ t₁ t₂ → s₁ ∧ s₂ ≤ t₁ ∨ t₂
    → (s₁ ≤ t₁ ∨ t₂ ⊎ s₂ ≤ t₁ ∨ t₂) ⊎ (s₁ ∧ s₂ ≤ t₁ ⊎ s₁ ∧ s₂ ≤ t₂)
```

#### Whitman's condition forbids doubly reducible elements

The second half of [Freese, Ježek, and Nation (1995)][], Corollary 1.9, says that
in a lattice satisfying (W) every element is join irreducible or meet irreducible.
Read constructively, `W-irreducible`{.AgdaFunction} says that if `a` is written
both as a join `b ∨ c` and as a meet `d ∧ e`, then one of the four decompositions
is trivial: `a` equals one of the meetands, or one of the joinands.  The proof
applies (W) to `d ∧ e ≤ b ∨ c`, which holds since both sides equal `a`.  A
meetand below `b ∨ c = a` equals `a`, since `a = d ∧ e` lies below it; and if
`d ∧ e = a` lies below a joinand, the joinand equals `a`, since `a = b ∨ c` lies
above it.

```agda
  module _ (W : SatisfiesW) where
    open Lattice-Order 𝑳      using ( ≤-antisym ; ≤-respˡ-≈ ; ≤-respʳ-≈ ; ≤-reflexive
                                    ; ∧-lowerˡ ; ∧-lowerʳ ; ∨-upperˡ ; ∨-upperʳ )
    open Setoid 𝔻[ proj₁ 𝑳 ]  using ( sym ; trans )

    W-irreducible : ∀ {a b c d e} → a ≈ b ∨ c → a ≈ d ∧ e
      → (a ≈ d ⊎ a ≈ e) ⊎ (a ≈ b ⊎ a ≈ c)
    W-irreducible {a} {b} {c} {d} {e} a≈b∨c a≈d∧e =
      ⊎-map (⊎-map (λ d≤ → ≤-antisym (below ∧-lowerˡ) (≤-respʳ-≈ (sym a≈b∨c) d≤))
                   (λ e≤ → ≤-antisym (below ∧-lowerʳ) (≤-respʳ-≈ (sym a≈b∨c) e≤)))
            (⊎-map (λ ≤b → ≤-antisym (≤-respˡ-≈ (sym a≈d∧e) ≤b) (above ∨-upperˡ))
                   (λ ≤c → ≤-antisym (≤-respˡ-≈ (sym a≈d∧e) ≤c) (above ∨-upperʳ)))
            (W d e b c (≤-reflexive (trans (sym a≈d∧e) a≈b∨c)))
      where
      below : ∀ {x} → d ∧ e ≤ x → a ≤ x
      below = ≤-respˡ-≈ (sym a≈d∧e)

      above : ∀ {x} → x ≤ b ∨ c → x ≤ a
      above = ≤-respʳ-≈ (sym a≈b∨c)
```

#### Homomorphisms and the order

A homomorphism of lattices is a homomorphism of the underlying algebras over
`Sig-Lattice`{.AgdaFunction}, so it commutes with the curried meet and join
(`hom-preserves-∧`{.AgdaFunction}, `hom-preserves-∨`{.AgdaFunction}): its
compatibility with an operation symbol, applied at the argument tuple
`pair x y`, followed by `interp-cong`{.AgdaFunction} at the two argument
positions.  It is therefore monotone for the meet order
(`hom-preserves-≤`{.AgdaFunction}), and an *injective* homomorphism also
reflects the order (`hom-reflects-≤`{.AgdaFunction}): if `h x ≤ h y`, then
`h (x ∧ y) ≈ h x ∧ h y ≈ h x`, so `x ∧ y ≈ x` by injectivity.  These four lemmas
carry each condition from a lattice to its sublattices.  The two lattices are
explicit arguments, since neither is determined by the type of a homomorphism
between their underlying algebras.

```agda
module _ (𝑲 : Lattice α ρᵃ) (𝑳 : Lattice β ρᵇ) where
  open Lattice-Op 𝑲            using () renaming ( _∧_ to _∧ᴷ_ ; _∨_ to _∨ᴷ_ )
  open Lattice-Order 𝑲         using () renaming ( _≤_ to _≤ᴷ_ )
  open Lattice-Op 𝑳            using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳         using ( _≤_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]     using ( _≈_ ; refl ; sym ; trans )

  module _ (h : hom (proj₁ 𝑲) (proj₁ 𝑳)) where
    private
      f : 𝕌[ proj₁ 𝑲 ] → 𝕌[ proj₁ 𝑳 ]
      f = proj₁ h ⟨$⟩_

    hom-preserves-∧ : ∀ x y → f (x ∧ᴷ y) ≈ f x ∧ f y
    hom-preserves-∧ x y =
      trans (IsHom.compatible (proj₂ h) {∧-Op} {pair x y})
            (interp-cong (proj₁ 𝑳) ∧-Op λ { 0F → refl ; 1F → refl })

    hom-preserves-∨ : ∀ x y → f (x ∨ᴷ y) ≈ f x ∨ f y
    hom-preserves-∨ x y =
      trans (IsHom.compatible (proj₂ h) {∨-Op} {pair x y})
            (interp-cong (proj₁ 𝑳) ∨-Op λ { 0F → refl ; 1F → refl })

    hom-preserves-≤ : ∀ {x y} → x ≤ᴷ y → f x ≤ f y
    hom-preserves-≤ {x} {y} x≤y = trans (sym (hom-preserves-∧ x y)) (cong (proj₁ h) x≤y)

    hom-reflects-≤ : IsInjective (proj₁ h) → ∀ {x y} → f x ≤ f y → x ≤ᴷ y
    hom-reflects-≤ inj {x} {y} fx≤fy = inj (trans (hom-preserves-∧ x y) fx≤fy)
```

#### Sublattices

A *sublattice* of `𝑳`{.AgdaBound} is a lattice `𝑲`{.AgdaBound} whose underlying
algebra is a subalgebra of that of `𝑳`{.AgdaBound}, that is, one with an injective
homomorphism into it ([Setoid.Subalgebras.Basic][]).  Each condition passes to
sublattices, which is the content of the remark after Theorem 1.8 in [Freese,
Ježek, and Nation (1995)][]: none of them refers to anything but the operations,
the equality, and universally quantified elements.  The proofs follow the names of
the invariance lemmas of [Setoid.Varieties.Properties][] (`⊧-S-invar`{.AgdaFunction}
for an identity): move the hypothesis into `𝑳`{.AgdaBound} along the
homomorphism `h`{.AgdaBound}, apply the condition there, and move the conclusion
back by injectivity, rewriting `h` past the operations with the lemmas above.

For the join semidistributive law, an equation `a ∨ b ≈ a ∨ c` in `𝑲`{.AgdaBound}
becomes `h a ∨ h b ≈ h a ∨ h c` in `𝑳`{.AgdaBound}, and the conclusion
`h a ∨ h b ≈ h a ∨ (h b ∧ h c)` there is the image of the conclusion in
`𝑲`{.AgdaBound}.  The meet semidistributive law is the dual, and
semidistributivity is the pair.

```agda
  module _ (sub : proj₁ 𝑲 IsSubalgebraOf proj₁ 𝑳) where
    private
      h : hom (proj₁ 𝑲) (proj₁ 𝑳)
      h = proj₁ sub

      f : 𝕌[ proj₁ 𝑲 ] → 𝕌[ proj₁ 𝑳 ]
      f = proj₁ h ⟨$⟩_

    open SetoidReasoning 𝔻[ proj₁ 𝑳 ]
    open Lattice-Op 𝑳  using ( ∧-cong ; ∨-cong )

    IsJoinSemidistributive-S-invar : IsJoinSemidistributive 𝑳 → IsJoinSemidistributive 𝑲
    IsJoinSemidistributive-S-invar sd a b c e = proj₂ sub (begin
      f (a ∨ᴷ b)          ≈⟨ hom-preserves-∨ h a b ⟩
      f a ∨ f b           ≈⟨ sd (f a) (f b) (f c) fe ⟩
      f a ∨ (f b ∧ f c)   ≈˘⟨ ∨-cong refl (hom-preserves-∧ h b c) ⟩
      f a ∨ f (b ∧ᴷ c)    ≈˘⟨ hom-preserves-∨ h a (b ∧ᴷ c) ⟩
      f (a ∨ᴷ (b ∧ᴷ c))   ∎)
      where
      fe : f a ∨ f b ≈ f a ∨ f c
      fe = trans (sym (hom-preserves-∨ h a b)) (trans (cong (proj₁ h) e) (hom-preserves-∨ h a c))

    IsMeetSemidistributive-S-invar : IsMeetSemidistributive 𝑳 → IsMeetSemidistributive 𝑲
    IsMeetSemidistributive-S-invar sd a b c e = proj₂ sub (begin
      f (a ∧ᴷ b)          ≈⟨ hom-preserves-∧ h a b ⟩
      f a ∧ f b           ≈⟨ sd (f a) (f b) (f c) fe ⟩
      f a ∧ (f b ∨ f c)   ≈˘⟨ ∧-cong refl (hom-preserves-∨ h b c) ⟩
      f a ∧ f (b ∨ᴷ c)    ≈˘⟨ hom-preserves-∧ h a (b ∨ᴷ c) ⟩
      f (a ∧ᴷ (b ∨ᴷ c))   ∎)
      where
      fe : f a ∧ f b ≈ f a ∧ f c
      fe = trans (sym (hom-preserves-∧ h a b)) (trans (cong (proj₁ h) e) (hom-preserves-∧ h a c))

    IsSemidistributive-S-invar : IsSemidistributive 𝑳 → IsSemidistributive 𝑲
    IsSemidistributive-S-invar (sd∨ , sd∧) =
      IsJoinSemidistributive-S-invar sd∨ , IsMeetSemidistributive-S-invar sd∧
```

For Whitman's condition, the hypothesis `s₁ ∧ s₂ ≤ t₁ ∨ t₂` in `𝑲`{.AgdaBound}
goes to `𝑳`{.AgdaBound} by monotonicity, and each of the four disjuncts that
(W) returns there comes back by `hom-reflects-≤`{.AgdaFunction}, after `h` is
moved back inside the meet on the left (`reflect-∧ˡ`{.AgdaFunction}) or the
join on the right (`reflect-∨ʳ`{.AgdaFunction}).

```agda
    private
      reflect-∨ʳ : ∀ {x y z} → f x ≤ f y ∨ f z → x ≤ᴷ y ∨ᴷ z
      reflect-∨ʳ {x} {y} {z} p =
        hom-reflects-≤ h (proj₂ sub) (≤-respʳ-≈ (sym (hom-preserves-∨ h y z)) p)
        where open Lattice-Order 𝑳 using ( ≤-respʳ-≈ )

      reflect-∧ˡ : ∀ {x y z} → f x ∧ f y ≤ f z → x ∧ᴷ y ≤ᴷ z
      reflect-∧ˡ {x} {y} {z} p =
        hom-reflects-≤ h (proj₂ sub) (≤-respˡ-≈ (sym (hom-preserves-∧ h x y)) p)
        where open Lattice-Order 𝑳 using ( ≤-respˡ-≈ )

    SatisfiesW-S-invar : SatisfiesW 𝑳 → SatisfiesW 𝑲
    SatisfiesW-S-invar W s₁ s₂ t₁ t₂ p =
      ⊎-map (⊎-map reflect-∨ʳ reflect-∨ʳ) (⊎-map reflect-∧ˡ reflect-∧ˡ)
            (W (f s₁) (f s₂) (f t₁) (f t₂) fp)
      where
      open Lattice-Order 𝑳 using ( ≤-respˡ-≈ ; ≤-respʳ-≈ )

      fp : f s₁ ∧ f s₂ ≤ f t₁ ∨ f t₂
      fp = ≤-respʳ-≈ (hom-preserves-∨ h t₁ t₂)
             (≤-respˡ-≈ (hom-preserves-∧ h s₁ s₂) (hom-preserves-≤ h p))
```

#### Isomorphic lattices

An isomorphism is in particular an injective homomorphism (`≅→≤`{.AgdaFunction}
of [Setoid.Subalgebras.Properties][]), so each condition is invariant under
isomorphism as a special case of the sublattice lemmas, applied to the inverse:
if `𝑲 ≅ 𝑳` and `𝑲`{.AgdaBound} satisfies a condition, then `𝑳`{.AgdaBound},
being isomorphic to a sublattice of `𝑲`{.AgdaBound}, satisfies it too.  The
direction of the lemmas follows `⊧-I-invar`{.AgdaFunction} of
[Setoid.Varieties.Properties][]: from the left-hand side of the isomorphism to
the right.

```agda
module _ (𝑲 : Lattice α ρᵃ) (𝑳 : Lattice β ρᵇ) (φ : proj₁ 𝑲 ≅ proj₁ 𝑳) where
  private
    sub : proj₁ 𝑳 IsSubalgebraOf proj₁ 𝑲
    sub = ≅→≤ (≅-sym φ)

  IsJoinSemidistributive-I-invar : IsJoinSemidistributive 𝑲 → IsJoinSemidistributive 𝑳
  IsJoinSemidistributive-I-invar = IsJoinSemidistributive-S-invar 𝑳 𝑲 sub

  IsMeetSemidistributive-I-invar : IsMeetSemidistributive 𝑲 → IsMeetSemidistributive 𝑳
  IsMeetSemidistributive-I-invar = IsMeetSemidistributive-S-invar 𝑳 𝑲 sub

  IsSemidistributive-I-invar : IsSemidistributive 𝑲 → IsSemidistributive 𝑳
  IsSemidistributive-I-invar = IsSemidistributive-S-invar 𝑳 𝑲 sub

  SatisfiesW-I-invar : SatisfiesW 𝑲 → SatisfiesW 𝑳
  SatisfiesW-I-invar = SatisfiesW-S-invar 𝑳 𝑲 sub
```
