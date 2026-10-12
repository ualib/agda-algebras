---
layout: default
file: "src/Classical/Structures/Lattice/Free/Canonical/Uniqueness.lagda.md"
title: "Classical.Structures.Lattice.Free.Canonical.Uniqueness module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Uniqueness of canonical forms

This is the [Classical.Structures.Lattice.Free.Canonical.Uniqueness][] module of the [Agda Universal Algebra Library][].

Two canonical terms that represent the same element of the free lattice are equal
up to the order of the joinands of each join and the meetands of each meet, at
every level ([Freese, Ježek, and Nation (1995)][], Theorems 1.17 and 1.18).  The
book makes "equal up to commutativity" precise by a recursive relation: two
generators are related when they are equal, and two joins (or two meets) are
related when some permutation of the children of one makes them pairwise related
to the children of the other.  This module defines that relation,
`_≈ᶜ_`{.AgdaDatatype}, with the standard library's permutations and pointwise
lifting, shows that it is an equivalence and that related terms represent the
same element, and proves the converse for canonical terms
(`≈ʷ⇒≈ᶜ`{.AgdaFunction}), which is the uniqueness theorem.

The proof is the book's.  Its engine is Lemma 1.16 (`⋁ᴶ-refines`{.AgdaFunction}):
if `t = t₁ ∨ ⋯ ∨ tₙ` satisfies condition 4 of Theorem 1.18 and `t = s₁ ∨ ⋯ ∨ sₘ`
in the free lattice, then every `tᵢ` lies below some `sⱼ`.  For two canonical
joins representing the same element this gives a refinement in each direction,
and two antichains that refine each other match up one to one, with matched
members equal in the free lattice (`antichain-match`{.AgdaFunction}); induction
on the children then turns the matching into the relation.  A join and a meet,
or a generator and a join or a meet, never represent the same element, because
a canonical join or meet has at least two pairwise incomparable children.

Comparing canonical forms decides equality in the free lattice
(`_≈ᶠ?_`{.AgdaFunction}): two terms are equal exactly when their canonical forms
are related, and the relation is decided on canonical terms by comparing
children recursively, never consulting Whitman's procedure.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Canonical.Uniqueness where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; [_] )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-∃++ ; ∈-insert )
open import Data.List.Relation.Binary.Permutation.Propositional
                                                   using ( _↭_ ; ↭-refl ; ↭-sym ; ↭-trans
                                                         ; ↭-prep ; ↭-reflexive )
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
                                                   using ( All-resp-↭ ; ∈-resp-↭ ; shift )
open import Data.List.Relation.Binary.Pointwise    using ( Pointwise ; [] ; _∷_ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ ; Σ
                                                         ; swap ; uncurry )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using ( _∘_ ; _⇔_ ; mk⇔ ; Equivalence )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans
                                                         ; cong )
open import Relation.Binary.Structures             using ( IsEquivalence )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; does ; map′
                                                         ; _×-dec_ ; _⊎-dec_ )

import Data.List.Relation.Binary.Permutation.Propositional  as Perm
import Data.List.Relation.Binary.Pointwise                  as Pointwise
import Data.List.Relation.Unary.All                         as All
import Data.List.Relation.Unary.AllPairs                    as AllPairs
import Data.List.Relation.Unary.Any                         as Any
import Data.List.Relation.Unary.Any.Properties              as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Canonical.Algorithm
  using  ( module Canonicalization )
open import Classical.Structures.Lattice.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin
         ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ⋁⁺ ; ⋀⁺
         ; gen-⋁⁺-prime ; ⋀⁺-gen-below ; ⋁ᴶ-upper ; ⋀ᴹ-lower ; ⋁ᴶ-dom ; ⋀ᴹ-dom
         ; ⋁ᴶ≡⋁⁺ ; ⋀ᴹ≡⋀⁺ ; gen-⋁ᴶ-prime ; ⋀ᴹ-gen-below ; W-list-ᴹ⁺ ; W-list-⁺ᴶ
         ; W-list-ᴹᴶ ; Cond4J ; Cond4M ; IsCanonical ; cjoin ; cmeet ; IsCanonicalJ
         ; cjmeet ; IsCanonicalM ; cmjoin )
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm ; ℊ )
open import Classical.Structures.Lattice.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ℊ≤ℊ-inv ; ≤ʷ-trans ; module Decision )

private variable
  a ℓ χ : Level
  A : Type a
  X : Type χ
  x y : X
  jh jh' : CJand X
  jt jt' js : List (CJand X)
  mh mh' : CMand X
  mt mt' ms : List (CMand X)
```
-->

#### Equality up to commutativity

`_≈ᶜ_`{.AgdaDatatype} is the book's "equivalent under commutativity", with its
companions `_≈ᶜᴶ_`{.AgdaDatatype} on joinands and `_≈ᶜᴹ_`{.AgdaDatatype} on
meetands.  Two joins are related when the children of the first, rearranged by a
permutation (`_↭_`{.AgdaDatatype}), are pointwise related to the children of the
second (`Pointwise`{.AgdaDatatype}); dually for meets; and generators are related
when they are equal.  The relation is defined by three mutually inductive families,
so that the pointwise lifting can refer to the relation being defined.

```agda
infix 4 _≈ᶜ_ _≈ᶜᴶ_ _≈ᶜᴹ_

data _≈ᶜ_   {X : Type χ} : CTerm X → CTerm X → Type χ
data _≈ᶜᴶ_  {X : Type χ} : CJand X → CJand X → Type χ
data _≈ᶜᴹ_  {X : Type χ} : CMand X → CMand X → Type χ

data _≈ᶜ_ where
  gen≈   : x ≡ y → genᶜ x ≈ᶜ genᶜ y
  join≈  : (jh ∷ jt) ↭ js → Pointwise _≈ᶜᴶ_ js (jh' ∷ jt') → joinᶜ jh jt ≈ᶜ joinᶜ jh' jt'
  meet≈  : (mh ∷ mt) ↭ ms → Pointwise _≈ᶜᴹ_ ms (mh' ∷ mt') → meetᶜ mh mt ≈ᶜ meetᶜ mh' mt'

data _≈ᶜᴶ_ where
  jgen≈   : x ≡ y → jgen x ≈ᶜᴶ jgen y
  jmeet≈  : meetᶜ mh mt ≈ᶜ meetᶜ mh' mt' → jmeet mh mt ≈ᶜᴶ jmeet mh' mt'

data _≈ᶜᴹ_ where
  mgen≈   : x ≡ y → mgen x ≈ᶜᴹ mgen y
  mjoin≈  : joinᶜ jh jt ≈ᶜ joinᶜ jh' jt' → mjoin jh jt ≈ᶜᴹ mjoin jh' jt'
```

#### Permutations and pointwise relations

A few facts about lists support the rest.  A permutation on one side of a pointwise
relation can be moved to the other side, carrying the same element proofs to new
positions (`PW-↭`{.AgdaFunction}, `↭-PW`{.AgdaFunction}).  A pointwise relation
finds a partner for each member of either list (`PW-∈`{.AgdaFunction},
`PW-∈ʳ`{.AgdaFunction}) and splits along an append (`PW-split`{.AgdaFunction}).
And the list `xs ++ y ∷ ys` is `xs ++ ys` with `y` inserted: a member of the one
is `y` or a member of the other (`Any-mid⁻`{.AgdaFunction},
`Any-mid⁺`{.AgdaFunction}), and an `All`{.AgdaDatatype} or a symmetric
`AllPairs`{.AgdaDatatype} on it says the same about `y` and `xs ++ ys`
(`All-mid`{.AgdaFunction}, `AllPairs-mid`{.AgdaFunction}).

```agda
module _ {R : A → A → Type ℓ} where

  PW-↭ : {zs bs cs : List A} → Pointwise R zs bs → bs ↭ cs
       → Σ (List A) λ ws → zs ↭ ws × Pointwise R ws cs
  PW-↭ q              Perm.refl          = _ , ↭-refl , q
  PW-↭ (r ∷ q)        (Perm.prep _ p)    = let (ws , p' , q') = PW-↭ q p
                                           in _ ∷ ws , ↭-prep _ p' , r ∷ q'
  PW-↭ (r₁ ∷ r₂ ∷ q)  (Perm.swap _ _ p)  = let (ws , p' , q') = PW-↭ q p
                                           in _ ∷ _ ∷ ws , Perm.swap _ _ p' , r₂ ∷ r₁ ∷ q'
  PW-↭ q              (Perm.trans p₁ p₂) = let (ws₁ , p₁' , q₁) = PW-↭ q p₁
                                               (ws₂ , p₂' , q₂) = PW-↭ q₁ p₂
                                           in ws₂ , ↭-trans p₁' p₂' , q₂

  ↭-PW : {xs ys zs : List A} → xs ↭ ys → Pointwise R ys zs
       → Σ (List A) λ ws → Pointwise R xs ws × ws ↭ zs
  ↭-PW Perm.refl           q              = _ , q , ↭-refl
  ↭-PW (Perm.prep _ p)     (r ∷ q)        = let (ws , q' , p') = ↭-PW p q
                                            in _ ∷ ws , r ∷ q' , ↭-prep _ p'
  ↭-PW (Perm.swap _ _ p)   (r₁ ∷ r₂ ∷ q)  = let (ws , q' , p') = ↭-PW p q
                                            in _ ∷ _ ∷ ws , r₂ ∷ r₁ ∷ q' , Perm.swap _ _ p'
  ↭-PW (Perm.trans p₁ p₂)  q              = let (ws₂ , q₂ , p₂') = ↭-PW p₂ q
                                                (ws₁ , q₁ , p₁') = ↭-PW p₁ q₂
                                            in ws₁ , q₁ , ↭-trans p₁' p₂'

  PW-∈ : {u : A} {as bs : List A} → Pointwise R as bs → u ∈ as → Any (R u) bs
  PW-∈ (r ∷ _)  (here refl)  = here r
  PW-∈ (_ ∷ q)  (there u∈)   = there (PW-∈ q u∈)

  PW-∈ʳ : {v : A} {as bs : List A} → Pointwise R as bs → v ∈ bs → Any (λ u → R u v) as
  PW-∈ʳ (r ∷ _)  (here refl)  = here r
  PW-∈ʳ (_ ∷ q)  (there v∈)   = there (PW-∈ʳ q v∈)

  PW-split : (bs₁ : List A) {bs₂ zs : List A} → Pointwise R zs (bs₁ ++ bs₂)
           → Σ (List A) λ zs₁ → Σ (List A) λ zs₂
             → (zs ≡ zs₁ ++ zs₂) × Pointwise R zs₁ bs₁ × Pointwise R zs₂ bs₂
  PW-split []         q        = [] , _ , refl , [] , q
  PW-split (_ ∷ bs₁)  (r ∷ q)  = let (zs₁ , zs₂ , e , q₁ , q₂) = PW-split bs₁ q
                                 in _ ∷ zs₁ , zs₂ , cong (_ ∷_) e , r ∷ q₁ , q₂

module _ {P : A → Type ℓ} where

  Any-mid⁻ : (xs : List A) {y : A} {ys : List A} → Any P (xs ++ y ∷ ys) → P y ⊎ Any P (xs ++ ys)
  Any-mid⁻ []        (here p)   = inj₁ p
  Any-mid⁻ []        (there i)  = inj₂ i
  Any-mid⁻ (_ ∷ _)   (here p)   = inj₂ (here p)
  Any-mid⁻ (_ ∷ xs)  (there i)  = [ inj₁ , inj₂ ∘ there ]′ (Any-mid⁻ xs i)

  Any-mid⁺ : (xs : List A) {y : A} {ys : List A} → Any P (xs ++ ys) → Any P (xs ++ y ∷ ys)
  Any-mid⁺ []        i          = there i
  Any-mid⁺ (_ ∷ _)   (here p)   = here p
  Any-mid⁺ (_ ∷ xs)  (there i)  = there (Any-mid⁺ xs i)

  All-mid : (xs : List A) {y : A} {ys : List A} → All P (xs ++ y ∷ ys) → P y × All P (xs ++ ys)
  All-mid []        (p ∷ ps)  = p , ps
  All-mid (_ ∷ xs)  (p ∷ ps)  = let (py , ps') = All-mid xs ps in py , p ∷ ps'

AllPairs-mid : {R : A → A → Type ℓ} → (∀ {u v} → R u v → R v u)
             → (xs : List A) {y : A} {ys : List A} → AllPairs R (xs ++ y ∷ ys)
             → All (R y) (xs ++ ys) × AllPairs R (xs ++ ys)
AllPairs-mid R-sym []        (r ∷ rs)  = r , rs
AllPairs-mid R-sym (_ ∷ xs)  (r ∷ rs)  =
  let (rxy , r') = All-mid xs r
      (ry , rs') = AllPairs-mid R-sym xs rs
  in R-sym rxy ∷ ry , r' ∷ rs'
```

#### The relation is an equivalence

Reflexivity is an induction on the term, with the identity permutation.  Symmetry
reverses the permutation and moves it across the pointwise relation; transitivity
composes the two permutations after moving the second across the first pointwise
relation.  Each recursion runs over the derivation given first, so that the
children's relations are composed by structural recursion.

```agda
≈ᶜ-refl    : (c : CTerm X) → c ≈ᶜ c
≈ᶜᴶ-refl   : (u : CJand X) → u ≈ᶜᴶ u
≈ᶜᴹ-refl   : (u : CMand X) → u ≈ᶜᴹ u
≈ᶜᴶs-refl  : (us : List (CJand X)) → Pointwise _≈ᶜᴶ_ us us
≈ᶜᴹs-refl  : (us : List (CMand X)) → Pointwise _≈ᶜᴹ_ us us

≈ᶜ-refl (genᶜ x)       = gen≈ refl
≈ᶜ-refl (joinᶜ h t)    = join≈ ↭-refl (≈ᶜᴶ-refl h ∷ ≈ᶜᴶs-refl t)
≈ᶜ-refl (meetᶜ h t)    = meet≈ ↭-refl (≈ᶜᴹ-refl h ∷ ≈ᶜᴹs-refl t)
≈ᶜᴶ-refl (jgen x)      = jgen≈ refl
≈ᶜᴶ-refl (jmeet h t)   = jmeet≈ (meet≈ ↭-refl (≈ᶜᴹ-refl h ∷ ≈ᶜᴹs-refl t))
≈ᶜᴹ-refl (mgen x)      = mgen≈ refl
≈ᶜᴹ-refl (mjoin h t)   = mjoin≈ (join≈ ↭-refl (≈ᶜᴶ-refl h ∷ ≈ᶜᴶs-refl t))
≈ᶜᴶs-refl []           = []
≈ᶜᴶs-refl (u ∷ us)     = ≈ᶜᴶ-refl u ∷ ≈ᶜᴶs-refl us
≈ᶜᴹs-refl []           = []
≈ᶜᴹs-refl (u ∷ us)     = ≈ᶜᴹ-refl u ∷ ≈ᶜᴹs-refl us

≈ᶜ-sym    : {s t : CTerm X} → s ≈ᶜ t → t ≈ᶜ s
≈ᶜᴶ-sym   : {u v : CJand X} → u ≈ᶜᴶ v → v ≈ᶜᴶ u
≈ᶜᴹ-sym   : {u v : CMand X} → u ≈ᶜᴹ v → v ≈ᶜᴹ u
≈ᶜᴶs-sym  : {us vs : List (CJand X)} → Pointwise _≈ᶜᴶ_ us vs → Pointwise _≈ᶜᴶ_ vs us
≈ᶜᴹs-sym  : {us vs : List (CMand X)} → Pointwise _≈ᶜᴹ_ us vs → Pointwise _≈ᶜᴹ_ vs us

≈ᶜ-sym (gen≈ e)       = gen≈ (sym e)
≈ᶜ-sym (join≈ p q)    = let (_ , p' , q') = PW-↭ (≈ᶜᴶs-sym q) (↭-sym p) in join≈ p' q'
≈ᶜ-sym (meet≈ p q)    = let (_ , p' , q') = PW-↭ (≈ᶜᴹs-sym q) (↭-sym p) in meet≈ p' q'
≈ᶜᴶ-sym (jgen≈ e)     = jgen≈ (sym e)
≈ᶜᴶ-sym (jmeet≈ e)    = jmeet≈ (≈ᶜ-sym e)
≈ᶜᴹ-sym (mgen≈ e)     = mgen≈ (sym e)
≈ᶜᴹ-sym (mjoin≈ e)    = mjoin≈ (≈ᶜ-sym e)
≈ᶜᴶs-sym []           = []
≈ᶜᴶs-sym (r ∷ q)      = ≈ᶜᴶ-sym r ∷ ≈ᶜᴶs-sym q
≈ᶜᴹs-sym []           = []
≈ᶜᴹs-sym (r ∷ q)      = ≈ᶜᴹ-sym r ∷ ≈ᶜᴹs-sym q

≈ᶜ-trans    : {s t u : CTerm X} → s ≈ᶜ t → t ≈ᶜ u → s ≈ᶜ u
≈ᶜᴶ-trans   : {u v w : CJand X} → u ≈ᶜᴶ v → v ≈ᶜᴶ w → u ≈ᶜᴶ w
≈ᶜᴹ-trans   : {u v w : CMand X} → u ≈ᶜᴹ v → v ≈ᶜᴹ w → u ≈ᶜᴹ w
≈ᶜᴶs-trans  : {us vs ws : List (CJand X)}
            → Pointwise _≈ᶜᴶ_ us vs → Pointwise _≈ᶜᴶ_ vs ws → Pointwise _≈ᶜᴶ_ us ws
≈ᶜᴹs-trans  : {us vs ws : List (CMand X)}
            → Pointwise _≈ᶜᴹ_ us vs → Pointwise _≈ᶜᴹ_ vs ws → Pointwise _≈ᶜᴹ_ us ws

≈ᶜ-trans (gen≈ e)     (gen≈ e')      = gen≈ (trans e e')
≈ᶜ-trans (join≈ p q)  (join≈ p' q')  =
  let (_ , q'' , p'') = ↭-PW p' q'
      (_ , p₀ , q₀)   = PW-↭ (≈ᶜᴶs-trans q q'') p''
  in join≈ (↭-trans p p₀) q₀
≈ᶜ-trans (meet≈ p q)  (meet≈ p' q')  =
  let (_ , q'' , p'') = ↭-PW p' q'
      (_ , p₀ , q₀)   = PW-↭ (≈ᶜᴹs-trans q q'') p''
  in meet≈ (↭-trans p p₀) q₀
≈ᶜᴶ-trans (jgen≈ e)   (jgen≈ e')     = jgen≈ (trans e e')
≈ᶜᴶ-trans (jmeet≈ e)  (jmeet≈ e')    = jmeet≈ (≈ᶜ-trans e e')
≈ᶜᴹ-trans (mgen≈ e)   (mgen≈ e')     = mgen≈ (trans e e')
≈ᶜᴹ-trans (mjoin≈ e)  (mjoin≈ e')    = mjoin≈ (≈ᶜ-trans e e')
≈ᶜᴶs-trans []         []             = []
≈ᶜᴶs-trans (r ∷ q)    (r' ∷ q')      = ≈ᶜᴶ-trans r r' ∷ ≈ᶜᴶs-trans q q'
≈ᶜᴹs-trans []         []             = []
≈ᶜᴹs-trans (r ∷ q)    (r' ∷ q')      = ≈ᶜᴹ-trans r r' ∷ ≈ᶜᴹs-trans q q'

≈ᶜ-isEquivalence : IsEquivalence (_≈ᶜ_ {X = X})
≈ᶜ-isEquivalence = record { refl = ≈ᶜ-refl _ ; sym = ≈ᶜ-sym ; trans = ≈ᶜ-trans }
```

#### Related terms represent the same element

If two canonical terms are related, they represent the same element of the free
lattice (`≈ᶜ⇒≈ʷ`{.AgdaFunction}).  The pointwise relation of the children is first
turned, by structural recursion, into a pointwise equality of the embedded
children; then each join lies below the other by domination, since every child of
one is related to a child of the other through the permutation.

```agda
≈ᶜ⇒≈ʷ    : {s t : CTerm X} → s ≈ᶜ t → ⌊ s ⌋ ≈ʷ ⌊ t ⌋
≈ᶜᴶ⇒≈ʷ   : {u v : CJand X} → u ≈ᶜᴶ v → ⌊ u ⌋ᴶ ≈ʷ ⌊ v ⌋ᴶ
≈ᶜᴹ⇒≈ʷ   : {u v : CMand X} → u ≈ᶜᴹ v → ⌊ u ⌋ᴹ ≈ʷ ⌊ v ⌋ᴹ
≈ᶜᴶs⇒≈ʷ  : {us vs : List (CJand X)} → Pointwise _≈ᶜᴶ_ us vs
         → Pointwise (λ u v → ⌊ u ⌋ᴶ ≈ʷ ⌊ v ⌋ᴶ) us vs
≈ᶜᴹs⇒≈ʷ  : {us vs : List (CMand X)} → Pointwise _≈ᶜᴹ_ us vs
         → Pointwise (λ u v → ⌊ u ⌋ᴹ ≈ʷ ⌊ v ⌋ᴹ) us vs

≈ᶜ⇒≈ʷ (gen≈ refl)    = ≈ʷ-refl
≈ᶜ⇒≈ʷ (join≈ p q)    =
  let q' = ≈ᶜᴶs⇒≈ʷ q in
  ⋁ᴶ-dom (λ u∈ → Any.map proj₁ (PW-∈ q' (∈-resp-↭ p u∈))) ,
  ⋁ᴶ-dom (λ v∈ → let (u , u∈ , e) = find (PW-∈ʳ q' v∈)
                 in lose (∈-resp-↭ (↭-sym p) u∈) (proj₂ e))
≈ᶜ⇒≈ʷ (meet≈ p q)    =
  let q' = ≈ᶜᴹs⇒≈ʷ q in
  ⋀ᴹ-dom (λ v∈ → let (u , u∈ , e) = find (PW-∈ʳ q' v∈)
                 in lose (∈-resp-↭ (↭-sym p) u∈) (proj₁ e)) ,
  ⋀ᴹ-dom (λ u∈ → Any.map proj₂ (PW-∈ q' (∈-resp-↭ p u∈)))
≈ᶜᴶ⇒≈ʷ (jgen≈ refl)  = ≈ʷ-refl
≈ᶜᴶ⇒≈ʷ (jmeet≈ e)    = ≈ᶜ⇒≈ʷ e
≈ᶜᴹ⇒≈ʷ (mgen≈ refl)  = ≈ʷ-refl
≈ᶜᴹ⇒≈ʷ (mjoin≈ e)    = ≈ᶜ⇒≈ʷ e
≈ᶜᴶs⇒≈ʷ []           = []
≈ᶜᴶs⇒≈ʷ (r ∷ q)      = ≈ᶜᴶ⇒≈ʷ r ∷ ≈ᶜᴶs⇒≈ʷ q
≈ᶜᴹs⇒≈ʷ []           = []
≈ᶜᴹs⇒≈ʷ (r ∷ q)      = ≈ᶜᴹ⇒≈ʷ r ∷ ≈ᶜᴹs⇒≈ʷ q
```

#### Lemma 1.16

A join of children satisfying condition 4 refines every join representation of the
element it represents (`⋁ᴶ-refines`{.AgdaFunction}): each child lies below some
joinand of the representation.  A generator child does by join primality; a meet
child `⋀ⱼ tᵢⱼ` lies below the join, so by Whitman's condition either it lies below
some joinand, or some meetand `tᵢⱼ` lies below the join, which is the element
itself, and condition 4 rules that out.  `⋀ᴹ-refines`{.AgdaFunction} is the dual.
The two primed forms (`⋁ᴶ-refinesᴶ`{.AgdaFunction}, `⋀ᴹ-refinesᴹ`{.AgdaFunction})
read the representation as a join or meet of children.

```agda
⋁ᴶ-refines : {h : CJand X} {t : List (CJand X)} {w : LatTerm X} {ws : List (LatTerm X)}
           → Cond4J h t → ⋁ᴶ h t ≈ʷ ⋁⁺ w ws
           → ∀ {u} → u ∈ (h ∷ t) → Any (⌊ u ⌋ᴶ ≤ʷ_) (w ∷ ws)
⋁ᴶ-refines c4 (p , _) {jgen _}       u∈ = gen-⋁⁺-prime (≤ʷ-trans (⋁ᴶ-upper u∈) p)
⋁ᴶ-refines c4 (p , q) {jmeet _ _}    u∈ with W-list-ᴹ⁺ (≤ʷ-trans (⋁ᴶ-upper u∈) p)
... | inj₁ r = let (_ , m∈ , m≤) = find r in ⊥-elim (c4 u∈ m∈ (≤ʷ-trans m≤ q))
... | inj₂ r = r

⋀ᴹ-refines : {h : CMand X} {t : List (CMand X)} {w : LatTerm X} {ws : List (LatTerm X)}
           → Cond4M h t → ⋀ᴹ h t ≈ʷ ⋀⁺ w ws
           → ∀ {u} → u ∈ (h ∷ t) → Any (_≤ʷ ⌊ u ⌋ᴹ) (w ∷ ws)
⋀ᴹ-refines c4 (_ , q) {mgen _}       u∈ = ⋀⁺-gen-below (≤ʷ-trans q (⋀ᴹ-lower u∈))
⋀ᴹ-refines c4 (p , q) {mjoin _ _}    u∈ with W-list-⁺ᴶ (≤ʷ-trans q (⋀ᴹ-lower u∈))
... | inj₁ r = r
... | inj₂ r = let (_ , j∈ , ≤j) = find r in ⊥-elim (c4 u∈ j∈ (≤ʷ-trans p ≤j))

⋁ᴶ-refinesᴶ : {h h' : CJand X} {t t' : List (CJand X)} → Cond4J h t → ⋁ᴶ h t ≈ʷ ⋁ᴶ h' t'
            → ∀ {u} → u ∈ (h ∷ t) → Any (λ v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) (h' ∷ t')
⋁ᴶ-refinesᴶ {h' = h'} {t' = t'} c4 e u∈ =
  Any.map⁻ (⋁ᴶ-refines c4 (subst≈ʳ (⋁ᴶ≡⋁⁺ h' t') e) u∈)
  where subst≈ʳ : {s t t' : LatTerm _} → t ≡ t' → s ≈ʷ t → s ≈ʷ t'
        subst≈ʳ refl e = e

⋀ᴹ-refinesᴹ : {h h' : CMand X} {t t' : List (CMand X)} → Cond4M h t → ⋀ᴹ h t ≈ʷ ⋀ᴹ h' t'
            → ∀ {u} → u ∈ (h ∷ t) → Any (λ v → ⌊ v ⌋ᴹ ≤ʷ ⌊ u ⌋ᴹ) (h' ∷ t')
⋀ᴹ-refinesᴹ {h' = h'} {t' = t'} c4 e u∈ =
  Any.map⁻ (⋀ᴹ-refines c4 (subst≈ʳ (⋀ᴹ≡⋀⁺ h' t') e) u∈)
  where subst≈ʳ : {s t t' : LatTerm _} → t ≡ t' → s ≈ʷ t → s ≈ʷ t'
        subst≈ʳ refl e = e
```

#### Antichains

The order facts the uniqueness proof needs about antichains hold for any
transitive relation `_≼_`{.AgdaBound}, and are proved once, in a module
parameterized by it.  An antichain (pairwise `Incomparable`{.AgdaFunction}
members) with at least two members has neither a greatest member
(`antichain-no-max`{.AgdaFunction}) nor a least one
(`antichain-no-min`{.AgdaFunction}).  And two antichains each of which refines
the other match up one to one (`antichain-match`{.AgdaFunction}): some
permutation of the first is pointwise equivalent, under `_≼_`{.AgdaBound} in
both directions, to the second.  This is the step "since both are antichains,
`n = m` and after renumbering `sᵢ ~ tᵢ`" of the book's proof of Theorem 1.17
(compare Lemma 1.15, parts (4) and (5)).

The matching is built by induction on the first antichain.  Its first member `u`
lies below some `b` of the second, which lies below some member of the first;
that member is `u` itself, since `u` is incomparable to the others, so `u` and `b`
are equivalent.  Removing `u` and `b` leaves two antichains that still refine each
other, because a member of either that refined through `u` or `b` would be
comparable to it.  The matching of the remainders, with `u` inserted at the
position of `b`, is the matching of the whole.

```agda
module Antichains {A : Type a} (_≼_ : A → A → Type ℓ)
                  (≼-trans : ∀ {u v w} → u ≼ v → v ≼ w → u ≼ w) where

  Incomparable : A → A → Type ℓ
  Incomparable u v = ¬ (u ≼ v) × ¬ (v ≼ u)

  antichain-no-max : {h u : A} {t : List A} → AllPairs Incomparable (h ∷ t) → t ≢ []
                   → u ∈ (h ∷ t) → (∀ {v} → v ∈ (h ∷ t) → v ≼ u) → ⊥
  antichain-no-max {t = []}     _          ne  _            _    = ne refl
  antichain-no-max {t = _ ∷ _}  (Ih ∷ _)   _   (here refl)  top  = proj₂ (All.head Ih) (top (there (here refl)))
  antichain-no-max {t = _ ∷ _}  (Ih ∷ _)   _   (there u∈)   top  = proj₁ (All.lookup Ih u∈) (top (here refl))

  antichain-no-min : {h u : A} {t : List A} → AllPairs Incomparable (h ∷ t) → t ≢ []
                   → u ∈ (h ∷ t) → (∀ {v} → v ∈ (h ∷ t) → u ≼ v) → ⊥
  antichain-no-min {t = []}     _          ne  _            _    = ne refl
  antichain-no-min {t = _ ∷ _}  (Ih ∷ _)   _   (here refl)  bot  = proj₁ (All.head Ih) (bot (there (here refl)))
  antichain-no-min {t = _ ∷ _}  (Ih ∷ _)   _   (there u∈)   bot  = proj₂ (All.lookup Ih u∈) (bot (here refl))

  Equivalent : A → A → Type ℓ
  Equivalent u v = u ≼ v × v ≼ u

  antichain-match : {us vs : List A} → AllPairs Incomparable us → AllPairs Incomparable vs
                  → (∀ {u} → u ∈ us → Any (u ≼_) vs) → (∀ {v} → v ∈ vs → Any (v ≼_) us)
                  → Σ (List A) λ zs → (us ↭ zs) × Pointwise Equivalent zs vs
  match-cons : {u b : A} {us vs₁ vs₂ : List A}
             → All (Incomparable u) us → AllPairs Incomparable us
             → AllPairs Incomparable (vs₁ ++ b ∷ vs₂)
             → (∀ {w} → w ∈ us → Any (w ≼_) (vs₁ ++ b ∷ vs₂))
             → (∀ {v} → v ∈ (vs₁ ++ b ∷ vs₂) → Any (v ≼_) (u ∷ us))
             → u ≼ b
             → Σ (List A) λ zs → (u ∷ us ↭ zs) × Pointwise Equivalent zs (vs₁ ++ b ∷ vs₂)

  antichain-match {[]}      {[]}     _          _    _  _ = [] , ↭-refl , []
  antichain-match {[]}      {_ ∷ _}  _          _    _  g with g (here refl)
  ... | ()
  antichain-match {u ∷ us}  {vs}     (Iu ∷ Ius) Ivs  f  g with find (f (here refl))
  ... | b , b∈ , u≼b with ∈-∃++ b∈
  ...   | vs₁ , vs₂ , refl =
    match-cons Iu Ius Ivs (λ w∈ → f (there w∈)) g u≼b

  match-cons {u} {b} {us} {vs₁} {vs₂} Iu Ius Ivs f g u≼b =
    let (Ib , Ivs') = AllPairs-mid swap vs₁ Ivs
        (zs , p , q) = antichain-match Ius Ivs' f' g'
        (zs₁ , zs₂ , e , q₁ , q₂) = PW-split vs₁ q
    in zs₁ ++ u ∷ zs₂
     , ↭-trans (↭-prep u (↭-trans p (↭-reflexive e))) (↭-sym (shift u zs₁ zs₂))
     , Pointwise.++⁺ q₁ ((u≼b , b≼u) ∷ q₂)
    where
    b≼u : b ≼ u
    b≼u with g (∈-insert vs₁)
    ... | here b≼u   = b≼u
    ... | there i    = let (_ , u'∈ , b≼u') = find i
                       in ⊥-elim (proj₁ (All.lookup Iu u'∈) (≼-trans u≼b b≼u'))

    f' : ∀ {w} → w ∈ us → Any (w ≼_) (vs₁ ++ vs₂)
    f' {w} w∈ with Any-mid⁻ vs₁ (f w∈)
    ... | inj₁ w≼b  = ⊥-elim (proj₂ (All.lookup Iu w∈) (≼-trans w≼b b≼u))
    ... | inj₂ i    = i

    g' : ∀ {v} → v ∈ (vs₁ ++ vs₂) → Any (v ≼_) us
    g' {v} v∈ with g (Any-mid⁺ vs₁ v∈)
    ... | here v≼u  = ⊥-elim (proj₂ (All.lookup (proj₁ (AllPairs-mid swap vs₁ Ivs)) v∈)
                                    (≼-trans v≼u u≼b))
    ... | there i   = i
```

#### Theorem 1.17

Two canonical terms that represent the same element are related by
`_≈ᶜ_`{.AgdaDatatype} (`≈ʷ⇒≈ᶜ`{.AgdaFunction}).  Terms of different shapes never
represent the same element.  A generator equal to a canonical join would lie below
one of its joinands by join primality, and every joinand lies below the join,
hence below that one, which no antichain of two or more members allows
(`gen≉join`{.AgdaFunction}); dually for a meet (`gen≉meet`{.AgdaFunction}); and
if a canonical join equals a canonical meet, Whitman's condition puts either a
meetand below the whole meet or the whole join below a joinand, with the same
contradiction (`join≉meet`{.AgdaFunction}).

```agda
module _ {X : Type χ} where
  open Antichains {A = CJand X} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans
    using () renaming ( antichain-no-max to no-maxᴶ )
  open Antichains {A = CMand X} (λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ) ≤ʷ-trans
    using () renaming ( antichain-no-min to no-minᴹ )

  gen≉join : {x : X} {h : CJand X} {t : List (CJand X)}
           → IsCanonical (joinᶜ h t) → ℊ x ≈ʷ ⋁ᴶ h t → ⊥
  gen≉join (cjoin ne _ ac _) (p , q) =
    let (_ , u∈ , x≤u) = find (gen-⋁ᴶ-prime p)
    in no-maxᴶ ac ne u∈ (λ v∈ → ≤ʷ-trans (⋁ᴶ-upper v∈) (≤ʷ-trans q x≤u))

  gen≉meet : {x : X} {h : CMand X} {t : List (CMand X)}
           → IsCanonical (meetᶜ h t) → ℊ x ≈ʷ ⋀ᴹ h t → ⊥
  gen≉meet (cmeet ne _ ac _) (p , q) =
    let (_ , u∈ , u≤x) = find (⋀ᴹ-gen-below q)
    in no-minᴹ ac ne u∈ (λ v∈ → ≤ʷ-trans u≤x (≤ʷ-trans p (⋀ᴹ-lower v∈)))

  join≉meet : {jh : CJand X} {jt : List (CJand X)} {mh : CMand X} {mt : List (CMand X)}
            → IsCanonical (joinᶜ jh jt) → IsCanonical (meetᶜ mh mt) → ⋁ᴶ jh jt ≈ʷ ⋀ᴹ mh mt → ⊥
  join≉meet (cjoin jne _ jac _) (cmeet mne _ mac _) (p , q) with W-list-ᴹᴶ q
  ... | inj₁ r = let (_ , m∈ , m≤) = find r
                 in no-minᴹ mac mne m∈ (λ v∈ → ≤ʷ-trans m≤ (≤ʷ-trans p (⋀ᴹ-lower v∈)))
  ... | inj₂ r = let (_ , j∈ , ≤j) = find r
                 in no-maxᴶ jac jne j∈ (λ v∈ → ≤ʷ-trans (⋁ᴶ-upper v∈) (≤ʷ-trans p ≤j))
```

For two joins, Lemma 1.16 gives a refinement each way, `antichain-match`{.AgdaFunction}
pairs the joinands, and the theorem for the joinands (an induction on the first
term) turns each pair into a relation.  The induction hypothesis is collected for
all the joinands of the first term before the matching permutes them
(`≈ʷ⇒≈ᶜᴶs`{.AgdaFunction} builds an `All`{.AgdaDatatype} of it, and
`All-resp-↭`{.AgdaFunction} carries it along the permutation), so that every
recursive call is on a child of the first term.  Meets are dual: the matching runs
on the reversed order.

```agda
private
  Uniqᴶ : {X : Type χ} → CJand X → Type χ
  Uniqᴶ u = ∀ v → IsCanonicalJ u → IsCanonicalJ v → ⌊ u ⌋ᴶ ≈ʷ ⌊ v ⌋ᴶ → u ≈ᶜᴶ v

  Uniqᴹ : {X : Type χ} → CMand X → Type χ
  Uniqᴹ u = ∀ v → IsCanonicalM u → IsCanonicalM v → ⌊ u ⌋ᴹ ≈ʷ ⌊ v ⌋ᴹ → u ≈ᶜᴹ v

  upgrade : {B : Type χ} {Can : B → Type χ} {R : B → B → Type χ} {S : B → B → Type χ}
            {zs vs : List B}
          → All (λ u → ∀ v → Can u → Can v → R u v → S u v) zs → All Can zs → All Can vs
          → Pointwise R zs vs → Pointwise S zs vs
  upgrade []        []          []          []        = []
  upgrade (f ∷ fs)  (cu ∷ cus)  (cv ∷ cvs)  (r ∷ rs)  = f _ cu cv r ∷ upgrade fs cus cvs rs

≈ʷ⇒≈ᶜ      : (s t : CTerm X) → IsCanonical s → IsCanonical t → ⌊ s ⌋ ≈ʷ ⌊ t ⌋ → s ≈ᶜ t
≈ʷ⇒≈ᶜᴶ     : (u : CJand X) → Uniqᴶ u
≈ʷ⇒≈ᶜᴹ     : (u : CMand X) → Uniqᴹ u
≈ʷ⇒≈ᶜᴶs    : (us : List (CJand X)) → All Uniqᴶ us
≈ʷ⇒≈ᶜᴹs    : (us : List (CMand X)) → All Uniqᴹ us
≈ʷ⇒≈ᶜ-join : (h : CJand X) (t : List (CJand X)) (s : CTerm X)
           → IsCanonical (joinᶜ h t) → IsCanonical s → ⋁ᴶ h t ≈ʷ ⌊ s ⌋ → joinᶜ h t ≈ᶜ s
≈ʷ⇒≈ᶜ-meet : (h : CMand X) (t : List (CMand X)) (s : CTerm X)
           → IsCanonical (meetᶜ h t) → IsCanonical s → ⋀ᴹ h t ≈ʷ ⌊ s ⌋ → meetᶜ h t ≈ᶜ s

≈ʷ⇒≈ᶜ (genᶜ x)     (genᶜ y)     _   _   e = gen≈ (ℊ≤ℊ-inv (proj₁ e))
≈ʷ⇒≈ᶜ (genᶜ x)     (joinᶜ _ _)  _   c'  e = ⊥-elim (gen≉join c' e)
≈ʷ⇒≈ᶜ (genᶜ x)     (meetᶜ _ _)  _   c'  e = ⊥-elim (gen≉meet c' e)
≈ʷ⇒≈ᶜ (joinᶜ h t)  s            c   c'  e = ≈ʷ⇒≈ᶜ-join h t s c c' e
≈ʷ⇒≈ᶜ (meetᶜ h t)  s            c   c'  e = ≈ʷ⇒≈ᶜ-meet h t s c c' e

≈ʷ⇒≈ᶜ-join h t (genᶜ _)       c   _   e = ⊥-elim (gen≉join c (≈ʷ-sym e))
≈ʷ⇒≈ᶜ-join h t (meetᶜ _ _)    c   c'  e = ⊥-elim (join≉meet c c' e)
≈ʷ⇒≈ᶜ-join h t (joinᶜ h' t')  (cjoin _ cs ac c4) (cjoin _ cs' ac' c4') e =
  let (_ , p , q) = antichain-match ac ac' (⋁ᴶ-refinesᴶ c4 e) (⋁ᴶ-refinesᴶ c4' (≈ʷ-sym e))
  in join≈ p (upgrade (All-resp-↭ p (≈ʷ⇒≈ᶜᴶ h ∷ ≈ʷ⇒≈ᶜᴶs t)) (All-resp-↭ p cs) cs' q)
  where open Antichains {A = CJand _} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans

≈ʷ⇒≈ᶜ-meet h t (genᶜ _)       c   _   e = ⊥-elim (gen≉meet c (≈ʷ-sym e))
≈ʷ⇒≈ᶜ-meet h t (joinᶜ _ _)    c   c'  e = ⊥-elim (join≉meet c' c (≈ʷ-sym e))
≈ʷ⇒≈ᶜ-meet h t (meetᶜ h' t')  (cmeet _ cs ac c4) (cmeet _ cs' ac' c4') e =
  let (_ , p , q) = antichain-match (AllPairs.map swap ac) (AllPairs.map swap ac')
                                    (⋀ᴹ-refinesᴹ c4 e) (⋀ᴹ-refinesᴹ c4' (≈ʷ-sym e))
  in meet≈ p (upgrade (All-resp-↭ p (≈ʷ⇒≈ᶜᴹ h ∷ ≈ʷ⇒≈ᶜᴹs t)) (All-resp-↭ p cs) cs'
                      (Pointwise.map swap q))
  where open Antichains {A = CMand _} (λ u v → ⌊ v ⌋ᴹ ≤ʷ ⌊ u ⌋ᴹ) (λ p q → ≤ʷ-trans q p)

≈ʷ⇒≈ᶜᴶ (jgen x)      (jgen y)       _           _            e = jgen≈ (ℊ≤ℊ-inv (proj₁ e))
≈ʷ⇒≈ᶜᴶ (jgen x)      (jmeet _ _)    _           (cjmeet c')  e = ⊥-elim (gen≉meet c' e)
≈ʷ⇒≈ᶜᴶ (jmeet _ _)   (jgen _)       (cjmeet c)  _            e = ⊥-elim (gen≉meet c (≈ʷ-sym e))
≈ʷ⇒≈ᶜᴶ (jmeet h t)   (jmeet h' t')  (cjmeet c)  (cjmeet c')  e =
  jmeet≈ (≈ʷ⇒≈ᶜ-meet h t (meetᶜ h' t') c c' e)

≈ʷ⇒≈ᶜᴹ (mgen x)      (mgen y)       _           _            e = mgen≈ (ℊ≤ℊ-inv (proj₁ e))
≈ʷ⇒≈ᶜᴹ (mgen x)      (mjoin _ _)    _           (cmjoin c')  e = ⊥-elim (gen≉join c' e)
≈ʷ⇒≈ᶜᴹ (mjoin _ _)   (mgen _)       (cmjoin c)  _            e = ⊥-elim (gen≉join c (≈ʷ-sym e))
≈ʷ⇒≈ᶜᴹ (mjoin h t)   (mjoin h' t')  (cmjoin c)  (cmjoin c')  e =
  mjoin≈ (≈ʷ⇒≈ᶜ-join h t (joinᶜ h' t') c c' e)

≈ʷ⇒≈ᶜᴶs []        = []
≈ʷ⇒≈ᶜᴶs (u ∷ us)  = ≈ʷ⇒≈ᶜᴶ u ∷ ≈ʷ⇒≈ᶜᴶs us
≈ʷ⇒≈ᶜᴹs []        = []
≈ʷ⇒≈ᶜᴹs (u ∷ us)  = ≈ʷ⇒≈ᶜᴹ u ∷ ≈ʷ⇒≈ᶜᴹs us
```

#### Comparing canonical forms

On canonical terms the relation is decided by comparing children
(`≈ᶜ?`{.AgdaFunction}).  Two canonical joins are related exactly when every child
of each is related to some child of the other: a permutation with pointwise
related children gives such partners (`≈ᴾ⇒partners`{.AgdaFunction}), and
conversely partners in both directions make each join lie below the other, hence
equal in the free lattice, hence related by Theorem 1.17
(`partners⇒≈ᶜ-join`{.AgdaFunction}).  The comparison of children is the same
procedure, one level down, so the decision is a structural recursion on the first
term; for generators it is the decision `_≟_`{.AgdaBound} of equality of
generators.  Nothing here consults Whitman's procedure.

```agda
≈ᴾ⇒partners : {R : A → A → Type ℓ} {us zs vs : List A} → us ↭ zs → Pointwise R zs vs
            → All (λ u → Any (R u) vs) us × All (λ v → Any (λ u → R u v) us) vs
≈ᴾ⇒partners p q =
  tabulate (λ u∈ → PW-∈ q (∈-resp-↭ p u∈)) ,
  tabulate (λ v∈ → let (_ , z∈ , r) = find (PW-∈ʳ q v∈)
                   in lose (∈-resp-↭ (↭-sym p) z∈) r)

partners⇒≈ᶜ-join : {h h' : CJand X} {t t' : List (CJand X)}
                 → IsCanonical (joinᶜ h t) → IsCanonical (joinᶜ h' t')
                 → All (λ u → Any (u ≈ᶜᴶ_) (h' ∷ t')) (h ∷ t)
                 → All (λ v → Any (_≈ᶜᴶ v) (h ∷ t)) (h' ∷ t')
                 → joinᶜ h t ≈ᶜ joinᶜ h' t'
partners⇒≈ᶜ-join {h = h} {h'} {t} {t'} c c' fwd bwd =
  ≈ʷ⇒≈ᶜ-join h t (joinᶜ h' t') c c'
    ( ⋁ᴶ-dom (λ u∈ → Any.map (proj₁ ∘ ≈ᶜᴶ⇒≈ʷ) (All.lookup fwd u∈))
    , ⋁ᴶ-dom (λ v∈ → Any.map (proj₂ ∘ ≈ᶜᴶ⇒≈ʷ) (All.lookup bwd v∈)) )

partners⇒≈ᶜ-meet : {h h' : CMand X} {t t' : List (CMand X)}
                 → IsCanonical (meetᶜ h t) → IsCanonical (meetᶜ h' t')
                 → All (λ u → Any (u ≈ᶜᴹ_) (h' ∷ t')) (h ∷ t)
                 → All (λ v → Any (_≈ᶜᴹ v) (h ∷ t)) (h' ∷ t')
                 → meetᶜ h t ≈ᶜ meetᶜ h' t'
partners⇒≈ᶜ-meet {h = h} {h'} {t} {t'} c c' fwd bwd =
  ≈ʷ⇒≈ᶜ-meet h t (meetᶜ h' t') c c'
    ( ⋀ᴹ-dom (λ v∈ → Any.map (proj₁ ∘ ≈ᶜᴹ⇒≈ʷ) (All.lookup bwd v∈))
    , ⋀ᴹ-dom (λ u∈ → Any.map (proj₂ ∘ ≈ᶜᴹ⇒≈ʷ) (All.lookup fwd u∈)) )
```

The decision itself searches for partners.  `any-canonical?`{.AgdaFunction} and
`partners?`{.AgdaFunction} decide the existence of a partner for one child and for
every child, given deciders for the children of the first term, which
`≈ᶜᴶs?`{.AgdaFunction} collects by structural recursion, in the way the uniqueness
proof collects its induction hypothesis.  The module `Comparison`{.AgdaModule}
takes the decision procedure for equality of generators as its parameter.  (The
lemma `does-unique`{.AgdaFunction}, that any two decisions of one proposition
return the same verdict, is used at the end of the module.)

```agda
module _ {B : Type χ} {Can : B → Type χ} {R : B → B → Type χ} where

  private
    Decider : B → Type χ
    Decider u = ∀ v → Can u → Can v → Dec (R u v)

  any-canonical? : {P : B → Type χ} {vs : List B}
                 → (∀ v → Can v → Dec (P v)) → All Can vs → Dec (Any P vs)
  any-canonical? P? []          = no λ ()
  any-canonical? P? (cv ∷ cvs)  =
    map′ [ here , there ]′ (λ { (here p) → inj₁ p ; (there i) → inj₂ i })
         (P? _ cv ⊎-dec any-canonical? P? cvs)

  partners? : {us vs : List B} → All Decider us → All Can us → All Can vs
            → Dec (All (λ u → Any (R u) vs) us × All (λ v → Any (λ u → R u v) us) vs)
  partners? {us} {vs} ds cus cvs = forth ds cus ×-dec back cvs
    where
    forth : {ws : List B} → All Decider ws → All Can ws → Dec (All (λ u → Any (R u) vs) ws)
    forth []        []          = yes []
    forth (d ∷ ds)  (cu ∷ cus)  =
      map′ (uncurry _∷_) (λ { (p ∷ ps) → p , ps })
           (any-canonical? (λ v cv → d v cu cv) cvs ×-dec forth ds cus)

    back : {ws : List B} → All Can ws → Dec (All (λ v → Any (λ u → R u v) us) ws)
    back []          = yes []
    back (cv ∷ cvs)  =
      map′ (uncurry _∷_) (λ { (p ∷ ps) → p , ps }) (partner cv ×-dec back cvs)
      where
      partner : {v : B} → Can v → Dec (Any (λ u → R u v) us)
      partner {v} cv = go ds cus
        where
        go : {ws : List B} → All Decider ws → All Can ws → Dec (Any (λ u → R u v) ws)
        go []        []          = no λ ()
        go (d ∷ ds)  (cu ∷ cus)  =
          map′ [ here , there ]′ (λ { (here p) → inj₁ p ; (there i) → inj₂ i })
               (d v cu cv ⊎-dec go ds cus)

does-unique : {P : Type ℓ} (d d' : Dec P) → does d ≡ does d'
does-unique (yes _)  (yes _)  = refl
does-unique (yes p)  (no ¬p)  = ⊥-elim (¬p p)
does-unique (no ¬p)  (yes p)  = ⊥-elim (¬p p)
does-unique (no _)   (no _)   = refl

module Comparison {X : Type χ} (_≟_ : DecidableEquality X) where

  ≈ᶜ?    : (s t : CTerm X) → IsCanonical s → IsCanonical t → Dec (s ≈ᶜ t)
  ≈ᶜᴶ?   : (u v : CJand X) → IsCanonicalJ u → IsCanonicalJ v → Dec (u ≈ᶜᴶ v)
  ≈ᶜᴹ?   : (u v : CMand X) → IsCanonicalM u → IsCanonicalM v → Dec (u ≈ᶜᴹ v)
  ≈ᶜᴶs?  : (us : List (CJand X)) → All (λ u → ∀ v → IsCanonicalJ u → IsCanonicalJ v → Dec (u ≈ᶜᴶ v)) us
  ≈ᶜᴹs?  : (us : List (CMand X)) → All (λ u → ∀ v → IsCanonicalM u → IsCanonicalM v → Dec (u ≈ᶜᴹ v)) us
  ≈ᶜ?-join : (h : CJand X) (t : List (CJand X)) (h' : CJand X) (t' : List (CJand X))
           → IsCanonical (joinᶜ h t) → IsCanonical (joinᶜ h' t') → Dec (joinᶜ h t ≈ᶜ joinᶜ h' t')
  ≈ᶜ?-meet : (h : CMand X) (t : List (CMand X)) (h' : CMand X) (t' : List (CMand X))
           → IsCanonical (meetᶜ h t) → IsCanonical (meetᶜ h' t') → Dec (meetᶜ h t ≈ᶜ meetᶜ h' t')

  ≈ᶜ? (genᶜ x)     (genᶜ y)       _  _   = map′ gen≈ (λ { (gen≈ e) → e }) (x ≟ y)
  ≈ᶜ? (genᶜ _)     (joinᶜ _ _)    _  _   = no λ ()
  ≈ᶜ? (genᶜ _)     (meetᶜ _ _)    _  _   = no λ ()
  ≈ᶜ? (joinᶜ _ _)  (genᶜ _)       _  _   = no λ ()
  ≈ᶜ? (joinᶜ h t)  (joinᶜ h' t')  c  c'  = ≈ᶜ?-join h t h' t' c c'
  ≈ᶜ? (joinᶜ _ _)  (meetᶜ _ _)    _  _   = no λ ()
  ≈ᶜ? (meetᶜ _ _)  (genᶜ _)       _  _   = no λ ()
  ≈ᶜ? (meetᶜ _ _)  (joinᶜ _ _)    _  _   = no λ ()
  ≈ᶜ? (meetᶜ h t)  (meetᶜ h' t')  c  c'  = ≈ᶜ?-meet h t h' t' c c'

  ≈ᶜ?-join h t h' t' c@(cjoin _ cs _ _) c'@(cjoin _ cs' _ _) =
    map′ (uncurry (partners⇒≈ᶜ-join c c')) (λ { (join≈ p q) → ≈ᴾ⇒partners p q })
         (partners? (≈ᶜᴶ? h ∷ ≈ᶜᴶs? t) cs cs')

  ≈ᶜ?-meet h t h' t' c@(cmeet _ cs _ _) c'@(cmeet _ cs' _ _) =
    map′ (uncurry (partners⇒≈ᶜ-meet c c')) (λ { (meet≈ p q) → ≈ᴾ⇒partners p q })
         (partners? (≈ᶜᴹ? h ∷ ≈ᶜᴹs? t) cs cs')

  ≈ᶜᴶ? (jgen x)     (jgen y)       _           _            = map′ jgen≈ (λ { (jgen≈ e) → e }) (x ≟ y)
  ≈ᶜᴶ? (jgen _)     (jmeet _ _)    _           _            = no λ ()
  ≈ᶜᴶ? (jmeet _ _)  (jgen _)       _           _            = no λ ()
  ≈ᶜᴶ? (jmeet h t)  (jmeet h' t')  (cjmeet c)  (cjmeet c')  =
    map′ jmeet≈ (λ { (jmeet≈ e) → e }) (≈ᶜ?-meet h t h' t' c c')

  ≈ᶜᴹ? (mgen x)     (mgen y)       _           _            = map′ mgen≈ (λ { (mgen≈ e) → e }) (x ≟ y)
  ≈ᶜᴹ? (mgen _)     (mjoin _ _)    _           _            = no λ ()
  ≈ᶜᴹ? (mjoin _ _)  (mgen _)       _           _            = no λ ()
  ≈ᶜᴹ? (mjoin h t)  (mjoin h' t')  (cmjoin c)  (cmjoin c')  =
    map′ mjoin≈ (λ { (mjoin≈ e) → e }) (≈ᶜ?-join h t h' t' c c')

  ≈ᶜᴶs? []        = []
  ≈ᶜᴶs? (u ∷ us)  = ≈ᶜᴶ? u ∷ ≈ᶜᴶs? us
  ≈ᶜᴹs? []        = []
  ≈ᶜᴹs? (u ∷ us)  = ≈ᶜᴹ? u ∷ ≈ᶜᴹs? us
```

#### Deciding equality by canonical forms

Two lattice terms are equal in the free lattice exactly when their canonical forms
are related (`canonical-≈ᶜ⇔`{.AgdaFunction}): one direction is the soundness of
canonicalization followed by Theorem 1.17, the other the soundness of the
relation followed by the soundness of canonicalization.  So comparing canonical
forms decides equality in the free lattice (`_≈ᶠ?_`{.AgdaFunction}).  Its verdict
agrees with that of Whitman's procedure, `_≈ʷ?_`{.AgdaFunction} of
[Classical.Structures.Lattice.Free.Whitman][] (`≈ᶠ?-agrees`{.AgdaFunction}), as
any two decisions of the same proposition do (`does-unique`{.AgdaFunction}).
These close the module `Comparison`{.AgdaModule}.

```agda
  open Canonicalization _≟_  using ( canonical ; canonical-sound ; canonical-isCanonical )
  open Decision _≟_          using ( _≈ʷ?_ )

  canonical-≈ᶜ⇔ : {s t : LatTerm X} → s ≈ʷ t ⇔ canonical s ≈ᶜ canonical t
  canonical-≈ᶜ⇔ {s} {t} = mk⇔
    (λ e → ≈ʷ⇒≈ᶜ (canonical s) (canonical t) (canonical-isCanonical s) (canonical-isCanonical t)
                 (≈ʷ-trans (canonical-sound s) (≈ʷ-trans e (≈ʷ-sym (canonical-sound t)))))
    (λ r → ≈ʷ-trans (≈ʷ-sym (canonical-sound s)) (≈ʷ-trans (≈ᶜ⇒≈ʷ r) (canonical-sound t)))

  infix 4 _≈ᶠ?_

  _≈ᶠ?_ : (s t : LatTerm X) → Dec (s ≈ʷ t)
  s ≈ᶠ? t = map′ (Equivalence.from canonical-≈ᶜ⇔) (Equivalence.to canonical-≈ᶜ⇔)
                 (≈ᶜ? (canonical s) (canonical t) (canonical-isCanonical s) (canonical-isCanonical t))

  ≈ᶠ?-agrees : (s t : LatTerm X) → does (s ≈ᶠ? t) ≡ does (s ≈ʷ? t)
  ≈ᶠ?-agrees s t = does-unique (s ≈ᶠ? t) (s ≈ʷ? t)
```
