---
layout: default
file: "src/Classical/Structures/Lattice/Free/Canonical/Algorithm.lagda.md"
title: "Classical.Structures.Lattice.Free.Canonical.Algorithm module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Computing canonical forms

This is the [Classical.Structures.Lattice.Free.Canonical.Algorithm][] module of the [Agda Universal Algebra Library][].

This module computes the canonical form of a lattice term, bottom up, and proves
that the result represents the same element of the free lattice and is canonical
in the sense of `IsCanonical`{.AgdaDatatype} of
[Classical.Structures.Lattice.Free.Canonical.Basic][].  The procedure is the one
Theorem 1.18 of [Freese, Ježek, and Nation (1995)][] suggests, which the book
describes as repeated use of the conditions of the theorem: to put the join of two
canonical terms into canonical form, collect their joinands and repeat the
following two steps until neither applies:

1.  delete every joinand that lies below another joinand, keeping one of any two
    equal joinands, which leaves an antichain;
2.  if some joinand is a meet `tᵢ = ⋀ⱼ tᵢⱼ` with a meetand `tᵢⱼ` below the whole
    join, replace `tᵢ` by the joinands of `tᵢⱼ`.

The first step establishes condition 3 of Theorem 1.18 and the absence of the
second establishes condition 4; conditions 1 and 2 hold throughout, since every
joinand ever in the list is a generator, a meet, or a joinand of a meetand of a
canonical meet.  Each replacement strictly lowers the sum of the ranks of the
joinands, since `tᵢⱼ` is a proper part of `tᵢ`, and deletion does not raise it,
so the loop is a well-founded recursion on that sum; it needs neither a
termination pragma nor fuel.  The canonical form of a meet is the dual of the
canonical form of the join of the duals.

The book's program for the same task (Chapter XI, Section 8, Listing 11.17) is
organized differently: it compares every meetand with the original join, which
the replacements do not change, so it can descend through the joinands once,
replacing as it goes, and keep the maximal elements at the end.  The loop here
re-prunes after each replacement instead, which costs comparisons but makes each
step an instance of one of the two conditions it establishes.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Canonical.Algorithm where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ )
open import Data.List.Relation.Binary.Sublist.Propositional
                                                   using ( _⊆_ ; ⊆-refl ; ⊆-trans )
open import Data.List.Relation.Binary.Sublist.Propositional.Properties
                                                   using ( All-resp-⊆ ; Any-resp-⊆ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there ; any? )
open import Data.Nat.Base                          using ( _+_ ; _<_ ; _≤_ ; s≤s ; z≤n )
open import Data.Nat.Induction                     using ( <-wellFounded )
open import Data.Nat.Properties                    using ( ≤-trans ; <-≤-trans ; m≤m+n
                                                         ; m≤n+m ; +-assoc ; +-mono-≤
                                                         ; +-monoˡ-≤ ; +-monoʳ-< ; ≤-refl )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Sum.Base                          using ( _⊎_ ; [_,_]′ )
open import Function                               using ( _∘_ )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong
                                                         ; cong₂ ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; map′ ; _×-dec_
                                                         ; ¬? )

import Data.List.Relation.Binary.Sublist.Propositional  as Sublist
import Data.List.Relation.Unary.All                     as All
import Data.List.Relation.Unary.All.Properties          as All
import Data.List.Relation.Unary.Any                     as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand
         ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁ᴶ ; crankJ ; crankM ; crankΣJ ; crankΣM
         ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∨̇-cong ; ∧̇-cong ; ∨̇-assoc
         ; ⋁ᴶ-upper ; ⋁ᴶ-least ; ⋀ᴹ-lower ; ⋁ᴶ-dom ; _≰ʷ_ ; AntichainJ ; Cond4J
         ; IsCanonical ; cgen ; cjoin ; IsCanonicalJ ; cjmeet ; cmeet
         ; JList ; asListJ ; ⋁ᴶL ; joinandsOf ; joinandsOfM ; joinandsOf-sound
         ; joinandsOfM-sound ; joinandsOf-canonical ; joinandsOfM-canonical
         ; joinandsOfM-crank ; dualᶜ ; ⌊dualᶜ⌋ ; dualᶜ-canonical )
open import Classical.Structures.Lattice.Free.Duality  using ( dual ; dual-involutive ; dual-cong )
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Classical.Structures.Lattice.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ∨≤-inv ; ≤ʷ-refl ; ≤ʷ-trans ; ∨̇-upperˡ ; ∨̇-upperʳ
         ; module Decision )

private variable
  χ : Level
  X : Type χ
  mh : CMand X
  mt : List (CMand X)
```
-->

#### Rank arithmetic

The termination argument consumes three facts about the rank sum
`crankΣJ`{.AgdaFunction} of [Classical.Structures.Lattice.Free.Canonical.Basic][]:
a member's rank is at most the sum over a list containing it
(`∈-≤-crankΣM`{.AgdaFunction}), the sum distributes over appending
(`crankΣJ-++`{.AgdaFunction}), and it is monotone along sublists
(`⊆-crankΣJ`{.AgdaFunction}).

```agda
∈-≤-crankΣM : {m : CMand X} {ms : List (CMand X)} → m ∈ ms → crankM m ≤ crankΣM ms
∈-≤-crankΣM (here refl)  = m≤m+n _ _
∈-≤-crankΣM (there m∈)   = ≤-trans (∈-≤-crankΣM m∈) (m≤n+m _ _)

crankΣJ-++ : (as bs : List (CJand X)) → crankΣJ (as ++ bs) ≡ crankΣJ as + crankΣJ bs
crankΣJ-++ []        bs = refl
crankΣJ-++ (a ∷ as)  bs =
  trans (cong (crankJ a +_) (crankΣJ-++ as bs)) (sym (+-assoc (crankJ a) (crankΣJ as) _))

⊆-crankΣJ : {as bs : List (CJand X)} → as ⊆ bs → crankΣJ as ≤ crankΣJ bs
⊆-crankΣJ Sublist.[]             = z≤n
⊆-crankΣJ (refl Sublist.∷ p)     = +-mono-≤ ≤-refl (⊆-crankΣJ p)
⊆-crankΣJ (_ Sublist.∷ʳ p)       = ≤-trans (⊆-crankΣJ p) (m≤n+m _ _)
```

#### Lists of joinands

A list of joinands is a `JList`{.AgdaFunction}, a first joinand and a list of the
rest.  Appending a list to it (`_++ᴶ_`{.AgdaFunction}) adds the ranks
(`crankΣJ-++ᴶ`{.AgdaFunction}), its members are those of the two parts
(`∈-++ᴶ⁻`{.AgdaFunction}, `∈-++ᴶ⁺ˡ`{.AgdaFunction}, `∈-++ᴶ⁺ʳ`{.AgdaFunction}),
and its join lies above the join of the first part
(`⋁ᴶL-++ᴶ-upper`{.AgdaFunction}).  The join of a concatenation of two lists of
joinands is the join of the two joins (`⋁ᴶ-++`{.AgdaFunction}), and every member
of a list lies below some member, namely itself (`∈⇒≤-Any`{.AgdaFunction}).
`AllPairs`{.AgdaDatatype} passes to sublists (`AllPairs-resp-⊆`{.AgdaFunction}),
as `All`{.AgdaDatatype} does by the standard library's
`All-resp-⊆`{.AgdaFunction}.

```agda
infixr 5 _++ᴶ_

_++ᴶ_ : JList X → List (CJand X) → JList X
(h , t) ++ᴶ u = h , t ++ u

crankΣJ-++ᴶ : (P : JList X) (u : List (CJand X))
            → crankΣJ (asListJ (P ++ᴶ u)) ≡ crankΣJ (asListJ P) + crankΣJ u
crankΣJ-++ᴶ (h , t) u = crankΣJ-++ (h ∷ t) u

∈-++ᴶ⁻ : (P : JList X) {u : List (CJand X)} {a : CJand X}
       → a ∈ asListJ (P ++ᴶ u) → (a ∈ asListJ P) ⊎ (a ∈ u)
∈-++ᴶ⁻ (h , t) = ∈-++⁻ (h ∷ t)

∈-++ᴶ⁺ˡ : {P : JList X} {u : List (CJand X)} {a : CJand X}
        → a ∈ asListJ P → a ∈ asListJ (P ++ᴶ u)
∈-++ᴶ⁺ˡ = ∈-++⁺ˡ

∈-++ᴶ⁺ʳ : (P : JList X) {u : List (CJand X)} {a : CJand X} → a ∈ u → a ∈ asListJ (P ++ᴶ u)
∈-++ᴶ⁺ʳ (h , t) = ∈-++⁺ʳ (h ∷ t)

⋁ᴶL-++ᴶ-upper : (P : JList X) {u : List (CJand X)} → ⋁ᴶL P ≤ʷ ⋁ᴶL (P ++ᴶ u)
⋁ᴶL-++ᴶ-upper P = ⋁ᴶ-least λ a∈ → ⋁ᴶ-upper (∈-++ᴶ⁺ˡ {P = P} a∈)

⋁ᴶ-++ : (h : CJand X) (t : List (CJand X)) (u : CJand X) (us : List (CJand X))
      → ⋁ᴶ h (t ++ u ∷ us) ≈ʷ ⋁ᴶ h t ∨̇ ⋁ᴶ u us
⋁ᴶ-++ h []        u us = ≈ʷ-refl
⋁ᴶ-++ h (a ∷ as)  u us = ≈ʷ-trans (∨̇-cong ≈ʷ-refl (⋁ᴶ-++ a as u us)) (≈ʷ-sym ∨̇-assoc)

∈⇒≤-Any : {a : CJand X} {as : List (CJand X)} → a ∈ as → Any (λ b → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ) as
∈⇒≤-Any = Any.map λ { refl → ≤ʷ-refl }

AllPairs-resp-⊆ : {A : Type χ} {R : A → A → Type χ} {xs ys : List A}
                → xs ⊆ ys → AllPairs R ys → AllPairs R xs
AllPairs-resp-⊆ Sublist.[]           []         = []
AllPairs-resp-⊆ (refl Sublist.∷ p)   (r ∷ rs)   = All-resp-⊆ p r ∷ AllPairs-resp-⊆ p rs
AllPairs-resp-⊆ (_ Sublist.∷ʳ p)     (_ ∷ rs)   = AllPairs-resp-⊆ p rs
```

#### Reducible joinands and the replacement step

A joinand is *reducible* in a join `z` if it is a meet one of whose meetands lies
below `z` (`Reducible`{.AgdaDatatype}).  Condition 4 of Theorem 1.18 says exactly
that no joinand of a canonical join is reducible in it
(`irreducible→Cond4J`{.AgdaFunction}).  The replacement step `splice`{.AgdaFunction}
takes a list of joinands and a reducible member of it, located by a proof of
`Any`{.AgdaDatatype}, and replaces that member by the joinands of its meetand
below `z`, the first such meetand in the list.

```agda
data Reducible {X : Type χ} (z : LatTerm X) : CJand X → Type χ where
  reducible : Any (λ m → ⌊ m ⌋ᴹ ≤ʷ z) (mh ∷ mt) → Reducible z (jmeet mh mt)

irreducible→Cond4J : {h : CJand X} {t : List (CJand X)}
                   → ¬ Any (Reducible (⋁ᴶ h t)) (h ∷ t) → Cond4J h t
irreducible→Cond4J ¬r jm∈ m∈ m≤ = ¬r (lose jm∈ (reducible (lose m∈ m≤)))

splice : {z : LatTerm X} {h : CJand X} {t : List (CJand X)} → Any (Reducible z) (h ∷ t) → JList X
splice {t = t}  (here (reducible r))  = joinandsOfM (proj₁ (find r)) ++ᴶ t
splice {t = []}      (there ())
splice {h = h} {_ ∷ _} (there i)     = h , asListJ (splice i)
```

The replacement preserves the join when the meetand lies below that very join.
In one direction every new joinand lies below the meetand, which lies below the
join (`splice-≤`{.AgdaFunction}); in the other, the replaced meet lies below its
meetand, which is the join of the new joinands (`splice-≥`{.AgdaFunction}).
Together these are `splice-sound`{.AgdaFunction}.  The replacement strictly
lowers the rank sum (`splice-μ`{.AgdaFunction}), because the joinands of a
meetand have total rank at most its rank, which is less than the rank of the
meet.  It also preserves the canonicity of the joinands
(`splice-canonical`{.AgdaFunction}), since a meetand of a canonical meet is
canonical, and so are its joinands.

```agda
splice-≤ : {z : LatTerm X} {h : CJand X} {t : List (CJand X)} (i : Any (Reducible z) (h ∷ t))
         → ⋁ᴶ h t ≤ʷ z → ⋁ᴶL (splice i) ≤ʷ z
splice-≤ (here (reducible r)) p =
  let (m , _ , m≤z) = find r
      P = joinandsOfM m
  in ⋁ᴶ-least λ a∈ → [ (λ a∈P → ≤ʷ-trans (⋁ᴶ-upper a∈P) (subst (_≤ʷ _) (sym (joinandsOfM-sound m)) m≤z))
                     , (λ a∈t → ≤ʷ-trans (⋁ᴶ-upper (there a∈t)) p)
                     ]′ (∈-++ᴶ⁻ P a∈)
splice-≤ {t = []} (there ()) _
splice-≤ {t = _ ∷ _} (there i) p = ∨≤ (proj₁ (∨≤-inv p)) (splice-≤ i (proj₂ (∨≤-inv p)))

splice-≥ : {z : LatTerm X} {h : CJand X} {t : List (CJand X)} (i : Any (Reducible z) (h ∷ t))
         → ⋁ᴶ h t ≤ʷ ⋁ᴶL (splice i)
splice-≥ {t = t} (here (reducible r)) =
  let (m , m∈ , _) = find r
      P = joinandsOfM m
  in ⋁ᴶ-least λ { (here refl)  → ≤ʷ-trans (⋀ᴹ-lower m∈)
                                   (≤ʷ-trans (subst (⌊ m ⌋ᴹ ≤ʷ_) (sym (joinandsOfM-sound m)) ≤ʷ-refl)
                                             (⋁ᴶL-++ᴶ-upper P))
                ; (there a∈t)  → ⋁ᴶ-upper (∈-++ᴶ⁺ʳ P a∈t) }
splice-≥ {t = []} (there ())
splice-≥ {t = _ ∷ _} (there i) = ∨≤ ∨̇-upperˡ (≤ʷ-trans (splice-≥ i) ∨̇-upperʳ)

splice-sound : {h : CJand X} {t : List (CJand X)} (i : Any (Reducible (⋁ᴶ h t)) (h ∷ t))
             → ⋁ᴶL (splice i) ≈ʷ ⋁ᴶ h t
splice-sound i = splice-≤ i ≤ʷ-refl , splice-≥ i

splice-μ : {z : LatTerm X} {h : CJand X} {t : List (CJand X)} (i : Any (Reducible z) (h ∷ t))
         → crankΣJ (asListJ (splice i)) < crankΣJ (h ∷ t)
splice-μ {t = t} (here (reducible {mh = mh} {mt} r)) =
  let (m , m∈ , _) = find r in
  subst (_< crankΣJ (jmeet mh mt ∷ t)) (sym (crankΣJ-++ᴶ (joinandsOfM m) t))
        (s≤s (+-monoˡ-≤ (crankΣJ t) (≤-trans (joinandsOfM-crank m) (∈-≤-crankΣM m∈))))
splice-μ {t = []} (there ())
splice-μ {h = h} {_ ∷ _} (there i) = +-monoʳ-< (crankJ h) (splice-μ i)

splice-canonical : {z : LatTerm X} {h : CJand X} {t : List (CJand X)} (i : Any (Reducible z) (h ∷ t))
                 → All IsCanonicalJ (h ∷ t) → All IsCanonicalJ (asListJ (splice i))
splice-canonical (here (reducible r)) (cjmeet (cmeet _ cs _ _) ∷ ct) =
  All.++⁺ (joinandsOfM-canonical (All.lookup cs (proj₁ (proj₂ (find r))))) ct
splice-canonical {t = []} (there ()) _
splice-canonical {t = _ ∷ _} (there i) (c ∷ cs) = c ∷ splice-canonical i cs
```

#### The result of the loop

The loop returns its output together with the facts the rest of the development
needs about it, rather than leaving them to be proved afterwards by unfolding a
well-founded recursion.  `ReducedJoin h t`{.AgdaRecord} is a list of joinands whose
join equals `⋁ᴶ h t`{.AgdaFunction}, which is an antichain and satisfies
condition 4, and whose members are canonical when those of `h ∷ t` are.  A
`ReducedJoin`{.AgdaRecord} of a list that represents the same join, and whose
canonicity follows, is one of the original list (`ReducedJoin-pre`{.AgdaFunction}).

```agda
record ReducedJoin {X : Type χ} (h : CJand X) (t : List (CJand X)) : Type χ where
  field
    head         : CJand X
    tail         : List (CJand X)
    sound        : ⋁ᴶ head tail ≈ʷ ⋁ᴶ h t
    antichain    : AntichainJ (head ∷ tail)
    cond4        : Cond4J head tail
    isCanonical  : All IsCanonicalJ (h ∷ t) → All IsCanonicalJ (head ∷ tail)

ReducedJoin-pre : {h h' : CJand X} {t t' : List (CJand X)}
                → ⋁ᴶ h' t' ≈ʷ ⋁ᴶ h t → (All IsCanonicalJ (h ∷ t) → All IsCanonicalJ (h' ∷ t'))
                → ReducedJoin h' t' → ReducedJoin h t
ReducedJoin-pre e c R = record
  { head         = R.head
  ; tail         = R.tail
  ; sound        = ≈ʷ-trans R.sound e
  ; antichain    = R.antichain
  ; cond4        = R.cond4
  ; isCanonical  = R.isCanonical ∘ c
  }
  where module R = ReducedJoin R
```

#### The canonicalization procedure

The module `Canonicalization`{.AgdaModule} takes the decision procedure for equality
of generators as its parameter, in the way `Decision`{.AgdaModule} of
[Classical.Structures.Lattice.Free.Whitman][] does, since every comparison of
joinands runs through `_≤ʷ?_`{.AgdaFunction}.

**Deleting the joinands below a joinand**.  `removeBelowᴶ j as`{.AgdaFunction}
keeps the members of `as` that do not lie below `j`.  It yields a sublist
(`removeBelowᴶ-⊆`{.AgdaFunction}) of members not below `j`
(`removeBelowᴶ-≰`{.AgdaFunction}), and keeps every member not below `j`
(`∈-removeBelowᴶ⁺`{.AgdaFunction}).  Each lemma decides the same comparisons the
function does, so its goal reduces along with the function.

```agda
module Canonicalization {X : Type χ} (_≟_ : DecidableEquality X) where
  open Decision _≟_ using ( _≤ʷ?_ )

  removeBelowᴶ : CJand X → List (CJand X) → List (CJand X)
  removeBelowᴶ j []        = []
  removeBelowᴶ j (a ∷ as)  with ⌊ a ⌋ᴶ ≤ʷ? ⌊ j ⌋ᴶ
  ... | yes _ = removeBelowᴶ j as
  ... | no  _ = a ∷ removeBelowᴶ j as

  removeBelowᴶ-⊆ : (j : CJand X) (as : List (CJand X)) → removeBelowᴶ j as ⊆ as
  removeBelowᴶ-⊆ j []        = Sublist.[]
  removeBelowᴶ-⊆ j (a ∷ as)  with ⌊ a ⌋ᴶ ≤ʷ? ⌊ j ⌋ᴶ
  ... | yes _ = a Sublist.∷ʳ removeBelowᴶ-⊆ j as
  ... | no  _ = refl Sublist.∷ removeBelowᴶ-⊆ j as

  removeBelowᴶ-≰ : (j : CJand X) (as : List (CJand X))
                 → All (λ a → ⌊ a ⌋ᴶ ≰ʷ ⌊ j ⌋ᴶ) (removeBelowᴶ j as)
  removeBelowᴶ-≰ j []        = []
  removeBelowᴶ-≰ j (a ∷ as)  with ⌊ a ⌋ᴶ ≤ʷ? ⌊ j ⌋ᴶ
  ... | yes _   = removeBelowᴶ-≰ j as
  ... | no  a≰  = a≰ ∷ removeBelowᴶ-≰ j as

  ∈-removeBelowᴶ⁺ : (j : CJand X) {a : CJand X} {as : List (CJand X)}
                  → ⌊ a ⌋ᴶ ≰ʷ ⌊ j ⌋ᴶ → a ∈ as → a ∈ removeBelowᴶ j as
  ∈-removeBelowᴶ⁺ j {as = []}      _  ()
  ∈-removeBelowᴶ⁺ j {as = b ∷ bs} a≰ a∈ with ⌊ b ⌋ᴶ ≤ʷ? ⌊ j ⌋ᴶ | a∈
  ... | yes b≤  | here refl  = ⊥-elim (a≰ b≤)
  ... | yes _   | there a∈'  = ∈-removeBelowᴶ⁺ j a≰ a∈'
  ... | no  _   | here refl  = here refl
  ... | no  _   | there a∈'  = there (∈-removeBelowᴶ⁺ j a≰ a∈')
```

**Inserting a joinand into an antichain**.  `insertᴶ j P`{.AgdaFunction} adds the
joinand `j` to the list `P`: if `j` lies strictly below some member of `P` it adds
nothing, and otherwise it puts `j` in front of the members of `P` that do not lie
below it.  The decision is an argument of the helper `insertᴶ-by`{.AgdaFunction},
so that the lemmas can case on it.  The result is a sublist of `j ∷ P`
(`insertᴶ-⊆`{.AgdaFunction}); every member of `j ∷ P` lies below some member of
the result (`insertᴶ-dom`{.AgdaFunction}); and if `P` is an antichain, so is the
result (`insertᴶ-antichain`{.AgdaFunction}): a kept `j` is not below the members
kept with it, since they are not below `j`, and `j` lies strictly below none of
them.

```agda
  StrictlyBelowSome : CJand X → List (CJand X) → Type χ
  StrictlyBelowSome j = Any λ a → (⌊ j ⌋ᴶ ≤ʷ ⌊ a ⌋ᴶ) × (⌊ a ⌋ᴶ ≰ʷ ⌊ j ⌋ᴶ)

  strictlyBelowSome? : (j : CJand X) (as : List (CJand X)) → Dec (StrictlyBelowSome j as)
  strictlyBelowSome? j = any? λ a → ⌊ j ⌋ᴶ ≤ʷ? ⌊ a ⌋ᴶ ×-dec ¬? (⌊ a ⌋ᴶ ≤ʷ? ⌊ j ⌋ᴶ)

  insertᴶ-by : (j h : CJand X) (t : List (CJand X)) → Dec (StrictlyBelowSome j (h ∷ t)) → JList X
  insertᴶ-by j h t (yes _)  = h , t
  insertᴶ-by j h t (no _)   = j , removeBelowᴶ j (h ∷ t)

  insertᴶ : CJand X → JList X → JList X
  insertᴶ j (h , t) = insertᴶ-by j h t (strictlyBelowSome? j (h ∷ t))

  insertᴶ-by-⊆ : (j h : CJand X) (t : List (CJand X)) (d : Dec (StrictlyBelowSome j (h ∷ t)))
               → asListJ (insertᴶ-by j h t d) ⊆ j ∷ h ∷ t
  insertᴶ-by-⊆ j h t (yes _)  = j Sublist.∷ʳ ⊆-refl
  insertᴶ-by-⊆ j h t (no _)   = refl Sublist.∷ removeBelowᴶ-⊆ j (h ∷ t)

  insertᴶ-by-dom : (j h : CJand X) (t : List (CJand X)) (d : Dec (StrictlyBelowSome j (h ∷ t)))
                 → {a : CJand X} → a ∈ (j ∷ h ∷ t)
                 → Any (λ b → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ) (asListJ (insertᴶ-by j h t d))
  insertᴶ-by-dom j h t (yes s)  (here refl)  = Any.map proj₁ s
  insertᴶ-by-dom j h t (yes _)  (there a∈)   = ∈⇒≤-Any a∈
  insertᴶ-by-dom j h t (no _)   (here refl)  = here ≤ʷ-refl
  insertᴶ-by-dom j h t (no _)   {a} (there a∈) with ⌊ a ⌋ᴶ ≤ʷ? ⌊ j ⌋ᴶ
  ... | yes a≤j  = here a≤j
  ... | no  a≰j  = there (∈⇒≤-Any (∈-removeBelowᴶ⁺ j a≰j a∈))

  insertᴶ-by-antichain : (j h : CJand X) (t : List (CJand X)) (d : Dec (StrictlyBelowSome j (h ∷ t)))
                       → AntichainJ (h ∷ t) → AntichainJ (asListJ (insertᴶ-by j h t d))
  insertᴶ-by-antichain j h t (yes _)   ac = ac
  insertᴶ-by-antichain j h t (no ¬s)   ac =
    tabulate (λ {a} a∈ → let a≰j = All.lookup (removeBelowᴶ-≰ j (h ∷ t)) a∈ in
                         (λ j≤a → ¬s (lose (Any-resp-⊆ (removeBelowᴶ-⊆ j (h ∷ t)) a∈) (j≤a , a≰j)))
                         , a≰j)
    ∷ AllPairs-resp-⊆ (removeBelowᴶ-⊆ j (h ∷ t)) ac

  insertᴶ-⊆ : (j : CJand X) (P : JList X) → asListJ (insertᴶ j P) ⊆ j ∷ asListJ P
  insertᴶ-⊆ j (h , t) = insertᴶ-by-⊆ j h t (strictlyBelowSome? j (h ∷ t))

  insertᴶ-dom : (j : CJand X) (P : JList X) {a : CJand X} → a ∈ (j ∷ asListJ P)
              → Any (λ b → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ) (asListJ (insertᴶ j P))
  insertᴶ-dom j (h , t) = insertᴶ-by-dom j h t (strictlyBelowSome? j (h ∷ t))

  insertᴶ-antichain : (j : CJand X) (P : JList X) → AntichainJ (asListJ P)
                    → AntichainJ (asListJ (insertᴶ j P))
  insertᴶ-antichain j (h , t) = insertᴶ-by-antichain j h t (strictlyBelowSome? j (h ∷ t))
```

**Pruning**.  `pruneᴶ h t`{.AgdaFunction} inserts the joinands of `h ∷ t` one at a
time, from the last to the first, so that of two equal joinands the first is the
one kept.  The result is a sublist of `h ∷ t` (`pruneᴶ-⊆`{.AgdaFunction}), so its
rank sum is no larger (`pruneᴶ-μ`{.AgdaFunction}) and its members are canonical if
those of `h ∷ t` are (`pruneᴶ-canonical`{.AgdaFunction}); every member of `h ∷ t`
lies below one of its members (`pruneᴶ-dom`{.AgdaFunction}), so the two lists have
the same join (`pruneᴶ-sound`{.AgdaFunction}, by domination in both directions);
and it is an antichain (`pruneᴶ-antichain`{.AgdaFunction}).

```agda
  pruneᴶ : CJand X → List (CJand X) → JList X
  pruneᴶ h []        = h , []
  pruneᴶ h (a ∷ as)  = insertᴶ h (pruneᴶ a as)

  pruneᴶ-⊆ : (h : CJand X) (t : List (CJand X)) → asListJ (pruneᴶ h t) ⊆ h ∷ t
  pruneᴶ-⊆ h []        = ⊆-refl
  pruneᴶ-⊆ h (a ∷ as)  = ⊆-trans (insertᴶ-⊆ h (pruneᴶ a as)) (refl Sublist.∷ pruneᴶ-⊆ a as)

  pruneᴶ-dom : (h : CJand X) (t : List (CJand X)) {a : CJand X} → a ∈ (h ∷ t)
             → Any (λ b → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ) (asListJ (pruneᴶ h t))
  pruneᴶ-dom h []        a∈          = ∈⇒≤-Any a∈
  pruneᴶ-dom h (a ∷ as)  (here refl) = insertᴶ-dom h (pruneᴶ a as) (here refl)
  pruneᴶ-dom h (a ∷ as)  (there a∈)  =
    let (b , b∈ , a≤b) = find (pruneᴶ-dom a as a∈) in
    Any.map (≤ʷ-trans a≤b) (insertᴶ-dom h (pruneᴶ a as) (there b∈))

  pruneᴶ-antichain : (h : CJand X) (t : List (CJand X)) → AntichainJ (asListJ (pruneᴶ h t))
  pruneᴶ-antichain h []        = [] ∷ []
  pruneᴶ-antichain h (a ∷ as)  = insertᴶ-antichain h (pruneᴶ a as) (pruneᴶ-antichain a as)

  pruneᴶ-sound : (h : CJand X) (t : List (CJand X)) → ⋁ᴶL (pruneᴶ h t) ≈ʷ ⋁ᴶ h t
  pruneᴶ-sound h t =
    ⋁ᴶ-dom (λ a∈ → ∈⇒≤-Any (Any-resp-⊆ (pruneᴶ-⊆ h t) a∈)) , ⋁ᴶ-dom (pruneᴶ-dom h t)

  pruneᴶ-μ : (h : CJand X) (t : List (CJand X)) → crankΣJ (asListJ (pruneᴶ h t)) ≤ crankΣJ (h ∷ t)
  pruneᴶ-μ h t = ⊆-crankΣJ (pruneᴶ-⊆ h t)

  pruneᴶ-canonical : (h : CJand X) (t : List (CJand X))
                   → All IsCanonicalJ (h ∷ t) → All IsCanonicalJ (asListJ (pruneᴶ h t))
  pruneᴶ-canonical h t = All-resp-⊆ (pruneᴶ-⊆ h t)
```

**The loop**.  `reduceᴶ h t`{.AgdaFunction} prunes `h ∷ t` and looks for a
reducible joinand of the pruned list (`reducibles?`{.AgdaFunction}).  If there is
none, the pruned list is the answer: it is an antichain, condition 4 holds by
`irreducible→Cond4J`{.AgdaFunction}, and the join and the canonicity of the
members are those of pruning.  If there is one, the loop replaces it and starts
over on the result, whose rank sum is smaller than that of the pruned list, hence
than that of `h ∷ t`; the accessibility proof of that sum under `_<_`, from the
standard library's `<-wellFounded`{.AgdaFunction}, is the termination measure.

```agda
  reducible? : (z : LatTerm X) (a : CJand X) → Dec (Reducible z a)
  reducible? z (jgen _)       = no λ ()
  reducible? z (jmeet mh mt)  =
    map′ reducible (λ { (reducible r) → r }) (any? (λ m → ⌊ m ⌋ᴹ ≤ʷ? z) (mh ∷ mt))

  reducibles? : (P : JList X) → Dec (Any (Reducible (⋁ᴶL P)) (asListJ P))
  reducibles? P = any? (reducible? (⋁ᴶL P)) (asListJ P)

  reduceᴶ : (h : CJand X) (t : List (CJand X)) → Acc _<_ (crankΣJ (h ∷ t)) → ReducedJoin h t
  reduceᴶ h t (acc rs) with reducibles? (pruneᴶ h t)
  ... | no ¬r = record
    { head         = proj₁ (pruneᴶ h t)
    ; tail         = proj₂ (pruneᴶ h t)
    ; sound        = pruneᴶ-sound h t
    ; antichain    = pruneᴶ-antichain h t
    ; cond4        = irreducible→Cond4J ¬r
    ; isCanonical  = pruneᴶ-canonical h t
    }
  ... | yes r =
    ReducedJoin-pre (≈ʷ-trans (splice-sound r) (pruneᴶ-sound h t))
                    (splice-canonical r ∘ pruneᴶ-canonical h t)
                    (reduceᴶ (proj₁ (splice r)) (proj₂ (splice r))
                             (rs (<-≤-trans (splice-μ r) (pruneᴶ-μ h t))))
```

**The join of two canonical terms**.  `s ∨ᶜ t`{.AgdaFunction} runs the loop on the
joinands of `s` followed by those of `t` (`joinands∨`{.AgdaFunction}) and turns the
result into a canonical term with `collapseᴶ`{.AgdaFunction}, which makes a single
joinand the term it is (a generator, or a meet) and a longer list a join.  The
join of the collected joinands is the join of the two terms
(`joinands∨-sound`{.AgdaFunction}), so the result represents `⌊ s ⌋ ∨̇ ⌊ t ⌋`
(`∨ᶜ-sound`{.AgdaFunction}), and when `s` and `t` are canonical the collected
joinands are canonical, whence the result is (`∨ᶜ-canonical`{.AgdaFunction}).

```agda
  joinands∨ : CTerm X → CTerm X → JList X
  joinands∨ s t = joinandsOf s ++ᴶ asListJ (joinandsOf t)

  reduce∨ : (s t : CTerm X) → ReducedJoin (proj₁ (joinands∨ s t)) (proj₂ (joinands∨ s t))
  reduce∨ s t = reduceᴶ _ _ (<-wellFounded _)

  collapseᴶ : CJand X → List (CJand X) → CTerm X
  collapseᴶ (jgen x)     []        = genᶜ x
  collapseᴶ (jmeet h t)  []        = meetᶜ h t
  collapseᴶ h@(jgen _)   (a ∷ as)  = joinᶜ h (a ∷ as)
  collapseᴶ h@(jmeet _ _) (a ∷ as) = joinᶜ h (a ∷ as)

  infixl 7 _∨ᶜ_ _∧ᶜ_

  _∨ᶜ_ : CTerm X → CTerm X → CTerm X
  s ∨ᶜ t = collapseᴶ (ReducedJoin.head (reduce∨ s t)) (ReducedJoin.tail (reduce∨ s t))
```

`collapseᴶ`{.AgdaFunction} changes the representation and not the term
represented (`⌊collapseᴶ⌋`{.AgdaFunction}), and a canonical antichain of joinands
satisfying condition 4 collapses to a canonical term
(`collapseᴶ-canonical`{.AgdaFunction}): a single canonical joinand is a canonical
term, and a longer list meets the four conditions of `cjoin`{.AgdaInductiveConstructor}.

```agda
  ⌊collapseᴶ⌋ : (h : CJand X) (t : List (CJand X)) → ⌊ collapseᴶ h t ⌋ ≡ ⋁ᴶ h t
  ⌊collapseᴶ⌋ (jgen x)     []       = refl
  ⌊collapseᴶ⌋ (jmeet h t)  []       = refl
  ⌊collapseᴶ⌋ (jgen x)     (_ ∷ _)  = refl
  ⌊collapseᴶ⌋ (jmeet h t)  (_ ∷ _)  = refl

  collapseᴶ-canonical : {h : CJand X} {t : List (CJand X)}
                      → All IsCanonicalJ (h ∷ t) → AntichainJ (h ∷ t) → Cond4J h t
                      → IsCanonical (collapseᴶ h t)
  collapseᴶ-canonical {jgen x}     {[]}     _                 _   _   = cgen
  collapseᴶ-canonical {jmeet h t}  {[]}     (cjmeet ic ∷ [])  _   _   = ic
  collapseᴶ-canonical {jgen x}     {_ ∷ _}  cs                ac  c4  = cjoin (λ ()) cs ac c4
  collapseᴶ-canonical {jmeet h t}  {_ ∷ _}  cs                ac  c4  = cjoin (λ ()) cs ac c4

  joinands∨-sound : (s t : CTerm X) → ⋁ᴶL (joinands∨ s t) ≈ʷ ⌊ s ⌋ ∨̇ ⌊ t ⌋
  joinands∨-sound s t =
    ≈ʷ-trans (⋁ᴶ-++ hs ts ht tt)
             (subst₂ (λ a b → ⋁ᴶ hs ts ∨̇ ⋁ᴶ ht tt ≈ʷ a ∨̇ b)
                     (joinandsOf-sound s) (joinandsOf-sound t) ≈ʷ-refl)
    where
    hs = proj₁ (joinandsOf s)
    ts = proj₂ (joinandsOf s)
    ht = proj₁ (joinandsOf t)
    tt = proj₂ (joinandsOf t)

  joinands∨-canonical : {s t : CTerm X} → IsCanonical s → IsCanonical t
                      → All IsCanonicalJ (asListJ (joinands∨ s t))
  joinands∨-canonical cs ct with joinandsOf-canonical cs
  ... | c ∷ cs' = c ∷ All.++⁺ cs' (joinandsOf-canonical ct)

  ∨ᶜ-sound : (s t : CTerm X) → ⌊ s ∨ᶜ t ⌋ ≈ʷ ⌊ s ⌋ ∨̇ ⌊ t ⌋
  ∨ᶜ-sound s t = subst (_≈ʷ _) (sym (⌊collapseᴶ⌋ R.head R.tail))
                       (≈ʷ-trans R.sound (joinands∨-sound s t))
    where module R = ReducedJoin (reduce∨ s t)

  ∨ᶜ-canonical : {s t : CTerm X} → IsCanonical s → IsCanonical t → IsCanonical (s ∨ᶜ t)
  ∨ᶜ-canonical {s} {t} cs ct =
    collapseᴶ-canonical (R.isCanonical (joinands∨-canonical cs ct)) R.antichain R.cond4
    where module R = ReducedJoin (reduce∨ s t)
```

**The meet of two canonical terms**.  The canonical form of a meet is computed by
duality: `s ∧ᶜ t`{.AgdaFunction} is the dual of the canonical join of the duals.
It represents `⌊ s ⌋ ∧̇ ⌊ t ⌋` (`∧ᶜ-sound`{.AgdaFunction}), because the dual
commutes with the embedding and is an involution (`dual⌊dualᶜ⌋`{.AgdaFunction})
that preserves equality in the free lattice; and it is canonical when `s` and `t`
are (`∧ᶜ-canonical`{.AgdaFunction}), because the dual of a canonical term is
canonical.

```agda
  _∧ᶜ_ : CTerm X → CTerm X → CTerm X
  s ∧ᶜ t = dualᶜ (dualᶜ s ∨ᶜ dualᶜ t)

  dual⌊dualᶜ⌋ : (c : CTerm X) → dual ⌊ dualᶜ c ⌋ ≡ ⌊ c ⌋
  dual⌊dualᶜ⌋ c = trans (cong dual (⌊dualᶜ⌋ c)) (dual-involutive ⌊ c ⌋)

  ∧ᶜ-sound : (s t : CTerm X) → ⌊ s ∧ᶜ t ⌋ ≈ʷ ⌊ s ⌋ ∧̇ ⌊ t ⌋
  ∧ᶜ-sound s t =
    subst₂ _≈ʷ_ (sym (⌊dualᶜ⌋ (dualᶜ s ∨ᶜ dualᶜ t))) (cong₂ _∧̇_ (dual⌊dualᶜ⌋ s) (dual⌊dualᶜ⌋ t))
           (dual-cong (∨ᶜ-sound (dualᶜ s) (dualᶜ t)))

  ∧ᶜ-canonical : {s t : CTerm X} → IsCanonical s → IsCanonical t → IsCanonical (s ∧ᶜ t)
  ∧ᶜ-canonical cs ct = dualᶜ-canonical (∨ᶜ-canonical (dualᶜ-canonical cs) (dualᶜ-canonical ct))
```

**The canonical form of a term**.  `canonical`{.AgdaFunction} replaces each formal
operation of a lattice term by the canonical join or meet of the canonical forms
of its two sides.  By induction, the result represents the term
(`canonical-sound`{.AgdaFunction}) and is canonical
(`canonical-isCanonical`{.AgdaFunction}).

```agda
  canonical : LatTerm X → CTerm X
  canonical (ℊ x)    = genᶜ x
  canonical (s ∨̇ t)  = canonical s ∨ᶜ canonical t
  canonical (s ∧̇ t)  = canonical s ∧ᶜ canonical t

  canonical-sound : (t : LatTerm X) → ⌊ canonical t ⌋ ≈ʷ t
  canonical-sound (ℊ x)    = ≈ʷ-refl
  canonical-sound (s ∨̇ t)  =
    ≈ʷ-trans (∨ᶜ-sound (canonical s) (canonical t)) (∨̇-cong (canonical-sound s) (canonical-sound t))
  canonical-sound (s ∧̇ t)  =
    ≈ʷ-trans (∧ᶜ-sound (canonical s) (canonical t)) (∧̇-cong (canonical-sound s) (canonical-sound t))

  canonical-isCanonical : (t : LatTerm X) → IsCanonical (canonical t)
  canonical-isCanonical (ℊ x)    = cgen
  canonical-isCanonical (s ∨̇ t)  = ∨ᶜ-canonical (canonical-isCanonical s) (canonical-isCanonical t)
  canonical-isCanonical (s ∧̇ t)  = ∧ᶜ-canonical (canonical-isCanonical s) (canonical-isCanonical t)
```
