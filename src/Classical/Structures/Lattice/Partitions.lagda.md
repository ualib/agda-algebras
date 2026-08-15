---
layout: default
file: "src/Classical/Structures/Lattice/Partitions.lagda.md"
title: "Classical.Structures.Lattice.Partitions module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### The partition lattice `Eq(n)`

This is the [Classical.Structures.Lattice.Partitions][] module of the [Agda Universal Algebra Library][].

This module constructs the **partition lattice** `Eq(n)`{.AgdaFunction} — the
equivalence relations on an `n`-element set, ordered by refinement — as a
level-zero equational `Lattice`{.AgdaFunction} of
[Classical.Structures.Lattice.Basic][], the presentation the FLRP program's
`IntervalIso`{.AgdaFunction} and `ConIso`{.AgdaFunction} target.  It is the lattice
whose *dual* Kurzweil's construction realizes as the interval `[D , Sⁿ]` in the
subgroup lattice of a power of a group (issue #521), and the classical sources
(`docs/papers/fin-lat-rep/SmallLatticeReps.tex` § "Lattice duals") work with the
same small carrier used here: a partition is a *function* `Fin n → Fin n`,
identified with its kernel.

**The presentation.**  A partition of `Fin n` is stored as a
`ParentVec`{.AgdaFunction} of [Setoid.Congruences.Certificates.Schema][] — a vector
of `n` labels — and *read through its kernel*: indices `i` and `j` lie in the same
block exactly when their labels agree (`SameBlock`{.AgdaFunction}, the standalone
form of the relation the certificate checkers use).  Two vectors present the same
partition when their kernels coincide, so the carrier setoid takes **mutual
refinement** as its equality, in the library's setoid discipline; no normal form is
imposed.  (The Freese normal form of the Schema module remains the right tool where
*syntactic* comparison of partitions is wanted, as in the certificate checkers; the
lattice here never needs canonical representatives, and its operations choose
whatever labels are convenient.)

**Order-first.**  Per the library's construction discipline, the lattice is built
from its order: refinement `_⊑_`{.AgdaFunction} is a partial order on the carrier
setoid, the meet and join constructed below are its infimum and supremum, and the
eight lattice equations then come for free — through the standard library's
order-to-algebra bridge (`algLattice`{.AgdaFunction} of
[`Relation.Binary.Lattice.Properties.Lattice`]) — before the final packaging by
`setoidEqsToLattice`{.AgdaFunction}.

**The operations.**  Both operations are elementary and total, with no fixpoint
iteration:

+  the **meet** relabels each index by the *least* index carrying the same pair of
   labels — its kernel is the intersection of the two kernels by construction;
+  the **join** folds over all index pairs `(i , j)`, and, whenever `i` and `j` lie
   in the same block of the second argument, merges the *whole blocks* of `i` and
   `j` in the accumulator by relabelling.  Because each step merges two entire
   blocks, the accumulated kernel is transitive at every stage, and no closure
   iteration or chain-length bound is ever needed: the result contains both
   kernels and is contained in every common coarsening.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.Partitions where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base       using ( Bool ; true ; false ; if_then_else_ )
open import Data.Empty           using ( ⊥-elim )
open import Data.Fin.Base as Fin using ( Fin ; _≤_ )
open import Data.Fin.Properties  using ( _≟_ ; ≤-antisym )
open import Data.List.Base       using ( List ; [] ; _∷_ ; foldr ; allFin
                                       ; cartesianProduct )
open import Data.List.Membership.Propositional             using ( _∈_ )
open import Data.List.Membership.Propositional.Properties  using ( ∈-allFin
                                                                 ; ∈-cartesianProduct⁺ )
open import Data.List.Relation.Unary.Any                   using ( here ; there )
open import Data.Nat.Base        using ( ℕ ; zero ; suc ; z≤n ; s≤s )
open import Data.Product         using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ ; swap )
open import Data.Sum.Base        using ( _⊎_ ; inj₁ ; inj₂ ; map₂ )
open import Data.Vec.Base        using ( tabulate )
open import Data.Vec.Properties  using ( lookup∘tabulate )
open import Function             using ( _∘_ )
open import Level                using ( 0ℓ )
open import Relation.Binary      using ( Setoid )
open import Relation.Binary.Lattice  using ( Supremum ; Infimum )
                                     renaming ( Lattice to OrderLattice
                                              ; IsLattice to IsOrderLattice )
open import Relation.Binary.PropositionalEquality
                                 using ( _≡_ ; refl ; sym ; trans ; cong )
open import Relation.Nullary     using ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable  using ( does ; _×-dec_ ; dec-true )

import Algebra.Lattice.Bundles                       as AlgLatticeBundles
import Algebra.Lattice.Properties.Lattice            as AlgLatticeProperties
import Relation.Binary.Lattice.Properties.Lattice    as OrderLatticeProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic           using  ( Lattice
                                                                ; setoidEqsToLattice )
open import Setoid.Congruences.Certificates.Schema       using  ( ParentVec ; parent )
```
-->

#### The kernel reading and the refinement order

`SameBlock`{.AgdaFunction} `pv i j` says the labels of `i` and `j` agree — `i` and
`j` lie in the same block of the partition presented by `pv`.  (This is the
standalone form of the relation the certificate checker of
[Setoid.Congruences.Certificates.Congruence][] defines locally against an ambient
algebra.)  Refinement `pu ⊑ pw` says every block relation of `pu` is one of `pw` —
`pu` refines `pw` — and partition equality is mutual refinement.

```agda
private variable n : ℕ

-- i and j lie in the same block of pv.
SameBlock : ParentVec n → Fin n → Fin n → Type
SameBlock pv i j = parent pv i ≡ parent pv j

infix 4 _⊑_ _≈ᵖ_

-- pu refines pw: every pu-block relation is a pw-block relation.
_⊑_ : ParentVec n → ParentVec n → Type
pu ⊑ pw = ∀ {i j} → SameBlock pu i j → SameBlock pw i j

-- Partition equality: the two vectors have the same kernel.
_≈ᵖ_ : ParentVec n → ParentVec n → Type
pu ≈ᵖ pw = (pu ⊑ pw) × (pw ⊑ pu)
```

Reflexivity, transitivity, and — because equality *is* mutual refinement —
antisymmetry of the order are immediate.

```agda
⊑-refl : {pv : ParentVec n} → pv ⊑ pv
⊑-refl e = e

⊑-trans : {pu pv pw : ParentVec n} → pu ⊑ pv → pv ⊑ pw → pu ⊑ pw
⊑-trans uv vw e = vw (uv e)

≈ᵖ-refl : {pv : ParentVec n} → pv ≈ᵖ pv
≈ᵖ-refl = (λ e → e) , (λ e → e)

≈ᵖ-sym : {pu pv : ParentVec n} → pu ≈ᵖ pv → pv ≈ᵖ pu
≈ᵖ-sym = swap

≈ᵖ-trans : {pu pv pw : ParentVec n} → pu ≈ᵖ pv → pv ≈ᵖ pw → pu ≈ᵖ pw
≈ᵖ-trans (uv , vu) (vw , wv) = (λ e → vw (uv e)) , (λ e → vu (wv e))

-- The carrier setoid of Eq(n): parent vectors up to kernel equality.
Eq-setoid : (n : ℕ) → Setoid 0ℓ 0ℓ
Eq-setoid n = record
  { Carrier        = ParentVec n
  ; _≈_            = _≈ᵖ_
  ; isEquivalence  = record
      { refl   = λ {pv} → ≈ᵖ-refl {pv = pv}
      ; sym    = λ {pu} {pv} → ≈ᵖ-sym {pu = pu} {pv = pv}
      ; trans  = λ {pu} {pv} {pw} → ≈ᵖ-trans {pu = pu} {pv = pv} {pw = pw}
      }
  }
```

Operations produce vectors by tabulating a relabelling function; this small lemma
is the only bridge ever needed between the vector and its function.

```agda
-- Reading back a tabulated relabelling function.
parent-tab : (f : Fin n → Fin n) (i : Fin n) → parent (tabulate f) i ≡ f i
parent-tab = lookup∘tabulate
```

#### Bounded search for a least satisfier

The meet relabels each index by the least member of its intersection block, so we
need one search primitive: the least index satisfying a decidable predicate, or a
proof that none does.  The search is structural recursion on `n`, scanning from
`zero` upward, so the first hit is the least.

```agda
findLeast : (n : ℕ) {P : Fin n → Type 0ℓ} (P? : (j : Fin n) → Dec (P j))
  →  (Σ[ j ∈ Fin n ] (P j × ((k : Fin n) → P k → j ≤ k)))
  ⊎  ((j : Fin n) → ¬ P j)
findLeast zero P? = inj₂ (λ ())
findLeast (suc m) {P} P? = check (P? Fin.zero)
  where
  check : Dec (P Fin.zero) → _
  check (yes p) = inj₁ (Fin.zero , p , λ k _ → z≤n)
  check (no ¬p) = lift-tail (findLeast m (P? ∘ Fin.suc))
    where
    lift-tail : _ → _
    lift-tail (inj₁ (j , p , least)) = inj₁ (Fin.suc j , p , least′)
      where
      least′ : (k : Fin (suc m)) → P k → Fin.suc j ≤ k
      least′ Fin.zero     pk = ⊥-elim (¬p pk)
      least′ (Fin.suc k)  pk = s≤s (least k pk)
    lift-tail (inj₂ none) = inj₂ none′
      where
      none′ : (j : Fin (suc m)) → ¬ P j
      none′ Fin.zero     = ¬p
      none′ (Fin.suc j)  = none j
```

Two least satisfiers of pointwise-equivalent predicates coincide — the
antisymmetry step every canonicity argument below routes through.

```agda
least-unique : {P Q : Fin n → Type 0ℓ}
  → ((k : Fin n) → P k → Q k) → ((k : Fin n) → Q k → P k)
  → (jp : Fin n) → P jp → ((k : Fin n) → P k → jp ≤ k)
  → (jq : Fin n) → Q jq → ((k : Fin n) → Q k → jq ≤ k)
  → jp ≡ jq
least-unique pq qp jp Pjp minP jq Qjq minQ =
  ≤-antisym (minP jq (qp jq Qjq)) (minQ jp (pq jp Pjp))
```

#### The meet

`MeetOf`{.AgdaModule} `pu pw` relabels each index `i` by the least index carrying
the same `pu`-label *and* the same `pw`-label as `i`.  The relabelling is constant
on intersection blocks and separates distinct ones, so its kernel is exactly the
intersection of the two kernels.

```agda
module MeetOf (pu pw : ParentVec n) where

  private
    -- The intersection block of i, as a predicate on candidate representatives.
    P : Fin n → Fin n → Type 0ℓ
    P i j = SameBlock pu j i × SameBlock pw j i

    P? : (i j : Fin n) → Dec (P i j)
    P? i j = (parent pu j ≟ parent pu i) ×-dec (parent pw j ≟ parent pw i)

    -- The search cannot fail: i itself is in the intersection block of i.
    found : (i : Fin n) → Σ[ j ∈ Fin n ] (P i j × ((k : Fin n) → P i k → j ≤ k))
    found i = extract (findLeast _ (P? i))
      where
      extract : _ → _
      extract (inj₁ f)     = f
      extract (inj₂ none)  = ⊥-elim (none i (refl , refl))

  -- The meet relabelling: the least member of the intersection block.
  meetF : Fin n → Fin n
  meetF i = proj₁ (found i)

  meetF-sat : (i : Fin n) → SameBlock pu (meetF i) i × SameBlock pw (meetF i) i
  meetF-sat i = proj₁ (proj₂ (found i))

  meetF-least : (i k : Fin n) → SameBlock pu k i × SameBlock pw k i → meetF i ≤ k
  meetF-least i = proj₂ (proj₂ (found i))
```

The relabelling is constant on intersection blocks (two indices related in both
kernels search pointwise-equivalent predicates), and conversely two indices with
the same relabel are related in both kernels (each is related in both kernels to
its representative).

```agda
  -- Same pu-block and same pw-block ⟹ same meet label.
  meetF-cong : {i j : Fin n} → SameBlock pu i j → SameBlock pw i j → meetF i ≡ meetF j
  meetF-cong {i} {j} eu ew =
    least-unique
      (λ k (a , b) → trans a eu , trans b ew)
      (λ k (a , b) → trans a (sym eu) , trans b (sym ew))
      (meetF i) (meetF-sat i) (meetF-least i)
      (meetF j) (meetF-sat j) (meetF-least j)

  -- Same meet label ⟹ same pu-block and same pw-block.
  meetF-ker : {i j : Fin n} → meetF i ≡ meetF j → SameBlock pu i j × SameBlock pw i j
  meetF-ker {i} {j} e =
      trans (sym (proj₁ (meetF-sat i))) (trans (cong (parent pu) e) (proj₁ (meetF-sat j)))
    , trans (sym (proj₂ (meetF-sat i))) (trans (cong (parent pw) e) (proj₂ (meetF-sat j)))
```

The meet vector, with its infimum properties at the vector level.

```agda
  -- The meet of the two partitions.
  meet-vec : ParentVec n
  meet-vec = tabulate meetF

  private
    to-meetF : {i j : Fin n} → SameBlock meet-vec i j → meetF i ≡ meetF j
    to-meetF {i} {j} e = trans (sym (parent-tab meetF i)) (trans e (parent-tab meetF j))

  ∧-lower₁ : meet-vec ⊑ pu
  ∧-lower₁ e = proj₁ (meetF-ker (to-meetF e))

  ∧-lower₂ : meet-vec ⊑ pw
  ∧-lower₂ e = proj₂ (meetF-ker (to-meetF e))

  ∧-greatest : (q : ParentVec n) → q ⊑ pu → q ⊑ pw → q ⊑ meet-vec
  ∧-greatest q qu qw {i} {j} e =
    trans (parent-tab meetF i) (trans (meetF-cong (qu e) (qw e)) (sym (parent-tab meetF j)))
```

#### The join

`JoinOf`{.AgdaModule} `pu pw` starts from the labels of `pu` and folds over all
index pairs; at a pair `(i , j)` lying in the same `pw`-block, it merges the
current blocks of `i` and `j` by relabelling `j`'s block with `i`'s label.  One
merge step joins the accumulated partition with one whole pair of blocks, so the
accumulated kernel is an equivalence at every stage — this is what makes the least
upper bound argument a plain fold induction, with no transitive-closure iteration.

```agda
module JoinOf (pu pw : ParentVec n) where

  private
    if-same : (b : Bool) (t : Fin n) → (if b then t else t) ≡ t
    if-same true   t = refl
    if-same false  t = refl

  -- Relabel the (current) block of j with the (current) label of i.
  relabel : (Fin n → Fin n) → Fin n → Fin n → (Fin n → Fin n)
  relabel v i j k = if does (v k ≟ v j) then v i else v k

  -- Relabelling only coarsens: the new label is a function of the old one.
  relabel-mono : (v : Fin n → Fin n) (i j : Fin n) {k l : Fin n}
    → v k ≡ v l → relabel v i j k ≡ relabel v i j l
  relabel-mono v i j = cong (λ t → if does (t ≟ v j) then v i else t)

  -- After the merge, i and j carry the same label.
  relabel-relates : (v : Fin n → Fin n) (i j : Fin n) → relabel v i j i ≡ relabel v i j j
  relabel-relates v i j =
    trans (if-same (does (v i ≟ v j)) (v i)) (sym at-j)
    where
    at-j : relabel v i j j ≡ v i
    at-j = cong (λ b → if b then v i else v j) (dec-true (v j ≟ v j) refl)

  -- A pair merged by the relabelling was already related, or straddles
  -- the two merged blocks.
  relabel-ker : (v : Fin n → Fin n) (i j : Fin n) {k l : Fin n}
    → relabel v i j k ≡ relabel v i j l
    → (v k ≡ v l) ⊎ ((v k ≡ v j × v l ≡ v i) ⊎ (v k ≡ v i × v l ≡ v j))
  relabel-ker v i j {k} {l} = split (v k ≟ v j) (v l ≟ v j)
    where
    split : (dk : Dec (v k ≡ v j)) (dl : Dec (v l ≡ v j))
      → (if does dk then v i else v k) ≡ (if does dl then v i else v l)
      → (v k ≡ v l) ⊎ ((v k ≡ v j × v l ≡ v i) ⊎ (v k ≡ v i × v l ≡ v j))
    split (yes ek)  (yes el)  _ = inj₁ (trans ek (sym el))
    split (yes ek)  (no _)    e = inj₂ (inj₁ (ek , sym e))
    split (no _)    (yes el)  e = inj₂ (inj₂ (e , el))
    split (no _)    (no _)    e = inj₁ e
```

One fold step: merge the blocks of `i` and `j` exactly when `i` and `j` lie in the
same `pw`-block.  Each `relabel` lemma has its conditional counterpart, by
inspecting the guard.

```agda
  -- Merge the blocks of i and j if (i , j) is a pw-block relation.
  step : Fin n × Fin n → (Fin n → Fin n) → (Fin n → Fin n)
  step (i , j) v = if does (parent pw i ≟ parent pw j) then relabel v i j else v

  step-mono : (p : Fin n × Fin n) (v : Fin n → Fin n) {k l : Fin n}
    → v k ≡ v l → step p v k ≡ step p v l
  step-mono (i , j) v {k} {l} e = guard (does (parent pw i ≟ parent pw j))
    where
    guard : (b : Bool) → (if b then relabel v i j else v) k ≡ (if b then relabel v i j else v) l
    guard true   = relabel-mono v i j e
    guard false  = e

  step-relates : (i j : Fin n) (v : Fin n → Fin n)
    → SameBlock pw i j → step (i , j) v i ≡ step (i , j) v j
  step-relates i j v sb = guard (parent pw i ≟ parent pw j)
    where
    guard : (d : Dec (SameBlock pw i j))
      → (if does d then relabel v i j else v) i ≡ (if does d then relabel v i j else v) j
    guard (yes _)   = relabel-relates v i j
    guard (no ¬sb)  = ⊥-elim (¬sb sb)

  step-ker : (i j : Fin n) (v : Fin n → Fin n) {k l : Fin n}
    → step (i , j) v k ≡ step (i , j) v l
    → (v k ≡ v l) ⊎ (SameBlock pw i j × ((v k ≡ v j × v l ≡ v i) ⊎ (v k ≡ v i × v l ≡ v j)))
  step-ker i j v {k} {l} = guard (parent pw i ≟ parent pw j)
    where
    guard : (d : Dec (SameBlock pw i j))
      → (if does d then relabel v i j else v) k ≡ (if does d then relabel v i j else v) l
      → (v k ≡ v l) ⊎ (SameBlock pw i j × ((v k ≡ v j × v l ≡ v i) ⊎ (v k ≡ v i × v l ≡ v j)))
    guard (yes sb)  e = map₂ (λ c → sb , c) (relabel-ker v i j e)
    guard (no _)    e = inj₁ e
```

The fold and its three invariants: it coarsens `pu`; it relates every `pw`-block
relation whose pair occurs in the processed list; and everything it relates is
related in every common coarsening of `pu` and `pw` — by induction, since a step
merges two blocks that any common coarsening already merges.

```agda
  -- The join relabelling: fold the conditional merges over a pair list.
  joinAcc : List (Fin n × Fin n) → (Fin n → Fin n)
  joinAcc = foldr step (parent pu)

  fold-mono : (ps : List (Fin n × Fin n)) {k l : Fin n}
    → SameBlock pu k l → joinAcc ps k ≡ joinAcc ps l
  fold-mono []        e = e
  fold-mono (p ∷ ps)  e = step-mono p (joinAcc ps) (fold-mono ps e)

  fold-relates : (ps : List (Fin n × Fin n)) {i j : Fin n}
    → (i , j) ∈ ps → SameBlock pw i j → joinAcc ps i ≡ joinAcc ps j
  fold-relates (_ ∷ ps) {i} {j} (here refl)   sb = step-relates i j (joinAcc ps) sb
  fold-relates (p ∷ ps)         (there mem)   sb = step-mono p (joinAcc ps) (fold-relates ps mem sb)

  fold-least : (ps : List (Fin n × Fin n)) (q : ParentVec n) → pu ⊑ q → pw ⊑ q
    → {k l : Fin n} → joinAcc ps k ≡ joinAcc ps l → SameBlock q k l
  fold-least [] q u w e = u e
  fold-least ((i , j) ∷ ps) q u w {k} {l} e = assemble (step-ker i j (joinAcc ps) e)
    where
    rec : {a b : Fin n} → joinAcc ps a ≡ joinAcc ps b → SameBlock q a b
    rec = fold-least ps q u w

    assemble :
        (joinAcc ps k ≡ joinAcc ps l)
      ⊎ (SameBlock pw i j
          × ((joinAcc ps k ≡ joinAcc ps j × joinAcc ps l ≡ joinAcc ps i)
            ⊎ (joinAcc ps k ≡ joinAcc ps i × joinAcc ps l ≡ joinAcc ps j)))
      → SameBlock q k l
    assemble (inj₁ e')                        = rec e'
    assemble (inj₂ (sb , inj₁ (ekj , eli)))  =
      trans (rec ekj) (trans (sym (w sb)) (sym (rec eli)))
    assemble (inj₂ (sb , inj₂ (eki , elj)))  =
      trans (rec eki) (trans (w sb) (sym (rec elj)))
```

The join vector folds over *all* index pairs, so every `pw`-block relation is
processed; its supremum properties are the three invariants read through
`parent-tab`{.AgdaFunction}.

```agda
  private
    allPairs : List (Fin n × Fin n)
    allPairs = cartesianProduct (allFin _) (allFin _)

  -- The join of the two partitions.
  join-vec : ParentVec n
  join-vec = tabulate (joinAcc allPairs)

  ∨-upper₁ : pu ⊑ join-vec
  ∨-upper₁ {i} {j} e =
    trans  (parent-tab (joinAcc allPairs) i)
           (trans (fold-mono allPairs e) (sym (parent-tab (joinAcc allPairs) j)))

  ∨-upper₂ : pw ⊑ join-vec
  ∨-upper₂ {i} {j} e =
    trans  (parent-tab (joinAcc allPairs) i)
           (trans  (fold-relates allPairs (∈-cartesianProduct⁺ (∈-allFin i) (∈-allFin j)) e)
                   (sym (parent-tab (joinAcc allPairs) j)))

  ∨-least : (q : ParentVec n) → pu ⊑ q → pw ⊑ q → join-vec ⊑ q
  ∨-least q u w {i} {j} e =
    fold-least allPairs q u w
      (trans (sym (parent-tab (joinAcc allPairs) i)) (trans e (parent-tab (joinAcc allPairs) j)))
```

#### The lattice `Eq(n)`

The binary operations, the order-theoretic lattice bundle, and — through the
standard library's order-to-algebra bridge — the equational `Lattice`.

```agda
infixr 6 _∨ᵖ_
infixr 7 _∧ᵖ_

_∧ᵖ_ : ParentVec n → ParentVec n → ParentVec n
pu ∧ᵖ pw = MeetOf.meet-vec pu pw

_∨ᵖ_ : ParentVec n → ParentVec n → ParentVec n
pu ∨ᵖ pw = JoinOf.join-vec pu pw

Eq-supremum : Supremum (_⊑_ {n}) _∨ᵖ_
Eq-supremum pu pw =
  JoinOf.∨-upper₁ pu pw , JoinOf.∨-upper₂ pu pw , λ q → JoinOf.∨-least pu pw q

Eq-infimum : Infimum (_⊑_ {n}) _∧ᵖ_
Eq-infimum pu pw =
  MeetOf.∧-lower₁ pu pw , MeetOf.∧-lower₂ pu pw , λ q → MeetOf.∧-greatest pu pw q

Eq-isOrderLattice : {n : ℕ} → IsOrderLattice (_≈ᵖ_ {n}) _⊑_ _∨ᵖ_ _∧ᵖ_
Eq-isOrderLattice {n} = record
  { isPartialOrder = record
      { isPreorder = record
          { isEquivalence  = Setoid.isEquivalence (Eq-setoid n)
          ; reflexive      = proj₁
          ; trans          = λ {pu} {pv} {pw} → ⊑-trans {pu = pu} {pv = pv} {pw = pw}
          }
      ; antisym = _,_
      }
  ; supremum  = Eq-supremum
  ; infimum   = Eq-infimum
  }

-- The order-theoretic partition lattice.
Eq-OrderLattice : (n : ℕ) → OrderLattice 0ℓ 0ℓ 0ℓ
Eq-OrderLattice n = record
  { Carrier    = ParentVec n
  ; _≈_        = _≈ᵖ_
  ; _≤_        = _⊑_
  ; _∨_        = _∨ᵖ_
  ; _∧_        = _∧ᵖ_
  ; isLattice  = Eq-isOrderLattice
  }
```

The eight equations of `Th-Lattice` now come from the order: the standard
library's `algLattice`{.AgdaFunction} turns the order-theoretic bundle into an
algebraic one (commutativity, associativity, congruence, absorption), its
`Properties` module supplies idempotence, and `setoidEqsToLattice`{.AgdaFunction}
packages everything as the library's Σ-typed equational lattice.

```agda
-- The partition lattice Eq(n), as a level-zero equational Lattice.
EqLattice : (n : ℕ) → Lattice 0ℓ 0ℓ
EqLattice n = setoidEqsToLattice (Eq-setoid n) _∧ᵖ_ _∨ᵖ_
  (λ {x} {y} {u} {v} → AL.∧-cong {x} {y} {u} {v})
  (λ {x} {y} {u} {v} → AL.∨-cong {x} {y} {u} {v})
  (λ {a} {b} {c} → AL.∧-assoc a b c)
  (λ {a} {b} → AL.∧-comm a b)
  (λ {a} → AP.∧-idem a)
  (λ {a} {b} {c} → AL.∨-assoc a b c)
  (λ {a} {b} → AL.∨-comm a b)
  (λ {a} → AP.∨-idem a)
  (λ {a} {b} → AL.∧-absorbs-∨ a b)
  (λ {a} {b} → ≈ᵖ-trans  {pu = (a ∧ᵖ b) ∨ᵖ a} {pv = a ∨ᵖ (a ∧ᵖ b)} {pw = a}
                         (AL.∨-comm (a ∧ᵖ b) a) (AL.∨-absorbs-∧ a b))
  where
  module OP  = OrderLatticeProperties (Eq-OrderLattice n)
  module AL  = AlgLatticeBundles.Lattice OP.algLattice
  module AP  = AlgLatticeProperties OP.algLattice
```

#### Extremes

The identity relabelling presents the discrete partition (all blocks singleton),
the least element; the constant relabelling presents the one-block partition, the
greatest.  For `n ≡ 0` the two coincide on the empty vector.

```agda
-- The discrete partition: every index its own label.
⊥ᵉ : (n : ℕ) → ParentVec n
⊥ᵉ n = tabulate (λ i → i)

-- The one-block partition: every index the label zero.
⊤ᵉ : (n : ℕ) → ParentVec n
⊤ᵉ zero     = tabulate (λ ())
⊤ᵉ (suc m)  = tabulate (λ _ → Fin.zero)

⊥ᵉ-minimum : (pv : ParentVec n) → ⊥ᵉ n ⊑ pv
⊥ᵉ-minimum {n} pv {i} {j} e =
  cong (parent pv) (trans (sym (parent-tab (λ k → k) i)) (trans e (parent-tab (λ k → k) j)))

⊤ᵉ-maximum : (n : ℕ) (pv : ParentVec n) → pv ⊑ ⊤ᵉ n
⊤ᵉ-maximum zero     pv {()}
⊤ᵉ-maximum (suc m)  pv {i} {j} _ =
  trans (parent-tab (λ _ → Fin.zero) i) (sym (parent-tab (λ _ → Fin.zero) j))
```

#### The refinement order is the meet order of the lattice

`Lattice-Order`{.AgdaModule} of [Classical.Properties.Lattice][] equips
`EqLattice n` with its meet order `x ≤ y = x ∧ y ≈ x`; that order coincides with
refinement.  (The interpretation clauses of `setoidEqsToLattice` apply argument
tuples directly, so the curried meet of the built lattice is definitionally
`_∧ᵖ_`, and both lemmas are one appeal to the infimum.)  Downstream consumers —
the interval isomorphism of Kurzweil's construction — pass between the two forms
through this bridge.

```agda
⊑→≤ : {pu pw : ParentVec n} → pu ⊑ pw → (pu ∧ᵖ pw) ≈ᵖ pu
⊑→≤ {n} {pu} {pw} h =
  MeetOf.∧-lower₁ pu pw , MeetOf.∧-greatest pu pw pu (λ e → e) h

≤→⊑ : {pu pw : ParentVec n} → (pu ∧ᵖ pw) ≈ᵖ pu → pu ⊑ pw
≤→⊑ {n} {pu} {pw} (_ , pu⊑∧) e = MeetOf.∧-lower₂ pu pw (pu⊑∧ e)
```
