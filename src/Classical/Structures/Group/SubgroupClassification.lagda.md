---
layout: default
file: "src/Classical/Structures/Group/SubgroupClassification.lagda.md"
title: "Classical.Structures.Group.SubgroupClassification module"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Classifying subgroups by generation certificates

This is the [Classical.Structures.Group.SubgroupClassification][] module of the [Agda Universal Algebra Library][].

This module answers questions of the form "which subgroups of a finite group
contain `H`?" or "which subgroups lie in a given interval of `Sub(G)`?".

An answer to such a question consists of a **certificate** which is derived
*verbally*, as follows: the engine (GAP, or the Python generator of
`scripts/python/flrp/`) supplies *words* (products of designated generators) and
the checkers here re-verify every word by evaluating it, so nothing is believed on
the engine's authority.

The problem being solved: an arbitrary decidable subgroup `K` is given only by its
membership decider, so "`K` is one of the listed subgroups" cannot be established
by enumerating subgroups; the type of deciders is not searchable.

What *can* be done constructively is to walk `K` up a finite family: if
`K` properly contains a listed member `K'`, a concrete element `g ∈ K ∖ K'` is
found by finite search (`sub⊈-witness`{.AgdaFunction}), and a certificate for the
pair (`K'`, `g`) names a *larger* listed member together with words proving that
the larger member's generators lie in `⟨K' ∪ {g}⟩ ⊆ K`.

Certified steps strictly increase a rank, so the walk terminates, and `K` is
identified (up to mutual containment) with a listed member. The two ingredients
are as follows.

+  **Words**: evaluation of index words over the carrier enumeration, and the one
   lemma that matters; a word whose letters lie in a subgroup evaluates into the
   subgroup (`evalWord-closed`{.AgdaFunction}).

+  **Escalation**: the certificate schema (per-member generators and expansion
   words, per-pair step words and a rank), the decidable well-formedness predicate
   `EscalationOK`{.AgdaFunction} that a data module discharges with
   `from-yes`{.AgdaFunction}, and the classifier `classify`{.AgdaFunction}.

The first consumer is the filter-ideal route to the census entries `L16` (interval
`[C3 , A5]` in `Sub(A5)`, exactly three intermediate subgroups) and `L11`: there the
classifier turns "a congruence of the regular action whose `ε`-class contains `C3`"
into one of five named subgroups.  The machinery is deliberately independent of
that application; any finite group with emitted word certificates can use it.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.SubgroupClassification where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using  ( ⊥-elim )
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Properties                    using  ( ¬∀⟶∃¬ )
                                                   renaming ( all? to allᶠ? ; _≟_ to _≟ᶠ_ )
open import Data.List.Base                         using  ( List ; [] ; _∷_ )
open import Data.List.Membership.Propositional     using  () renaming ( _∈_ to _∈ˡ_ )
open import Data.List.Relation.Unary.All           using  ( All ; [] ; _∷_ )
                                                   renaming  ( all? to allˡ?
                                                             ; lookup to All-lookup
                                                             ; map to All-map )
open import Data.List.Relation.Unary.Any           using  ( here ; there )
open import Data.List.Relation.Binary.Pointwise    using  ( Pointwise ; [] ; _∷_ )
import Data.List.Membership.DecPropositional as DecMembership
import Data.List.Relation.Binary.Pointwise.Properties as PointwiseProps
open import Data.Nat.Base                          using  ( ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_ )
open import Data.Nat.Properties                    using  ( _<?_ ; ≤-trans ; m≤m+n ; +-suc
                                                          ; <⇒≱ ; +-monoʳ-≤ )
open import Data.Product                           using  ( _×_ ; _,_ ; Σ-syntax
                                                          ; proj₁ ; proj₂ )
open import Level                                  using  ( Level ; _⊔_ )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( refl ; sym ; subst )
open import Relation.Nullary                       using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable.Core        using  ( ¬? ; _×-dec_ ; _→-dec_ )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic       using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups   using  ( IsSubgroup ; Subgroup
                                                          ; DecSubgroup )
open import Setoid.Algebras.Basic                  using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                 using  ( FiniteAlgebra )
```
-->

#### The setting

Everything is parameterized by a group and a finiteness witness for its carrier.
`set`{.AgdaFunction} and `memb?`{.AgdaFunction} are the two projections of a
decidable subgroup that the development reads constantly.

```agda
module Classify {α ρ ℓ : Level} (𝒢@(𝑮 , _) : Group α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝒢)) where

  open Setoid 𝔻[ 𝑮 ]    using ( _≈_ ) renaming ( sym to ≈sym )
  open Group-Op 𝒢       using ( _∙_ ; ε )
  open FiniteAlgebra 𝑭  renaming ( _≟_ to _≈?_ )

  -- The underlying predicate, subgroup structure, and membership decider.
  set : DecSubgroup 𝒢 ℓ → Pred 𝕌[ 𝑮 ] ℓ
  set K = K .proj₁ .proj₁

  isSub : (K : DecSubgroup 𝒢 ℓ) → IsSubgroup 𝒢 (set K)
  isSub K = K .proj₁ .proj₂

  memb? : (K : DecSubgroup 𝒢 ℓ) → ∀ x → Dec (x ∈ set K)
  memb? K = K .proj₂
```

#### Decidable containment, with witness extraction

Containment of decidable subgroups reduces to finitely many decidable implications
over the enumeration, lifted through surjectivity by the `respects`{.AgdaField}
fields; a *failed* containment yields the **index** of a violating element; the
index, not just the element, because certificate rows are keyed by enumeration
indices.

```agda
  private
    Table⊆ : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ → Type ℓ
    Table⊆ K L = ∀ i → enum i ∈ set K → enum i ∈ set L

    table⊆? : (K L : DecSubgroup 𝒢 ℓ) → Dec (Table⊆ K L)
    table⊆? K L = allᶠ? (λ i → memb? K (enum i) →-dec memb? L (enum i))

    table→⊆ : (K L : DecSubgroup 𝒢 ℓ) → Table⊆ K L → set K ⊆ set L
    table→⊆ K L tbl {x} x∈K with enum-sur x
    ... | i , ei≈x =
      IsSubgroup.respects (isSub L) ei≈x
        (tbl i (IsSubgroup.respects (isSub K) (≈sym ei≈x) x∈K))

  -- Containment of decidable subgroups is decidable.
  sub⊆-dec : (K L : DecSubgroup 𝒢 ℓ) → Dec (set K ⊆ set L)
  sub⊆-dec K L with table⊆? K L
  ... | yes tbl  = yes (table→⊆ K L tbl)
  ... | no ¬tbl  = no (λ sub → ¬tbl (λ i i∈K → sub i∈K))

  -- A failed containment yields the index of a violating element.
  sub⊈-witness : (K L : DecSubgroup 𝒢 ℓ) → ¬ (set K ⊆ set L)
    → Σ[ i ∈ Fin card ] (enum i ∈ set K × ¬ (enum i ∈ set L))
  sub⊈-witness K L ¬sub with table⊆? K L
  ... | yes tbl  = ⊥-elim (¬sub (table→⊆ K L tbl))
  ... | no ¬tbl  = unpack
    where
    ¬→-split : {P Q : Type ℓ} → Dec P → ¬ (P → Q) → P × ¬ Q
    ¬→-split (yes p) ¬imp  = p , λ q → ¬imp (λ _ → q)
    ¬→-split (no ¬p) ¬imp  = ⊥-elim (¬imp (λ p → ⊥-elim (¬p p)))

    unpack : Σ[ i ∈ Fin card ] (enum i ∈ set K × ¬ (enum i ∈ set L))
    unpack with ¬∀⟶∃¬ _ _ (λ i → memb? K (enum i) →-dec memb? L (enum i)) ¬tbl
    ... | i , ¬impᵢ = i , ¬→-split (memb? K (enum i)) ¬impᵢ
```

#### Words over the enumeration

A word is a list of enumeration indices; it evaluates to the left-to-right
product of the corresponding elements (the empty word to `ε`).  The letters
of a certified word always lie in a designated set by construction, so the
single consumption lemma is closure of subgroups under products.

```agda
  Word : Type
  Word = List (Fin card)

  evalWord : Word → 𝕌[ 𝑮 ]
  evalWord []       = ε
  evalWord (l ∷ w)  = enum l ∙ evalWord w

  -- A word whose letters lie in a subgroup evaluates into the subgroup.
  evalWord-closed :  (K : Subgroup 𝒢 ℓ) (w : Word)
    →                All (λ l → enum l ∈ proj₁ K) w → evalWord w ∈ proj₁ K
  evalWord-closed K []       []           = IsSubgroup.ε-closed (proj₂ K)
  evalWord-closed K (l ∷ w)  (l∈K ∷ w∈K)  =
    IsSubgroup.∙-closed (proj₂ K) l∈K (evalWord-closed K w w∈K)
```

#### The escalation certificate schema

For a family `sub : Fin m → DecSubgroup` the certificate data comprise, per
member `k`:

+  `gens k`: indices of a generating set, each lying in `sub k`;
+  `expWords k i`: for each carrier index `i` with `enum i ∈ sub k`, a word
   over the letters `gens k` evaluating to `enum i` (the member's *expansion*:
   every element as a product of the generators);
+  `rank k`: a rank below `m`, strictly increased by every step;

and, per pair `(k , j)` with `enum j` inside the ambient member
`top` but off `sub k`:

+  `stepNext k j` — the larger member reached by adjoining `enum j`;
+  `stepWords k j` — one word per generator of the target, over the letters
   `j ∷ gens k`, evaluating to that generator.

The ambient `top` confines the walk: step certificates are owed only for adjoined
elements inside it, and in exchange the classifier applies only to subgroups `K ⊆ top`.
This is what makes interval families certifiable; for the ideal `[1 , C5]` of the
`L16` instance, say, the family `{1 , C5}` owes step rows only for the four
nontrivial elements of `C5`, not for the whole ambient group (adjoining an element
of order 2 to the trivial subgroup reaches no family member, and never occurs for
`K ⊆ C5`).  For an unconstrained walk take `top` to be the full subgroup.

`EscalationOK`{.AgdaFunction} is the conjunction of the well-formedness
conditions; every conjunct is decidable (`escalationOK?`{.AgdaFunction}), so a
concrete data module discharges it with `from-yes`{.AgdaFunction}; evaluating the
decision *is* the re-verification of every emitted word.

```agda
  private
    _∈ˡ?_ : (l : Fin card) (xs : List (Fin card)) → Dec (l ∈ˡ xs)
    _∈ˡ?_ = DecMembership._∈?_ _≟ᶠ_

  module Escalate
    {m : ℕ}
    (top        : DecSubgroup 𝒢 ℓ)
    (sub        : Fin m → DecSubgroup 𝒢 ℓ)
    (gens       : Fin m → List (Fin card))
    (expWords   : Fin m → Fin card → Word)
    (rank       : Fin m → ℕ)
    (stepNext   : Fin m → Fin card → Fin m)
    (stepWords  : Fin m → Fin card → List Word)
    where

    -- The member's generators lie in the member, and its expansion words
    -- cover every member element using only those generators.
    ExpOK : Fin m → Type (ρ ⊔ ℓ)
    ExpOK k =
        All (λ l → enum l ∈ set (sub k)) (gens k)
      × (∀ i → enum i ∈ set (sub k)
             → All (_∈ˡ gens k) (expWords k i) × (evalWord (expWords k i) ≈ enum i))

    -- For an ambient index j off the member: the step target strictly
    -- increases the rank, and its generators are realized by words over
    -- j ∷ gens k.
    StepOK : Fin m → Fin card → Type (ρ ⊔ ℓ)
    StepOK k j =
      enum j ∈ set top
      → ¬ (enum j ∈ set (sub k))
      →   rank k < rank (stepNext k j)
        × Pointwise  (λ l w → All (_∈ˡ (j ∷ gens k)) w × (evalWord w ≈ enum l))
                     (gens (stepNext k j)) (stepWords k j)

    -- The full certificate: expansions, steps, and the rank bound.
    EscalationOK : Type (ρ ⊔ ℓ)
    EscalationOK = (∀ k → ExpOK k) × (∀ k j → StepOK k j) × (∀ k → rank k < m)

    private
      expOK? : ∀ k → Dec (ExpOK k)
      expOK? k =
        allˡ? (λ l → memb? (sub k) (enum l)) (gens k)
        ×-dec allᶠ? (λ i → memb? (sub k) (enum i) →-dec
                (allˡ? (_∈ˡ? gens k) (expWords k i)
                 ×-dec (evalWord (expWords k i) ≈? enum i)))

      stepOK? : ∀ k j → Dec (StepOK k j)
      stepOK? k j =
        memb? top (enum j) →-dec (¬? (memb? (sub k) (enum j)) →-dec
          (  (rank k <? rank (stepNext k j))
           ×-dec PointwiseProps.decidable
                   (λ l w → allˡ? (_∈ˡ? (j ∷ gens k)) w ×-dec (evalWord w ≈? enum l))
                   (gens (stepNext k j)) (stepWords k j)))

    escalationOK? : Dec EscalationOK
    escalationOK? =
            allᶠ? expOK?
      ×-dec allᶠ? (λ k → allᶠ? (stepOK? k))
      ×-dec allᶠ? (λ k → rank k <? m)
```

#### The classifier

Given a certified table, an arbitrary decidable subgroup `K` containing a listed
member is walked up the family.  At each stage either `K ⊆ sub c` is decided
positively, closing the identification, or a violating index escalates to a
strictly higher-ranked member whose elements all lie in `K`.  The fuel is the
family size; the rank bound makes fuel exhaustion absurd.

```agda
    module _ (OK : EscalationOK) where

      private
        exps   = proj₁ OK
        steps  = proj₁ (proj₂ OK)
        bound  = proj₂ (proj₂ OK)

        -- Extract, from a Pointwise certificate, the word for one generator.
        pw-find :
          {r : Level}
          {R : Fin card → Word → Type r}
          {xs : List (Fin card)}
          {ys : List Word}
          → Pointwise R xs ys
          → {l : Fin card} → l ∈ˡ xs
          → Σ[ w ∈ Word ] R l w

        pw-find (r ∷ rs) (here refl) = _ , r
        pw-find (r ∷ rs) (there p) = pw-find rs p

      -- One escalation step: adjoining a violating element carries the
      -- containment invariant to the next member.
      step-⊆ :  (K : DecSubgroup 𝒢 ℓ) (c : Fin m) (j : Fin card)
        → set (sub c) ⊆ set K
        → enum j ∈ set top → enum j ∈ set K → ¬ (enum j ∈ set (sub c))
        → set (sub (stepNext c j)) ⊆ set K

      step-⊆ K c j c⊆K j∈top j∈K j∉c {x} x∈next = x∈K
        where
        K-resp = IsSubgroup.respects (isSub K)

        -- A letter of a step word lies in K: it is either the adjoined
        -- element or a generator of the current member.
        letter∈K : {l : Fin card} → l ∈ˡ (j ∷ gens c) → enum l ∈ set K
        letter∈K (here refl)  = j∈K
        letter∈K (there p)    = c⊆K (All-lookup (proj₁ (exps c)) p)

        -- Every generator of the next member lies in K, via its step word.
        gen∈K : {l : Fin card} → l ∈ˡ gens (stepNext c j) → enum l ∈ set K
        gen∈K l∈gens with pw-find (proj₂ (steps c j j∈top j∉c)) l∈gens
        ... | w , (letters , ev≈) =
          K-resp ev≈ (evalWord-closed (proj₁ K) w (All-map letter∈K letters))

        -- Hence every element of the next member lies in K, via its expansion.
        x∈K : x ∈ set K
        x∈K with enum-sur x
        ... | i , ei≈x = K-resp ei≈x (K-resp ev≈ w∈K)
          where
          i∈next = IsSubgroup.respects (isSub (sub (stepNext c j))) (≈sym ei≈x) x∈next

          expo = proj₂ (exps (stepNext c j)) i i∈next

          ev≈ : evalWord (expWords (stepNext c j) i) ≈ enum i
          ev≈ = proj₂ expo

          w∈K : evalWord (expWords (stepNext c j) i) ∈ set K
          w∈K = evalWord-closed (proj₁ K) _ (All-map gen∈K (proj₁ expo))

      -- The classification loop, on fuel, with the rank invariant.
      private
        classify-loop :  (K : DecSubgroup 𝒢 ℓ) (fuel : ℕ) (c : Fin m)
          → set K ⊆ set top
          → m ≤ fuel + rank c
          → set (sub c) ⊆ set K
          → Σ[ k ∈ Fin m ] ((set (sub k) ⊆ set K) × (set K ⊆ set (sub k)))

        classify-loop K zero c K⊆top inv c⊆K = ⊥-elim (<⇒≱ (bound c) inv)
        classify-loop K (suc f) c K⊆top inv c⊆K with sub⊆-dec K (sub c)
        ... | yes K⊆c = c , c⊆K , K⊆c
        ... | no ¬K⊆c with sub⊈-witness K (sub c) ¬K⊆c
        ...   | j , j∈K , j∉c =
          classify-loop K f (stepNext c j) K⊆top inv'
            (step-⊆ K c j c⊆K (K⊆top j∈K) j∈K j∉c)
          where
          inv' : m ≤ f + rank (stepNext c j)
          inv' = ≤-trans  (subst (m ≤_) (sym (+-suc f (rank c))) inv)
                          (+-monoʳ-≤ f (proj₁ (steps c j (K⊆top j∈K) j∉c)))

      -- The classifier: any decidable subgroup within the ambient member and
      -- containing a listed member is, up to mutual containment, a listed
      -- member.
      classify :  (K : DecSubgroup 𝒢 ℓ) (c : Fin m)
        → set K ⊆ set top
        → set (sub c) ⊆ set K
        → Σ[ k ∈ Fin m ] ((set (sub k) ⊆ set K) × (set K ⊆ set (sub k)))
      classify K c K⊆top c⊆K = classify-loop K m c K⊆top (m≤m+n m (rank c)) c⊆K
```

--------------------------------------
