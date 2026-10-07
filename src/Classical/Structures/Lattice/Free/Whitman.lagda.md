---
layout: default
file: "src/Classical/Structures/Lattice/Free/Whitman.lagda.md"
title: "Classical.Structures.Lattice.Free.Whitman module"
date: "2026-10-07"
author: "the agda-algebras development team"
---

### Whitman's solution to the word problem

This is the [Classical.Structures.Lattice.Free.Whitman][] module of the [Agda Universal Algebra Library][].

In 1941 Whitman showed that the order of a free lattice is decided by a recursion
on pairs of terms ([Freese, Ježek, and Nation (1995)][], Theorem 1.11).  For lattice
terms `s` and `t` over generators `X`, the inequality `s ≤ t` holds in `FL(X)` if
and only if it is derived by Whitman's rules, which are the following:

1.  `x ≤ y`, for generators `x` and `y`, iff `x = y`;
2.  `s₁ ∨ s₂ ≤ t` iff `s₁ ≤ t` and `s₂ ≤ t`;
3.  `s ≤ t₁ ∧ t₂` iff `s ≤ t₁` and `s ≤ t₂`;
4.  `x ≤ t₁ ∨ t₂`, for a generator `x`, iff `x ≤ t₁` or `x ≤ t₂`;
5.  `s₁ ∧ s₂ ≤ y`, for a generator `y`, iff `s₁ ≤ y` or `s₂ ≤ y`;
6.  `s₁ ∧ s₂ ≤ t₁ ∨ t₂` iff `s₁ ≤ t₁ ∨ t₂` or `s₂ ≤ t₁ ∨ t₂` or `s₁ ∧ s₂ ≤ t₁`
    or `s₁ ∧ s₂ ≤ t₂`.

Rule 6 is *Whitman's condition* (W).  The book proves the theorem semantically,
through Day's doubling construction; this module takes the syntactic route.  It
*defines* a relation `_≤ʷ_`{.AgdaDatatype} on lattice terms by the six rules, proves
it decidable, reflexive, and transitive, and shows that formal meet and join are
its infimum and supremum.  [Classical.Structures.Lattice.Free.Universal][] then
builds `FL(X)` as the terms ordered by `_≤ʷ_`{.AgdaDatatype} and proves that the
rules are sound and complete for the order of every lattice, which is the
content of Theorem 1.11.

**The dispatch order**.  Rules 2 and 3 overlap when `s` is a join and `t` a meet.
The relation fixes an order: a join on the left is split first, then a meet on the
right, and only then do rules 1, 4, 5, and 6 apply, to a left side that is a
generator or a meet and a right side that is a generator or a join.  With that
order every pair of terms falls under exactly one rule, and every rule reduces a
question about `(s , t)` to questions about pairs in which one term is kept and
the other is replaced by a proper subterm.  That is a lexicographic structural
descent, which Agda's termination checker accepts as written; no measure and no
well-founded induction is needed.

**Derivations as data**.  `_≤ʷ_`{.AgdaDatatype} is an inductive family with one
constructor for each rule and each disjunct of a rule, and with the indices of the
constructors following the dispatch order, so an inhabitant of `s ≤ʷ t` is a
derivation by the procedure.  Defining the relation instead as a type-valued
recursion on the pair would make each inversion definitional, but such a type does
not determine its arguments, so no implicit term argument of any lemma could be
inferred; a family's indices can be.  The inversions become one-clause lemmas, and
the decision procedure (`Decision`{.AgdaModule}) pairs each rule with its
inversion.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Whitman where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂
                                                         ; uncurry )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Binary.Structures             using ( IsEquivalence )
open import Relation.Nullary.Decidable.Core        using ( Dec ; map′ ; _×-dec_ ; _⊎-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Term  using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )

private variable
  χ : Level
  X : Type χ
  x y : X
  s s₁ s₂ t t₁ t₂ u u₁ u₂ : LatTerm X
```
-->

#### The rules

The constructors are named by the shapes they relate, with `ℊ` for a generator, `∧`
for a meet, and `∨` for a join; a superscript `ˡ` or `ʳ` marks which child of a
meet on the left, or of a join on the right, the premise is about.  So
`∧ˡ≤∨`{.AgdaInductiveConstructor} is the disjunct of rule 6 that compares the
left meetand with the whole join, and `∧≤∨ˡ`{.AgdaInductiveConstructor} the one
that compares the whole meet with the left joinand.  Rule 3 has two constructors,
`ℊ≤∧`{.AgdaInductiveConstructor} and `∧≤∧`{.AgdaInductiveConstructor}, because a
join on the left is dispatched by rule 2 first; `≤∧`{.AgdaFunction} below states
rule 3 for every left side.  The premise of `ℊ≤ℊ`{.AgdaInductiveConstructor} is an
equation, not an index, so that matching on it never asks the unifier to delete a
reflexive equation, which `--without-K` forbids.

```agda
infix 4 _≤ʷ_

data _≤ʷ_ {X : Type χ} : LatTerm X → LatTerm X → Type χ where
  -- Rule 2: a join on the left.
  ∨≤    : s₁ ≤ʷ t → s₂ ≤ʷ t → s₁ ∨̇ s₂ ≤ʷ t
  -- Rule 3: a meet on the right, for a left side that is not a join.
  ℊ≤∧   : ℊ x ≤ʷ t₁ → ℊ x ≤ʷ t₂ → ℊ x ≤ʷ t₁ ∧̇ t₂
  ∧≤∧   : s₁ ∧̇ s₂ ≤ʷ t₁ → s₁ ∧̇ s₂ ≤ʷ t₂ → s₁ ∧̇ s₂ ≤ʷ t₁ ∧̇ t₂
  -- Rule 1: two generators.
  ℊ≤ℊ   : x ≡ y → ℊ x ≤ʷ ℊ y
  -- Rule 4: a generator below a join.
  ℊ≤∨ˡ  : ℊ x ≤ʷ t₁ → ℊ x ≤ʷ t₁ ∨̇ t₂
  ℊ≤∨ʳ  : ℊ x ≤ʷ t₂ → ℊ x ≤ʷ t₁ ∨̇ t₂
  -- Rule 5: a meet below a generator.
  ∧ˡ≤ℊ  : s₁ ≤ʷ ℊ y → s₁ ∧̇ s₂ ≤ʷ ℊ y
  ∧ʳ≤ℊ  : s₂ ≤ʷ ℊ y → s₁ ∧̇ s₂ ≤ʷ ℊ y
  -- Rule 6, Whitman's condition: a meet below a join.
  ∧ˡ≤∨  : s₁ ≤ʷ t₁ ∨̇ t₂ → s₁ ∧̇ s₂ ≤ʷ t₁ ∨̇ t₂
  ∧ʳ≤∨  : s₂ ≤ʷ t₁ ∨̇ t₂ → s₁ ∧̇ s₂ ≤ʷ t₁ ∨̇ t₂
  ∧≤∨ˡ  : s₁ ∧̇ s₂ ≤ʷ t₁ → s₁ ∧̇ s₂ ≤ʷ t₁ ∨̇ t₂
  ∧≤∨ʳ  : s₁ ∧̇ s₂ ≤ʷ t₂ → s₁ ∧̇ s₂ ≤ʷ t₁ ∨̇ t₂
```

#### Inversion

Each rule is an equivalence, and these lemmas are its other direction: from a
derivation of the conclusion they recover the premises (for rules 1, 2, 4, and 5)
or the disjunct that holds (for rules 4, 5, and 6).  Since the indices of the
constructors follow the dispatch order, a derivation of each conclusion can end
in only the constructors of its own rule, and each proof is a single match.
`∧≤∨-inv`{.AgdaFunction} is Whitman's condition read as a property of
`_≤ʷ_`{.AgdaDatatype}, the form in which free lattices are shown to satisfy (W).

```agda
∨≤-inv : s₁ ∨̇ s₂ ≤ʷ t → s₁ ≤ʷ t × s₂ ≤ʷ t
∨≤-inv (∨≤ p q) = p , q

ℊ≤ℊ-inv : ℊ x ≤ʷ ℊ y → x ≡ y
ℊ≤ℊ-inv (ℊ≤ℊ e) = e

ℊ≤∨-inv : ℊ x ≤ʷ t₁ ∨̇ t₂ → ℊ x ≤ʷ t₁ ⊎ ℊ x ≤ʷ t₂
ℊ≤∨-inv (ℊ≤∨ˡ p) = inj₁ p
ℊ≤∨-inv (ℊ≤∨ʳ p) = inj₂ p

∧≤ℊ-inv : s₁ ∧̇ s₂ ≤ʷ ℊ y → s₁ ≤ʷ ℊ y ⊎ s₂ ≤ʷ ℊ y
∧≤ℊ-inv (∧ˡ≤ℊ p) = inj₁ p
∧≤ℊ-inv (∧ʳ≤ℊ p) = inj₂ p

∧≤∨-inv : s₁ ∧̇ s₂ ≤ʷ t₁ ∨̇ t₂
  → (s₁ ≤ʷ t₁ ∨̇ t₂ ⊎ s₂ ≤ʷ t₁ ∨̇ t₂) ⊎ (s₁ ∧̇ s₂ ≤ʷ t₁ ⊎ s₁ ∧̇ s₂ ≤ʷ t₂)
∧≤∨-inv (∧ˡ≤∨ p) = inj₁ (inj₁ p)
∧≤∨-inv (∧ʳ≤∨ p) = inj₁ (inj₂ p)
∧≤∨-inv (∧≤∨ˡ p) = inj₂ (inj₁ p)
∧≤∨-inv (∧≤∨ʳ p) = inj₂ (inj₂ p)
```

Rule 3 is stated for every left side, although its constructors cover only a
generator or a meet: a join on the left is dispatched by rule 2 first, so for
`s = s₁ ∨ s₂` both directions go through the two joinands.  Its introduction,
`≤∧`{.AgdaFunction}, and its inversion, `≤∧-inv`{.AgdaFunction}, are therefore
proved by induction, on the left term and on the derivation respectively.  In
lattice terms, `≤∧`{.AgdaFunction} says that a formal meet is the greatest of the
lower bounds of its two meetands.

```agda
≤∧ : s ≤ʷ t₁ → s ≤ʷ t₂ → s ≤ʷ t₁ ∧̇ t₂
≤∧ {s = ℊ x}      p          q          = ℊ≤∧ p q
≤∧ {s = s₁ ∧̇ s₂}  p          q          = ∧≤∧ p q
≤∧ {s = s₁ ∨̇ s₂}  (∨≤ p₁ p₂) (∨≤ q₁ q₂) = ∨≤ (≤∧ p₁ q₁) (≤∧ p₂ q₂)

≤∧-inv : s ≤ʷ t₁ ∧̇ t₂ → s ≤ʷ t₁ × s ≤ʷ t₂
≤∧-inv (ℊ≤∧ p q)   = p , q
≤∧-inv (∧≤∧ p q)   = p , q
≤∧-inv (∨≤ p₁ p₂)  = ∨≤ (proj₁ (≤∧-inv p₁)) (proj₁ (≤∧-inv p₂))
                   , ∨≤ (proj₂ (≤∧-inv p₁)) (proj₂ (≤∧-inv p₂))
```

#### Weakening

Two weakening lemmas make room on either side.  On the right, a derivation of
`s ≤ʷ tᵢ` gives `s ≤ʷ t₁ ∨̇ t₂` (`≤∨ˡ`{.AgdaFunction}, `≤∨ʳ`{.AgdaFunction}), by
induction on `s`: a join splits by rule 2, and a generator or a meet uses its own
disjunct of rule 4 or rule 6.  On the left, a derivation of `sᵢ ≤ʷ u` gives
`s₁ ∧̇ s₂ ≤ʷ u` (`∧ˡ≤`{.AgdaFunction}, `∧ʳ≤`{.AgdaFunction}), by induction on `u`:
a meet on the right splits by rule 3 after inverting the premise with
`≤∧-inv`{.AgdaFunction}, and a generator or a join uses its own disjunct of rule 5
or rule 6.  The four lemmas extend the constructors of rules 4, 5, and 6 from the
shapes the dispatch order allows them to every shape.

```agda
≤∨ˡ : s ≤ʷ t₁ → s ≤ʷ t₁ ∨̇ t₂
≤∨ˡ {s = ℊ x}      p           = ℊ≤∨ˡ p
≤∨ˡ {s = s₁ ∧̇ s₂}  p           = ∧≤∨ˡ p
≤∨ˡ {s = s₁ ∨̇ s₂}  (∨≤ p₁ p₂)  = ∨≤ (≤∨ˡ p₁) (≤∨ˡ p₂)

≤∨ʳ : s ≤ʷ t₂ → s ≤ʷ t₁ ∨̇ t₂
≤∨ʳ {s = ℊ x}      p           = ℊ≤∨ʳ p
≤∨ʳ {s = s₁ ∧̇ s₂}  p           = ∧≤∨ʳ p
≤∨ʳ {s = s₁ ∨̇ s₂}  (∨≤ p₁ p₂)  = ∨≤ (≤∨ʳ p₁) (≤∨ʳ p₂)

∧ˡ≤ : s₁ ≤ʷ u → s₁ ∧̇ s₂ ≤ʷ u
∧ˡ≤ {u = ℊ y}      p = ∧ˡ≤ℊ p
∧ˡ≤ {u = u₁ ∨̇ u₂}  p = ∧ˡ≤∨ p
∧ˡ≤ {u = u₁ ∧̇ u₂}  p = ∧≤∧ (∧ˡ≤ (proj₁ (≤∧-inv p))) (∧ˡ≤ (proj₂ (≤∧-inv p)))

∧ʳ≤ : s₂ ≤ʷ u → s₁ ∧̇ s₂ ≤ʷ u
∧ʳ≤ {u = ℊ y}      p = ∧ʳ≤ℊ p
∧ʳ≤ {u = u₁ ∨̇ u₂}  p = ∧ʳ≤∨ p
∧ʳ≤ {u = u₁ ∧̇ u₂}  p = ∧≤∧ (∧ʳ≤ (proj₁ (≤∧-inv p))) (∧ʳ≤ (proj₂ (≤∧-inv p)))
```

#### Reflexivity

Every term is below itself, by induction on the term: a generator by rule 1, a
join by rule 2 with each joinand weakened on the right, and a meet by rule 3 with
each meetand weakened on the left.

```agda
≤ʷ-refl : t ≤ʷ t
≤ʷ-refl {t = ℊ x}      = ℊ≤ℊ refl
≤ʷ-refl {t = t₁ ∨̇ t₂}  = ∨≤ (≤∨ˡ ≤ʷ-refl) (≤∨ʳ ≤ʷ-refl)
≤ʷ-refl {t = t₁ ∧̇ t₂}  = ∧≤∧ (∧ˡ≤ ≤ʷ-refl) (∧ʳ≤ ≤ʷ-refl)
```

#### Transitivity

Transitivity is the one substantial proof.  Given `p : s ≤ʷ t` and `q : t ≤ʷ u`,
the proof cases on the last rule of `p`, which fixes the shapes of `s` and `t`,
as follows:

+  If `s` is a join (rule 2), the proof splits it and recurses on each joinand.
+  If `s` and `t` are generators (rule 1), they are equal, and `q` is the answer.
+  If `p` reduces to `s ≤ʷ tᵢ` for a join `t` (rule 4, or the last two disjuncts
   of rule 6), then `q` must end in rule 2, which supplies `tᵢ ≤ʷ u`, and the
   proof recurses on the two.
+  If `p` reduces to `sᵢ ≤ʷ t` for a meet `s` (rule 5, or the first two
   disjuncts of rule 6), the proof recurses to get `sᵢ ≤ʷ u` and weakens on the
   left.
+  If `t` is a meet (rule 3), `p` supplies `s ≤ʷ t₁` and `s ≤ʷ t₂`, and the
   auxiliary `≤ʷ-trans-∧`{.AgdaFunction} cases on the last rule of `q`.

`≤ʷ-trans-∧`{.AgdaFunction} handles `t₁ ∧̇ t₂ ≤ʷ u` with both premises of rule 3
in hand.  If `u` is a meet (rule 3), it recurses into each meetand and
recombines with `≤∧`{.AgdaFunction}; if `q` reduces to `tᵢ ≤ʷ u` (rule 5, or the
first two disjuncts of rule 6), it composes that with the matching premise; and if
`q` reduces to `t₁ ∧̇ t₂ ≤ʷ uⱼ` (the last two disjuncts of rule 6), it recurses
and weakens on the right.  The auxiliary takes the premises `s ≤ʷ t₁` and
`s ≤ʷ t₂` apart rather than the derivation of `s ≤ʷ t₁ ∧̇ t₂` whole, so that
every call, of either function by the other or by itself, passes in each
argument the same derivation or a structurally smaller one, and in at least one
argument a smaller one; that is the measure Agda's termination checker finds.
This is where the dispatch order earns its keep: once a join on the left has
been split, rule 3 is the only rule whose conclusion has a meet on the right, so
the premises `s ≤ʷ t₁` and `s ≤ʷ t₂` are the arguments of the last constructor
of `p`, available without the induction of `≤∧-inv`{.AgdaFunction}.

```agda
≤ʷ-trans    : s ≤ʷ t → t ≤ʷ u → s ≤ʷ u
≤ʷ-trans-∧  : s ≤ʷ t₁ → s ≤ʷ t₂ → t₁ ∧̇ t₂ ≤ʷ u → s ≤ʷ u

≤ʷ-trans (∨≤ p₁ p₂)   q           = ∨≤ (≤ʷ-trans p₁ q) (≤ʷ-trans p₂ q)
≤ʷ-trans (ℊ≤ℊ refl)   q           = q
≤ʷ-trans (ℊ≤∧ p₁ p₂)  q           = ≤ʷ-trans-∧ p₁ p₂ q
≤ʷ-trans (∧≤∧ p₁ p₂)  q           = ≤ʷ-trans-∧ p₁ p₂ q
≤ʷ-trans (ℊ≤∨ˡ p₁)    (∨≤ q₁ q₂)  = ≤ʷ-trans p₁ q₁
≤ʷ-trans (ℊ≤∨ʳ p₂)    (∨≤ q₁ q₂)  = ≤ʷ-trans p₂ q₂
≤ʷ-trans (∧ˡ≤ℊ p₁)    q           = ∧ˡ≤ (≤ʷ-trans p₁ q)
≤ʷ-trans (∧ʳ≤ℊ p₂)    q           = ∧ʳ≤ (≤ʷ-trans p₂ q)
≤ʷ-trans (∧ˡ≤∨ p₁)    q           = ∧ˡ≤ (≤ʷ-trans p₁ q)
≤ʷ-trans (∧ʳ≤∨ p₂)    q           = ∧ʳ≤ (≤ʷ-trans p₂ q)
≤ʷ-trans (∧≤∨ˡ p₁)    (∨≤ q₁ q₂)  = ≤ʷ-trans p₁ q₁
≤ʷ-trans (∧≤∨ʳ p₂)    (∨≤ q₁ q₂)  = ≤ʷ-trans p₂ q₂

≤ʷ-trans-∧ p₁ p₂ (∧≤∧ q₁ q₂)  = ≤∧ (≤ʷ-trans-∧ p₁ p₂ q₁) (≤ʷ-trans-∧ p₁ p₂ q₂)
≤ʷ-trans-∧ p₁ p₂ (∧ˡ≤ℊ q₁)    = ≤ʷ-trans p₁ q₁
≤ʷ-trans-∧ p₁ p₂ (∧ʳ≤ℊ q₂)    = ≤ʷ-trans p₂ q₂
≤ʷ-trans-∧ p₁ p₂ (∧ˡ≤∨ q₁)    = ≤ʷ-trans p₁ q₁
≤ʷ-trans-∧ p₁ p₂ (∧ʳ≤∨ q₂)    = ≤ʷ-trans p₂ q₂
≤ʷ-trans-∧ p₁ p₂ (∧≤∨ˡ q₁)    = ≤∨ˡ (≤ʷ-trans-∧ p₁ p₂ q₁)
≤ʷ-trans-∧ p₁ p₂ (∧≤∨ʳ q₂)    = ≤∨ʳ (≤ʷ-trans-∧ p₁ p₂ q₂)
```

#### Meet and join are infimum and supremum

With reflexivity in hand, the weakening lemmas say that a formal join lies above
its joinands (`∨̇-upperˡ`{.AgdaFunction}, `∨̇-upperʳ`{.AgdaFunction}) and a formal
meet below its meetands (`∧̇-lowerˡ`{.AgdaFunction}, `∧̇-lowerʳ`{.AgdaFunction}).
The other halves of the two characterizations are rules already: rule 2,
`∨≤`{.AgdaInductiveConstructor}, says a join is below every common upper bound of
its joinands, and `≤∧`{.AgdaFunction} says a meet is above every common lower
bound of its meetands.

```agda
∨̇-upperˡ : s ≤ʷ s ∨̇ t
∨̇-upperˡ = ≤∨ˡ ≤ʷ-refl

∨̇-upperʳ : t ≤ʷ s ∨̇ t
∨̇-upperʳ = ≤∨ʳ ≤ʷ-refl

∧̇-lowerˡ : s ∧̇ t ≤ʷ s
∧̇-lowerˡ = ∧ˡ≤ ≤ʷ-refl

∧̇-lowerʳ : s ∧̇ t ≤ʷ t
∧̇-lowerʳ = ∧ʳ≤ ≤ʷ-refl
```

#### Equality in the free lattice

Two terms name the same element of `FL(X)` when each is below the other.
`_≈ʷ_`{.AgdaFunction} is that relation, an equivalence by reflexivity and
transitivity of `_≤ʷ_`{.AgdaDatatype} (`≈ʷ-isEquivalence`{.AgdaFunction}).

```agda
infix 4 _≈ʷ_

_≈ʷ_ : {X : Type χ} → LatTerm X → LatTerm X → Type χ
s ≈ʷ t = s ≤ʷ t × t ≤ʷ s

≈ʷ-isEquivalence : IsEquivalence (_≈ʷ_ {X = X})
≈ʷ-isEquivalence = record
  { refl   = ≤ʷ-refl , ≤ʷ-refl
  ; sym    = λ (p , q) → q , p
  ; trans  = λ (p , q) (p' , q') → ≤ʷ-trans p p' , ≤ʷ-trans q' q
  }
```

#### Deciding the order

Given decidable equality of generators, `s ≤ʷ? t`{.AgdaFunction} decides
`s ≤ʷ t`, by the same recursion as the rules: each clause decides the premises
of one rule, combines the answers by `_×-dec_`{.AgdaFunction} or
`_⊎-dec_`{.AgdaFunction} as the rule is a conjunction or a disjunction, and
transports the answer along the rule and its inversion with
`map′`{.AgdaFunction}.  The recursion is the lexicographic structural descent
described above.  Its positive answers are derivations, built as it runs, and
its negative answers are refutations, so `does (s ≤ʷ? t)` computes the verdict
by evaluation, and `from-yes` or `from-no` turns a closed instance into a proof.
Equality in `FL(X)` is then decided by two calls (`_≈ʷ?_`{.AgdaFunction}).  This
is the solution of the word problem proper: two terms are equal in every lattice
under every assignment exactly when `s ≈ʷ? t` answers `yes`.  The module
`Decision`{.AgdaModule} takes the decision procedure for equality of generators
as its parameter.

```agda
module Decision {X : Type χ} (_≟_ : DecidableEquality X) where
  infix 4 _≤ʷ?_ _≈ʷ?_

  _≤ʷ?_ : (s t : LatTerm X) → Dec (s ≤ʷ t)
  (s₁ ∨̇ s₂)    ≤ʷ? t            = map′ (uncurry ∨≤) ∨≤-inv (s₁ ≤ʷ? t ×-dec s₂ ≤ʷ? t)
  s@(ℊ x)      ≤ʷ? (t₁ ∧̇ t₂)    = map′ (uncurry ℊ≤∧) ≤∧-inv (s ≤ʷ? t₁ ×-dec s ≤ʷ? t₂)
  s@(s₁ ∧̇ s₂)  ≤ʷ? (t₁ ∧̇ t₂)    = map′ (uncurry ∧≤∧) ≤∧-inv (s ≤ʷ? t₁ ×-dec s ≤ʷ? t₂)
  ℊ x          ≤ʷ? ℊ y          = map′ ℊ≤ℊ ℊ≤ℊ-inv (x ≟ y)
  s@(ℊ x)      ≤ʷ? (t₁ ∨̇ t₂)    = map′ [ ℊ≤∨ˡ , ℊ≤∨ʳ ]′ ℊ≤∨-inv (s ≤ʷ? t₁ ⊎-dec s ≤ʷ? t₂)
  (s₁ ∧̇ s₂)    ≤ʷ? t@(ℊ y)      = map′ [ ∧ˡ≤ℊ , ∧ʳ≤ℊ ]′ ∧≤ℊ-inv (s₁ ≤ʷ? t ⊎-dec s₂ ≤ʷ? t)
  s@(s₁ ∧̇ s₂)  ≤ʷ? t@(t₁ ∨̇ t₂)  =
    map′ [ [ ∧ˡ≤∨ , ∧ʳ≤∨ ]′ , [ ∧≤∨ˡ , ∧≤∨ʳ ]′ ]′ ∧≤∨-inv
         ((s₁ ≤ʷ? t ⊎-dec s₂ ≤ʷ? t) ⊎-dec (s ≤ʷ? t₁ ⊎-dec s ≤ʷ? t₂))

  _≈ʷ?_ : (s t : LatTerm X) → Dec (s ≈ʷ t)
  s ≈ʷ? t = s ≤ʷ? t ×-dec t ≤ʷ? s
```
