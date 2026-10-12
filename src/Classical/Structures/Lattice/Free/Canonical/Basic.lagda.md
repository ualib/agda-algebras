---
layout: default
file: "src/Classical/Structures/Lattice/Free/Canonical/Basic.lagda.md"
title: "Classical.Structures.Lattice.Free.Canonical.Basic module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Canonical terms

This is the [Classical.Structures.Lattice.Free.Canonical.Basic][] module of the [Agda Universal Algebra Library][].

Every element of a free lattice has a term of minimal rank representing it,
unique up to commutativity, its *canonical form* ([Freese, Ježek, and Nation
(1995)][], Theorem 1.17), and Theorem 1.18 characterizes that form syntactically.
A join `t = t₁ ∨ ⋯ ∨ tₙ` with `n > 1` is in canonical form if and only if the
following four conditions hold:

1.  each `tᵢ` is a generator or a formal meet;
2.  each `tᵢ` is in canonical form;
3.  the `tᵢ` form an antichain (`tᵢ ≰ tⱼ` for `i ≠ j`);
4.  if `tᵢ = ⋀ⱼ tᵢⱼ`, then `tᵢⱼ ≰ t` for every `j`.

A meet is in canonical form if and only if the duals of the four conditions hold,
and a generator is always in canonical form.

This module supplies the vocabulary the rest of the canonical-form development
speaks: the type of canonical terms, their embedding into the lattice terms of
[Classical.Structures.Lattice.Free.Term][], their rank, the predicate
`IsCanonical`{.AgdaDatatype} that states the four conditions, the bounds that the
join and meet of a list obey under Whitman's order, and the duality that
exchanges joins and meets.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Canonical.Basic where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( ℕ ; suc ; _+_ ; _≤_ )
open import Data.Nat.Properties                    using ( ≤-refl ; n≤1+n )
open import Data.Product                           using ( _×_ ; _,_ ; Σ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; cong
                                                         ; cong₂ ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )

import Data.List.Relation.Unary.Any             as Any
import Data.List.Relation.Unary.Any.Properties  as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Free.Duality  using ( dual ; dual-reflects )
open import Classical.Structures.Lattice.Free.Term     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Classical.Structures.Lattice.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ∧ˡ≤∨ ; ∧ʳ≤∨ ; ∧≤∨ˡ ; ∧≤∨ʳ ; ℊ≤∨-inv ; ∧≤ℊ-inv ; ≤∧
         ; ≤ʷ-refl ; ≤ʷ-trans ; ∨̇-upperˡ ; ∨̇-upperʳ ; ∧̇-lowerˡ ; ∧̇-lowerʳ )

private variable
  χ : Level
  X : Type χ
  x : X
  s t u v z : LatTerm X
```
-->

#### The type of canonical terms

`CTerm X`{.AgdaDatatype} has three constructors: `genᶜ`{.AgdaInductiveConstructor}
embeds a generator, and `joinᶜ`{.AgdaInductiveConstructor} and
`meetᶜ`{.AgdaInductiveConstructor} form the join and the meet of a nonempty family
of children, given as a first child and a list of the rest.  The children of a join
have type `CJand X`{.AgdaDatatype}, whose values are a generator
(`jgen`{.AgdaInductiveConstructor}) or a formal meet
(`jmeet`{.AgdaInductiveConstructor}); dually the children of a meet have type
`CMand X`{.AgdaDatatype}, a generator (`mgen`{.AgdaInductiveConstructor}) or a
formal join (`mjoin`{.AgdaInductiveConstructor}).  A join of joins and a meet of
meets are therefore not representable, so condition 1 of Theorem 1.18 holds by
construction, and joins and meets are flattened, as the terms of [Freese, Ježek,
and Nation (1995)][], Section I.2, are.

Nonemptiness is structural too.  Carrying the first child separately makes every
recursion over the children an ordinary structural recursion on a
`List`{.AgdaDatatype}; the standard library's `List⁺`{.AgdaRecord} is a record, and
a recursion through its fields does not pass the termination checker in the
mutual definitions below.

```agda
data CTerm (X : Type χ) : Type χ
data CJand (X : Type χ) : Type χ
data CMand (X : Type χ) : Type χ

data CTerm X where
  genᶜ   : X → CTerm X
  joinᶜ  : CJand X → List (CJand X) → CTerm X
  meetᶜ  : CMand X → List (CMand X) → CTerm X

data CJand X where
  jgen   : X → CJand X
  jmeet  : CMand X → List (CMand X) → CJand X

data CMand X where
  mgen   : X → CMand X
  mjoin  : CJand X → List (CJand X) → CMand X
```

#### Embedding into lattice terms

Each canonical term denotes a lattice term: `⌊_⌋`{.AgdaFunction} folds the child
lists with the formal operations `_∨̇_`{.AgdaInductiveConstructor} and
`_∧̇_`{.AgdaInductiveConstructor}, associating to the right.  The folds
`⋁ᴶ`{.AgdaFunction} and `⋀ᴹ`{.AgdaFunction} are defined by structural recursion
on the tail, in the same mutual block as the embedding, since the termination
checker does not accept the same recursion written through
`map`{.AgdaFunction} and a generic fold.  Everything later said about the element
of `FL X`{.AgdaFunction} a canonical term represents is said through this
embedding.

```agda
⌊_⌋   : CTerm X → LatTerm X
⌊_⌋ᴶ  : CJand X → LatTerm X
⌊_⌋ᴹ  : CMand X → LatTerm X
⋁ᴶ    : CJand X → List (CJand X) → LatTerm X
⋀ᴹ    : CMand X → List (CMand X) → LatTerm X

⌊ genᶜ x ⌋      = ℊ x
⌊ joinᶜ h t ⌋   = ⋁ᴶ h t
⌊ meetᶜ h t ⌋   = ⋀ᴹ h t
⌊ jgen x ⌋ᴶ     = ℊ x
⌊ jmeet h t ⌋ᴶ  = ⋀ᴹ h t
⌊ mgen x ⌋ᴹ     = ℊ x
⌊ mjoin h t ⌋ᴹ  = ⋁ᴶ h t

⋁ᴶ h []        = ⌊ h ⌋ᴶ
⋁ᴶ h (a ∷ as)  = ⌊ h ⌋ᴶ ∨̇ ⋁ᴶ a as
⋀ᴹ h []        = ⌊ h ⌋ᴹ
⋀ᴹ h (a ∷ as)  = ⌊ h ⌋ᴹ ∧̇ ⋀ᴹ a as
```

#### Rank

[Freese, Ježek, and Nation (1995)][], Section I.2, measure a term by its *rank*,
which counts the occurrences of generators plus the pairs of parentheses.  On a
flattened term this reads: a generator has rank 1, and a join or meet of `k`
children has rank one more than the sum of their ranks.  `crankΣJ`{.AgdaFunction}
and `crankΣM`{.AgdaFunction} sum the ranks of a list of children; the first is the
termination measure of the canonicalization algorithm.

```agda
crank    : CTerm X → ℕ
crankJ   : CJand X → ℕ
crankM   : CMand X → ℕ
crankΣJ  : List (CJand X) → ℕ
crankΣM  : List (CMand X) → ℕ

crank (genᶜ x)      = 1
crank (joinᶜ h t)   = suc (crankJ h + crankΣJ t)
crank (meetᶜ h t)   = suc (crankM h + crankΣM t)
crankJ (jgen x)     = 1
crankJ (jmeet h t)  = suc (crankM h + crankΣM t)
crankM (mgen x)     = 1
crankM (mjoin h t)  = suc (crankJ h + crankΣJ t)
crankΣJ []          = 0
crankΣJ (a ∷ as)    = crankJ a + crankΣJ as
crankΣM []          = 0
crankΣM (a ∷ as)    = crankM a + crankΣM as
```

#### Equality in the free lattice

The proofs about canonical terms rearrange joins and meets up to equality in the
free lattice, `_≈ʷ_`{.AgdaFunction} of [Classical.Structures.Lattice.Free.Whitman][].
The three properties of an equivalence get names of their own
(`≈ʷ-refl`{.AgdaFunction}, `≈ʷ-sym`{.AgdaFunction}, `≈ʷ-trans`{.AgdaFunction}),
and formal join and meet are congruences, commutative, and associative up to
`_≈ʷ_`{.AgdaFunction}, each by the supremum and infimum properties of the formal
operations.

```agda
≈ʷ-refl : t ≈ʷ t
≈ʷ-refl = ≤ʷ-refl , ≤ʷ-refl

≈ʷ-sym : s ≈ʷ t → t ≈ʷ s
≈ʷ-sym (p , q) = q , p

≈ʷ-trans : s ≈ʷ t → t ≈ʷ u → s ≈ʷ u
≈ʷ-trans (p , q) (p' , q') = ≤ʷ-trans p p' , ≤ʷ-trans q' q

∨̇-cong : s ≈ʷ u → t ≈ʷ v → s ∨̇ t ≈ʷ u ∨̇ v
∨̇-cong (p₁ , p₂) (q₁ , q₂) =
  ∨≤ (≤ʷ-trans p₁ ∨̇-upperˡ) (≤ʷ-trans q₁ ∨̇-upperʳ) ,
  ∨≤ (≤ʷ-trans p₂ ∨̇-upperˡ) (≤ʷ-trans q₂ ∨̇-upperʳ)

∧̇-cong : s ≈ʷ u → t ≈ʷ v → s ∧̇ t ≈ʷ u ∧̇ v
∧̇-cong (p₁ , p₂) (q₁ , q₂) =
  ≤∧ (≤ʷ-trans ∧̇-lowerˡ p₁) (≤ʷ-trans ∧̇-lowerʳ q₁) ,
  ≤∧ (≤ʷ-trans ∧̇-lowerˡ p₂) (≤ʷ-trans ∧̇-lowerʳ q₂)

∨̇-comm : s ∨̇ t ≈ʷ t ∨̇ s
∨̇-comm = ∨≤ ∨̇-upperʳ ∨̇-upperˡ , ∨≤ ∨̇-upperʳ ∨̇-upperˡ

∧̇-comm : s ∧̇ t ≈ʷ t ∧̇ s
∧̇-comm = ≤∧ ∧̇-lowerʳ ∧̇-lowerˡ , ≤∧ ∧̇-lowerʳ ∧̇-lowerˡ

∨̇-assoc : (s ∨̇ t) ∨̇ u ≈ʷ s ∨̇ (t ∨̇ u)
∨̇-assoc =
  ∨≤ (∨≤ ∨̇-upperˡ (≤ʷ-trans ∨̇-upperˡ ∨̇-upperʳ)) (≤ʷ-trans ∨̇-upperʳ ∨̇-upperʳ) ,
  ∨≤ (≤ʷ-trans ∨̇-upperˡ ∨̇-upperˡ) (∨≤ (≤ʷ-trans ∨̇-upperʳ ∨̇-upperˡ) ∨̇-upperʳ)

∧̇-assoc : (s ∧̇ t) ∧̇ u ≈ʷ s ∧̇ (t ∧̇ u)
∧̇-assoc =
  ≤∧ (≤ʷ-trans ∧̇-lowerˡ ∧̇-lowerˡ) (≤∧ (≤ʷ-trans ∧̇-lowerˡ ∧̇-lowerʳ) ∧̇-lowerʳ) ,
  ≤∧ (≤∧ ∧̇-lowerˡ (≤ʷ-trans ∧̇-lowerʳ ∧̇-lowerˡ)) (≤ʷ-trans ∧̇-lowerʳ ∧̇-lowerʳ)
```

#### Joins and meets of lists of lattice terms

Theorem 1.19 speaks of an arbitrary join representation `w = u₁ ∨ ⋯ ∨ uₘ`, so the
development needs the join and the meet of a nonempty list of lattice terms,
`⋁⁺`{.AgdaFunction} and `⋀⁺`{.AgdaFunction}, given as a first term and a list of
the rest.  Their bounds are the list forms of the supremum and infimum properties
of [Classical.Structures.Lattice.Free.Whitman][]: every member lies below the join
(`⋁⁺-upper`{.AgdaFunction}), the join lies below every common upper bound of the
members (`⋁⁺-least`{.AgdaFunction}), and dually (`⋀⁺-lower`{.AgdaFunction},
`⋀⁺-greatest`{.AgdaFunction}).

```agda
⋁⁺ : LatTerm X → List (LatTerm X) → LatTerm X
⋁⁺ u []        = u
⋁⁺ u (w ∷ ws)  = u ∨̇ ⋁⁺ w ws

⋀⁺ : LatTerm X → List (LatTerm X) → LatTerm X
⋀⁺ u []        = u
⋀⁺ u (w ∷ ws)  = u ∧̇ ⋀⁺ w ws

private variable
  w : LatTerm X
  ws : List (LatTerm X)

⋁⁺-upper : u ∈ (w ∷ ws) → u ≤ʷ ⋁⁺ w ws
⋁⁺-upper {ws = []}      (here refl)  = ≤ʷ-refl
⋁⁺-upper {ws = _ ∷ _}   (here refl)  = ∨̇-upperˡ
⋁⁺-upper {ws = _ ∷ _}   (there u∈)   = ≤ʷ-trans (⋁⁺-upper u∈) ∨̇-upperʳ

⋁⁺-least : (∀ {u} → u ∈ (w ∷ ws) → u ≤ʷ z) → ⋁⁺ w ws ≤ʷ z
⋁⁺-least {ws = []}      f = f (here refl)
⋁⁺-least {ws = _ ∷ _}   f = ∨≤ (f (here refl)) (⋁⁺-least λ u∈ → f (there u∈))

⋀⁺-lower : u ∈ (w ∷ ws) → ⋀⁺ w ws ≤ʷ u
⋀⁺-lower {ws = []}      (here refl)  = ≤ʷ-refl
⋀⁺-lower {ws = _ ∷ _}   (here refl)  = ∧̇-lowerˡ
⋀⁺-lower {ws = _ ∷ _}   (there u∈)   = ≤ʷ-trans ∧̇-lowerʳ (⋀⁺-lower u∈)

⋀⁺-greatest : (∀ {u} → u ∈ (w ∷ ws) → z ≤ʷ u) → z ≤ʷ ⋀⁺ w ws
⋀⁺-greatest {ws = []}     f = f (here refl)
⋀⁺-greatest {ws = _ ∷ _}  f = ≤∧ (f (here refl)) (⋀⁺-greatest λ u∈ → f (there u∈))
```

Rules 4 and 5 of Whitman's procedure, read along a list, say that a generator
below a join lies below one of the joinands (`gen-⋁⁺-prime`{.AgdaFunction}: the
generators are join prime) and that a meet below a generator has a meetand below
it (`⋀⁺-gen-below`{.AgdaFunction}: the generators are meet prime).  Rule 6,
Whitman's condition, read along two lists, is `W-list`{.AgdaFunction}: a meet of
a list below a join of a list either has a meetand below the whole join or lies
below one of the joinands.  It is the engine of Lemma 1.16.  Its recursion
descends on the two tails lexicographically, as the transitivity proof of
[Classical.Structures.Lattice.Free.Whitman][] descends on its two derivations,
and it matches on the constructors of rule 6 directly.

```agda
gen-⋁⁺-prime : ℊ x ≤ʷ ⋁⁺ w ws → Any (ℊ x ≤ʷ_) (w ∷ ws)
gen-⋁⁺-prime {ws = []}     p = here p
gen-⋁⁺-prime {ws = _ ∷ _}  p with ℊ≤∨-inv p
... | inj₁ q = here q
... | inj₂ q = there (gen-⋁⁺-prime q)

⋀⁺-gen-below : ⋀⁺ w ws ≤ʷ ℊ x → Any (_≤ʷ ℊ x) (w ∷ ws)
⋀⁺-gen-below {ws = []}     p = here p
⋀⁺-gen-below {ws = _ ∷ _}  p with ∧≤ℊ-inv p
... | inj₁ q = here q
... | inj₂ q = there (⋀⁺-gen-below q)

W-list : (ms js : List (LatTerm X)) {m j : LatTerm X} → ⋀⁺ m ms ≤ʷ ⋁⁺ j js
       → Any (_≤ʷ ⋁⁺ j js) (m ∷ ms) ⊎ Any (⋀⁺ m ms ≤ʷ_) (j ∷ js)
W-list []         _          p = inj₁ (here p)
W-list (_ ∷ _)    []         p = inj₂ (here p)
W-list (_ ∷ _)    (_ ∷ _)    (∧ˡ≤∨ q)  = inj₁ (here q)
W-list (_ ∷ ms)   js@(_ ∷ _) (∧ʳ≤∨ q)  with W-list ms js q
... | inj₁ r = inj₁ (there r)
... | inj₂ r = inj₂ (Any.map (≤ʷ-trans ∧̇-lowerʳ) r)
W-list (_ ∷ _)    (_ ∷ _)    (∧≤∨ˡ q)  = inj₂ (here q)
W-list ms@(_ ∷ _) (_ ∷ js)   (∧≤∨ʳ q)  with W-list ms js q
... | inj₁ r = inj₁ (Any.map (λ p → ≤ʷ-trans p ∨̇-upperʳ) r)
... | inj₂ r = inj₂ (there r)
```

#### Joins and meets of children

The child folds `⋁ᴶ`{.AgdaFunction} and `⋀ᴹ`{.AgdaFunction} of the embedding obey
the same bounds (`⋁ᴶ-upper`{.AgdaFunction}, `⋁ᴶ-least`{.AgdaFunction},
`⋀ᴹ-lower`{.AgdaFunction}, `⋀ᴹ-greatest`{.AgdaFunction}).  A consequence used
throughout is *domination*: if every child of one join lies below some child of
another, the first join lies below the second (`⋁ᴶ-dom`{.AgdaFunction}), and
dually for meets (`⋀ᴹ-dom`{.AgdaFunction}).  This is part (1) of [Freese, Ježek,
and Nation (1995)][], Lemma 1.15: join refinement implies the inequality of the
joins.

```agda
⋁ᴶ-upper : {h a : CJand X} {t : List (CJand X)} → a ∈ (h ∷ t) → ⌊ a ⌋ᴶ ≤ʷ ⋁ᴶ h t
⋁ᴶ-upper {t = []}     (here refl)  = ≤ʷ-refl
⋁ᴶ-upper {t = _ ∷ _}  (here refl)  = ∨̇-upperˡ
⋁ᴶ-upper {t = _ ∷ _}  (there a∈)   = ≤ʷ-trans (⋁ᴶ-upper a∈) ∨̇-upperʳ

⋁ᴶ-least : {h : CJand X} {t : List (CJand X)}
         → (∀ {a} → a ∈ (h ∷ t) → ⌊ a ⌋ᴶ ≤ʷ z) → ⋁ᴶ h t ≤ʷ z
⋁ᴶ-least {t = []}     f = f (here refl)
⋁ᴶ-least {t = _ ∷ _}  f = ∨≤ (f (here refl)) (⋁ᴶ-least λ a∈ → f (there a∈))

⋀ᴹ-lower : {h a : CMand X} {t : List (CMand X)} → a ∈ (h ∷ t) → ⋀ᴹ h t ≤ʷ ⌊ a ⌋ᴹ
⋀ᴹ-lower {t = []}     (here refl)  = ≤ʷ-refl
⋀ᴹ-lower {t = _ ∷ _}  (here refl)  = ∧̇-lowerˡ
⋀ᴹ-lower {t = _ ∷ _}  (there a∈)   = ≤ʷ-trans ∧̇-lowerʳ (⋀ᴹ-lower a∈)

⋀ᴹ-greatest : {h : CMand X} {t : List (CMand X)}
            → (∀ {a} → a ∈ (h ∷ t) → z ≤ʷ ⌊ a ⌋ᴹ) → z ≤ʷ ⋀ᴹ h t
⋀ᴹ-greatest {t = []}     f = f (here refl)
⋀ᴹ-greatest {t = _ ∷ _}  f = ≤∧ (f (here refl)) (⋀ᴹ-greatest λ a∈ → f (there a∈))

⋁ᴶ-dom : {h h' : CJand X} {t t' : List (CJand X)}
       → (∀ {a} → a ∈ (h ∷ t) → Any (λ b → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ) (h' ∷ t'))
       → ⋁ᴶ h t ≤ʷ ⋁ᴶ h' t'
⋁ᴶ-dom f = ⋁ᴶ-least λ a∈ → let (_ , b∈ , p) = find (f a∈) in ≤ʷ-trans p (⋁ᴶ-upper b∈)

⋀ᴹ-dom : {h h' : CMand X} {t t' : List (CMand X)}
       → (∀ {b} → b ∈ (h' ∷ t') → Any (λ a → ⌊ a ⌋ᴹ ≤ʷ ⌊ b ⌋ᴹ) (h ∷ t))
       → ⋀ᴹ h t ≤ʷ ⋀ᴹ h' t'
⋀ᴹ-dom f = ⋀ᴹ-greatest λ b∈ → let (_ , a∈ , p) = find (f b∈) in ≤ʷ-trans (⋀ᴹ-lower a∈) p
```

A child fold is the list fold of the embedded children (`⋁ᴶ≡⋁⁺`{.AgdaFunction},
`⋀ᴹ≡⋀⁺`{.AgdaFunction}), and through these two equations the list forms of rules
4, 5, and 6 apply to children: a generator below a join of children lies below one
of them (`gen-⋁ᴶ-prime`{.AgdaFunction}), a meet of children below a generator has a
child below it (`⋀ᴹ-gen-below`{.AgdaFunction}), and `W-list`{.AgdaFunction} holds
for the three mixed shapes the later proofs need: a meet of children below a join
of lattice terms (`W-list-ᴹ⁺`{.AgdaFunction}, the case of Lemma 1.16), a meet of
lattice terms below a join of children (`W-list-⁺ᴶ`{.AgdaFunction}, its dual), and
a meet of children below a join of children (`W-list-ᴹᴶ`{.AgdaFunction}).

```agda
⋁ᴶ≡⋁⁺ : (h : CJand X) (t : List (CJand X)) → ⋁ᴶ h t ≡ ⋁⁺ ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t)
⋁ᴶ≡⋁⁺ h []        = refl
⋁ᴶ≡⋁⁺ h (a ∷ as)  = cong (⌊ h ⌋ᴶ ∨̇_) (⋁ᴶ≡⋁⁺ a as)

⋀ᴹ≡⋀⁺ : (h : CMand X) (t : List (CMand X)) → ⋀ᴹ h t ≡ ⋀⁺ ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t)
⋀ᴹ≡⋀⁺ h []        = refl
⋀ᴹ≡⋀⁺ h (a ∷ as)  = cong (⌊ h ⌋ᴹ ∧̇_) (⋀ᴹ≡⋀⁺ a as)

gen-⋁ᴶ-prime : {h : CJand X} {t : List (CJand X)}
             → ℊ x ≤ʷ ⋁ᴶ h t → Any (λ a → ℊ x ≤ʷ ⌊ a ⌋ᴶ) (h ∷ t)
gen-⋁ᴶ-prime {h = h} {t} p =
  Any.map⁻ (gen-⋁⁺-prime (subst (ℊ _ ≤ʷ_) (⋁ᴶ≡⋁⁺ h t) p))

⋀ᴹ-gen-below : {h : CMand X} {t : List (CMand X)}
             → ⋀ᴹ h t ≤ʷ ℊ x → Any (λ a → ⌊ a ⌋ᴹ ≤ʷ ℊ x) (h ∷ t)
⋀ᴹ-gen-below {h = h} {t} p =
  Any.map⁻ (⋀⁺-gen-below (subst (_≤ʷ ℊ _) (⋀ᴹ≡⋀⁺ h t) p))

W-list-ᴹ⁺ : {h : CMand X} {t : List (CMand X)} → ⋀ᴹ h t ≤ʷ ⋁⁺ w ws
          → Any (λ a → ⌊ a ⌋ᴹ ≤ʷ ⋁⁺ w ws) (h ∷ t) ⊎ Any (⋀ᴹ h t ≤ʷ_) (w ∷ ws)
W-list-ᴹ⁺ {w = w} {ws} {h} {t} p
  with W-list (map ⌊_⌋ᴹ t) ws (subst (_≤ʷ ⋁⁺ w ws) (⋀ᴹ≡⋀⁺ h t) p)
... | inj₁ r = inj₁ (Any.map⁻ r)
... | inj₂ r = inj₂ (Any.map (subst (_≤ʷ _) (sym (⋀ᴹ≡⋀⁺ h t))) r)

W-list-⁺ᴶ : {h : CJand X} {t : List (CJand X)} → ⋀⁺ w ws ≤ʷ ⋁ᴶ h t
          → Any (_≤ʷ ⋁ᴶ h t) (w ∷ ws) ⊎ Any (λ a → ⋀⁺ w ws ≤ʷ ⌊ a ⌋ᴶ) (h ∷ t)
W-list-⁺ᴶ {w = w} {ws} {h} {t} p
  with W-list ws (map ⌊_⌋ᴶ t) (subst (⋀⁺ w ws ≤ʷ_) (⋁ᴶ≡⋁⁺ h t) p)
... | inj₁ r = inj₁ (Any.map (subst (_ ≤ʷ_) (sym (⋁ᴶ≡⋁⁺ h t))) r)
... | inj₂ r = inj₂ (Any.map⁻ r)

W-list-ᴹᴶ : {mh : CMand X} {mt : List (CMand X)} {jh : CJand X} {jt : List (CJand X)}
          → ⋀ᴹ mh mt ≤ʷ ⋁ᴶ jh jt
          → Any (λ a → ⌊ a ⌋ᴹ ≤ʷ ⋁ᴶ jh jt) (mh ∷ mt) ⊎ Any (λ b → ⋀ᴹ mh mt ≤ʷ ⌊ b ⌋ᴶ) (jh ∷ jt)
W-list-ᴹᴶ {mh = mh} {mt} {jh} {jt} p
  with W-list-ᴹ⁺ (subst (⋀ᴹ mh mt ≤ʷ_) (⋁ᴶ≡⋁⁺ jh jt) p)
... | inj₁ r = inj₁ (Any.map (subst (_ ≤ʷ_) (sym (⋁ᴶ≡⋁⁺ jh jt))) r)
... | inj₂ r = inj₂ (Any.map⁻ r)
```

#### The canonicality predicate

`IsCanonical`{.AgdaDatatype} is Theorem 1.18 read as a predicate on canonical
terms.  Condition 1 is the type; condition 2 is the mutual recursion of the
predicate through `IsCanonicalJ`{.AgdaDatatype} and `IsCanonicalM`{.AgdaDatatype};
condition 3 is `AntichainJ`{.AgdaFunction} (and `AntichainM`{.AgdaFunction} for
meets), the pairwise incomparability of the children, stated with
`AllPairs`{.AgdaDatatype}; and condition 4 is `Cond4J`{.AgdaFunction} (and its dual
`Cond4M`{.AgdaFunction}).  A join or meet must have at least two children (the
tail is not empty), matching the `n > 1` of the theorem: a join of one child is
that child.

```agda
_≰ʷ_ : {X : Type χ} → LatTerm X → LatTerm X → Type χ
s ≰ʷ t = ¬ (s ≤ʷ t)

AntichainJ : {X : Type χ} → List (CJand X) → Type χ
AntichainJ = AllPairs λ a b → (⌊ a ⌋ᴶ ≰ʷ ⌊ b ⌋ᴶ) × (⌊ b ⌋ᴶ ≰ʷ ⌊ a ⌋ᴶ)

AntichainM : {X : Type χ} → List (CMand X) → Type χ
AntichainM = AllPairs λ a b → (⌊ a ⌋ᴹ ≰ʷ ⌊ b ⌋ᴹ) × (⌊ b ⌋ᴹ ≰ʷ ⌊ a ⌋ᴹ)

Cond4J : {X : Type χ} → CJand X → List (CJand X) → Type χ
Cond4J h t = ∀ {mh mt m} → jmeet mh mt ∈ (h ∷ t) → m ∈ (mh ∷ mt) → ⌊ m ⌋ᴹ ≰ʷ ⋁ᴶ h t

Cond4M : {X : Type χ} → CMand X → List (CMand X) → Type χ
Cond4M h t = ∀ {jh jt j} → mjoin jh jt ∈ (h ∷ t) → j ∈ (jh ∷ jt) → ⋀ᴹ h t ≰ʷ ⌊ j ⌋ᴶ

private variable
  jh : CJand X
  jt : List (CJand X)
  mh : CMand X
  mt : List (CMand X)

data IsCanonical   {X : Type χ} : CTerm X → Type χ
data IsCanonicalJ  {X : Type χ} : CJand X → Type χ
data IsCanonicalM  {X : Type χ} : CMand X → Type χ

data IsCanonical where
  cgen   : IsCanonical (genᶜ x)
  cjoin  : jt ≢ [] → All IsCanonicalJ (jh ∷ jt) → AntichainJ (jh ∷ jt) → Cond4J jh jt
         → IsCanonical (joinᶜ jh jt)
  cmeet  : mt ≢ [] → All IsCanonicalM (mh ∷ mt) → AntichainM (mh ∷ mt) → Cond4M mh mt
         → IsCanonical (meetᶜ mh mt)

data IsCanonicalJ where
  cjgen   : IsCanonicalJ (jgen x)
  cjmeet  : IsCanonical (meetᶜ mh mt) → IsCanonicalJ (jmeet mh mt)

data IsCanonicalM where
  cmgen   : IsCanonicalM (mgen x)
  cmjoin  : IsCanonical (joinᶜ jh jt) → IsCanonicalM (mjoin jh jt)
```

#### Joinands and meetands

A canonical term has a list of *joinands*: the children of a join, or the term
itself if it is a generator or a meet (`joinandsOf`{.AgdaFunction}).  The list is
returned as a pair of a first joinand and the rest, a `JList`{.AgdaFunction}, so
that its join is defined (`⋁ᴶL`{.AgdaFunction}), and that join is the term
(`joinandsOf-sound`{.AgdaFunction}, by definition in each case).  When the term is
canonical so is each joinand (`joinandsOf-canonical`{.AgdaFunction}).  A meetand
of a meet contributes joinands the same way (`joinandsOfM`{.AgdaFunction}); its
joinands have total rank at most its own (`joinandsOfM-crank`{.AgdaFunction}),
which is what makes a replacement step of the canonicalization algorithm lower the
rank.  The meetands of a term (`meetandsOf`{.AgdaFunction}) are dual.

```agda
JList : Type χ → Type χ
JList X = CJand X × List (CJand X)

MList : Type χ → Type χ
MList X = CMand X × List (CMand X)

asListJ : JList X → List (CJand X)
asListJ (h , t) = h ∷ t

asListM : MList X → List (CMand X)
asListM (h , t) = h ∷ t

⋁ᴶL : JList X → LatTerm X
⋁ᴶL (h , t) = ⋁ᴶ h t

⋀ᴹL : MList X → LatTerm X
⋀ᴹL (h , t) = ⋀ᴹ h t

joinandsOf : CTerm X → JList X
joinandsOf (genᶜ x)     = jgen x , []
joinandsOf (joinᶜ h t)  = h , t
joinandsOf (meetᶜ h t)  = jmeet h t , []

meetandsOf : CTerm X → MList X
meetandsOf (genᶜ x)     = mgen x , []
meetandsOf (joinᶜ h t)  = mjoin h t , []
meetandsOf (meetᶜ h t)  = h , t

joinandsOfM : CMand X → JList X
joinandsOfM (mgen x)     = jgen x , []
joinandsOfM (mjoin h t)  = h , t

joinandsOf-sound : (c : CTerm X) → ⋁ᴶL (joinandsOf c) ≡ ⌊ c ⌋
joinandsOf-sound (genᶜ x)     = refl
joinandsOf-sound (joinᶜ h t)  = refl
joinandsOf-sound (meetᶜ h t)  = refl

meetandsOf-sound : (c : CTerm X) → ⋀ᴹL (meetandsOf c) ≡ ⌊ c ⌋
meetandsOf-sound (genᶜ x)     = refl
meetandsOf-sound (joinᶜ h t)  = refl
meetandsOf-sound (meetᶜ h t)  = refl

joinandsOfM-sound : (m : CMand X) → ⋁ᴶL (joinandsOfM m) ≡ ⌊ m ⌋ᴹ
joinandsOfM-sound (mgen x)     = refl
joinandsOfM-sound (mjoin h t)  = refl

joinandsOf-canonical : {c : CTerm X} → IsCanonical c → All IsCanonicalJ (asListJ (joinandsOf c))
joinandsOf-canonical cgen                   = cjgen ∷ []
joinandsOf-canonical (cjoin _ cs _ _)       = cs
joinandsOf-canonical ic@(cmeet _ _ _ _)     = cjmeet ic ∷ []

meetandsOf-canonical : {c : CTerm X} → IsCanonical c → All IsCanonicalM (asListM (meetandsOf c))
meetandsOf-canonical cgen                   = cmgen ∷ []
meetandsOf-canonical ic@(cjoin _ _ _ _)     = cmjoin ic ∷ []
meetandsOf-canonical (cmeet _ cs _ _)       = cs

joinandsOfM-canonical : {m : CMand X} → IsCanonicalM m → All IsCanonicalJ (asListJ (joinandsOfM m))
joinandsOfM-canonical cmgen                     = cjgen ∷ []
joinandsOfM-canonical (cmjoin (cjoin _ cs _ _))  = cs

joinandsOfM-crank : (m : CMand X) → crankΣJ (asListJ (joinandsOfM m)) ≤ crankM m
joinandsOfM-crank (mgen x)     = ≤-refl
joinandsOfM-crank (mjoin h t)  = n≤1+n _
```

#### Duality

The dual of a canonical term exchanges joins and meets throughout
(`dualᶜ`{.AgdaFunction}), sending joinands to meetands (`dualᴶ`{.AgdaFunction}) and
meetands to joinands (`dualᴹ`{.AgdaFunction}).  It commutes with the embedding:
the embedded dual is the dual, in the sense of
[Classical.Structures.Lattice.Free.Duality][], of the embedded term
(`⌊dualᶜ⌋`{.AgdaFunction}).  The lists of children are dualized by the mutual
functions `dualᴶs`{.AgdaFunction} and `dualᴹs`{.AgdaFunction} rather than through
`map`{.AgdaFunction}, for the same reason the embedding folds its own lists.

```agda
dualᶜ   : CTerm X → CTerm X
dualᴶ   : CJand X → CMand X
dualᴹ   : CMand X → CJand X
dualᴶs  : List (CJand X) → List (CMand X)
dualᴹs  : List (CMand X) → List (CJand X)

dualᶜ (genᶜ x)      = genᶜ x
dualᶜ (joinᶜ h t)   = meetᶜ (dualᴶ h) (dualᴶs t)
dualᶜ (meetᶜ h t)   = joinᶜ (dualᴹ h) (dualᴹs t)
dualᴶ (jgen x)      = mgen x
dualᴶ (jmeet h t)   = mjoin (dualᴹ h) (dualᴹs t)
dualᴹ (mgen x)      = jgen x
dualᴹ (mjoin h t)   = jmeet (dualᴶ h) (dualᴶs t)
dualᴶs []           = []
dualᴶs (a ∷ as)     = dualᴶ a ∷ dualᴶs as
dualᴹs []           = []
dualᴹs (a ∷ as)     = dualᴹ a ∷ dualᴹs as

⌊dualᶜ⌋  : (c : CTerm X) → ⌊ dualᶜ c ⌋ ≡ dual ⌊ c ⌋
⌊dualᴶ⌋  : (a : CJand X) → ⌊ dualᴶ a ⌋ᴹ ≡ dual ⌊ a ⌋ᴶ
⌊dualᴹ⌋  : (a : CMand X) → ⌊ dualᴹ a ⌋ᴶ ≡ dual ⌊ a ⌋ᴹ
⋀ᴹ-dual  : (h : CJand X) (t : List (CJand X)) → ⋀ᴹ (dualᴶ h) (dualᴶs t) ≡ dual (⋁ᴶ h t)
⋁ᴶ-dual  : (h : CMand X) (t : List (CMand X)) → ⋁ᴶ (dualᴹ h) (dualᴹs t) ≡ dual (⋀ᴹ h t)

⌊dualᶜ⌋ (genᶜ x)      = refl
⌊dualᶜ⌋ (joinᶜ h t)   = ⋀ᴹ-dual h t
⌊dualᶜ⌋ (meetᶜ h t)   = ⋁ᴶ-dual h t
⌊dualᴶ⌋ (jgen x)      = refl
⌊dualᴶ⌋ (jmeet h t)   = ⋁ᴶ-dual h t
⌊dualᴹ⌋ (mgen x)      = refl
⌊dualᴹ⌋ (mjoin h t)   = ⋀ᴹ-dual h t
⋀ᴹ-dual h []          = ⌊dualᴶ⌋ h
⋀ᴹ-dual h (a ∷ as)    = cong₂ _∧̇_ (⌊dualᴶ⌋ h) (⋀ᴹ-dual a as)
⋁ᴶ-dual h []          = ⌊dualᴹ⌋ h
⋁ᴶ-dual h (a ∷ as)    = cong₂ _∨̇_ (⌊dualᴹ⌋ h) (⋁ᴶ-dual a as)
```

The dual of a canonical term is canonical (`dualᶜ-canonical`{.AgdaFunction}).  Each
of the four conditions passes to the dual: the dual of a list of children is a
list of children of the other kind and nonempty if the list is; incomparability is
preserved, because `dual`{.AgdaFunction} reverses and reflects the order
(`≰-dualᴶ`{.AgdaFunction}, `≰-dualᴹ`{.AgdaFunction}); and condition 4 for a join
is condition 4 for the dual meet read through the same reversal
(`Cond4-dualᴶ`{.AgdaFunction}, `Cond4-dualᴹ`{.AgdaFunction}), after locating the
member of a dualized list among the originals (`∈-dualᴶs⁻`{.AgdaFunction},
`∈-dualᴹs⁻`{.AgdaFunction}).

```agda
∈-dualᴶs⁻ : {b : CMand X} {as : List (CJand X)} → b ∈ dualᴶs as
          → Σ (CJand X) λ a → a ∈ as × b ≡ dualᴶ a
∈-dualᴶs⁻ {as = a ∷ _}  (here e)  = a , here refl , e
∈-dualᴶs⁻ {as = _ ∷ _}  (there i) = let (a , a∈ , e) = ∈-dualᴶs⁻ i in a , there a∈ , e

∈-dualᴹs⁻ : {b : CJand X} {as : List (CMand X)} → b ∈ dualᴹs as
          → Σ (CMand X) λ a → a ∈ as × b ≡ dualᴹ a
∈-dualᴹs⁻ {as = a ∷ _}  (here e)  = a , here refl , e
∈-dualᴹs⁻ {as = _ ∷ _}  (there i) = let (a , a∈ , e) = ∈-dualᴹs⁻ i in a , there a∈ , e

dualᴶs-≢[] : {as : List (CJand X)} → as ≢ [] → dualᴶs as ≢ []
dualᴶs-≢[] {as = []}     ne = ⊥-elim (ne refl)
dualᴶs-≢[] {as = _ ∷ _}  ne = λ ()

dualᴹs-≢[] : {as : List (CMand X)} → as ≢ [] → dualᴹs as ≢ []
dualᴹs-≢[] {as = []}     ne = ⊥-elim (ne refl)
dualᴹs-≢[] {as = _ ∷ _}  ne = λ ()

≰-dualᴶ : {a b : CJand X} → ⌊ b ⌋ᴶ ≰ʷ ⌊ a ⌋ᴶ → ⌊ dualᴶ a ⌋ᴹ ≰ʷ ⌊ dualᴶ b ⌋ᴹ
≰-dualᴶ {a = a} {b} nb p = nb (dual-reflects (subst₂ _≤ʷ_ (⌊dualᴶ⌋ a) (⌊dualᴶ⌋ b) p))

≰-dualᴹ : {a b : CMand X} → ⌊ b ⌋ᴹ ≰ʷ ⌊ a ⌋ᴹ → ⌊ dualᴹ a ⌋ᴶ ≰ʷ ⌊ dualᴹ b ⌋ᴶ
≰-dualᴹ {a = a} {b} nb p = nb (dual-reflects (subst₂ _≤ʷ_ (⌊dualᴹ⌋ a) (⌊dualᴹ⌋ b) p))

All-dualᴶs : {P : CJand X → Type χ} {Q : CMand X → Type χ} {as : List (CJand X)}
           → (∀ {a} → P a → Q (dualᴶ a)) → All P as → All Q (dualᴶs as)
All-dualᴶs f []        = []
All-dualᴶs f (p ∷ ps)  = f p ∷ All-dualᴶs f ps

All-dualᴹs : {P : CMand X → Type χ} {Q : CJand X → Type χ} {as : List (CMand X)}
           → (∀ {a} → P a → Q (dualᴹ a)) → All P as → All Q (dualᴹs as)
All-dualᴹs f []        = []
All-dualᴹs f (p ∷ ps)  = f p ∷ All-dualᴹs f ps

Antichain-dualᴶ : {as : List (CJand X)} → AntichainJ as → AntichainM (dualᴶs as)
Antichain-dualᴶ []  = []
Antichain-dualᴶ {as = a ∷ _} (r ∷ rs) =
  All-dualᴶs (λ {b} (na , nb) → ≰-dualᴶ {a = a} {b} nb , ≰-dualᴶ {a = b} {a} na) r
  ∷ Antichain-dualᴶ rs

Antichain-dualᴹ : {as : List (CMand X)} → AntichainM as → AntichainJ (dualᴹs as)
Antichain-dualᴹ []  = []
Antichain-dualᴹ {as = a ∷ _} (r ∷ rs) =
  All-dualᴹs (λ {b} (na , nb) → ≰-dualᴹ {a = a} {b} nb , ≰-dualᴹ {a = b} {a} na) r
  ∷ Antichain-dualᴹ rs

Cond4-dualᴶ : {h : CJand X} {t : List (CJand X)} → Cond4J h t → Cond4M (dualᴶ h) (dualᴶs t)
Cond4-dualᴶ {h = h} {t} c4 mj∈ j∈ p with ∈-dualᴶs⁻ {as = h ∷ t} mj∈
... | jgen _ , _ , ()
... | jmeet mh mt , a∈ , refl with ∈-dualᴹs⁻ {as = mh ∷ mt} j∈
...   | m , m∈ , refl = c4 a∈ m∈ (dual-reflects (subst₂ _≤ʷ_ (⋀ᴹ-dual h t) (⌊dualᴹ⌋ m) p))

Cond4-dualᴹ : {h : CMand X} {t : List (CMand X)} → Cond4M h t → Cond4J (dualᴹ h) (dualᴹs t)
Cond4-dualᴹ {h = h} {t} c4 jm∈ m∈ p with ∈-dualᴹs⁻ {as = h ∷ t} jm∈
... | mgen _ , _ , ()
... | mjoin jh jt , a∈ , refl with ∈-dualᴶs⁻ {as = jh ∷ jt} m∈
...   | j , j∈ , refl = c4 a∈ j∈ (dual-reflects (subst₂ _≤ʷ_ (⌊dualᴶ⌋ j) (⋁ᴶ-dual h t) p))

dualᶜ-canonical   : {c : CTerm X} → IsCanonical c → IsCanonical (dualᶜ c)
dualᴶ-canonical   : {a : CJand X} → IsCanonicalJ a → IsCanonicalM (dualᴶ a)
dualᴹ-canonical   : {a : CMand X} → IsCanonicalM a → IsCanonicalJ (dualᴹ a)
dualᴶs-canonical  : {as : List (CJand X)} → All IsCanonicalJ as → All IsCanonicalM (dualᴶs as)
dualᴹs-canonical  : {as : List (CMand X)} → All IsCanonicalM as → All IsCanonicalJ (dualᴹs as)

dualᶜ-canonical cgen                 = cgen
dualᶜ-canonical (cjoin ne cs ac c4)  =
  cmeet (dualᴶs-≢[] ne) (dualᴶs-canonical cs) (Antichain-dualᴶ ac) (Cond4-dualᴶ c4)
dualᶜ-canonical (cmeet ne cs ac c4)  =
  cjoin (dualᴹs-≢[] ne) (dualᴹs-canonical cs) (Antichain-dualᴹ ac) (Cond4-dualᴹ c4)
dualᴶ-canonical cjgen                = cmgen
dualᴶ-canonical (cjmeet ic)          = cmjoin (dualᶜ-canonical ic)
dualᴹ-canonical cmgen                = cjgen
dualᴹ-canonical (cmjoin ic)          = cjmeet (dualᶜ-canonical ic)
dualᴶs-canonical []                  = []
dualᴶs-canonical (c ∷ cs)            = dualᴶ-canonical c ∷ dualᴶs-canonical cs
dualᴹs-canonical []                  = []
dualᴹs-canonical (c ∷ cs)            = dualᴹ-canonical c ∷ dualᴹs-canonical cs
```
