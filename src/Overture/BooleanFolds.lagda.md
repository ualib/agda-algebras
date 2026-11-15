---
layout: default
file: "src/Overture/BooleanFolds.lagda.md"
title: "Overture.BooleanFolds module"
date: "2026-11-09"
author: "the agda-algebras development team"
---

### Boolean folds over finite index sets

This is the [Overture.BooleanFolds][] module of the [Agda Universal Algebra Library][].

A universal statement over a finite index set, `∀ i → P i` with `i : Fin n`,
can be decided in two ways when `P` is decidable.  The standard library's
`all?`{.AgdaFunction} (in `Data.Fin.Properties`) returns a `Dec`{.AgdaRecord},
whose proof component carries one payload per case.  Alternatively, a fold of
the cases' Booleans returns a plain `Bool`{.AgdaDatatype}, and a soundness
lemma, proved once by induction, reads the universal statement back from the
fold's truth.

The two agree on the Boolean (the standard library notes beside
`all?`{.AgdaFunction} that `does (all? P?)` is the `∧`-fold of the cases), but
they differ in what the type checker must do to accept a concrete instance,
and on a large instance the difference is most of a module's memory and time.
An instance accepts a fold by stating its truth as an equation `b ≡ true` and
proving it by `refl`, which the type checker decides by evaluating `b` once and
comparing the result with `true`; accepting the same fold by `tt` against
`T b` took four times as long.  [Setoid.Congruences.Certificates.Lattice][]
records the measurements, made on a large concrete certificate.

This module gives the folds and the lemmas that read them back.  It mentions
only `Bool`{.AgdaDatatype}, `Fin`{.AgdaDatatype} and `Dec`{.AgdaRecord}, so it
lands in [Overture][], beside its consumers' other utilities.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.BooleanFolds where

open import Agda.Primitive using ( Level ) renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Bool.Base                   using  ( Bool ; true ; false ; T ; _∧_ )
open import Data.Bool.ListAction             using  ( and )
open import Data.Empty                       using  ( ⊥-elim )
open import Data.Fin.Base                    using  ( Fin ; zero ; suc )
open import Data.List.Base                   using  ( List ; [] ; _∷_ )
open import Data.List.Relation.Unary.All     using  ( All ; [] ; _∷_ )
open import Data.Nat.Base                    using  ( ℕ )
open import Data.Unit.Base                   using  ( tt )
open import Relation.Binary.PropositionalEquality
                                             using  ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core  using  ( Dec ; does ; _because_ ; map′ ; T? )
open import Relation.Nullary.Reflects        using  ( ofʸ ; ofⁿ )

private variable a p : Level
```
-->

#### Conjunction, read back

The lemmas below take every Boolean explicitly.  A conjunction `b ∧ c` whose
first conjunct is still a metavariable cannot be reduced, so the unifier
cannot recover `b` from the type `T (b ∧ c)` alone; with both Booleans given,
the lemmas apply wherever they are needed.

```agda
-- The left conjunct of a true conjunction is true.
T-∧ˡ : (b c : Bool) → T (b ∧ c) → T b
T-∧ˡ true  c _ = tt

-- The right conjunct of a true conjunction is true.
T-∧ʳ : (b c : Bool) → T (b ∧ c) → T c
T-∧ʳ true  c t = t

-- Two true Booleans make a true conjunction.
T-∧-intro : (b c : Bool) → T b → T c → T (b ∧ c)
T-∧-intro true  c _ t = t
```

A Boolean equal to `true` is true.  A concrete instance states its fold's
truth as an equation proved by `refl`, which the type checker accepts by
evaluating the Boolean once, and this lemma turns the equation into the truth
the soundness lemmas take.  The Boolean should be spelled once, as the type of
a definition of its own or as the argument of a lemma that names it, the way
`latticeCertOK-sound`{.AgdaFunction} of
[Setoid.Congruences.Certificates.Lattice][] does.  Spelled twice, as in
`allᵈ-sound P? (≡true→T (allᵈ P?) refl)`, one sweep of that module's
benchmark took about six times as long.

```agda
-- A Boolean equal to true is true.
≡true→T : (b : Bool) → b ≡ true → T b
≡true→T true refl = tt
```

#### The Boolean of a decision

`does-sound`{.AgdaFunction} is the standard library's
`toWitness`{.AgdaFunction}, stated for `T (does d)` rather than `True d`.  The
two types agree on every decision computed to a constructor, but not on a
decision that is a variable (`True d` is defined by matching on `d`), so a
fold whose cases are `does`{.AgdaField} of a decision needs this form.
`does-complete`{.AgdaFunction} is the converse, `fromWitness`{.AgdaFunction}
for `T (does d)`.

```agda
-- A decision whose Boolean is true is a proof.
does-sound : {A : Type a} (d : Dec A) → T (does d) → A
does-sound (true because ofʸ x) _ = x

-- A decision of a true statement has a true Boolean.
does-complete : {A : Type a} (d : Dec A) → A → T (does d)
does-complete (true  because _)     _ = tt
does-complete (false because ofⁿ ¬x) x = ⊥-elim (¬x x)
```

Conversely, a Boolean that is sound and complete for a statement decides it.
The decision's Boolean is the given one, so a decider built this way computes
exactly as its Boolean does, and `from-yes`{.AgdaFunction} of it evaluates
nothing more.

```agda
-- The decision whose Boolean is b, for a statement b is sound and complete for.
decideᵇ : {A : Type a} (b : Bool) → (T b → A) → (A → T b) → Dec A
decideᵇ b sound complete = map′ sound complete (T? b)
```

#### Folds over `Fin`

`allᵇ`{.AgdaFunction} is the conjunction of a Boolean function's values on
`Fin n`, by structural recursion on `n`; `allᵇ-sound`{.AgdaFunction} reads
every value back from the conjunction, and `allᵇ-complete`{.AgdaFunction} is
the converse.

```agda
-- The conjunction of the values of f on Fin n.
allᵇ : {n : ℕ} → (Fin n → Bool) → Bool
allᵇ {ℕ.zero}   _ = true
allᵇ {ℕ.suc n}  f = f zero ∧ allᵇ (λ i → f (suc i))

-- Every value of f is true if the fold is.
allᵇ-sound : {n : ℕ} (f : Fin n → Bool) → T (allᵇ f) → ∀ i → T (f i)
allᵇ-sound f t zero     = T-∧ˡ (f zero) (allᵇ (λ i → f (suc i))) t
allᵇ-sound f t (suc i)  =
  allᵇ-sound (λ j → f (suc j)) (T-∧ʳ (f zero) (allᵇ (λ j → f (suc j))) t) i

-- The fold is true if every value of f is.
allᵇ-complete : {n : ℕ} (f : Fin n → Bool) → (∀ i → T (f i)) → T (allᵇ f)
allᵇ-complete {ℕ.zero}   _ _ = tt
allᵇ-complete {ℕ.suc n}  f h =
  T-∧-intro (f zero) (allᵇ (λ i → f (suc i)))
            (h zero) (allᵇ-complete (λ i → f (suc i)) (λ i → h (suc i)))
```

The nested form for a statement over pairs of indices, possibly from two
index sets of different sizes.  A statement over four indices is two nested
pairs.

```agda
-- The conjunction of the values of f on Fin m × Fin n.
all²ᵇ : {m n : ℕ} → (Fin m → Fin n → Bool) → Bool
all²ᵇ f = allᵇ (λ i → allᵇ (f i))

-- Every value of f is true if the fold is.
all²ᵇ-sound : {m n : ℕ} (f : Fin m → Fin n → Bool)
  →  T (all²ᵇ f) → ∀ i j → T (f i j)
all²ᵇ-sound f t i = allᵇ-sound (f i) (allᵇ-sound (λ i′ → allᵇ (f i′)) t i)

-- The fold is true if every value of f is.
all²ᵇ-complete : {m n : ℕ} (f : Fin m → Fin n → Bool)
  →  (∀ i j → T (f i j)) → T (all²ᵇ f)
all²ᵇ-complete f h =
  allᵇ-complete (λ i → allᵇ (f i)) (λ i → allᵇ-complete (f i) (h i))
```

#### Folds of decisions

`allᵈ`{.AgdaFunction} is the Boolean twin of the standard library's
`all?`{.AgdaFunction}: it takes the same argument, a decision for each index,
and folds the decisions' Booleans; `allᵈ-sound`{.AgdaFunction} returns what
`from-yes (all? P?)` would, and `allᵈ-complete`{.AgdaFunction} is its
converse.  The nested forms take a decision for each pair
and each quadruple of indices, the shapes of the sweeps in
[Setoid.Congruences.Certificates.Lattice][].

```agda
-- The Booleans of a decision for each index, conjoined.
allᵈ : {n : ℕ} {P : Fin n → Type p} → (∀ i → Dec (P i)) → Bool
allᵈ P? = allᵇ (λ i → does (P? i))

-- The statement for every index, from the fold.
allᵈ-sound : {n : ℕ} {P : Fin n → Type p} (P? : ∀ i → Dec (P i))
  →  T (allᵈ P?) → ∀ i → P i
allᵈ-sound P? t i = does-sound (P? i) (allᵇ-sound (λ j → does (P? j)) t i)

-- The fold, from the statement for every index.
allᵈ-complete : {n : ℕ} {P : Fin n → Type p} (P? : ∀ i → Dec (P i))
  →  (∀ i → P i) → T (allᵈ P?)
allᵈ-complete P? h =
  allᵇ-complete (λ i → does (P? i)) (λ i → does-complete (P? i) (h i))

-- The Booleans of a decision for each pair of indices, conjoined.
all²ᵈ : {m n : ℕ} {P : Fin m → Fin n → Type p}
  →  (∀ i j → Dec (P i j)) → Bool
all²ᵈ P? = all²ᵇ (λ i j → does (P? i j))

-- The statement for every pair of indices, from the fold.
all²ᵈ-sound : {m n : ℕ} {P : Fin m → Fin n → Type p}
  →  (P? : ∀ i j → Dec (P i j)) → T (all²ᵈ P?) → ∀ i j → P i j
all²ᵈ-sound P? t i j =
  does-sound (P? i j) (all²ᵇ-sound (λ i′ j′ → does (P? i′ j′)) t i j)

-- The fold, from the statement for every pair of indices.
all²ᵈ-complete : {m n : ℕ} {P : Fin m → Fin n → Type p}
  →  (P? : ∀ i j → Dec (P i j)) → (∀ i j → P i j) → T (all²ᵈ P?)
all²ᵈ-complete P? h =
  all²ᵇ-complete (λ i j → does (P? i j)) (λ i j → does-complete (P? i j) (h i j))

-- The Booleans of a decision for each quadruple of indices, conjoined.
all⁴ᵈ : {k l m n : ℕ} {P : Fin k → Fin l → Fin m → Fin n → Type p}
  →  (∀ a b i j → Dec (P a b i j)) → Bool
all⁴ᵈ P? = all²ᵇ (λ a b → all²ᵈ (P? a b))

-- The statement for every quadruple of indices, from the fold.
all⁴ᵈ-sound : {k l m n : ℕ} {P : Fin k → Fin l → Fin m → Fin n → Type p}
  →  (P? : ∀ a b i j → Dec (P a b i j)) → T (all⁴ᵈ P?) → ∀ a b i j → P a b i j
all⁴ᵈ-sound P? t a b =
  all²ᵈ-sound (P? a b) (all²ᵇ-sound (λ a′ b′ → all²ᵈ (P? a′ b′)) t a b)

-- The fold, from the statement for every quadruple of indices.
all⁴ᵈ-complete : {k l m n : ℕ} {P : Fin k → Fin l → Fin m → Fin n → Type p}
  →  (P? : ∀ a b i j → Dec (P a b i j)) → (∀ a b i j → P a b i j) → T (all⁴ᵈ P?)
all⁴ᵈ-complete P? h =
  all²ᵇ-complete (λ a b → all²ᵈ (P? a b)) (λ a b → all²ᵈ-complete (P? a b) (h a b))
```

#### Conjunctions of a list

`and`{.AgdaFunction} (from `Data.Bool.ListAction`) conjoins a list of Booleans;
`and-sound`{.AgdaFunction} reads back each member, and
`and-complete`{.AgdaFunction} is its converse.  A checker that conjoins a
fixed list of named conditions takes the resulting `All`{.AgdaDatatype} apart
with one pattern match.

```agda
-- Every member of a true conjunction is true.
and-sound : (bs : List Bool) → T (and bs) → All T bs
and-sound []        _ = []
and-sound (b ∷ bs)  t = T-∧ˡ b (and bs) t ∷ and-sound bs (T-∧ʳ b (and bs) t)

-- A conjunction of true Booleans is true.
and-complete : (bs : List Bool) → All T bs → T (and bs)
and-complete []        []        = tt
and-complete (b ∷ bs)  (t ∷ ts)  = T-∧-intro b (and bs) t (and-complete bs ts)
```
