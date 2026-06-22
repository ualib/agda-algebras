---
layout: default
title : "Setoid.Operations.Properties module (The Agda Universal Algebra Library)"
date : "2026-06-21"
author: "the agda-algebras development team"
---

### Decidable equational laws over a searchable decidable setoid

This is the [Setoid.Operations.Properties][] module of the [Agda Universal Algebra Library][].

The finite law-checkers of [Overture.Operations.Properties][] decide each equational
law of an operation `Fin n → Fin n → Fin n` by nesting `all?`{.AgdaFunction}
(`Data.Fin.Properties.all?`) over decidable equality `_≟_`{.AgdaFunction} on
`Fin n`{.AgdaDatatype}.  Their decidability rests on exactly two facts about the
carrier, and *neither is special to* `Fin n`{.AgdaDatatype} *or to*
`_≡_`{.AgdaDatatype}.

1.  The carrier is **exhaustively searchable** — a pointwise decision procedure
    `∀ x → Dec (P x)` can be turned into a decision `Dec (∀ x → P x)` for the
    universally-quantified statement (this is what `all?`{.AgdaFunction} provides).
2.  The carrier has **decidable equality** — supplied here by the decidable
    `_≈_`{.AgdaFunction} of a `DecSetoid`{.AgdaRecord}.

This module restates the eleven checkers over an arbitrary `DecSetoid`{.AgdaRecord}
`S` — deciding `_≈_`{.AgdaFunction} through the decidable equality relation
`_≟_`{.AgdaFunction} of `S` — together with an exhaustive-search witness for its
carrier, writing each law with `_≈_`{.AgdaFunction} in place of `_≡_`{.AgdaDatatype}.

The operation remains a bare function `Carrier → Carrier → Carrier`; the decision
never needs it to respect `_≈_`{.AgdaFunction}, exactly as in the concrete versions.
The finite `Fin n`{.AgdaDatatype} / `_≡_`{.AgdaDatatype} checkers are then recovered
as a single instance: take `S` to be the propositional `DecSetoid`{.AgdaRecord} on
`Fin n`{.AgdaDatatype} and the search witness to be the `all?`{.AgdaFunction} of
`Fin`.

The final section proves that each concrete checker *equals* its generalized form at
this instance, by `refl`{.AgdaInductiveConstructor}; so the fast-reducing concrete
checkers (on which the finite examples and their `from-yes`{.AgdaFunction} proofs
depend) are kept exactly as they are, with the generalization exhibited alongside
rather than replacing them.

The search ingredient is isolated below as a one-field interface,
`Exhaustible`{.AgdaRecord}, deliberately kept independent of `Fin`{.AgdaDatatype} so
that any carrier that admits such a search functional can drive the checkers.

Finite carriers are the obvious source, but not the only one.  For instance, Martín
Escardó's work on *exhaustively searchable* types shows that even some *infinite*
carriers (e.g. `ℕ∞`, the one-point compactification of `ℕ`) admit a total search
functional.  Supplying those carriers' search functionals is planned work;[^1]
this module only fixes the interface they would implement.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Operations.Properties where

open import Agda.Primitive                         renaming ( Set to Type ; Setω to Typeω )

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Bool.Base                         using ( Bool ; false ; true ; _∧_ ; _∨_ )
open import Data.Fin                               using ( Fin )
open import Data.Nat                               using ( ℕ )
open import Data.Product                           using ( _×_ ; _,_ )
open import Relation.Binary.Bundles                using ( DecSetoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core        using ( Dec ; map′ ; from-yes ; _×-dec_ )

import Data.Bool.Properties as BoolP
open import Data.Fin.Properties  using (≡-decSetoid) renaming (all? to FinAll?)

-- Imports from the Agda Universal Algebra Library -----------------------------
import Overture.Operations.Properties as Concrete
```

#### The exhaustive-search interface

A carrier `A` is *exhaustively searchable* — for the purpose of deciding
universally-quantified decidable predicates — when it carries a single functional
that turns any pointwise decision procedure `∀ x → Dec (P x)` into a decision
`Dec (∀ x → P x)` for the universal statement.  This is exactly the shape of
`Data.Fin.Properties.all?`, but here we abstract the carrier beyond `Fin`.

We package the interface as a single-field record so that a witness
`E : Exhaustible A` can be passed to the checkers and its search functional opened
under the name `all?`{.AgdaFunction}, making the generalized call sites read
identically to the concrete `Fin` ones.  The record mentions no setoid and no
`Fin`{.AgdaDatatype}; it is a property of a bare carrier.[^2]

The field is universe-polymorphic in the predicate level `p`, so the record lives in
`Typeω`{.AgdaPrimitiveType}.  This is needed because the nested checkers apply the
same functional at two different predicate levels (`ℓ` innermost and `c ⊔ ℓ` after a
quantifier).

```agda
-- An exhaustive-search witness for a carrier A: it decides any universally-
-- quantified predicate whose pointwise instances are decidable.  The abstraction
-- of Data.Fin.Properties.all?, independent of Fin and of any equality.
record Exhaustible {c} (A : Type c) : Typeω where
  field
    all? : ∀ {p} {P : A → Type p} → (∀ x → Dec (P x)) → Dec (∀ x → P x)
```

#### Laws of a single operation

Throughout, `S` is a decidable setoid, `E` an exhaustive-search witness for its
carrier, and `_·_` a bare binary operation on that carrier.

+  Opening `S` exposes the carrier, its setoid equality `_≈_`{.AgdaFunction}, and the
   decidable equality `_≟_`{.AgdaFunction} for `_≈_`{.AgdaFunction};
+  opening `E` exposes the search functional `all?`{.AgdaFunction}.

Each law is then decided by nesting `all?`{.AgdaFunction} over `_≟_`{.AgdaFunction},
one nesting per universally-quantified variable.

```agda
module _ {c ℓ} (S : DecSetoid c ℓ) (E : Exhaustible (DecSetoid.Carrier S)) where
  open DecSetoid S    using ( Carrier ; _≈_ ; _≟_ )
  open Exhaustible E  using ( all? )

  module _ (_·_ : Carrier → Carrier → Carrier) where

    -- a · a ≈ a for every a.
    Idempotent? : Dec ∀ a → a · a ≈ a
    Idempotent? = all? λ a → a · a ≟ a

    -- a · b ≈ b · a for every a, b.
    Commutative? : Dec ∀ a b → a · b ≈ b · a
    Commutative? = all? λ a → all? λ b → a · b ≟ b · a

    -- (a · b) · c ≈ a · (b · c) for every a, b, c.
    Associative? : Dec ∀ a b c → (a · b) · c ≈ a · (b · c)
    Associative? = all? λ a → all? λ b → all? λ c → (a · b) · c ≟ a · (b · c)

    module _ (e : Carrier) where

      -- e · a ≈ a for every a.
      LeftIdentity? : Dec ∀ a → e · a ≈ a
      LeftIdentity? = all? λ a → e · a ≟ a

      -- a · e ≈ a for every a.
      RightIdentity? : Dec ∀ a → a · e ≈ a
      RightIdentity? = all? λ a → a · e ≟ a

      module _ (i : Carrier → Carrier) where

        -- (i a) · a ≈ e for every a.
        LeftInverse? : Dec ∀ a → (i a) · a ≈ e
        LeftInverse? = all? λ a → (i a) · a ≟ e

        -- a · (i a) ≈ e for every a.
        RightInverse? : Dec ∀ a → a · (i a) ≈ e
        RightInverse? = all? λ a → a · (i a) ≟ e
```

#### Laws relating two operations

These take two bare operations `_∧_` and `_∨_` over the same decidable setoid; e.g.,
the meet and join of a lattice.  The shapes match the two-operation checkers
of [Overture.Operations.Properties][] — absorption and distributivity — now stated
over `_≈_`{.AgdaFunction}.

```agda
module _ {c ℓ} (S : DecSetoid c ℓ) (E : Exhaustible (DecSetoid.Carrier S)) where
  open DecSetoid S    using ( Carrier ; _≈_ ; _≟_ )
  open Exhaustible E  using ( all? )

  module _ (_∧_ _∨_ : Carrier → Carrier → Carrier) where

    -- a ∧ (a ∨ b) ≈ a for every a, b.
    Absorbsˡ? : Dec ∀ a b → a ∧ (a ∨ b) ≈ a
    Absorbsˡ? = all? λ a → all? λ b → a ∧ (a ∨ b) ≟ a

    -- (a ∧ b) ∨ a ≈ a for every a, b.
    Absorbsʳ? : Dec ∀ a b → (a ∧ b) ∨ a ≈ a
    Absorbsʳ? = all? λ a → all? λ b → (a ∧ b) ∨ a ≟ a

    -- a ∧ (b ∨ c) ≈ (a ∧ b) ∨ (a ∧ c) for every a, b, c.
    Distributesˡ? : Dec ∀ a b c → a ∧ (b ∨ c) ≈ (a ∧ b) ∨ (a ∧ c)
    Distributesˡ? = all? λ a → all? λ b → all? λ c → a ∧ (b ∨ c) ≟ (a ∧ b) ∨ (a ∧ c)

    -- (b ∨ c) ∧ a ≈ (b ∧ a) ∨ (c ∧ a) for every a, b, c.
    Distributesʳ? : Dec (∀ a b c → ((b ∨ c) ∧ a) ≈ ((b ∧ a) ∨ (c ∧ a)))
    Distributesʳ? = all? (λ a → all? (λ b → all? (λ c → ((b ∨ c) ∧ a) ≟ ((b ∧ a) ∨ (c ∧ a)))))
```

#### The finite instance

`Fin n`{.AgdaDatatype} is exhaustively searchable: its search functional is precisely
`Data.Fin.Properties.all?`.  Wrapping it gives the canonical `Exhaustible`{.AgdaRecord}
witness for `Fin n`{.AgdaDatatype}, the one that recovers the concrete checkers.

```agda
-- The exhaustive-search witness for Fin n, given by all? of Fin.
Fin-Exhaustible : ∀ {n} → Exhaustible (Fin n)
Fin-Exhaustible = record { all? = FinAll? }
```

#### The finite checkers as the propositional instance

Take `S` to be `≡-decSetoid n` — the propositional decidable setoid on
`Fin n`{.AgdaDatatype}, whose `_≈_`{.AgdaFunction} is `_≡_`{.AgdaDatatype} and whose
`_≟_`{.AgdaFunction} is `Data.Fin.Properties._≟_` — and `E` to be
`Fin-Exhaustible`{.AgdaFunction}.

Each generalized checker then *unfolds definitionally* to the corresponding concrete
checker of [Overture.Operations.Properties][]: the search functional reduces to
`all?`{.AgdaFunction} of `Fin` and `_≟_`{.AgdaFunction} reduces to decidable equality
of `Fin`.  We record this as eleven `refl`{.AgdaInductiveConstructor} equations, one
per checker.

This is the precise sense in which the concrete checkers *are* the propositional
instance of the generalized ones — and, because the equalities are definitional, the
concrete checkers keep reducing exactly as before for `from-yes`{.AgdaFunction}, so
the finite examples are unaffected.

(We leave present each of the remaining observations as an anonymous theorem, since
they serve to confirm and demonstrate fact which likely will not be used elsewhere.)

```agda
module _ {n : ℕ} (_·_ : Fin n → Fin n → Fin n) where

  _ : Concrete.Idempotent? _·_ ≡ Idempotent? (≡-decSetoid n) Fin-Exhaustible _·_
  _ = refl

  _ : Concrete.Commutative? _·_ ≡ Commutative? (≡-decSetoid n) Fin-Exhaustible _·_
  _ = refl

  _ : Concrete.Associative? _·_ ≡ Associative? (≡-decSetoid n) Fin-Exhaustible _·_
  _ = refl

  module _ (e : Fin n) where

    _ : Concrete.LeftIdentity? _·_ e ≡ LeftIdentity? (≡-decSetoid n) Fin-Exhaustible _·_ e
    _ = refl

    _ : Concrete.RightIdentity? _·_ e ≡ RightIdentity? (≡-decSetoid n) Fin-Exhaustible _·_ e
    _ = refl

    module _ (i : Fin n → Fin n) where

      _ : Concrete.LeftInverse? _·_ e i ≡ LeftInverse? (≡-decSetoid n) Fin-Exhaustible _·_ e i
      _ = refl

      _ : Concrete.RightInverse? _·_ e i ≡ RightInverse? (≡-decSetoid n) Fin-Exhaustible _·_ e i
      _ = refl

module _ {n : ℕ} (_∧_ _∨_ : Fin n → Fin n → Fin n) where

  _ : Concrete.Absorbsˡ? _∧_ _∨_ ≡ Absorbsˡ? (≡-decSetoid n) Fin-Exhaustible _∧_ _∨_
  _ = refl

  _ : Concrete.Absorbsʳ? _∧_ _∨_ ≡ Absorbsʳ? (≡-decSetoid n) Fin-Exhaustible _∧_ _∨_
  _ = refl

  _ : Concrete.Distributesˡ? _∧_ _∨_ ≡ Distributesˡ? (≡-decSetoid n) Fin-Exhaustible _∧_ _∨_
  _ = refl

  _ : Concrete.Distributesʳ? _∧_ _∨_ ≡ Distributesʳ? (≡-decSetoid n) Fin-Exhaustible _∧_ _∨_
  _ = refl
```

#### A non-Fin instance: the two-element Boolean setoid

To exercise the generality on a carrier that is *not* `Fin n`{.AgdaDatatype}, we
supply an exhaustive-search witness for `Bool`{.AgdaDatatype} directly and run the
checkers over the propositional decidable setoid on `Bool`{.AgdaDatatype}.  Searching
`Bool`{.AgdaDatatype} is immediate: `∀ b → P b` holds iff both `P false` and `P true`
do, so a pointwise decider for `P` decides the universal by a single
`_×-dec_`{.AgdaFunction}.  This both demonstrates the abstraction and previews, in
miniature, the kind of witness an M9-1 `Searchable` carrier would provide
generically.  The section is `private`{.AgdaKeyword}: it validates the generalization
without enlarging the module's public surface.

```agda
private

  -- Bool is exhaustively searchable: ∀ b → P b reduces to P false and P true.
  Bool-Exhaustible : Exhaustible Bool
  Bool-Exhaustible = record { all? = bool-all? }
    where
    bool-all? : ∀ {p} {P : Bool → Type p} → (∀ b → Dec (P b)) → Dec (∀ b → P b)
    bool-all? {P = P} P? = map′ to from (P? false ×-dec P? true)
      where
      to : P false × P true → (∀ b → P b)
      to (pf , _ ) false = pf
      to ( _ , pt) true  = pt
      from : (∀ b → P b) → P false × P true
      from p = p false , p true
```

The generalized checkers now decide the Boolean-lattice laws of conjunction and
disjunction directly over `Bool`{.AgdaDatatype}, with no detour through
`Fin 2`{.AgdaDatatype}.  Each proof is extracted by `from-yes`{.AgdaFunction} from the
generalized decision; a wrong claim would make the decision compute to
`no`{.AgdaInductiveConstructor} and fail to type-check, just as in the finite
examples.

```agda
  -- Conjunction is idempotent, commutative, and associative on Bool, and absorbs
  -- disjunction — each decided by the generalized checkers at the Bool setoid.
  ∧-idem-bool : ∀ a → a ∧ a ≡ a
  ∧-idem-bool = from-yes (Idempotent? BoolP.≡-decSetoid Bool-Exhaustible _∧_)

  ∧-comm-bool : ∀ a b → a ∧ b ≡ b ∧ a
  ∧-comm-bool = from-yes (Commutative? BoolP.≡-decSetoid Bool-Exhaustible _∧_)

  ∧-assoc-bool : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc-bool = from-yes (Associative? BoolP.≡-decSetoid Bool-Exhaustible _∧_)

  ∧-absorbs-∨-bool : ∀ a b → a ∧ (a ∨ b) ≡ a
  ∧-absorbs-∨-bool = from-yes (Absorbsˡ? BoolP.≡-decSetoid Bool-Exhaustible _∧_ _∨_)
```

--------------------------------------

[^1]: See Milestone 9, especially Issue [M9-1].

[^2]: which is why a future Escardó-style `Searchable`/`Exhaustible` carrier could
supply it without change.


<span style="float:left;">[↑ Setoid](Setoid.html)</span>

{% include UALib.Links.md %}
