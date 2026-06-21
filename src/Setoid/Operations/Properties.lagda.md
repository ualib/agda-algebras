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
`_≡_`{.AgdaDatatype}:

+  the carrier is **exhaustively searchable** — a pointwise decision procedure
   `∀ x → Dec (P x)` can be turned into a decision `Dec (∀ x → P x)` for the
   universally-quantified statement (this is what `all?`{.AgdaFunction} provides); and
+  the carrier has **decidable equality** — supplied here by the decidable
   `_≈_`{.AgdaFunction} of a `DecSetoid`{.AgdaRecord}.

This module restates the eleven checkers over an arbitrary `DecSetoid`{.AgdaRecord}
`S` — deciding `_≈_`{.AgdaFunction} through `S`'s `_≟_`{.AgdaFunction} — together with
an exhaustive-search witness for its carrier, writing each law with
`_≈_`{.AgdaFunction} in place of `_≡_`{.AgdaDatatype}.  The operation stays a *bare*
function `Carrier → Carrier → Carrier`; the *decision* never needs it to respect
`_≈_`{.AgdaFunction}, exactly as in the concrete versions.  The finite
`Fin n`{.AgdaDatatype} / `_≡_`{.AgdaDatatype} checkers are then recovered as a single
instance: take `S` to be the propositional `DecSetoid`{.AgdaRecord} on
`Fin n`{.AgdaDatatype} and the search witness to be `Fin`'s `all?`{.AgdaFunction}.
The final section proves that each concrete checker *equals* its generalized form at
this instance, by `refl`{.AgdaInductiveConstructor}; so the fast-reducing concrete
checkers (on which the finite examples and their `from-yes`{.AgdaFunction} proofs
depend) are kept exactly as they are, with the generalization exhibited alongside
rather than replacing them.

The search ingredient is isolated below as a one-field interface,
`Exhaustible`{.AgdaRecord}, deliberately kept independent of `Fin`{.AgdaDatatype}: any
carrier that admits such a search functional can drive the checkers.  Finite carriers
are the obvious source, but not the only one — Martín Escardó's work on
*exhaustively searchable* types shows that even some *infinite* carriers (e.g.
`ℕ∞`, the one-point compactification of `ℕ`) admit a total search functional.
Supplying those carriers' search functionals is the planned **M9-1** work; this
module only fixes the interface they would implement, and is not itself M9-1.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Operations.Properties where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive                          using ( Level )
                                                    renaming ( Set to Type ; Setω to Typeω )
open import Data.Bool.Base                          using ( Bool ; false ; true ; _∧_ ; _∨_ )
open import Data.Fin                                using ( Fin )
open import Data.Nat                                using ( ℕ )
open import Data.Product                            using ( _×_ ; _,_ )
open import Relation.Binary.Bundles                 using ( DecSetoid )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core         using ( Dec ; map′ ; from-yes ; _×-dec_ )

import Data.Bool.Properties              as BoolP
import Data.Fin.Properties               as FinP

-- Imports from the Agda Universal Algebra Library -----------------------------
import Overture.Operations.Properties    as Concrete
```

#### The exhaustive-search interface

A carrier `A` is *exhaustively searchable* — for the purpose of deciding
universally-quantified decidable predicates — when it carries a single functional
that turns any pointwise decision procedure `∀ x → Dec (P x)` into a decision
`Dec (∀ x → P x)` for the universal statement.  This is exactly the shape of
`Data.Fin.Properties.all?`, with the carrier abstracted away from `Fin`.  We package
it as a one-field record so that a witness `E : Exhaustible A` can be passed to the
checkers and its search functional opened under the name `all?`{.AgdaFunction},
making the generalized call sites read identically to the concrete `Fin` ones.

The field is universe-polymorphic in the predicate level `p`, so the record lives in
`Typeω`{.AgdaPrimitiveType}; this is needed because the nested checkers apply the same
functional at two different predicate levels (`ℓ` innermost and `c ⊔ ℓ` after a
quantifier).  The record mentions no setoid and no `Fin`{.AgdaDatatype}; it is a
property of a bare carrier, which is why a future Escardó-style
`Searchable`/`Exhaustible` carrier (M9-1) could supply it without change.

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
carrier, and `_·_` a bare binary operation on that carrier.  Opening `S` exposes the
carrier, its setoid equality `_≈_`{.AgdaFunction}, and the decision `_≟_`{.AgdaFunction}
for `_≈_`{.AgdaFunction}; opening `E` exposes the search functional `all?`{.AgdaFunction}.
Each law is then decided by nesting `all?`{.AgdaFunction} over `_≟_`{.AgdaFunction},
one nesting per universally-quantified variable.

```agda
module _ {c ℓ} (S : DecSetoid c ℓ) (E : Exhaustible (DecSetoid.Carrier S)) where
  open DecSetoid S   using ( Carrier ; _≈_ ; _≟_ )
  open Exhaustible E using ( all? )

  module _ (_·_ : Carrier → Carrier → Carrier) where

    -- a · a ≈ a for every a.
    Idempotentᴰ? : Dec (∀ a → (a · a) ≈ a)
    Idempotentᴰ? = all? (λ a → (a · a) ≟ a)

    -- a · b ≈ b · a for every a, b.
    Commutativeᴰ? : Dec (∀ a b → (a · b) ≈ (b · a))
    Commutativeᴰ? = all? (λ a → all? (λ b → (a · b) ≟ (b · a)))

    -- (a · b) · c ≈ a · (b · c) for every a, b, c.
    Associativeᴰ? : Dec (∀ a b c → ((a · b) · c) ≈ (a · (b · c)))
    Associativeᴰ? = all? (λ a → all? (λ b → all? (λ c → ((a · b) · c) ≟ (a · (b · c)))))

    module _ (e : Carrier) where

      -- e · a ≈ a for every a.
      LeftIdentityᴰ? : Dec (∀ a → (e · a) ≈ a)
      LeftIdentityᴰ? = all? (λ a → (e · a) ≟ a)

      -- a · e ≈ a for every a.
      RightIdentityᴰ? : Dec (∀ a → (a · e) ≈ a)
      RightIdentityᴰ? = all? (λ a → (a · e) ≟ a)

      module _ (i : Carrier → Carrier) where

        -- (i a) · a ≈ e for every a.
        LeftInverseᴰ? : Dec (∀ a → ((i a) · a) ≈ e)
        LeftInverseᴰ? = all? (λ a → ((i a) · a) ≟ e)

        -- a · (i a) ≈ e for every a.
        RightInverseᴰ? : Dec (∀ a → (a · (i a)) ≈ e)
        RightInverseᴰ? = all? (λ a → (a · (i a)) ≟ e)
```

#### Laws relating two operations

These take two bare operations `_·_` and `_∘_` over the same decidable setoid; in a
lattice they are typically the meet `∧` and join `∨`.  The shapes match the
two-operation checkers of [Overture.Operations.Properties][] — absorption and
distributivity — now stated over `_≈_`{.AgdaFunction}.

```agda
module _ {c ℓ} (S : DecSetoid c ℓ) (E : Exhaustible (DecSetoid.Carrier S)) where
  open DecSetoid S   using ( Carrier ; _≈_ ; _≟_ )
  open Exhaustible E using ( all? )

  module _ (_·_ _∘_ : Carrier → Carrier → Carrier) where

    -- a · (a ∘ b) ≈ a for every a, b.
    Absorbsˡᴰ? : Dec (∀ a b → (a · (a ∘ b)) ≈ a)
    Absorbsˡᴰ? = all? (λ a → all? (λ b → (a · (a ∘ b)) ≟ a))

    -- (a · b) ∘ a ≈ a for every a, b.
    Absorbsʳᴰ? : Dec (∀ a b → ((a · b) ∘ a) ≈ a)
    Absorbsʳᴰ? = all? (λ a → all? (λ b → ((a · b) ∘ a) ≟ a))

    -- a · (b ∘ c) ≈ (a · b) ∘ (a · c) for every a, b, c.
    Distributesˡᴰ? : Dec (∀ a b c → (a · (b ∘ c)) ≈ ((a · b) ∘ (a · c)))
    Distributesˡᴰ? = all? (λ a → all? (λ b → all? (λ c → (a · (b ∘ c)) ≟ ((a · b) ∘ (a · c)))))

    -- (b ∘ c) · a ≈ (b · a) ∘ (c · a) for every a, b, c.
    Distributesʳᴰ? : Dec (∀ a b c → ((b ∘ c) · a) ≈ ((b · a) ∘ (c · a)))
    Distributesʳᴰ? = all? (λ a → all? (λ b → all? (λ c → ((b ∘ c) · a) ≟ ((b · a) ∘ (c · a)))))
```

#### The finite instance

`Fin n`{.AgdaDatatype} is exhaustively searchable: its search functional is precisely
`Data.Fin.Properties.all?`.  Wrapping it gives the canonical `Exhaustible`{.AgdaRecord}
witness for `Fin n`{.AgdaDatatype}, the one that recovers the concrete checkers.

```agda
-- The exhaustive-search witness for Fin n, given by Fin's all?.
Fin-Exhaustible : ∀ {n} → Exhaustible (Fin n)
Fin-Exhaustible = record { all? = FinP.all? }
```

#### The finite checkers as the propositional instance

Take `S` to be `FinP.≡-decSetoid n` — the propositional decidable setoid on
`Fin n`{.AgdaDatatype}, whose `_≈_`{.AgdaFunction} is `_≡_`{.AgdaDatatype} and whose
`_≟_`{.AgdaFunction} is `Data.Fin.Properties._≟_` — and `E` to be
`Fin-Exhaustible`{.AgdaFunction}.  Each generalized checker then *unfolds definitionally*
to the corresponding concrete checker of [Overture.Operations.Properties][]: the
search functional reduces to `Fin`'s `all?`{.AgdaFunction} and `_≟_`{.AgdaFunction}
reduces to `Fin`'s decidable equality.  We record that as eleven `refl`{.AgdaInductiveConstructor}
equations, one per checker.  This is the precise sense in which the concrete checkers
*are* the propositional instance of the generalized ones — and, because the equalities
are definitional, the concrete checkers keep reducing exactly as before for
`from-yes`{.AgdaFunction}, so the finite examples are unaffected.

```agda
module _ {n : ℕ} (_·_ : Fin n → Fin n → Fin n) where

  Idempotent?≡ : Concrete.Idempotent? _·_ ≡ Idempotentᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_
  Idempotent?≡ = refl

  Commutative?≡ : Concrete.Commutative? _·_ ≡ Commutativeᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_
  Commutative?≡ = refl

  Associative?≡ : Concrete.Associative? _·_ ≡ Associativeᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_
  Associative?≡ = refl

  module _ (e : Fin n) where

    LeftIdentity?≡ : Concrete.LeftIdentity? _·_ e ≡ LeftIdentityᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ e
    LeftIdentity?≡ = refl

    RightIdentity?≡ : Concrete.RightIdentity? _·_ e ≡ RightIdentityᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ e
    RightIdentity?≡ = refl

    module _ (i : Fin n → Fin n) where

      LeftInverse?≡ : Concrete.LeftInverse? _·_ e i ≡ LeftInverseᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ e i
      LeftInverse?≡ = refl

      RightInverse?≡ : Concrete.RightInverse? _·_ e i ≡ RightInverseᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ e i
      RightInverse?≡ = refl

module _ {n : ℕ} (_·_ _∘_ : Fin n → Fin n → Fin n) where

  Absorbsˡ?≡ : Concrete.Absorbsˡ? _·_ _∘_ ≡ Absorbsˡᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ _∘_
  Absorbsˡ?≡ = refl

  Absorbsʳ?≡ : Concrete.Absorbsʳ? _·_ _∘_ ≡ Absorbsʳᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ _∘_
  Absorbsʳ?≡ = refl

  Distributesˡ?≡ : Concrete.Distributesˡ? _·_ _∘_ ≡ Distributesˡᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ _∘_
  Distributesˡ?≡ = refl

  Distributesʳ?≡ : Concrete.Distributesʳ? _·_ _∘_ ≡ Distributesʳᴰ? (FinP.≡-decSetoid n) Fin-Exhaustible _·_ _∘_
  Distributesʳ?≡ = refl
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
      to (_  , pt) true  = pt
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
  ∧-idem-bool : ∀ a → (a ∧ a) ≡ a
  ∧-idem-bool = from-yes (Idempotentᴰ? BoolP.≡-decSetoid Bool-Exhaustible _∧_)

  ∧-comm-bool : ∀ a b → (a ∧ b) ≡ (b ∧ a)
  ∧-comm-bool = from-yes (Commutativeᴰ? BoolP.≡-decSetoid Bool-Exhaustible _∧_)

  ∧-assoc-bool : ∀ a b c → ((a ∧ b) ∧ c) ≡ (a ∧ (b ∧ c))
  ∧-assoc-bool = from-yes (Associativeᴰ? BoolP.≡-decSetoid Bool-Exhaustible _∧_)

  ∧-absorbs-∨-bool : ∀ a b → (a ∧ (a ∨ b)) ≡ a
  ∧-absorbs-∨-bool = from-yes (Absorbsˡᴰ? BoolP.≡-decSetoid Bool-Exhaustible _∧_ _∨_)
```

--------------------------------------

<span style="float:left;">[↑ Setoid](Setoid.html)</span>

{% include UALib.Links.md %}
