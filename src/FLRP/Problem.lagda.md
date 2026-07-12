---
layout: default
file: "src/FLRP/Problem.lagda.md"
title: "FLRP.Problem module (The Agda Universal Algebra Library)"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### The Finite Lattice Representation Problem: statement and first instances

This is the [FLRP.Problem][] module of the [Agda Universal Algebra Library][].

The **Finite Lattice Representation Problem** (FLRP) asks: is every finite
lattice isomorphic to the congruence lattice `Con 𝑨`{.AgdaFunction} of some
*finite* algebra `𝑨`{.AgdaBound}?

By Grätzer–Schmidt every algebraic lattice is the congruence lattice of an *infinite*
algebra, so the finiteness of the algebra is the crucial content of the question,
which has been open since the 1960s.

This module opens the library's FLRP research tree[^1] by making the problem itself a
first-class, type-checked object.

+  `Representable`{.AgdaRecord} `𝑳`: the data of a finite algebra whose congruence
   lattice is order-isomorphic to the lattice `𝑳`{.AgdaBound};

+  `FLRP-Statement`{.AgdaFunction}: the formal statement "every finite lattice is
   representable", as a type that the library *states but does not assert*;

+  a first worked instance (the one-element chain), and (in place of the two-element
   instance) a machine-checked *constructivity "no-go" theorem* explaining why no
   nontrivial instance can be produced under this library's `--safe`, postulate-free
   discipline.

A standing warning applies: the FLRP is a research track of its own and should not be
conflated with the algebraic-complexity / finite-CSP work elsewhere in the library.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Problem where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive       using () renaming ( Set to Type )
open import Data.Empty           using ( ⊥ ; ⊥-elim )
open import Data.Fin             using ( Fin )
open import Data.Fin.Patterns    using ( 0F ; 1F )
open import Data.Fin.Properties  using ( _≟_ )
open import Data.Nat.Base        using ( ℕ ; suc )
open import Data.Product         using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base        using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base       using ( tt )
open import Data.Vec.Base        using ( _∷_ ; [] )
open import Function             using (_∘_)
open import Level                using ( Level ; 0ℓ ; _⊔_ ; lift ; lower )
                                 renaming ( suc to lsuc )
open import Relation.Binary      using ( Setoid ) renaming ( Rel to BinaryRel )
open import Relation.Binary.PropositionalEquality
                                 using ( _≡_ ; refl ; sym ; trans ; subst ; module ≡-Reasoning)
open import Relation.Nullary     using ( ¬_ ; yes ; no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture                            using ( Signature )
open import Overture.Cayley                     using ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties      using ( Associative? ; Commutative?
                                                      ; Idempotent? ; Absorbsˡ?
                                                      ; Absorbsʳ? )
open import Classical.Signatures.Lattice        using ( Sig-Lattice )
open import Classical.Small.Structures.Lattice  using ( Lattice ; eqsToLattice )
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Setoid.Algebras.Basic as SetoidAlgebras using (Algebra ; 𝔻[_])

import Setoid.Congruences.Basic             as SetoidCongruences
import Setoid.Congruences.Lattice           as CongruenceOrder
import Setoid.Congruences.Generation        as CongruenceGeneration
import Setoid.Algebras.Finite               as FiniteAlgebras
```
-->

#### Order isomorphisms

Both sides of a representation are *ordered* objects: the congruence lattice of an
algebra is the poset `(Con 𝑨 , ≑ , ⊆)` of [Setoid.Congruences.Lattice][], and a
classical lattice carries its meet order from [Classical.Properties.Lattice][].

The right notion of "the same lattice" for two such posets is an **order isomorphism**:
a pair of monotone maps that are mutually inverse up to the respective equivalences.

Because both maps are monotone and the round trips are the identity up to `≈`, an
order isomorphism transports every existing infimum and supremum, so isomorphic
posets carry the same lattice (indeed, complete-lattice) structure; this is why no
separate preservation clauses for meet and join are needed.

`OrderIso`{.AgdaRecord} states this for raw relations, so it applies uniformly to
setoid-valued and propositional orders.  It is kept here, next to its first use; once
the group-theoretic side of the program needs it (work package WP-3,
`Con (G ↷ G/H) ≅ [H , G]`), it should migrate to the `Order/` tree beside
[Order.CompleteLattice][].

(The standard library's `IsOrderIsomorphism`{.AgdaRecord} packages one map with
surjectivity instead of an explicit inverse; the two presentations are
interconvertible, and the inverse-pair form is the convenient one for transporting
structure.)

```agda
record OrderIso
  {a b ℓ₁ ℓ₂ m₁ m₂ : Level}
  {A : Type a} {B : Type b}
  (_≈₁_ : BinaryRel A ℓ₁) (_≤₁_ : BinaryRel A ℓ₂)
  (_≈₂_ : BinaryRel B m₁) (_≤₂_ : BinaryRel B m₂) : Type (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ m₁ ⊔ m₂) where
  field
    to         : A → B
    from       : B → A
    to-mono    : ∀ {x y} → x ≤₁ y → to x ≤₂ to y
    from-mono  : ∀ {u v} → u ≤₂ v → from u ≤₁ from v
    to∘from    : ∀ u → to (from u) ≈₂ u
    from∘to    : ∀ x → from (to x) ≈₁ x
```

#### Congruence lattices versus classical lattices

A representation compares two differently-presented ordered structures, and the
comparison is deliberately arranged so that *no bridging construction is needed* on
either side.

+  **The algebra side**.  For an algebra `𝑨` over a signature `𝑆 : Signature 0ℓ 0ℓ`,
   the congruences `Con 𝑨` at relation level `0ℓ` form a poset under containment
   `_⊆_` with equivalence `_≑_` (mutual containment).

   This is `Con-Poset`{.AgdaFunction} of [Setoid.Congruences.Lattice][], and
   [Setoid.Congruences.CompleteLattice][] upgrades it to a complete lattice.

   With all levels at `0ℓ` the absorbing congruence level is again `0ℓ`, so a
   single relation level suffices throughout.

+  **The lattice side**.  The input lattice is a `Lattice`{.AgdaFunction} of
   [Classical.Small.Structures.Lattice][], an equational algebra over
   `Sig-Lattice`{.AgdaFunction}, the Cayley-table style presentation used by the
   worked examples such as [Examples.Classical.Lattices.L7][].

   Its meet partial order `x ≤ y := x ∧ y ≈ x`, together with proofs that this is a
   genuine partial order whose meet and join are the greatest lower and least upper
   bounds, is already provided by `Lattice-Order`{.AgdaRecord} of
   [Classical.Properties.Lattice][].

`ConIso`{.AgdaFunction} `𝑨`{.AgdaBound} `𝑳`{.AgdaBound} says the congruence poset of
`𝑨`{.AgdaBound} is order-isomorphic to the meet order of `𝑳`{.AgdaBound}.  Since both
sides are lattices and order isomorphisms transport meets and joins, this is exactly
"`Con 𝑨` and `𝑳` are isomorphic lattices", stated without redundant clauses.

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}
  where
  open CongruenceOrder {𝑆 = 𝑆} using ( _⊆_ ; _≑_ )
  ConIso : Algebra 0ℓ 0ℓ → Lattice → Type (lsuc 0ℓ)
  ConIso 𝑨 𝑳 = OrderIso  (_≑_ {𝑨 = 𝑨}) _⊆_ (Setoid._≈_ 𝔻[ proj₁ 𝑳 ]) (Lattice-Order._≤_ 𝑳)
```

#### Finite lattices

The FLRP quantifies over *finite* lattices, so the formal statement needs a finite
presentation to range over.  A `FiniteLattice`{.AgdaRecord} is a lattice given by
finite data in the style of the library's Cayley-table examples: a carrier
`Fin (suc size)` (lattices are nonempty, hence the successor), two binary operations,
and the eight lattice equations, each a decidable statement over the finite carrier
that concrete instances discharge with `from-yes`{.AgdaFunction}.  Every finite
lattice is isomorphic to one presented this way (enumerate the carrier), so
quantifying over `FiniteLattice`{.AgdaRecord} is quantifying over finite lattices up
to isomorphism, which is all the FLRP asks.

```agda
record FiniteLattice : Type 0ℓ where
  field
    size : ℕ

  -- The carrier of the presentation; suc keeps it nonempty.
  Carrier : Type 0ℓ
  Carrier = Fin (suc size)

  infixr 6 _∧_
  infixr 6 _∨_

  field
    _∧_ _∨_  : Carrier → Carrier → Carrier
    ∧-assoc  : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
    ∧-comm   : ∀ a b → a ∧ b ≡ b ∧ a
    ∧-idem   : ∀ a → a ∧ a ≡ a
    ∨-assoc  : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
    ∨-comm   : ∀ a b → a ∨ b ≡ b ∨ a
    ∨-idem   : ∀ a → a ∨ a ≡ a
    absorbˡ  : ∀ a b → a ∧ (a ∨ b) ≡ a
    absorbʳ  : ∀ a b → (a ∧ b) ∨ a ≡ a
```

A finite presentation yields a classical lattice by feeding its data to
`eqsToLattice`{.AgdaFunction}; this is how each `FiniteLattice`{.AgdaRecord}
below enters the `Representable`{.AgdaRecord} predicate.

```agda
toLattice : FiniteLattice → Lattice
toLattice 𝑳 = eqsToLattice Carrier _∧_ _∨_
                ∧-assoc ∧-comm ∧-idem ∨-assoc ∨-comm ∨-idem absorbˡ absorbʳ
  where open FiniteLattice 𝑳
```

#### Representability

`Representable 𝑳`{.AgdaRecord} is the constructive reading of "there exists a
finite algebra whose congruence lattice is isomorphic to `𝑳`{.AgdaBound}": a
signature, an algebra over it, a witness that the algebra is finite, and the
order isomorphism.  Two design choices deserve comment.

+  **Levels**.  Signature, algebra, and congruences all live at level `0ℓ`.  A
   finite algebra needs no more room than that, and fixing the levels keeps the
   existential quantification over signatures first-order (Agda cannot
   quantify existentially over universe levels).
+  **Finiteness**.  "Finite algebra" is the bare `FiniteAlgebra`{.AgdaRecord}
   interface of [Setoid.Algebras.Finite][]: decidable setoid equality and a
   finite surjective enumeration of the carrier — carrier-level data only,
   free of classical content.  The congruence-side interface
   (`FiniteCongruences`{.AgdaRecord} of [Setoid.Congruences.Finite][], whose
   completeness field is precisely the classical content of "finite" for
   congruence-lattice purposes) is deliberately *not* required here;
   `Representable`{.AgdaRecord} carries an explicit isomorphism instead, and
   complete congruence enumerations enter only with the decidable-layer
   reformulation of ADR-008.  There they are also exactly the shape of datum
   an external search emits, lining up with the certificate discipline of the
   `FLRP.Certificates` work package.

```agda
record Representable (𝑳 : Lattice) : Type (lsuc 0ℓ) where
  field
    sig      : Signature 0ℓ 0ℓ
    alg      : Algebra {𝑆 = sig} 0ℓ 0ℓ
    finite   : FiniteAlgebras.FiniteAlgebra {𝑆 = sig} alg
    con-iso  : ConIso {𝑆 = sig} alg 𝑳
```

#### The FLRP statement

The Finite Lattice Representation Problem, as the type
`FLRP-Statement`{.AgdaFunction}: every finite lattice is representable.

```agda
FLRP-Statement : Type (lsuc 0ℓ)
FLRP-Statement = (𝑳 : FiniteLattice) → Representable (toLattice 𝑳)
```

Note that we have merely definee a type, without providing an inhabitant.
Indeed, no definition below (or anywhere in the library for that matter) inhabits
`FLRP-Statement`{.AgdaFunction} or its negation; whether the classical reading of the
statement is true is exactly the open problem, and the research program tracked in
`docs/notes/flrp-research-roadmap.md` is an attempt to decide it.

Two glosses keep the formal statement honest.

+  **The constructive reading is strictly stronger than the classical one**.

   The no-go theorem at the end of this module shows that any inhabitant of
   `Representable (toLattice chain₂)`{.AgdaRecord} — the *two-element chain*
   — already yields **weak excluded middle** for level-zero types.

   So `FLRP-Statement`{.AgdaFunction} is not merely unproved but *unprovable* in Agda
   `--safe` mode without classical axioms, independently of the fate of the FLRP; it
   is the faithful formal statement whose classical truth is open, not a statement
   the program expects to inhabit directly.

   A future negative solution would likewise be formalized against classical
   assumptions registered explicitly (the planned `FLRP.Assumptions` module), not
   against this type alone.

+  **The distinguished open instance is `L7`**.

   The seven-element lattice `L7-lattice`{.AgdaFunction} of
   [Examples.Classical.Lattices.L7][] is, to our knowledge, the smallest lattice for
   which no representation as the congruence lattice of a finite algebra is known;
   every lattice with at most seven elements except possibly `L7` is representable.

   Since `L7-lattice`{.AgdaFunction} is a `Lattice`{.AgdaFunction} in exactly the
   sense used here, `Representable L7-lattice`{.AgdaRecord} is a well-formed type
   as-is.[^2]


#### The empty signature and the one-element algebra

The first worked instance lives over the **empty signature** — no operation
symbols, hence no arities, hence vacuous compatibility.  (The same signature,
under the name `𝑆₀`{.AgdaFunction}, drives the two-element congruence-lattice
example in [Examples.Setoid.CongruenceLattice][]; any signature would do here,
and the empty one is the smallest.)

```agda
𝑆∅ : Signature 0ℓ 0ℓ
𝑆∅ = ⊥ , λ ()
```

The representing algebra is the one-element algebra `𝟏`{.AgdaFunction} of
[Setoid.Algebras.Finite][], instantiated at `𝑆∅`{.AgdaFunction},
together with its ready-made finiteness witness
`𝟏-FiniteAlgebra`{.AgdaFunction}.  We also fix the diagonal congruence and its
minimality at this signature, renamed with a `∅` mark to keep them apart from
the same names used at other signatures below.

```agda
open FiniteAlgebras     {𝑆 = 𝑆∅}  using ( 𝟏 ; 𝟏-FiniteAlgebra )
open SetoidCongruences  {𝑆 = 𝑆∅}  using () renaming ( 𝟘[_] to 𝟘∅[_] )
open CongruenceOrder    {𝑆 = 𝑆∅}  using () renaming ( 𝟘-min to 𝟘∅-min )
```

#### Instance: the one-element chain is representable

`chain₁`{.AgdaFunction} is the one-element lattice, presented by the constant
operations on `Fin 1`; its laws are discharged by decision over the
(one-element) carrier.

```agda
_∧₁_ _∨₁_ : Fin 1 → Fin 1 → Fin 1
_ ∧₁ _ = 0F
_ ∨₁ _ = 0F

chain₁ : FiniteLattice
chain₁ = record
  { size     = 0
  ; _∧_      = _∧₁_
  ; _∨_      = _∨₁_
  ; ∧-assoc  = from-yes (Associative? _∧₁_)
  ; ∧-comm   = from-yes (Commutative? _∧₁_)
  ; ∧-idem   = from-yes (Idempotent? _∧₁_)
  ; ∨-assoc  = from-yes (Associative? _∨₁_)
  ; ∨-comm   = from-yes (Commutative? _∨₁_)
  ; ∨-idem   = from-yes (Idempotent? _∨₁_)
  ; absorbˡ  = from-yes (Absorbsˡ? _∧₁_ _∨₁_)
  ; absorbʳ  = from-yes (Absorbsʳ? _∧₁_ _∨₁_)
  }

chain₁-lattice : Lattice
chain₁-lattice = toLattice chain₁
```

Every congruence of `𝟏`{.AgdaFunction} is `≑`-equal to the diagonal
`𝟘∅[ 𝟏 ]`{.AgdaFunction}: the setoid equality of `𝟏`{.AgdaFunction} relates
everything, and a congruence contains the setoid equality by reflexivity, so
`Con 𝟏` is a one-element poset up to `_≑_`{.AgdaFunction}.  The isomorphism
with `chain₁-lattice`{.AgdaFunction} is therefore given by constant maps, and
every proof obligation is either `refl`{.AgdaFunction} or the (two-line)
collapse of `Con 𝟏`.  This instance is **fully constructive** — no decidability
beyond the finite carrier is consumed — and it instantiates
`FLRP-Statement`{.AgdaFunction} at `chain₁`{.AgdaFunction}.

```agda
private
  -- Fin 1 is propositional: everything equals 0F.
  0F≡ : (u : Fin 1) → 0F ≡ u
  0F≡ 0F = refl

chain₁-Representable : Representable chain₁-lattice
chain₁-Representable = record
  { sig      = 𝑆∅
  ; alg      = 𝟏
  ; finite   = 𝟏-FiniteAlgebra
  ; con-iso  = record
      { to         = λ _ → 0F
      ; from       = λ _ → 𝟘∅[ 𝟏 ]
      ; to-mono    = λ _ → refl
      ; from-mono  = λ _ p → p
      ; to∘from    = 0F≡
      ; from∘to    = λ θ → 𝟘∅-min θ , (λ _ → lift tt)
      }
  }
open Representable
```

#### The two-element chain

`chain₂`{.AgdaFunction} is the two-element chain `0 < 1`, presented by Cayley
tables exactly as in [Examples.Classical.Lattices.L7][]: meet is minimum, join
is maximum, and the laws are decided over the carrier.

```agda
∧₂-table ∨₂-table : Table 2
∧₂-table = (0F ∷ 0F ∷ []) ∷ (0F ∷ 1F ∷ []) ∷ []
∨₂-table = (0F ∷ 1F ∷ []) ∷ (1F ∷ 1F ∷ []) ∷ []

_∧₂_ _∨₂_ : Fin 2 → Fin 2 → Fin 2
_∧₂_ = ⟦ ∧₂-table ⟧
_∨₂_ = ⟦ ∨₂-table ⟧

chain₂ : FiniteLattice
chain₂ = record
  { size     = 1
  ; _∧_      = _∧₂_
  ; _∨_      = _∨₂_
  ; ∧-assoc  = from-yes (Associative? _∧₂_)
  ; ∧-comm   = from-yes (Commutative? _∧₂_)
  ; ∧-idem   = from-yes (Idempotent? _∧₂_)
  ; ∨-assoc  = from-yes (Associative? _∨₂_)
  ; ∨-comm   = from-yes (Commutative? _∨₂_)
  ; ∨-idem   = from-yes (Idempotent? _∨₂_)
  ; absorbˡ  = from-yes (Absorbsˡ? _∧₂_ _∨₂_)
  ; absorbʳ  = from-yes (Absorbsʳ? _∧₂_ _∨₂_)
  }

chain₂-lattice : Lattice
chain₂-lattice = toLattice chain₂
```

Classically, representing `chain₂`{.AgdaFunction} is trivial: the two-element
algebra `𝟚` over the empty signature has exactly two congruences (the diagonal
and the total relation), so `Con 𝟚` *is* the two-element chain — the library
already builds its lattice bundles in [Examples.Setoid.CongruenceLattice][].
Constructively, however, the instance is unattainable, and the obstruction is a
theorem, proved next.

#### The constructivity no-go theorem

A congruence in this library is a `Type`-valued relation, so `Con 𝑨` contains,
for *every* proposition `P`, the **switch congruence**
`θ[ P ] = Cg (λ _ _ → P)` — the congruence generated by the
relation that relates everything exactly when `P` holds.  If `P` holds,
`θ[ P ]` is the total congruence; if `¬ P`, it collapses to the diagonal.
An order isomorphism `to : Con 𝑨 → Fin 2` would therefore act as an oracle:
where `to θ[ P ]` lands in the two-element chain *decides* `P` — up to the double
negation inherent in reading membership of a generated congruence — and no such
oracle is definable in `--safe` Agda.

Concretely, `chain₂-ConIso→WLEM`{.AgdaFunction} extracts from any
`ConIso 𝑨 chain₂-lattice`{.AgdaFunction} (over *any* signature and *any* algebra)
**weak excluded middle** for level-zero types, which is the *non-constructive*
formula,

```agda
WLEM₀ : Type (lsuc 0ℓ)
WLEM₀ = ∀ P → ¬ P ⊎ ¬ ¬ P
```

The proof needs three small facts, each with a one-line justification.

+  `to-cong`{.AgdaFunction}: `≑`-equal congruences have equal images, because both
   images lie below one another in the chain and the meet order of a lattice is
   antisymmetric (`≤-antisym`{.AgdaFunction} of [Classical.Properties.Lattice][]).
+  `no-collapse`: `to` cannot identify the diagonal `Δ` and the total
   congruence `∇`.  If it did, the round trip would force `Δ ≑ ∇`, making the
   setoid equality of `𝑨`{.AgdaBound} total; then *all* congruences are
   `≑`-equal (each contains the setoid equality by reflexivity), so `to` after
   `from` would identify the two elements of the chain — but `0F ≢ 1F`.
+  The decision: `Fin 2` has decidable equality, so we may ask whether
   `to θ[ P ]` equals `to ∇`.  A *yes* refutes `¬ P` (if `¬ P` held, `θ[ P ]`
   would collapse to `Δ` by `Cg-least`{.AgdaFunction}, contradicting
   `no-collapse`), giving `¬ ¬ P`; a *no* refutes `P` (if `P` held, `θ[ P ]`
   would equal `∇` by the `base`{.AgdaFunction} rule of the generated
   congruence), giving `¬ P`.

```agda
module _ {𝑆 : Signature 0ℓ 0ℓ} where
  open SetoidCongruences     {𝑆 = 𝑆}  using ( Con ; 𝟘[_] ; 𝟙[_] ; reflexive )
  open CongruenceOrder       {𝑆 = 𝑆}  using ( _⊆_ ; _≑_ ; 𝟘-min )
  open CongruenceGeneration  {𝑆 = 𝑆}  using ( Cg ; Cg-least ; base )

  module _ (𝑨 : Algebra 0ℓ 0ℓ) (iso : ConIso 𝑨 chain₂-lattice) where
    open OrderIso       iso
    open Setoid         𝔻[ 𝑨 ]         using ( _≈_ )
    open Lattice-Order  chain₂-lattice  using ( ≤-antisym )

    private
      -- The diagonal and total congruences of 𝑨, at level 0ℓ.
      Δ ∇ : Con 𝑨 0ℓ
      Δ = 𝟘[ 𝑨 ] ; ∇ = 𝟙[ 𝑨 ]

      -- The switch congruence of P: total if P holds, diagonal if P fails.
      θ[_] : Type 0ℓ → Con 𝑨 0ℓ
      θ[ P ] = Cg {𝑨 = 𝑨} (λ _ _ → P)

      -- ≑-equal congruences land on the same chain element.
      to-cong : (θ φ : Con 𝑨 0ℓ) → θ ≑ φ → to θ ≡ to φ
      to-cong θ φ (θ⊆φ , φ⊆θ) = ≤-antisym (to-mono θ⊆φ) (to-mono φ⊆θ)

      -- The images of Δ and ∇ are distinct: otherwise 𝑨 would be trivial,
      -- Con 𝑨 would collapse, and 0F ≡ 1F would follow via the round trips.
      no-collapse : to Δ ≡ to ∇ → ⊥
      no-collapse e = absurd01 0F≡1F
        where
        all-≈ : ∀ x y → x ≈ y
        all-≈ x y =
          lower (proj₁ (from∘to Δ)
                 (subst  (λ c → proj₁ (from c) x y) (sym e)
                         (proj₂ (from∘to ∇) (lift tt))))

        collapse : (θ φ : Con 𝑨 0ℓ) → θ ≑ φ
        collapse (_ , θcon) (_ , φcon) = (λ {x} {y} _ → reflexive φcon (all-≈ x y))
                                       , (λ {x} {y} _ → reflexive θcon (all-≈ x y))

        0F≡1F : 0F ≡ 1F
        0F≡1F = begin
          0F            ≡˘⟨ to∘from 0F ⟩
          to (from 0F)  ≡⟨ to-cong  (from 0F) (from 1F) (collapse (from 0F) (from 1F)) ⟩
          to (from 1F)  ≡⟨ to∘from 1F ⟩
          1F            ∎
          where open ≡-Reasoning

        absurd01 : 0F ≡ 1F → ⊥
        absurd01 ()

    -- Any order isomorphism Con 𝑨 ≅ chain₂ decides, for every level-zero
    -- type P, between ¬ P and ¬ ¬ P: weak excluded middle.
    chain₂-ConIso→WLEM : WLEM₀
    chain₂-ConIso→WLEM P with to θ[ P ] ≟ to ∇
    ... | no ne = inj₁ ¬P
      where
      ξ : P → to θ[ P ] ≡ to ∇
      ξ = λ p → to-cong θ[ P ] ∇ ((λ _ → lift tt) , λ _ → base p)

      ¬P : ¬ P
      ¬P = λ p → ne (ξ p)

    ... | yes e = inj₂ ¬¬P
      where
      ξ : ¬ P → to Δ ≡ to θ[ P ]
      ξ = λ ¬p → to-cong Δ θ[ P ] ( 𝟘-min θ[ P ] , Cg-least Δ λ p → ⊥-elim (¬p p) )

      γ : ¬ P → to Δ ≡ to ∇
      γ = λ ¬p → trans (ξ ¬p) e

      ¬¬P : ¬ ¬ P
      ¬¬P = no-collapse ∘ γ
```

The corollary about representability just forgets the finiteness witness.

```agda
chain₂-Representable→WLEM : Representable chain₂-lattice → WLEM₀
chain₂-Representable→WLEM r = chain₂-ConIso→WLEM (r .alg) (r .con-iso)
```

#### What the no-go theorem means, and where the program goes next

Weak excluded middle is independent of the type theory this library works in,
so `Representable chain₂-lattice`{.AgdaRecord} has no inhabitant under
`--safe` — and none is expected: the two-element chain already exhibits the
full classical content of the problem statement.  Three consequences are worth
recording, since they shape the work packages that follow.

+  **The obstruction is in `Con`, not in `FiniteAlgebra`**.

   The theorem never touches the finiteness witness; the non-constructive taboo
   flows from the order isomorphism alone, because `Con 𝑨` contains indicator
   congruences for arbitrary propositions.  Baking decidability into the algebra
   cannot help.

   Indeed, the carrier-level `FiniteAlgebra`{.AgdaRecord} interface of
   [Setoid.Algebras.Finite][] is constructively innocent, and the classical
   strength sits precisely in the congruence-side `FiniteCongruences`{.AgdaRecord}
   of [Setoid.Congruences.Finite][] — over the empty signature, its
   `complete`{.AgdaFunction} field applied to an indicator congruence on a
   two-element carrier would decide arbitrary propositions outright, so
   `FiniteCongruences 𝟚` is as unprovable as excluded middle (LEM).[^3]

   This is the promised sharpening of that module's warning that the complete
   congruence list is "exactly the classical content" of finiteness.

+  **`Representable` is constructively inhabited by the one-element lattice alone**.

   Every lattice with two provably distinct elements admits an
   order embedding of `chain₂`, and the argument above then applies verbatim,
   so every nontrivial instance of `Representable`{.AgdaRecord} is
   LEM-hard.

   As such, positive results in this tree will be *relative* to

   +  a classical postulate, or
   +  hypotheses registered in the planned `FLRP.Assumptions` module,

   or will be reformulated as in the next point.

+  **Certificates must target the decidable-congruence poset**.

   For a concrete finite algebra given by tables, the poset of *decidable*
   congruences (`DecCon`{.AgdaFunction} of [Setoid.Congruences.Finite][], up to
   `_≑_`{.AgdaFunction}) is itself finite data: a decidable congruence on `Fin n`
   can be tabulated, and completeness of a candidate list *of decidable congruences*
   is decidable.

   An Agda-checked certificate that `Con 𝑨 ≅ 𝑳` should therefore assert the
   isomorphism against the decidable-congruence poset — classically the same
   lattice, constructively checkable — and this reformulation, not
   `Representable`{.AgdaRecord} itself, is the correct target for the
   certificate pipeline.  Stating that reformulation and proving its classical
   equivalence to `Representable`{.AgdaRecord} is left as the natural sequel to this
   module.

---

[^1]: see `docs/notes/flrp-research-roadmap.md`, § 6-7, work package WP-1.


[^2]: We deliberately do not import the example module (examples consume the library,
      not conversely); a `FiniteLattice`{.AgdaRecord} presentation of `L7` will
      accompany the certificate tooling of a later work package.

[^3]: Recall, the classical **law of the excluded middle** (lem) asserts that
      every proposition either holds or not (`∀ P → P ∨ ¬ P`), the quintessential
      non-constructive axiom which, here, does not abide.
