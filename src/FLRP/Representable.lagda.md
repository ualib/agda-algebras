---
layout: default
file: "src/FLRP/Representable.lagda.md"
title: "FLRP.Representable module (The Agda Universal Algebra Library)"
date: "2026-07-20"
author: "the agda-algebras development team"
---

### The decidable-layer reformulation of the FLRP, and the constructive two-element chain

This is the [FLRP.Representable][] module of the [Agda Universal Algebra Library][].

[FLRP.Problem][] states the Finite Lattice Representation Problem at the *semantic*
congruence layer (Layer S of [ADR-008][]) and proves the constructivity no-go
theorem: any order isomorphism `Con 𝑨 ≅ chain₂-lattice`{.AgdaFunction} yields weak
excluded middle, so `Representable chain₂-lattice`{.AgdaRecord} has no inhabitant
under `--safe`.  The obstruction is that `Con 𝑨`{.AgdaFunction} contains an oracle
congruence for every proposition, and reading off where an isomorphism sends it
decides that proposition.

This module supplies the **Layer-D reformulation** (L5 of the two-layer discipline,
`docs/notes/flrp-two-layer-congruences.md` § 3), which quantifies not over all
semantic congruences but over the *decidable* congruences `DecCon`{.AgdaFunction} of
[Setoid.Congruences.Finite.Basic][].  A decidable congruence carries its own decision
procedure, so it *can* be asked where it lands in a two-element chain — constructively,
with no axiom.  Concretely, this module provides:

+  `Representableᵈ`{.AgdaRecord} `𝑳`: the data of a *finite finitary* algebra whose
   decidable-congruence poset, up to `≑`{.AgdaFunction}, is order-isomorphic to the
   meet order of `𝑳`{.AgdaBound}; and `FLRP-Statementᵈ`{.AgdaFunction}, the Layer-D
   analogue of `FLRP-Statement`{.AgdaFunction}, stated but not asserted;

+  the **constructive `chain₂` representation** `chain₂-Representableᵈ`{.AgdaFunction}:
   the two-element algebra `𝟚`{.AgdaFunction} over the empty signature has, up to
   `≑`{.AgdaFunction}, exactly two decidable congruences — the diagonal and the total
   relation — so its `DecCon`{.AgdaFunction} poset *is* the two-element chain, proved
   with **no postulate**.  This is the object the no-go theorem showed impossible at
   Layer S; making it constructive here closes that loop.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Representable where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive       using () renaming ( Set to Type )
open import Data.Empty           using ( ⊥-elim )
open import Data.Fin.Base        using ( Fin )
open import Data.Fin.Patterns    using ( 0F ; 1F )
open import Data.Fin.Properties  using ( ¬Fin0 ; all? ; ¬∀⟶∃¬ ) renaming ( _≟_ to _≟ᶠ_ )
open import Data.Nat.Base        using ( zero ; suc )
open import Data.Product         using ( _,_ ; _×_ ; proj₁ ; proj₂ ; Σ-syntax )
open import Data.Sum.Base        using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base       using ( tt )
open import Level                using ( Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower )
                                 renaming ( suc to lsuc )
open import Relation.Binary      using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality
                                 using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary     using ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable
                                 using ( _→-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice         using  ( module Lattice-Order
                                                        ; TopOf ; BottomOf )
open import Classical.Small.Structures.Lattice   using  ( Lattice )
open import FLRP.Problem                         using  ( OrderIso ; FiniteLattice
                                                        ; toLattice ; 𝑆∅ ; chain₂-lattice )
open import Overture                             using  ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic                using  ( Algebra ; 𝔻[_] ; 𝕌[_]
                                                        ; mkAlgebraₚ )
open import Setoid.Algebras.Finite               using  ( FiniteAlgebra ; 𝟏
                                                        ; 𝟏-FiniteAlgebra )
open import Setoid.Congruences.Basic             using  ( reflexive ; 𝟘[_]
                                                        ; is-equivalence ; 𝟙[_] )
open import Setoid.Congruences.Finite.Basic      using  ( DecCon ; ConRel )
open import Setoid.Congruences.Finite.Decidable  using  ( FiniteCongruencesᵈ
                                                        ; FiniteAlgebra→FiniteCongruencesᵈ )
open import Setoid.Congruences.Lattice           using  ( _⊆_ ; _≑_ ; 𝟘-min ; 𝟙-max )
open import Setoid.Signatures.Finite             using  ( FiniteSignature )

private variable α ρ ℓ : Level
```
-->

#### The decidable-congruence poset order

A decidable congruence `d : DecCon 𝑨 ℓ`{.AgdaFunction} is a semantic congruence
`proj₁ d : Con 𝑨 ℓ`{.AgdaFunction} bundled with a decision procedure.  The
`DecCon`{.AgdaFunction} poset therefore inherits its order from the underlying
semantic congruences: containment and its induced equivalence are exactly the
containment `_⊆_`{.AgdaFunction} and mutual containment `_≑_`{.AgdaFunction} of
[Setoid.Congruences.Lattice][] read off the underlying `Con`{.AgdaFunction}s.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- Containment of decidable congruences: containment of their underlying congruences.
  _⊆ᵈ_ : DecCon 𝑨 ℓ → DecCon 𝑨 ℓ → Type (α ⊔ ℓ)
  d ⊆ᵈ e = proj₁ d ⊆ proj₁ e
  infix 4 _⊆ᵈ_

  -- Equivalence of decidable congruences: mutual containment of the underlying ones.
  _≑ᵈ_ : DecCon 𝑨 ℓ → DecCon 𝑨 ℓ → Type (α ⊔ ℓ)
  d ≑ᵈ e = proj₁ d ≑ proj₁ e
  infix 4 _≑ᵈ_
```

`ConIsoᵈ`{.AgdaFunction} `𝑨`{.AgdaBound} `𝑳`{.AgdaBound} is the decidable-layer
sibling of `ConIso`{.AgdaFunction} of [FLRP.Problem][], with the *same* presentation:
an `OrderIso`{.AgdaRecord} between the decidable-congruence poset `(DecCon 𝑨, ≑ᵈ, ⊆ᵈ)`
and the meet order of the classical lattice `𝑳`{.AgdaBound}.  Because both sides are
lattices and order isomorphisms transport meets and joins, this is exactly "the
`DecCon`{.AgdaFunction} poset of `𝑨`{.AgdaBound} and `𝑳`{.AgdaBound} are isomorphic
lattices", stated without redundant preservation clauses.

The "`DecCon`{.AgdaFunction} poset as a finite lattice with decidable order" claim is
left implicit in exactly this order-isomorphism target: the honest minimum needed to
state representability and to inhabit it for `chain₂`{.AgdaFunction} is the
`OrderIso`{.AgdaRecord} below, and the independent construction of the full finite
lattice bundle on `DecCon 𝑨`{.AgdaFunction} (a decidable order with meets and joins,
whose completeness on the enumerated list of [Setoid.Congruences.Finite.Decidable][]
is decidable) is deferred to the certificate tooling of a later work package.

```agda
ConIsoᵈ : {𝑆 : Signature 0ℓ 0ℓ} → Algebra {𝑆 = 𝑆} 0ℓ 0ℓ → Lattice → Type (lsuc 0ℓ)
ConIsoᵈ 𝑨 𝑳 = OrderIso  (_≑ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ}) (_⊆ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ})
                        (Setoid._≈_ 𝔻[ proj₁ 𝑳 ]) (Lattice-Order._≤_ 𝑳)
```

#### Decidable representability and the Layer-D FLRP statement

`Representableᵈ 𝑳`{.AgdaRecord} is the constructive reading of "there is a *finite
finitary* algebra whose decidable-congruence lattice is isomorphic to `𝑳`{.AgdaBound}":
a signature, an algebra over it, a witness that the carrier is finite
(`FiniteAlgebra`{.AgdaRecord}), a witness that the signature is finite finitary
(`FiniteSignature`{.AgdaRecord}), and the order isomorphism `ConIsoᵈ`{.AgdaFunction}.
It mirrors `Representable`{.AgdaRecord} of [FLRP.Problem][] with two differences: the
finiteness datum is the finite finitary pair `(FiniteAlgebra, FiniteSignature)` — the
exact input from which [Setoid.Congruences.Finite.Decidable][] builds a complete list
of decidable congruences — and the isomorphism is over `DecCon`{.AgdaFunction} rather
than semantic `Con`{.AgdaFunction}.

A note on the field superscripts.  The `ᵈ`{.AgdaBound} on `sigᵈ`{.AgdaField},
`algᵈ`{.AgdaField}, `finiteᵈ`{.AgdaField}, and `finsigᵈ`{.AgdaField} is *namespacing*,
not a claim of decidability: those fields hold the very same interfaces
`Representable`{.AgdaRecord} uses (`Signature`{.AgdaRecord}, `Algebra`{.AgdaRecord},
`FiniteAlgebra`{.AgdaRecord}, `FiniteSignature`{.AgdaRecord}), and `finiteᵈ`{.AgdaField}
in particular is carrier-finiteness, which is constructive.  Only
`con-isoᵈ`{.AgdaField} (`: ConIsoᵈ`{.AgdaFunction}) is a genuinely decidable-layer
datum.  The superscripts are carried on every field so that `Representable`{.AgdaRecord}
and `Representableᵈ`{.AgdaRecord} can be `open`ed together without their field names
clashing — which is what keeps the cross-layer transports of [FLRP.LayerBridge][]
legible — matching the all-superscripted convention of the sibling record
`FiniteCongruencesᵈ`{.AgdaRecord}.

```agda
record Representableᵈ (𝑳 : Lattice) : Type (lsuc 0ℓ) where
  field
    sigᵈ      : Signature 0ℓ 0ℓ
    algᵈ      : Algebra {𝑆 = sigᵈ} 0ℓ 0ℓ
    finiteᵈ   : FiniteAlgebra {𝑆 = sigᵈ} algᵈ
    finsigᵈ   : FiniteSignature sigᵈ
    con-isoᵈ  : ConIsoᵈ {𝑆 = sigᵈ} algᵈ 𝑳
```

The Finite Lattice Representation Problem, reformulated at Layer D: every finite
lattice is decidably representable.  As with `FLRP-Statement`{.AgdaFunction}, this is a
type the library *states but does not assert* — but, unlike its Layer-S sibling, its
`chain₂`{.AgdaFunction} instance is now *inhabited* (`chain₂-Representableᵈ`{.AgdaFunction}
below), so the Layer-D reformulation is not blocked by the no-go theorem.

```agda
FLRP-Statementᵈ : Type (lsuc 0ℓ)
FLRP-Statementᵈ = (𝑳 : FiniteLattice) → Representableᵈ (toLattice 𝑳)
```

#### The two-element algebra over the empty signature

The representing algebra of the two-element chain is the **two-element algebra**
`𝟚`{.AgdaFunction} over the empty signature `𝑆∅`{.AgdaFunction} of [FLRP.Problem][]:
carrier `Fin 2`{.AgdaDatatype} with propositional equality, and — since the empty
signature has no operation symbols — no operations to interpret.  This mirrors the
one-element algebra `𝟏`{.AgdaFunction} of [Setoid.Algebras.Finite][]; the smart
constructor `mkAlgebraₚ`{.AgdaFunction} discharges the (vacuous) compatibility
obligation from the empty operation set.

```agda
𝟚 : Algebra {𝑆 = 𝑆∅} 0ℓ 0ℓ
𝟚 = mkAlgebraₚ {𝑆 = 𝑆∅} (Fin 2) (λ ()) (λ ())
```

The carrier is finite: propositional equality on `Fin 2`{.AgdaDatatype} is decidable,
the identity enumerates the two elements, and it is (trivially) surjective.

```agda
open FiniteAlgebra

𝟚-FiniteAlgebra : FiniteAlgebra 𝟚
𝟚-FiniteAlgebra ._≟_       = _≟ᶠ_
𝟚-FiniteAlgebra .card      = 2
𝟚-FiniteAlgebra .enum      = λ i → i
𝟚-FiniteAlgebra .enum-sur  = λ x → x , refl
```

The empty signature is finite finitary for the trivial reason that it has no
operation symbols: the symbol enumeration has `opCard = 0`{.AgdaField}, and every
per-symbol obligation (`opEnum`{.AgdaField}, `opEnum-sur`{.AgdaField},
`finitary`{.AgdaField}) is a function out of the empty symbol type `⊥`.

```agda
𝑆∅-FiniteSignature : FiniteSignature 𝑆∅
𝑆∅-FiniteSignature = record
  { opCard      = 0
  ; opEnum      = λ ()
  ; opEnum-sur  = λ ()
  ; finitary    = λ ()
  }
```

Hence, via `FiniteAlgebra→FiniteCongruencesᵈ`{.AgdaFunction}, `𝟚`{.AgdaFunction} has a
constructively complete list of its decidable congruences — the Layer-D interface
`FiniteCongruencesᵈ`{.AgdaRecord} of [Setoid.Congruences.Finite.Decidable][], with no
classical assumption.  (The order isomorphism below does not route through this list;
it is recorded to exhibit that the L3 machinery applies to `𝟚`{.AgdaFunction}.)

```agda
𝟚-FiniteCongruencesᵈ : FiniteCongruencesᵈ 𝟚
𝟚-FiniteCongruencesᵈ = FiniteAlgebra→FiniteCongruencesᵈ 𝟚-FiniteAlgebra 𝑆∅-FiniteSignature
```

#### The two decidable congruences of `𝟚`

Up to `≑`{.AgdaFunction}, the two-element algebra has exactly two congruences: the
diagonal `𝟘[ 𝟚 ]`{.AgdaFunction} (relate the `≈`-equal pairs) and the total relation
`𝟙[ 𝟚 ]`{.AgdaFunction} (relate everything).  Both are decidable — the diagonal
because propositional equality on `Fin 2`{.AgdaDatatype} is decidable, the total
relation trivially — so both upgrade to `DecCon`{.AgdaFunction}s.

```agda
-- The diagonal congruence of 𝟚, as a decidable congruence.
Δᵈ : DecCon 𝟚 0ℓ
Δᵈ = 𝟘[ 𝟚 ] {0ℓ} , decΔ
  where
  decΔ : (x y : Fin 2) → Dec (Lift 0ℓ (x ≡ y))
  decΔ x y with x ≟ᶠ y
  ... | yes p  = yes (lift p)
  ... | no ¬p  = no λ q → ¬p (lower q)

-- The total congruence of 𝟚, as a decidable congruence.
∇ᵈ : DecCon 𝟚 0ℓ
∇ᵈ = 𝟙[ 𝟚 ] {0ℓ} , λ _ _ → yes (lift tt)
```

#### Classifying the decidable congruences of `𝟚`

The whole constructive content is one dichotomy: a decidable congruence `d` of
`𝟚`{.AgdaFunction} *decides its own value* at the one distinct pair `(0 , 1)`, and its
verdict determines it up to `≑`{.AgdaFunction}.  If `d` relates `0` and `1` it relates
everything (by reflexivity and symmetry over the two-point carrier), so it is
`≑`{.AgdaFunction} the total congruence; if it does not, every `d`-related pair is
`≡`-equal, so it is `≑`{.AgdaFunction} the diagonal.  These are the two named lemmas
below; `decRefl`{.AgdaFunction} and `decSym`{.AgdaFunction} are the reflexivity and
symmetry of `d`'s underlying congruence, named for legibility.

```agda
-- Reflexivity (over ≈, which is ≡ here) of a decidable congruence's relation.
decRefl : (d : DecCon 𝟚 0ℓ) {x y : Fin 2} → x ≡ y → ConRel d x y
decRefl d = reflexive (proj₂ (proj₁ d))

-- Symmetry of a decidable congruence's relation.
decSym : (d : DecCon 𝟚 0ℓ) {x y : Fin 2} → ConRel d x y → ConRel d y x
decSym d = IsEquivalence.sym (is-equivalence (proj₂ (proj₁ d)))

-- If d relates 0 and 1, then d relates every pair of the two-point carrier.
relates→all : (d : DecCon 𝟚 0ℓ) → ConRel d 0F 1F → ∀ x y → ConRel d x y
relates→all d r 0F 0F = decRefl d refl
relates→all d r 0F 1F = r
relates→all d r 1F 0F = decSym d r
relates→all d r 1F 1F = decRefl d refl

-- Hence its underlying congruence is ≑ the total congruence.
relates→∇ : (d : DecCon 𝟚 0ℓ) → ConRel d 0F 1F → proj₁ d ≑ 𝟙[ 𝟚 ] {0ℓ}
relates→∇ d r = 𝟙-max (proj₁ d) , λ {x} {y} _ → relates→all d r x y

-- If d does not relate 0 and 1, then every d-related pair is ≡-equal.
¬relates→≡ : (d : DecCon 𝟚 0ℓ) → ¬ ConRel d 0F 1F → ∀ x y → ConRel d x y → x ≡ y
¬relates→≡ d ¬r 0F 0F _   = refl
¬relates→≡ d ¬r 0F 1F dxy = ⊥-elim (¬r dxy)
¬relates→≡ d ¬r 1F 0F dxy = ⊥-elim (¬r (decSym d dxy))
¬relates→≡ d ¬r 1F 1F _   = refl

-- Hence its underlying congruence is ≑ the diagonal congruence.
¬relates→Δ : (d : DecCon 𝟚 0ℓ) → ¬ ConRel d 0F 1F → proj₁ d ≑ 𝟘[ 𝟚 ] {0ℓ}
¬relates→Δ d ¬r = (λ {x} {y} dxy → lift (¬relates→≡ d ¬r x y dxy)) , 𝟘-min (proj₁ d)
```

#### The order isomorphism `DecCon 𝟚 ≅ chain₂`

**The maps**.

+  `to`{.AgdaFunction} sends a decidable congruence to its verdict at
   `(0 , 1)`: `1` (the top) if it merges the two points, `0` (the bottom) otherwise —
   computed by running `d`'s own decision procedure.
+  `from`{.AgdaFunction} sends the top to the total congruence and the bottom to the
   diagonal.

`to`{.AgdaFunction} is a single-clause definition through `decToFin`{.AgdaFunction}
so that its decision-scrutinee stays visible for the `with`-based proofs below.

```agda
private
  decToFin : {p : Level} {P : Type p} → Dec P → Fin 2
  decToFin (yes _)  = 1F
  decToFin (no _)   = 0F

  -- A positive verdict lands on 1, a negative one on 0.
  decToFin-yes : {p : Level} {P : Type p} (dp : Dec P) → P → decToFin dp ≡ 1F
  decToFin-yes (yes _)   _  = refl
  decToFin-yes (no ¬p)   p  = ⊥-elim (¬p p)

  decToFin-no : {p : Level} {P : Type p} (dp : Dec P) → ¬ P → decToFin dp ≡ 0F
  decToFin-no (yes p)    ¬p = ⊥-elim (¬p p)
  decToFin-no (no _)     _  = refl

to : DecCon 𝟚 0ℓ → Fin 2
to d = decToFin (proj₂ d 0F 1F)

from : Fin 2 → DecCon 𝟚 0ℓ
from 0F = Δᵈ
from 1F = ∇ᵈ
```

Characterizing `to`{.AgdaFunction}: it lands on `1` exactly when the congruence is
known to merge `0` and `1`, on `0` when it is known not to — obtained by feeding the
verdict to the two `decToFin`{.AgdaFunction} lemmas above.  (These re-expose the
decision procedure `proj₂ d 0F 1F`{.AgdaFunction} as an *explicit* argument, which is
what lets the case analysis proceed without abstracting a projection of the congruence
variable.)

```agda
to≡1 : (d : DecCon 𝟚 0ℓ) → ConRel d 0F 1F → to d ≡ 1F
to≡1 d r = decToFin-yes (proj₂ d 0F 1F) r

to≡0 : (d : DecCon 𝟚 0ℓ) → ¬ ConRel d 0F 1F → to d ≡ 0F
to≡0 d ¬r = decToFin-no (proj₂ d 0F 1F) ¬r
```

The chain's meet order, and the fact `0 ≢ 1`, discharge the four order-isomorphism
obligations.  `_≤_`{.AgdaFunction} below is the meet order of
`chain₂-lattice`{.AgdaFunction}, i.e. `x ≤ y := x ∧ y ≡ x`, which on the two-element
chain is decided by table lookup.

```agda
open Lattice-Order chain₂-lattice using ( _≤_ )
```

Monotonicity of `to`{.AgdaFunction}: containment can only send `0` up.  The only
non-trivial case is where `d` merges `0,1` but `e` does not — impossible, since
`d ⊆ e` propagates the merge from `d` to `e`.

```agda
private
  to-mono-aux : (d e : DecCon 𝟚 0ℓ) → d ⊆ᵈ e
    → (dd : Dec (ConRel d 0F 1F)) (de : Dec (ConRel e 0F 1F))
    → decToFin dd ≤ decToFin de
  to-mono-aux d e d⊆e (yes _)  (yes _)  = refl
  to-mono-aux d e d⊆e (yes rd) (no ¬re) = ⊥-elim (¬re (d⊆e rd))
  to-mono-aux d e d⊆e (no _)   (yes _)  = refl
  to-mono-aux d e d⊆e (no _)   (no _)   = refl

to-mono : {d e : DecCon 𝟚 0ℓ} → d ⊆ᵈ e → to d ≤ to e
to-mono {d} {e} d⊆e = to-mono-aux d e d⊆e (proj₂ d 0F 1F) (proj₂ e 0F 1F)
```

Monotonicity of `from`{.AgdaFunction}: the diagonal is below the total congruence, and
`1 ≤ 0` is impossible in the chain.

```agda
from-mono : {u v : Fin 2} → u ≤ v → from u ⊆ᵈ from v
from-mono {0F} {0F} _  = λ p → p
from-mono {0F} {1F} _  = λ _ → lift tt
from-mono {1F} {0F} ()
from-mono {1F} {1F} _  = λ p → p
```

The round trips.  Starting from a chain element: the diagonal does not merge `0,1`, so
`to`{.AgdaFunction} sends it back to `0`; the total congruence does, so it goes back
to `1`.

```agda
to∘from : (u : Fin 2) → to (from u) ≡ u
to∘from 0F = to≡0 Δᵈ λ { (lift ()) }
to∘from 1F = to≡1 ∇ᵈ (lift tt)
```

Starting from a decidable congruence: the classification lemmas say `from (to d)` is
`≑`{.AgdaFunction} to `d` — the total congruence when `d` merges `0,1`, the diagonal
otherwise.

```agda
from∘to : (d : DecCon 𝟚 0ℓ) → from (to d) ≑ᵈ d
from∘to d = from∘to-aux (proj₂ d 0F 1F)
  where
  -- The motive rewrites `to d` to the literal chain element the case fixes, so
  -- that `from` reduces on a constructor rather than on a stuck decision.
  from∘to-aux : (dd : Dec (ConRel d 0F 1F)) → from (to d) ≑ᵈ d
  from∘to-aux (yes r) =
    subst (λ z → proj₁ (from z) ≑ proj₁ d) (sym (to≡1 d r))
          (proj₂ (relates→∇ d r) , proj₁ (relates→∇ d r))
  from∘to-aux (no ¬r) =
    subst (λ z → proj₁ (from z) ≑ proj₁ d) (sym (to≡0 d ¬r))
          (proj₂ (¬relates→Δ d ¬r) , proj₁ (¬relates→Δ d ¬r))
```

Assembling the four obligations gives the order isomorphism from the `DecCon 𝟚`
poset to the meet order of `chain₂-lattice`{.AgdaFunction}.

```agda
𝟚-ConIsoᵈ : ConIsoᵈ 𝟚 chain₂-lattice
𝟚-ConIsoᵈ = record
  { to         = to
  ; from       = from
  ; to-mono    = λ {d} {e} → to-mono {d} {e}
  ; from-mono  = from-mono
  ; to∘from    = to∘from
  ; from∘to    = from∘to
  }
```

#### The two-element chain is decidably and constructively representable

Packaging the finite finitary witnesses of `𝟚`{.AgdaFunction} with the order
isomorphism gives the headline result: the two-element chain is decidably
representable, with **no postulate**.  The object the WP-1 no-go theorem showed
unattainable at Layer S is thus attained, constructively, at Layer D.

```agda
chain₂-Representableᵈ : Representableᵈ chain₂-lattice
chain₂-Representableᵈ = record
  { sigᵈ       = 𝑆∅
  ; algᵈ       = 𝟚
  ; finiteᵈ    = 𝟚-FiniteAlgebra
  ; finsigᵈ    = 𝑆∅-FiniteSignature
  ; con-isoᵈ  = 𝟚-ConIsoᵈ
  }
```

#### The extreme decidable congruences

Every algebra has a least and a greatest decidable congruence.  The total
congruence `𝟙[ 𝑨 ]`{.AgdaFunction} is decidable outright; the diagonal
`𝟘[ 𝑨 ]`{.AgdaFunction} upgrades to a `DecCon`{.AgdaFunction} exactly when the
setoid equality is decidable — the datum the `_≟_`{.AgdaField} field of
`FiniteAlgebra`{.AgdaRecord} supplies.  (These generalize the two-element-specific
`Δᵈ`{.AgdaFunction} and `∇ᵈ`{.AgdaFunction} above; the closure constructions of
[FLRP.Closure][] use them at their composite witness algebras.)

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

  -- The diagonal congruence, as a DecCon, given a decision procedure for ≈.
  𝟘ᵈ : (∀ x y → Dec (x ≈ y)) → DecCon 𝑨 (ρ ⊔ ℓ)
  𝟘ᵈ {ℓ} _≟_ = 𝟘[ 𝑨 ] {ℓ} , dec
    where
    dec : ∀ x y → Dec (Lift ℓ (x ≈ y))
    dec x y with x ≟ y
    ... | yes p  = yes (lift p)
    ... | no ¬p  = no λ q → ¬p (lower q)

  -- The total congruence, as a DecCon.
  𝟙ᵈ : DecCon 𝑨 ℓ
  𝟙ᵈ {ℓ} = 𝟙[ 𝑨 ] {ℓ} , λ _ _ → yes (lift tt)

  -- A congruence's relation respects the setoid equality on both sides
  -- (reflexivity feeds ≈ into the relation, equivalence moves it around).
  ConRel-resp : (d : DecCon 𝑨 ℓ) {x x' y y' : 𝕌[ 𝑨 ]}
    → x ≈ x' → y ≈ y' → ConRel d x y → ConRel d x' y'
  ConRel-resp d x≈x' y≈y' p = θtrans (θsym (θrefl x≈x')) (θtrans p (θrefl y≈y'))
    where
    θcon    = proj₂ (proj₁ d)
    θrefl   = reflexive θcon
    θsym    = IsEquivalence.sym (is-equivalence θcon)
    θtrans  = IsEquivalence.trans (is-equivalence θcon)
```

#### Congruence-trivial algebras

`ConTrivialᵈ`{.AgdaFunction} says the decidable-congruence poset of
`𝑨`{.AgdaBound} is trivial: any two decidable congruences are mutually contained.
Two sources matter downstream: an algebra with *empty* carrier (there are no pairs
to relate) and the one-element algebra `𝟏`{.AgdaFunction} (every pair is related
by reflexivity, since the setoid equality of `𝟏`{.AgdaFunction} is total).  A
decidable-layer isomorphism transports across congruence-trivial algebras
(`trivial-ConIsoᵈ-transport`{.AgdaFunction} below), which is how the closure
constructions replace a possibly-empty witness algebra by `𝟏`{.AgdaFunction}.

```agda
  -- All decidable congruences of 𝑨 are ≑ᵈ-equal.
  ConTrivialᵈ : (ℓ : Level) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ lsuc ℓ)
  ConTrivialᵈ ℓ = (d e : DecCon 𝑨 ℓ) → d ≑ᵈ e

  -- An algebra with empty carrier is congruence-trivial: no pairs exist to relate.
  empty→ConTrivialᵈ : ¬ 𝕌[ 𝑨 ] → ConTrivialᵈ ℓ
  empty→ConTrivialᵈ ¬x d e = (λ {x} _ → ⊥-elim (¬x x)) , (λ {x} _ → ⊥-elim (¬x x))

-- The one-element algebra is congruence-trivial: its setoid equality is total,
-- so reflexivity of any congruence relates every pair.
𝟏-ConTrivialᵈ : {𝑆 : Signature 𝓞 𝓥} → ConTrivialᵈ {𝑨 = 𝟏 {𝑆 = 𝑆}} ℓ
𝟏-ConTrivialᵈ d e =
  (λ _ → reflexive (proj₂ (proj₁ e)) tt) , (λ _ → reflexive (proj₂ (proj₁ d)) tt)
```

#### Containment of decidable congruences is decidable

On a finite algebra, `d ⊆ᵈ e` reduces to finitely many decidable implications:
check the enumerated pairs and lift the verdict through surjectivity via
`ConRel-resp`{.AgdaFunction}.  Consequently a *failed* containment yields a
concrete violating pair (of enumerated elements) — the constructive
witness-extraction step the ordinal-sum closure's comparability argument runs
on.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑭 : FiniteAlgebra 𝑨) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym )

  private
    -- The enumerated-pairs table of a containment.
    Table : DecCon 𝑨 ℓ → DecCon 𝑨 ℓ → Type ℓ
    Table d e = ∀ i j → ConRel d (𝑭 .enum i) (𝑭 .enum j) → ConRel e (𝑭 .enum i) (𝑭 .enum j)

    table? : (d e : DecCon 𝑨 ℓ) → Dec (Table d e)
    table? d e = all? (λ i → all? (λ j →
      proj₂ d (𝑭 .enum i) (𝑭 .enum j) →-dec proj₂ e (𝑭 .enum i) (𝑭 .enum j)))

    -- Lift a full table to the containment, through surjectivity.
    table→⊆ : (d e : DecCon 𝑨 ℓ) → Table d e → d ⊆ᵈ e
    table→⊆ d e tbl {x} {y} dxy with 𝑭 .enum-sur x | 𝑭 .enum-sur y
    ... | i , pi | j , pj =
      ConRel-resp e pi pj (tbl i j (ConRel-resp d (≈sym pi) (≈sym pj) dxy))

  -- Containment of decidable congruences is decidable.
  ⊆ᵈ-dec : (d e : DecCon 𝑨 ℓ) → Dec (d ⊆ᵈ e)
  ⊆ᵈ-dec d e with table? d e
  ... | yes tbl  = yes (table→⊆ d e tbl)
  ... | no ¬tbl  = no (λ sub → ¬tbl (λ i j dij → sub dij))

  -- A failed containment yields a concrete violating pair.
  ⊈ᵈ-witness : (d e : DecCon 𝑨 ℓ) → ¬ (d ⊆ᵈ e)
    → Σ[ x ∈ 𝕌[ 𝑨 ] ] Σ[ y ∈ 𝕌[ 𝑨 ] ] (ConRel d x y × ¬ ConRel e x y)
  ⊈ᵈ-witness d e ¬sub with table? d e
  ... | yes tbl  = ⊥-elim (¬sub (table→⊆ d e tbl))
  ... | no ¬tbl  = unpack
    where
    -- Peel the two Fin quantifiers off the refuted table, then split the
    -- refuted (decidable) implication into premise and refuted conclusion.
    ¬→-split : {P Q : Type ℓ} → Dec P → ¬ (P → Q) → P × ¬ Q
    ¬→-split (yes p) ¬imp  = p , λ q → ¬imp (λ _ → q)
    ¬→-split (no ¬p) ¬imp  = ⊥-elim (¬imp (λ p → ⊥-elim (¬p p)))

    unpack : Σ[ x ∈ 𝕌[ 𝑨 ] ] Σ[ y ∈ 𝕌[ 𝑨 ] ] (ConRel d x y × ¬ ConRel e x y)
    unpack with ¬∀⟶∃¬ _ _ (λ i → all? (λ j →
                   proj₂ d (𝑭 .enum i) (𝑭 .enum j) →-dec proj₂ e (𝑭 .enum i) (𝑭 .enum j))) ¬tbl
    ... | i , ¬rowᵢ with ¬∀⟶∃¬ _ _ (λ j →
                   proj₂ d (𝑭 .enum i) (𝑭 .enum j) →-dec proj₂ e (𝑭 .enum i) (𝑭 .enum j)) ¬rowᵢ
    ...   | j , ¬impᵢⱼ =
      𝑭 .enum i , 𝑭 .enum j , ¬→-split (proj₂ d (𝑭 .enum i) (𝑭 .enum j)) ¬impᵢⱼ
```

#### Consequences of a decidable-layer isomorphism

An order isomorphism transports more than the order: it respects
`≑ᵈ`{.AgdaFunction} (monotonicity in both directions plus antisymmetry of the
lattice's meet order), it respects `≈`{.AgdaFunction} in the reverse direction
(via `≤-reflexive`{.AgdaFunction}), and it sends the extreme congruences to
extrema of the target lattice.  The last point equips every decidably
representable lattice with *chosen* extrema — the `TopOf`{.AgdaFunction} /
`BottomOf`{.AgdaFunction} data of [Classical.Properties.Lattice][] that the
ordinal-sum construction consumes.

```agda
module ConIsoᵈ-Consequences {𝑆 : Signature 0ℓ 0ℓ} {𝑨 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ}
                            {𝑳 : Lattice} (iso : ConIsoᵈ 𝑨 𝑳) where
  -- The isomorphism's own maps are renamed ᴸ-side to keep them distinct from the
  -- 𝟚-specific `to`/`from` defined above.
  open OrderIso iso
    renaming ( to to toᴸ ; from to fromᴸ ; to-mono to to-monoᴸ ; from-mono to from-monoᴸ
             ; to∘from to to∘fromᴸ ; from∘to to from∘toᴸ )
  open Setoid 𝔻[ proj₁ 𝑳 ] using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans )
  open Lattice-Order 𝑳 using ( _≤_ ; ≤-antisym ; ≤-reflexive ; ≤-respˡ-≈ ; ≤-respʳ-≈
                             ; IsTop ; IsBottom )

  -- ≑ᵈ-equal congruences have ≈-equal images.
  to-cong≑ : {d e : DecCon 𝑨 0ℓ} → d ≑ᵈ e → toᴸ d ≈ toᴸ e
  to-cong≑ (d⊆e , e⊆d) = ≤-antisym (to-monoᴸ d⊆e) (to-monoᴸ e⊆d)

  -- ≈-equal lattice elements have ≑ᵈ-equal preimages.
  from-cong≈ : {u v : 𝕌[ proj₁ 𝑳 ]} → u ≈ v → fromᴸ u ≑ᵈ fromᴸ v
  from-cong≈ e = from-monoᴸ (≤-reflexive e) , from-monoᴸ (≤-reflexive (≈sym e))

  -- The image of the total congruence is a top of the target lattice ...
  to-𝟙-top : IsTop (toᴸ (𝟙ᵈ {ℓ = 0ℓ}))
  to-𝟙-top u = ≤-respˡ-≈ (to∘fromᴸ u) (to-monoᴸ λ _ → lift tt)

  -- ... and the image of the diagonal is a bottom.
  to-𝟘-bot : (≈dec : ∀ x y → Dec (Setoid._≈_ 𝔻[ 𝑨 ] x y)) → IsBottom (toᴸ (𝟘ᵈ ≈dec))
  to-𝟘-bot ≈dec u = ≤-respʳ-≈ (to∘fromᴸ u) (to-monoᴸ (𝟘-min (proj₁ (fromᴸ u))))

-- Chosen extrema for any decidably representable lattice.
module _ {𝑳 : Lattice} (r : Representableᵈ 𝑳) where
  open Representableᵈ r
  open OrderIso con-isoᵈ using () renaming ( to to toᴸ )
  -- ConIsoᵈ is not injective in its lattice argument, so the module's implicit
  -- parameters are supplied explicitly.
  open ConIsoᵈ-Consequences {𝑆 = sigᵈ} {𝑨 = algᵈ} {𝑳 = 𝑳} con-isoᵈ

  Representableᵈ-TopOf : TopOf 𝑳
  Representableᵈ-TopOf = toᴸ (𝟙ᵈ {ℓ = 0ℓ}) , to-𝟙-top

  Representableᵈ-BottomOf : BottomOf 𝑳
  Representableᵈ-BottomOf = toᴸ (𝟘ᵈ (finiteᵈ ._≟_)) , to-𝟘-bot (finiteᵈ ._≟_)
```

#### Inhabited witnesses

A decidable-layer isomorphism transports across congruence-trivial algebras: both
sides have exactly one congruence up to `≑ᵈ`{.AgdaFunction}, so constant maps do
the job, with the round trips supplied by triviality and the original round trip.

```agda
module _ {𝑆₁ 𝑆₂ : Signature 0ℓ 0ℓ} {𝑨 : Algebra {𝑆 = 𝑆₁} 0ℓ 0ℓ}
         {𝑩 : Algebra {𝑆 = 𝑆₂} 0ℓ 0ℓ} {𝑳 : Lattice} where

  trivial-ConIsoᵈ-transport : ConTrivialᵈ {𝑨 = 𝑨} 0ℓ → ConTrivialᵈ {𝑨 = 𝑩} 0ℓ
    → ConIsoᵈ 𝑨 𝑳 → ConIsoᵈ 𝑩 𝑳
  trivial-ConIsoᵈ-transport trivA trivB iso = record
    { to         = λ _ → toᴸ (𝟙ᵈ {ℓ = 0ℓ})
    ; from       = λ _ → 𝟙ᵈ {ℓ = 0ℓ}
    ; to-mono    = λ _ → ≤-refl
    ; from-mono  = λ _ p → p
    ; to∘from    = λ u → ≈trans (to-cong≑ (trivA (𝟙ᵈ {ℓ = 0ℓ}) (fromᴸ u))) (to∘fromᴸ u)
    ; from∘to    = λ d → trivB (𝟙ᵈ {ℓ = 0ℓ}) d
    }
    where
    open OrderIso iso
      renaming ( to to toᴸ ; from to fromᴸ ; to-mono to to-monoᴸ ; from-mono to from-monoᴸ
               ; to∘from to to∘fromᴸ ; from∘to to from∘toᴸ )
    open ConIsoᵈ-Consequences {𝑆 = 𝑆₁} {𝑨 = 𝑨} {𝑳 = 𝑳} iso using ( to-cong≑ )
    open Setoid 𝔻[ proj₁ 𝑳 ] using () renaming ( trans to ≈trans )
    open Lattice-Order 𝑳 using ( ≤-refl )
```

The carrier of a finite algebra is inhabited or provably empty — run the
enumeration.  Hence every decidably representable lattice has a witness with
*inhabited* carrier: either the given one, or — when its carrier is empty, which
forces the decidable-congruence poset trivial — the one-element algebra
`𝟏`{.AgdaFunction} over the empty signature, with the isomorphism transported
across the two trivial posets.  The closure constructions of [FLRP.Closure][]
normalize their inputs through this lemma, so their basepoint-hungry composite
algebras never meet an empty summand.

```agda
-- Decide inhabitation of a finite algebra's carrier from its enumeration.
carrier-inhabited? : {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ}
  → FiniteAlgebra 𝑨 → 𝕌[ 𝑨 ] ⊎ ¬ 𝕌[ 𝑨 ]
carrier-inhabited? 𝑭 with 𝑭 .card | 𝑭 .enum | 𝑭 .enum-sur
... | zero   | e | sur = inj₂ (λ x → ¬Fin0 (proj₁ (sur x)))
... | suc k  | e | sur = inj₁ (e 0F)

-- Every decidably representable lattice has a witness with inhabited carrier.
inhabited-witness : {𝑳 : Lattice} (r : Representableᵈ 𝑳)
  → Σ[ r' ∈ Representableᵈ 𝑳 ] 𝕌[ Representableᵈ.algᵈ r' ]
inhabited-witness {𝑳} r with carrier-inhabited? (Representableᵈ.finiteᵈ r)
... | inj₁ x   = r , x
... | inj₂ ¬x  = record
    { sigᵈ      = 𝑆∅
    ; algᵈ      = 𝟏
    ; finiteᵈ   = 𝟏-FiniteAlgebra
    ; finsigᵈ   = 𝑆∅-FiniteSignature
    ; con-isoᵈ  = trivial-ConIsoᵈ-transport
                    {𝑆₁ = Representableᵈ.sigᵈ r} {𝑆₂ = 𝑆∅}
                    {𝑨 = Representableᵈ.algᵈ r} {𝑩 = 𝟏} {𝑳 = 𝑳}
                    (empty→ConTrivialᵈ {𝑨 = Representableᵈ.algᵈ r} ¬x)
                    (𝟏-ConTrivialᵈ {𝑆 = 𝑆∅})
                    (Representableᵈ.con-isoᵈ r)
    } , tt
```

--------------------------------------
