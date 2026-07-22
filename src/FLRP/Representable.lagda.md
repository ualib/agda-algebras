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

The standing FLRP research-track separation warning of [FLRP.Problem][] applies here
too: this is problem-specific formal content, not to be conflated with the
algebraic-complexity / finite-CSP work elsewhere in the library.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Representable where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive       using () renaming ( Set to Type )
open import Data.Empty           using ( ⊥-elim )
open import Data.Fin.Base        using ( Fin )
open import Data.Fin.Patterns    using ( 0F ; 1F )
open import Data.Fin.Properties  using () renaming ( _≟_ to _≟ᶠ_ )
open import Data.Product         using ( _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Base       using ( tt )
open import Level                using ( Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower )
                                 renaming ( suc to lsuc )
open import Relation.Binary      using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality
                                 using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary     using ( ¬_ ; Dec ; yes ; no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice         using  ( module Lattice-Order )
open import Classical.Small.Structures.Lattice   using  ( Lattice )
open import FLRP.Problem                         using  ( OrderIso ; FiniteLattice
                                                        ; toLattice ; 𝑆∅ ; chain₂-lattice )
open import Overture                             using  ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic                using  ( Algebra ; 𝔻[_] ; mkAlgebraₚ )
open import Setoid.Algebras.Finite               using  ( FiniteAlgebra )
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

--------------------------------------
