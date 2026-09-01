---
layout: default
file: "src/FLRP/KurzweilNetter/Duality.lagda.md"
title: "FLRP.KurzweilNetter.Duality module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### The Kurzweil–Netter duality theorem

This is the [FLRP.KurzweilNetter.Duality][] module of the [Agda Universal Algebra Library][].

**Theorem (Kurzweil 1985, Netter 1986)**.
If a finite lattice is decidably representable, then so is its dual.

This module assembles the formal proof from its three prepared stages,
following the argument of `docs/papers/fin-lat-rep/SmallLatticeReps.tex`
§ "Lattice duals: the theorem of Kurzweil and Netter" (after Pálfy's 2009
lectures).  Given a representation `𝑳 ≅ DecCon 𝑨`, proceed as follows:

1. present the carrier of `𝑨`{.AgdaBound} by an irredundant enumeration `Fin m`
   ([Setoid.Algebras.Finite.Irredundant][]), and its congruences as the partitions
   of `Fin m`{.AgdaDatatype} invariant under the basic translations
   ([FLRP.KurzweilNetter.Blocks][], [FLRP.KurzweilNetter.Translations][], the
   translation criterion);

2. expand the coset algebra of the diagonal `D ≤ Sᵐ` by the lifted translations;
   its decidable congruence poset is the *reversed* poset of invariant partitions
   ([FLRP.KurzweilNetter.Expansion][], composing the WP-3 bridge
   `DecCon (Sᵐ ↷ Sᵐ/D) ≅ [D , Sᵐ]` of [FLRP.Bridge][] with the
   decidable-instance passage of Kurzweil's interval isomorphism
   `[D , Sᵐ] ≅ Eq(m)′` of [FLRP.KurzweilInterval][]);

3. compose the two, and the original representation, into
   `DecCon 𝑬 ≅ dualLattice 𝑳`, the record `dual-representation`{.AgdaFunction} below.

#### What the proof assumes of the simple group

For now, we parameterize by the group `S` rather than instantiated at a concrete
simple group, and the module parameters are the deliverable list of properties the
argument actually uses:

+  **a finite carrier with decidable equality**
   (`𝑭ₛ`{.AgdaBound}` : ``FiniteAlgebra`{.AgdaRecord}),
   for finiteness of the power `Sᵐ`, decidable coset equality, and the membership
   deciders of the partition subgroups;

+  **a nontriviality witness** `s₀`{.AgdaBound} with `¬ (s₀ ≈ ε)`, for the
   order reflection and injectivity of `π ↦ K_π`, and for extracting
   invariance from closure in the expansion step (the indicator tuples);

+  **Kurzweil surjectivity at every exponent, in the decidable form**
   (`KurzweilSurjectivityᵈAt`{.AgdaFunction}` 𝒮 n`, the working form of
   Entry 4 of [FLRP.Assumptions][]): every *decidable* subgroup in
   `[D , Sⁿ]` is a partition subgroup.  The semantic form is deliberately
   not consumed: it is unprovable outright (the no-go of
   [FLRP.KurzweilInterval][]), while the decidable form is exactly what the
   construction's base-coset classes deliver.

*Nonabelianness and simplicity of `S` enter only through the third item*;
they are what makes Entry 4 true classically.  Thus no simplicity predicate is
needed anywhere in the formal development.  Retiring Entry 4 and instantiating `𝒮`
at a concrete finite nonabelian simple group such as `A₅` are tracked separately
as follow-on work; on either completion this module's statements strengthen with
no change to consumers.

#### What the proof does not assume

The manuscript reduces to unary operations by citing the unary-reduction theorem
`Con 𝑨 = Con ⟨A , Pol₁ 𝑨⟩` (not yet formalized).  The formal proof here does
**not** take that result as a hypothesis: the expansion lifts only the
*basic translations* of `𝑨`{.AgdaBound}, and the translation criterion of
[FLRP.KurzweilNetter.Translations][], a self-contained Mal'cev-style walk, shows
these already determine the congruences.[^1]

#### Size

The construction represents `dualLattice 𝑳` on the coset space `Sᵐ / D` of
`|S|ᵐ⁻¹` elements, which is at least `60ᵐ⁻¹` once `𝒮` is instantiated at `A₅`, so
the census's dual entries become assumption-free in *statement* while remaining
computationally out of reach: no concrete certificate algebra is materialized by
this theorem.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter.Duality where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Nat.Base    using ( ℕ )
open import Data.Product     using ( _,_ ; proj₁ )
open import Level            using ( 0ℓ )
open import Function         using ( id ; _∘_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Nullary using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using  ( module Lattice-Order )
open import Classical.Small.Structures.Lattice  using  ( Lattice )
open import Classical.Structures.Group.Basic    using  ( Group ; module Group-Op )
open import Classical.Structures.Lattice.Dual   using  ( dualLattice
                                                       ; module LatticeDual )
open import FLRP.Assumptions                    using  ( KurzweilNetterDualityAt
                                                       ; KurzweilNetterDuality
                                                       ; KurzweilSurjectivityᵈAt )
open import FLRP.KurzweilNetter.Blocks          using  ( module KNBlocks )
open import FLRP.KurzweilNetter.Expansion       using  ( module KNExpansion )
open import FLRP.KurzweilNetter.Translations    using  ( module KNTranslations )
open import FLRP.Representable                  using  ( Representableᵈ ; ConIsoᵈ
                                                       ; _⊆ᵈ_ ; _≑ᵈ_
                                                       ; module ConIsoᵈ-Consequences )
open import Order.Iso                           using  ( OrderIso ; OrderIso-trans )
open import Overture                            using  ( Signature )
open import Setoid.Algebras.Basic               using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite              using  ( FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant  using  ( IrredundantEnumeration
                                                       ; irredundantEnumeration )
open import Setoid.Congruences.Finite.Basic     using  ( DecCon )
open import Setoid.Signatures.Finite            using  ( FiniteSignature )
```
-->

#### The glue module

`KNGlue`{.AgdaModule} assembles the composite over an abstract irredundant
enumeration and an abstract surjectivity witness at its size, and glues the
stages with the generic composition `OrderIso-trans`{.AgdaFunction} of
[Order.Iso][] rather than by hand.  Both choices are measured type-checking
requirements, not style: with the concrete `irredundantEnumeration`{.AgdaFunction}
value substituted throughout, or with the composite's round trips elaborated
inline, the conversion checker re-normalizes the whole construction at each step
(profiled at over three minutes for this one module) whereas over inert
parameters, with the composition checked once against abstract relations, the same
content checks in seconds.  The instantiation happens once, in
`KurzweilNetterProof`{.AgdaModule} at the bottom.

```agda
module KNGlue
  {𝑆          : Signature 0ℓ 0ℓ}
  {𝑨          : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ}
  (𝑆fin       : FiniteSignature 𝑆)
  (𝑬ᵢ         : IrredundantEnumeration 𝑨)
  (𝒮@(𝑺 , _)  : Group 0ℓ 0ℓ)  (open Setoid 𝔻[ 𝑺 ] using (_≈_))
                              (open Group-Op 𝒮 using (ε))
  (𝑭ₛ         : FiniteAlgebra 𝑺)
  (s₀         : 𝕌[ 𝑺 ])
  (s₀≉ε       : ¬ s₀ ≈ ε)
  (surjm      : KurzweilSurjectivityᵈAt 𝒮 (IrredundantEnumeration.icard 𝑬ᵢ))
  (𝓛@(𝑳 , _)  : Lattice)
  (iso        : ConIsoᵈ 𝑨 𝓛)
  where
```

**The three stages are instantiated**.  The irredundant enumeration fixes the
exponent `m`, the translation toolkit supplies the family the expansion lifts, and
the expansion module builds the representing algebra `𝑬` on `Sᵐ/D`.

```agda
  private
    module KB = KNBlocks 𝑨 𝑬ᵢ
    module KT = KNTranslations 𝑨 𝑆fin 𝑬ᵢ
    module KE = KNExpansion 𝒮 𝑭ₛ s₀ s₀≉ε  (IrredundantEnumeration.icard 𝑬ᵢ)
                                          KT.trCount KT.trFamily surjm

    module I₀ = OrderIso iso
    module KEIso = OrderIso KE.expansionIso

    open ConIsoᵈ-Consequences {𝑆 = 𝑆} {𝑨 = 𝑨} {𝑳 = 𝓛} iso using ( to-cong≑ )

    open Setoid 𝔻[ 𝑳 ] using () renaming ( trans to ≈ᴸ-trans )
```

**The middle stage of the composite**.  The family-invariant partitions are the
decidable congruences of `𝑨`{.AgdaBound}, by the translation toolkit — the
congruence of an invariant partition one way, the invariant partition of a
congruence the other.

```agda
    -- an invariant partition presents a congruence of the represented algebra ...
    midTo : KE.InvPart → DecCon 𝑨 0ℓ
    midTo (pv , h) = KT.blockConᶠ pv h

    -- ... and a congruence has an invariant partition.
    midFrom : DecCon 𝑨 0ℓ → KE.InvPart
    midFrom d = KB.pvOf d , KT.pvOf-invariant-family d
```

**The middle stage as an order isomorphism in its own right**.  The round trips
are the two dictionary round trips of [FLRP.KurzweilNetter.Blocks][], with the
relation of `midTo`{.AgdaFunction} definitionally the block relation of the
partition, so both directions of each round trip are the prepared lemmas applied
verbatim.

```agda
    infix 4 _⊇ᵈ_

    -- reversed congruence containment (the middle stages run dually)
    _⊇ᵈ_ : DecCon 𝑨 0ℓ → DecCon 𝑨 0ℓ → Type _
    d ⊇ᵈ e = e ⊆ᵈ d

    midIso : OrderIso KE._≈ᵛ_ KE._≥ᵛ_ (_≑ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ}) _⊇ᵈ_
    midIso = record
      { to         = midTo
      ; from       = midFrom
      ; to-mono    = λ {(P , _)} {(Q , _)} ge → KB.blockRel-mono {pu = Q} {pw = P} ge
      ; from-mono  = λ {d} {e} sup → KB.pvOf-mono e d sup
      ; to∘from    = λ d → KB.blockRel-pvOf-out d , KB.blockRel-pvOf-in d
      ; from∘to    = λ P → KB.pvOf-blockRel (midTo P) (proj₁ P) id id
      }
```

**The lattice stage, dualized**: the maps and round trips of the given
representation, with the monotonicity directions flipped through the two flip
lemmas of [Classical.Structures.Lattice.Dual][].

```agda
    I₀-dual : OrderIso  (_≑ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ}) _⊇ᵈ_
                        (Setoid._≈_ 𝔻[ proj₁ (dualLattice 𝓛) ])
                        (Lattice-Order._≤_ (dualLattice 𝓛))
    I₀-dual = record
      { to = I₀.to
      ; from = I₀.from
      ; to-mono = λ sup → LatticeDual.≤ᵈ-unflip 𝓛 (I₀.to-mono sup)
      ; from-mono = λ le → I₀.from-mono (LatticeDual.≤ᵈ-flip 𝓛 le)
      ; to∘from = I₀.to∘from
      ; from∘to = I₀.from∘to
      }
```

**The junction data for composing the three stages**: transitivity of the mutual
containments, and the congruence of each map with respect to the middle
equivalence it crosses; every one of them is monotonicity applied twice.

```agda
    ≑ᴱ-trans : {a b c : DecCon KE.expandedAlgebra 0ℓ} → a ≑ᵈ b → b ≑ᵈ c → a ≑ᵈ c
    ≑ᴱ-trans (p₁ , p₂) (q₁ , q₂) = q₁ ∘ p₁ , p₂ ∘ q₂

    ≑ᴬ-trans : {a b c : DecCon 𝑨 0ℓ} → a ≑ᵈ b → b ≑ᵈ c → a ≑ᵈ c
    ≑ᴬ-trans (p₁ , p₂) (q₁ , q₂) = q₁ ∘ p₁ , p₂ ∘ q₂

    midTo-cong : {P Q : KE.InvPart} → P KE.≈ᵛ Q → midTo P ≑ᵈ midTo Q
    midTo-cong {(P , _)} {(Q , _)} (uw , wu) =
        KB.blockRel-mono {pu = P} {pw = Q} uw
      , KB.blockRel-mono {pu = Q} {pw = P} wu

    midFrom-cong : {d e : DecCon 𝑨 0ℓ} → d ≑ᵈ e → midFrom d KE.≈ᵛ midFrom e
    midFrom-cong {d} {e} (p , q) = KB.pvOf-mono d e p , KB.pvOf-mono e d q

    KEfrom-cong : {P Q : KE.InvPart} → P KE.≈ᵛ Q → KEIso.from P ≑ᵈ KEIso.from Q
    KEfrom-cong {P} {Q} (uw , wu) =
      KEIso.from-mono {P} {Q} wu , KEIso.from-mono {Q} {P} uw

    stage₁-from-cong : {d e : DecCon 𝑨 0ℓ}
      → d ≑ᵈ e → KEIso.from (midFrom d) ≑ᵈ KEIso.from (midFrom e)
    stage₁-from-cong {d} {e} de =
      KEfrom-cong {midFrom d} {midFrom e} (midFrom-cong {d} {e} de)
```

**The composite isomorphism `DecCon 𝑬 ≅ dualLattice 𝑳`**: by two applications of
`OrderIso-trans`{.AgdaFunction} of [Order.Iso][]; order reversal happens once,
inside the expansion isomorphism; the middle stages run against the reversed
orders, and the boundary lands in the dual lattice's meet order.

```agda
    stage₁ : OrderIso  (_≑ᵈ_ {𝑨 = KE.expandedAlgebra} {ℓ = 0ℓ})
                       (_⊆ᵈ_ {𝑨 = KE.expandedAlgebra} {ℓ = 0ℓ})
                       (_≑ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ}) _⊇ᵈ_
    stage₁ = OrderIso-trans KE.expansionIso midIso
      (λ {P} {Q} → midTo-cong {P} {Q})
      (λ {P} {Q} → KEfrom-cong {P} {Q})
      (λ {a} {b} {c} → ≑ᴱ-trans {a} {b} {c})
      (λ {a} {b} {c} → ≑ᴬ-trans {a} {b} {c})

    dualConIso : ConIsoᵈ {𝑆 = KE.Sig-Exp} KE.expandedAlgebra (dualLattice 𝓛)
    dualConIso = OrderIso-trans stage₁ I₀-dual
      (λ {d} {e} → to-cong≑ {d} {e})
      (λ {d} {e} → stage₁-from-cong {d} {e})
      (λ {a} {b} {c} → ≑ᴱ-trans {a} {b} {c})
      (λ {x} {y} {z} → ≈ᴸ-trans {x} {y} {z})
```

**The representation of the dual**: the expanded coset algebra, its finiteness
and finite signature from the expansion module, and the composite isomorphism.

```agda
  -- The dual of a decidably representable lattice is decidably representable.
  dual-representation : Representableᵈ (dualLattice 𝓛)
  dual-representation = record
    { sigᵈ      = KE.Sig-Exp
    ; algᵈ      = KE.expandedAlgebra
    ; finiteᵈ   = KE.expandedAlgebra-FiniteAlgebra
    ; finsigᵈ   = KE.Sig-Exp-FiniteSignature
    ; con-isoᵈ  = dualConIso
    }
```

#### The theorem

`KurzweilNetterProof`{.AgdaModule} fixes the base group with exactly the three
property witnesses of the deliverable list, and instantiates the glue at the
canonical irredundant enumeration of each representation.

One reading note, so the module cannot overstate itself: the definitions below
inhabit `KurzweilNetterDuality`{.AgdaFunction} *inside* this parameterized
module; the library holds no closed inhabitant of the statement, and Entry 4's
decidable family is a genuine hypothesis of the result.  Entry 2 of [FLRP.Assumptions][] is
thereby *reduced to Entry 4*, not discharged; the registry entry records the same
reading.

```agda
module KurzweilNetterProof
  (𝒮@(𝑺 , _)  : Group 0ℓ 0ℓ)
  (𝑭ₛ         : FiniteAlgebra 𝑺)
  (s₀         : 𝕌[ 𝑺 ])
  (s₀≉ε       : ¬ (Setoid._≈_ 𝔻[ 𝑺 ] s₀ (Group-Op.ε 𝒮)))
  (surj       : (n : ℕ) → KurzweilSurjectivityᵈAt 𝒮 n)
  where

  -- Kurzweil–Netter duality at a lattice.
  kurzweilNetterDualityAt : (𝑳 : Lattice) → KurzweilNetterDualityAt 𝑳
  kurzweilNetterDualityAt 𝑳 r =
    KNGlue.dual-representation {𝑆 = sigᵈ} {𝑨 = algᵈ} finsigᵈ 𝑬ᵢ
      𝒮 𝑭ₛ s₀ s₀≉ε (surj (IrredundantEnumeration.icard 𝑬ᵢ)) 𝑳 con-isoᵈ
    where
    open Representableᵈ r  -- sigᵈ, algᵈ, finiteᵈ, finsigᵈ, con-isoᵈ

    𝑬ᵢ : IrredundantEnumeration algᵈ
    𝑬ᵢ = irredundantEnumeration finiteᵈ

  -- The Kurzweil–Netter duality theorem, conditional on the module's package.
  kurzweilNetterDuality : KurzweilNetterDuality
  kurzweilNetterDuality 𝑳 = kurzweilNetterDualityAt 𝑳
```

--------------------------------------

[^1]: Issue #501 remains open as the full polynomial-clone statement; nothing here
      waits on it.
