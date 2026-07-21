---
layout: default
file: "src/FLRP/Assumptions.lagda.md"
title: "FLRP.Assumptions module (The Agda Universal Algebra Library)"
date: "2026-07-20"
author: "the agda-algebras development team"
---

### The registry of classical assumptions of the FLRP program

This is the [FLRP.Assumptions][] module of the [Agda Universal Algebra Library][].

The [Agda Universal Algebra Library][] is postulate-free, confined to
[*Safe Agda*](https://agda.readthedocs.io/en/v2.8.0-r3/language/safe-agda.html#safe-agda),
and the FLRP tree is no execption.  Where a result genuinely depends on a classical
theorem, that theorem is never introduced as a `postulate`; it is stated as an
*explicit hypothesis* and threaded through the results that consume it.

The present module is the single place these hypotheses are *named, documented, and
given their logical strength*, so that the classical content of the FLRP research
program is auditable at one site rather than smeared across the development.[^1]

**Entry 1**: the congruence-completeness bridge.  This is the *single* classical
assumption of the two-layer discipline: the one place a result may cross from the
semantic congruence layer (Layer S, `Con`{.AgdaFunction}) to the decidable layer
(Layer D, `DecCon`{.AgdaFunction}).  It is registered here as
`CongruenceCompleteness`{.AgdaFunction} `𝑨`.

+  **Meaning**.  Every *semantic* congruence of `𝑨`{.AgdaBound} is `≑`{.AgdaFunction}
   to a *decidable* one.  (`≑`{.AgdaFunction} is mutual containment.)

+  **Source**.  It is exactly the `complete`{.AgdaField} field of
   `FiniteCongruences`{.AgdaRecord} of [Setoid.Congruences.Finite.Basic][], with the
   finite list and its membership proof forgotten (the list side is *constructive* —
   see below), so `fromFiniteCongruences`{.AgdaFunction} extracts it from the canonical
   record.

+  **Strength**.  It sits strictly *between weak excluded middle and excluded middle*
   at the working relation level.  The lower bound is the no-go theorem
   `chain₂-ConIso→WLEM`{.AgdaFunction} / `chain₂-Representable→WLEM`{.AgdaFunction} of
   [FLRP.Problem][]: on a nontrivial algebra the bridge lets an oracle congruence be
   decided, yielding weak excluded middle.  The upper bound is that full excluded
   middle at the working level supplies it.[^2]

The constructive *complement* of this assumption is already discharged with no axiom:
the finite list of decidable congruences and its completeness *for the decidable layer*
is `FiniteCongruencesᵈ`{.AgdaRecord} of [Setoid.Congruences.Finite.Decidable][], built
from carrier- and signature-finiteness alone.  `toFiniteCongruences`{.AgdaFunction}
below makes this precise: adjoining `CongruenceCompleteness`{.AgdaFunction} to that
free constructive data reconstitutes the full semantic
`FiniteCongruences`{.AgdaRecord}, so the assumption is exactly the classical delta
between the two layers, no more, no less.

**Coordination note**.  Work package 5 (WP-5) also plans to register
its Kurzweil–Netter duality in this module.[^3]  The module is structured as
*per-assumption statement definitions* (rather than one monolithic record) precisely
so that a second entry can be appended without disturbing the first: WP-5 should add
its duality as "Entry 2" alongside `CongruenceCompleteness`{.AgdaFunction}, and
downstream results take whichever entry they need as an ordinary argument.[^4]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Assumptions where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Membership.Propositional    using  ( _∈_ )
open import Data.Product                          using  ( _×_ ; _,_ ; Σ-syntax
                                                         ; proj₁ ; proj₂ )
open import Function                              using  (_∘_)
open import Level                                 using  ( Level ; _⊔_ )
                                                  renaming ( suc to lsuc )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture                              using  ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic                 using  ( Algebra )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
open import Setoid.Signatures.Finite              using  ( FiniteSignature )
open import Setoid.Congruences.Basic              using  ( Con )
open import Setoid.Congruences.Lattice            using  ( _≑_ )
open import Setoid.Congruences.Finite.Basic       using  ( DecCon ; FiniteCongruences )
open import Setoid.Congruences.Finite.Decidable   using  ( FiniteCongruencesᵈ
                                                         ; FiniteAlgebra→FiniteCongruencesᵈ )

private variable α ρ : Level
```
-->

#### Entry 1: the congruence-completeness bridge

Throughout we fix an algebra `𝑨`{.AgdaBound} and work at its
**working congruence level** `ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` — the absorbing level at which the
decidable-layer machinery of [Setoid.Congruences.Finite.Basic][] and
[Setoid.Congruences.Finite.Decidable][] lives, and the level at which the `complete`
field of `FiniteCongruences`{.AgdaRecord} quantifies.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra {𝑆 = 𝑆} α ρ) where
  private
    ℓ : Level
    ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ
```

`CongruenceCompleteness`{.AgdaFunction} `𝑨` is the assumption itself; it is a
function that, given *any* semantic congruence `φ`{.AgdaBound}, produces a decidable
congruence `≑`{.AgdaFunction} to it.

This is the `complete`{.AgdaField} field of `FiniteCongruences`{.AgdaRecord} with the
list `cons`{.AgdaField} and the membership proof `d ∈ cons`{.AgdaFunction} dropped;
those record the *finiteness* of the collection of decidable congruences, which is
constructive (`FiniteCongruencesᵈ`{.AgdaRecord}), whereas the classical content is
precisely the existence of a decidable `≑`-representative for a congruence that need
carry no decision procedure of its own.

```agda
  -- For each semantic congruence φ, there exists a decidable congruence d such that φ ≑ d.
  CongruenceCompleteness : Type (lsuc ℓ)
  CongruenceCompleteness = (φ : Con 𝑨 ℓ) → Σ[ (d , _) ∈ DecCon 𝑨 ℓ ] φ ≑ d
```

**The source**.  A `FiniteCongruences`{.AgdaRecord} witness — the canonical form of
the assumption in the library — yields the bridge by forgetting the list and its
membership proof.  This is the direction a consumer already in posession of the full
record would use.

```agda
  fromFiniteCongruences : FiniteCongruences 𝑨 → CongruenceCompleteness
  fromFiniteCongruences 𝑪 φ = witness φ , witness≑ φ
    where open FiniteCongruences 𝑪 using ( witness ; witness≑ )
  -- Recall, `witness φ` is d and `witness≑ φ` is the proof of `φ ≑ proj₁ d`

```

**The classical delta**.  Conversely, adjoining the bridge to the *free constructive*
data of a finite finitary algebra — its carrier finiteness
(`FiniteAlgebra`{.AgdaRecord}) and signature finiteness (`FiniteSignature`{.AgdaRecord}),
from which `FiniteAlgebra→FiniteCongruencesᵈ`{.AgdaFunction} builds a complete list of
*decidable* congruences with no axiom — reconstitutes the full semantic
`FiniteCongruences`{.AgdaRecord}.

So `CongruenceCompleteness`{.AgdaFunction} is neither more nor less than the
classical content of "finite" for congruence-lattice purposes: it is the gap
between Layer D and Layer S, and nothing else.

The list is the constructive `consᵈ`{.AgdaField}; completeness chains the bridge's
`≑`{.AgdaFunction} into the decidable-layer completeness `completeᵈ`{.AgdaField} by
transitivity.

```agda
  toFiniteCongruences : CongruenceCompleteness
    → FiniteAlgebra 𝑨 → FiniteSignature 𝑆 → FiniteCongruences 𝑨
  toFiniteCongruences cc 𝑭 𝑺 = record { cons = consᵈ ; complete = comp }
    where
    open FiniteCongruencesᵈ (FiniteAlgebra→FiniteCongruencesᵈ 𝑭 𝑺)
      using ( consᵈ ; witnessᵈ ; witnessᵈ∈ ; witnessᵈ≑ )

    comp : (φ : Con 𝑨 ℓ) → Σ[ e ∈ DecCon 𝑨 ℓ ] e ∈ consᵈ × φ ≑ proj₁ e
    comp φ = e , witnessᵈ∈ d , φ≑e
      where
      d : DecCon 𝑨 ℓ
      d = cc φ .proj₁

      φ≑d : φ ≑ d .proj₁
      φ≑d = cc φ .proj₂

      e : DecCon 𝑨 ℓ
      e = witnessᵈ d

      d≑e : d .proj₁ ≑ e .proj₁
      d≑e = witnessᵈ≑ d

      φ≑e : φ ≑ e .proj₁
      φ≑e = d≑e .proj₁ ∘ φ≑d .proj₁ , φ≑d .proj₂ ∘ d≑e .proj₂
```

--------------------------------------

[^1]: This is the assumption-registry discipline of [ADR-008][] and the FLRP roadmap.

[^2]: Pinning the exact strength is a side question the program does not need
      (see `docs/notes/flrp-two-layer-congruences.md` § 2.1, L4).

[^3]: **WP-5: closure toolkit** formalizes product and ordinal-sum closure of
      representability (see
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 7
      and GitHub [Issue #456](https://github.com/ualib/agda-algebras/issues/456).

[^4]: The standing FLRP research-track separation warning of [FLRP.Problem][] applies
      here too: this is problem-specific formal content, not to be conflated with the
      algebraic-complexity / finite-CSP work elsewhere in the library.
