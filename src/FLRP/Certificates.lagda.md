---
layout: default
file: "src/FLRP/Certificates.lagda.md"
title: "FLRP.Certificates module (The Agda Universal Algebra Library)"
date: "2026-07-22"
author: "the agda-algebras development team"
---

### Machine-checked representation certificates

This is the [FLRP.Certificates][] module of the [Agda Universal Algebra Library][].

The FLRP program's computational campaigns[^1] produce claims of the form "`Con 𝑨 ≅
𝑳` for this finite algebra `𝑨` and this finite lattice `𝑳`" from external engines —
GAP, UACalc, SAT and model finders.

Per the certificate discipline of [the roadmap](docs/notes/flrp-research-roadmap.md)
§ 6 and [the WP-6 design note](docs/notes/flrp-wp6-freese-certificates.md), nothing
enters the corpus on the authority of an external tool: the engine emits a
whole-lattice certificate (normal-form parent vectors, Freese traces, and pointer
tables — [Setoid.Congruences.Certificates.Schema][]), the generic checkers verify it
with no search and no `Cg-dec`{.AgdaFunction}
([Setoid.Congruences.Certificates.Congruence][],
[Setoid.Congruences.Certificates.Lattice][]), and *this* module turns the
checked certificate into the FLRP-facing theorem: a
`Representableᵈ`{.AgdaRecord} witness ([FLRP.Representable][]) for the target
lattice.

Concretely, we are given

+  a finite finitary algebra (`𝑭`, `𝑺`, everything at level `0ℓ`, as
   `ConIsoᵈ`{.AgdaFunction} demands),
+  a target `FiniteLattice`{.AgdaRecord} `𝑳` ([FLRP.Problem][]), and
+  a whole-lattice certificate `lc` whose entry list is indexed by `𝑳`'s carrier.

Then two checked hypotheses produce the order isomorphism; the hypotheses are
as follows:

+  `LatticeCertOK lc`{.AgdaRecord} — the whole-lattice checker's bundle
   (decided by one `latticeCertOK?`{.AgdaFunction});
+  `MeetMatches lc`{.AgdaFunction} — the certificate's meet table is
   *syntactically* the target lattice's `∧`{.AgdaFunction} table (decided by
   `meetMatches?`{.AgdaFunction}).

The isomorphism's two maps are the whole-lattice checker's completeness fold
`indexOf`{.AgdaFunction} (which executes only the given congruence's own decision
procedure and table lookups) and the certificate's entry decoder
`entryDec`{.AgdaFunction}; the four order-isomorphism laws are exactly the exported
fold lemmas, with the meet-table match translating containment of entries into the
lattice's meet order `x ≤ y := x ∧ y ≈ x` ([Classical.Properties.Lattice][]).

Since `toLattice`{.AgdaFunction} builds its carrier setoid on propositional equality,
the translation is definitional.

The standing FLRP research-track separation warning applies: this is problem-specific
wiring; all reusable mathematics lives under the `Setoid` tree; in this case, under
`Setoid.Congruences.Certificates`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Certificates where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Properties                    using  ( all? )
                                                   renaming ( _≟_ to _≟ᶠ_ )
open import Data.Nat.Base                          using  ( suc )
open import Data.Product                           using  ( proj₁ )
open import Level                                  using  ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; sym ; trans )
open import Relation.Nullary.Decidable             using  ( Dec )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import FLRP.Problem                                using  ( FiniteLattice
                                                               ; toLattice ; OrderIso )
open import FLRP.Representable                          using  ( Representableᵈ ; _⊆ᵈ_
                                                               ; ConIsoᵈ ; _≑ᵈ_ )
open import Overture                                    using  ( Signature )
open import Setoid.Algebras.Basic                       using  ( Algebra )
open import Setoid.Algebras.Finite                      using  ( FiniteAlgebra )
open import Setoid.Congruences.Finite.Basic             using  ( DecCon )
open import Setoid.Congruences.Lattice                  using  ( ≑-sym )
open import Setoid.Congruences.Certificates.Schema      using  ( LatticeCert )
open import Setoid.Congruences.Certificates.Congruence  using  ( module CertCheck )
open import Setoid.Congruences.Certificates.Lattice     using  ( module LatticeCheck )
open import Setoid.Signatures.Finite                    using  ( FiniteSignature )
```
-->

#### The certified order isomorphism

Fix the finite finitary algebra, the target finite lattice, and a certificate
whose entry list is indexed by the lattice's carrier `Fin (suc size)`.

```agda
module _ {𝑆 : Signature 0ℓ 0ℓ} {𝑨 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ}
         (𝑭 : FiniteAlgebra 𝑨) (𝑺 : FiniteSignature 𝑆) (𝑳 : FiniteLattice)
  where

  open FiniteAlgebra 𝑭 using ( card )
  open FiniteSignature 𝑺 using ( opCard )
  open CertCheck 𝑭 𝑺 using ( arOf )
  open LatticeCheck 𝑭 𝑺
  open FiniteLattice 𝑳 using ( size ; _∧_ )

  module _ (lc : LatticeCert card opCard arOf (suc size)) where
    open LatticeCert lc using ( meet )
```

The meet-table match: the certificate's meet table *is* the target lattice's
`∧`{.AgdaFunction} table.  This is what pins the certificate's entry indexing
to the intended lattice, and it is decided by an `m ²` sweep of
`Fin`{.AgdaDatatype} comparisons.

```agda
    -- The certificate's meet table is the target lattice's ∧ table.
    MeetMatches : Type
    MeetMatches = ∀ k l → meet k l ≡ k ∧ l

    meetMatches? : Dec MeetMatches
    meetMatches? = all? (λ k → all? (λ l → meet k l ≟ᶠ k ∧ l))
```

Given the two checked hypotheses, the order isomorphism between the decidable
congruences of `𝑨` and the meet order of the target lattice.  The maps and all
four laws are the whole-lattice checker's exports; only the two monotonicity
clauses do any translation, moving between containment of entries and
meet-table idempotence through `MeetMatches`{.AgdaFunction} — definitionally,
because the classical lattice's carrier equality is propositional.

```agda
    module _ (OK : LatticeCertOK lc) (mm : MeetMatches) where

      private
        -- the two maps of the isomorphism
        toIdx : DecCon 𝑨 0ℓ → Fin (suc size)
        toIdx = indexOf lc OK

        fromIdx : Fin (suc size) → DecCon 𝑨 0ℓ
        fromIdx = entryDec lc OK

      -- The certified order isomorphism Con(𝑨) ≅ 𝑳, at Layer D.
      certConIsoᵈ : ConIsoᵈ 𝑨 (toLattice 𝑳)
      certConIsoᵈ = record
        { to         = toIdx
        ; from       = fromIdx
        ; to-mono    = λ {d} {e} d⊆e →
            trans (sym (mm (toIdx d) (toIdx e)))
                  (⊆→meetIdem lc OK (toIdx d) (toIdx e)
                    (fold-mono lc OK d e d⊆e))
        ; from-mono  = λ {u} {v} u≤v →
            meetIdem→⊆ lc OK u v (trans (mm u v) u≤v)
        ; to∘from    = fold-entry lc OK
        ; from∘to    = λ d →
            ≑-sym {θ = proj₁ d} {φ = proj₁ (fromIdx (toIdx d))}
                  (d≑fold lc OK d)
        }
```

#### The certified representability witness

Packaging the finite finitary data with the certified isomorphism gives the
headline: the target lattice is decidably representable — a machine-checked
representation, on no authority but the checker's.

```agda
      -- The certificate's Representableᵈ witness for the target lattice.
      certRepresentableᵈ : Representableᵈ (toLattice 𝑳)
      certRepresentableᵈ = record
        { sigᵈ      = 𝑆
        ; algᵈ      = 𝑨
        ; finiteᵈ   = 𝑭
        ; finsigᵈ   = 𝑺
        ; con-isoᵈ  = certConIsoᵈ
        }
```

--------------------------------------


[^1]: See [the roadmap](docs/notes/flrp-research-roadmap.md) § 5, Avenue A.
