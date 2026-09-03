---
layout: default
file: "src/FLRP/KurzweilInterval/Surjectivity.lagda.md"
title: "FLRP.KurzweilInterval.Surjectivity module (The Agda Universal Algebra Library)"
date: "2026-09-02"
author: "the agda-algebras development team"
---

### Kurzweil surjectivity, proved: the retirement of Entry 4

This is the [FLRP.KurzweilInterval.Surjectivity][] module of the [Agda Universal Algebra Library][].

This module discharges the working form of **Entry 4** of [FLRP.Assumptions][]: for a finite nonabelian simple base group, every decidable interval element of `[D , Sⁿ]` is a partition subgroup, with the partition produced as data.  [FLRP.KurzweilInterval][] states Kurzweil's lemma; this companion proves its surjectivity half, by reading the blockwise collapse of [Classical.Structures.Group.PowerCollapse][] through the interval vocabulary, and packages it in the two forms native to the lemma:

+  `kurzweilSurjectivityᵈ`{.AgdaFunction}: the surjectivity family itself, `KurzweilSurjectivityᵈAt 𝒮 n` for every exponent, the hypothesis of the Kurzweil–Netter route, now a theorem;
+  `kurzweilIntervalIsoᵈ`{.AgdaFunction}: **Kurzweil's lemma**, unconditionally: the decidable interval `[D , Sⁿ]` is isomorphic to the dual of the partition lattice `Eq(n)`.

The hypotheses of both are a `FiniteAlgebra`{.AgdaRecord} witness and the `IsNonabelianSimple`{.AgdaRecord} bundle of [Classical.Structures.Group.Simple][]; the nontriviality witness the interval isomorphism needs is derived from the bundle's non-commuting pair.  The Layer-S form of Entry 4 stays behind in the registry as the classical statement of record: it is excluded middle (the no-go of [FLRP.KurzweilInterval][]), so this decidable form is not one honest layer of two but the *only* provable layer, exactly as the registry's strength note records.

What is deliberately *not* here is any consequence for the Kurzweil–Netter duality theorem: that theorem lives in the [FLRP.KurzweilNetter][] namespace, and its closure over the base-group package (`kurzweilNetterDuality-ofSimple`{.AgdaFunction}) sits at the bottom of [FLRP.KurzweilNetter.Duality][], consuming this module's family.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilInterval.Surjectivity where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Nat.Base    using ( ℕ )
open import Data.Product     using ( _,_ ; proj₁ ; proj₂ )
open import Level            using ( 0ℓ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice             using  ( module Lattice-Order )
open import Classical.Structures.Group.Basic         using  ( Group )
open import Classical.Structures.Group.PowerCollapse using  ( module PowerCollapse )
open import Classical.Structures.Group.Simple        using  ( module Simple )
open import Classical.Structures.Lattice.Dual        using  ( dualLattice
                                                            ; module LatticeDual )
open import Classical.Structures.Lattice.Partitions  using  ( EqLattice ; _⊑_ ; ⊑→≤ ; ≤→⊑ )
open import FLRP.Assumptions                         using  ( KurzweilSurjectivityᵈAt )
open import FLRP.KurzweilInterval                    using  ( module KurzweilInterval )
open import Order.Iso                                using  ( OrderIso )
open import Setoid.Algebras.Basic                    using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                   using  ( FiniteAlgebra )
open import Setoid.Congruences.Certificates.Schema   using  ( ParentVec )
```
-->

#### The theorem

The whole module is parameterized by the base-group package: the group, its finiteness witness, and the nonabelian-simplicity bundle.

```agda
module _ (𝒮@(𝑺 , _)  : Group 0ℓ 0ℓ)
         (𝑭ₛ          : FiniteAlgebra 𝑺)
         (nas         : Simple.IsNonabelianSimple 𝒮 0ℓ)
  where

  open Simple 𝒮 0ℓ using ( elt ; elt≉ε )
```

**Entry 4, discharged.**  A decidable interval element unbundles into exactly the four hypotheses of the collapse module, and the collapse's Σ-package is the surjectivity statement verbatim.

```agda
  -- Kurzweil surjectivity holds at every exponent.
  kurzweilSurjectivityᵈ : (n : ℕ) → KurzweilSurjectivityᵈAt 𝒮 n
  kurzweilSurjectivityᵈ n (𝑴 , 𝑴?) =
    PowerCollapse.collapse n 𝒮 𝑭ₛ nas (set 𝑴) (element-isSubgroup 𝑴) 𝑴? (above 𝑴)
    where open KurzweilInterval 𝒮 n using ( set ; element-isSubgroup ; above )
```

#### Kurzweil's lemma, unconditionally

With surjectivity a theorem, the conditional interval isomorphism of [FLRP.KurzweilInterval][] closes over the decidable carrier: `[D , Sⁿ]` with decidable membership is dually isomorphic to the partition lattice.  The maps and round trips are those of the conditional isomorphism; the deciders ride along, produced by `K-dec`{.AgdaFunction} on the way in and forgotten on the way out.

```agda
  module _ (n : ℕ) where

    open KurzweilInterval 𝒮 n
    open LatticeDual (EqLattice n) using ( ≤ᵈ-flip ; ≤ᵈ-unflip )

    private
      -- The partition attached to a decidable interval element by the theorem.
      part : Intervalᵈ → ParentVec n
      part 𝑴 = kurzweilSurjectivityᵈ n 𝑴 .proj₁

      part-in : (𝑴 : Intervalᵈ) → set (𝑴 .proj₁) ⊆ K (part 𝑴)
      part-in 𝑴 = kurzweilSurjectivityᵈ n 𝑴 .proj₂ .proj₁

      part-out : (𝑴 : Intervalᵈ) → K (part 𝑴) ⊆ set (𝑴 .proj₁)
      part-out 𝑴 = kurzweilSurjectivityᵈ n 𝑴 .proj₂ .proj₂

      -- Inclusion of decidable interval elements reflects to reversed refinement.
      mono-flip : {𝑴 𝑵 : Intervalᵈ} → 𝑴 ≤ᵢᵈ 𝑵 → part 𝑵 ⊑ part 𝑴
      mono-flip {𝑴} {𝑵} le =
        K-reflects (elt nas) (elt≉ε nas) {pu = part 𝑵} {pw = part 𝑴}
          λ k → part-in 𝑵 (le (part-out 𝑴 k))

    -- Kurzweil's lemma: [D , Sⁿ]ᵈ ≅ Eq(n)′, with no hypothesis.
    kurzweilIntervalIsoᵈ :
      OrderIso _≈ᵢᵈ_ _≤ᵢᵈ_
        (Setoid._≈_ 𝔻[ proj₁ (dualLattice (EqLattice n)) ])
        (Lattice-Order._≤_ (dualLattice (EqLattice n)))
    kurzweilIntervalIsoᵈ = record
      { to         = part
      ; from       = λ pv → toInterval pv , K-dec 𝑭ₛ pv
      ; to-mono    = λ {𝑴} {𝑵} le → ≤ᵈ-unflip ( ⊑→≤ {pu = part 𝑵} {pw = part 𝑴}
                                                   ( mono-flip {𝑴} {𝑵} le ) )
      ; from-mono  = λ {pu} {pw} le → K-antitone {pu = pw} {pw = pu}
                                        ( ≤→⊑ (≤ᵈ-flip {x = pu} {y = pw} le) )
      ; to∘from    = λ pv → K-injective (elt nas) (elt≉ε nas)
                              {pu = part (toInterval pv , K-dec 𝑭ₛ pv)} {pw = pv}
                              ( part-in  (toInterval pv , K-dec 𝑭ₛ pv) )
                              ( part-out (toInterval pv , K-dec 𝑭ₛ pv) )
      ; from∘to    = λ 𝑴 → part-out 𝑴 , part-in 𝑴
      }
```
