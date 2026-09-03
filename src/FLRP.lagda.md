---
layout: default
file: "src/FLRP.lagda.md"
title: "FLRP module (The Agda Universal Algebra Library)"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### The Finite Lattice Representation Problem

This is the [FLRP][] module of the [Agda Universal Algebra Library][].

This top-level `FLRP/` tree hosts the library's research program on the
**Finite Lattice Representation Problem**: is every finite lattice isomorphic to the
congruence lattice of a *finite* algebra?

The program's plan (the state of the art, the primary avenue of attack via
interval-enforceable properties, and the breakdown into work packages) lives in
[`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md).

The `FLRP/` tree holds only problem-specific formal content, while reusable
mathematics developed along the way (group actions, subgroup lattices, closure
combinatorics) lives in the `Setoid/`, `Classical/`, and `Order/` trees.

Two standing warnings apply to everything under this namespace.

+  **Research-track separation**.  The FLRP is distinct from the algebraic-complexity
   / finite-CSP track and from the Maltsev and interpretability infrastructure, even
   where they share modules.
+  **Experimental status**.  FLRP modules are research material and are exempt from
   the stable-API deprecation discipline until their results stabilize.

**Current submodules**.

+  [FLRP.Problem][]: the representability predicate `Representable`, the
   formal statement of the problem, the first worked instance (the one-element
   chain), and the constructive no-go theorem for the two-element chain.
+  [FLRP.Enforceable][]: group representability of a lattice, the
   interval-enforceability classification (IE, cf-IE, min-IE), the fattening
   isomorphism `[H × K, G × K] ≅ [H, G]`, the no-contradictory-IE theorem
   (the research note's Lemma 3.2), and hypothesis-parameterized statements of
   Lemma 3.1 and the parachute meta-theorem.
+  [FLRP.Bridge][]: the easy (constructive) direction of the Pálfy–Pudlák
   correspondence, at both layers: the Layer-S order isomorphism
   `Con (𝒢 ↷ 𝒢/H) ≅ [H, 𝒢]` between the semantic congruence lattice of the
   transitive G-set of cosets and the respecting upper interval in the subgroup
   lattice, and its Layer-D counterpart `DecCon (𝒢 ↷ 𝒢/H) ≅ [H, 𝒢]ᵈ` over the
   decidably presented interval (`bridgeᵈ`), proved directly with no classical
   assumption, together with the representability corollaries — in particular
   `GroupRepresentable→Representableᵈ`: every group-representable lattice is
   decidably representable (issue #454).
+  [FLRP.Representable][]: the Layer-D reformulation of the problem:
   decidable representability `Representableᵈ`, the statement
   `FLRP-Statementᵈ`, and the constructive two-element-chain representation
   `chain₂-Representableᵈ` (the object the no-go theorem forbids at Layer S,
   attained here with no postulate).
+  [FLRP.Assumptions][]: the registry of classical theorems imported as
   explicit hypotheses (never postulates), keeping the tree honest under
   `--safe`; Entry 1 is the congruence-completeness bridge
   `CongruenceCompleteness`, the single Layer-S→Layer-D assumption of ADR-008;
   Entry 2 (Kurzweil–Netter duality) is reduced by the proof in
   [FLRP.KurzweilNetter][] to Entry 4 (Kurzweil surjectivity), which
   [FLRP.KurzweilNetter.Surjectivity][] proves in its decidable working form, so both
   entries are retired and neither enters anywhere as a hypothesis.
+  [FLRP.Closure][]: the WP-5 closure toolkit: product and ordinal-sum
   closure of `Representableᵈ` (issue #456), the adjoin-a-new-extremum
   corollaries at `chain₂`, and the duality theorem `dual-Representableᵈ`,
   rewired from the retired Entry 2 to the Kurzweil–Netter proof.
+  [FLRP.KurzweilNetter][]: the Kurzweil–Netter theorem, complete (issues
   #502, #522, #527): Kurzweil's interval lemma stated (with the
   excluded-middle no-go for its Layer-S form) and proved (the blockwise
   collapse, retiring Entry 4), the algebra-side reduction of congruences to
   translation-invariant partitions, the expansion of the coset algebra on
   `Sᵐ/D`, the assembled theorem `kurzweilNetterDuality` parameterized by
   exactly the properties of the base group the argument uses, and the closed
   instantiation `kurzweilNetterDuality-A₅` at the certified `A₅`.
+  [FLRP.LayerBridge][]: the cross-layer bridge: under the congruence-completeness
   assumption, the semantic and decidable congruence posets are order-isomorphic
   (`conDecIso`), whence `Representable 𝑳 ↔ Representableᵈ 𝑳`.
+  [FLRP.Certificates][]: machine-checked representation certificates: the
   assembly turning a checked whole-lattice certificate (Freese traces and
   pointer tables, verified search-free by the
   `Setoid.Congruences.Certificates` checkers) into a `Representableᵈ` witness
   for the target lattice, so external searches (GAP, UACalc, SAT) enter the
   corpus only through the checker.
+  [FLRP.L7EqSix][]: the explicit Pudlák–Tůma witness for the distinguished
   open instance: seven partitions of a six-element set (the minimum possible)
   forming a sublattice of `Eq(6)` isomorphic to `L7`, with meets, join upper
   bounds, injectivity, and normal forms decided over the finite carrier and
   join least-ness proved against arbitrary equivalence relations via bounded
   alternating chains (issue #484; session note `docs/notes/flrp-l7-eq6.md`).

+  [FLRP.WreathNoGo][]: the RP-4 **wreath no-go**: the note's Lemma 3.3 by
   the double Kurzweil construction (a property cf-IE by a group-representable
   lattice has wreath products `S ≀ Ū` over every admissible base), with the
   core-freeness preservation proved in [Classical.Structures.Group.Wreath][]
   and the coset action's faithfulness derived from core-freeness; the
   omission corollary for wreath-omitting classes; the joint-wreath-richness
   constraint on a contradictory pair; and the statement of RP-4's dead-end
   question, reduced formally to statement (C).  Consumes Entry 5 of the
   assumptions registry; design note `docs/notes/flrp-rp4-wreath.md`.

+  [FLRP.Reductions][]: the RP-2 **enforcement catalog**: the literature's
   "an interval of this shape forces a group of this kind" theorems, each recast
   as a precise (cf-/min-)IE statement, with the vacuity discipline tracked
   entry by entry.  Entries 1–3 (the note's classes `𝒢₂`, `𝒢₃`, `𝒢₄`) are
   *derived* from the parachute theorems; Entries 4–8 import their sources'
   theorems as named hypotheses (Pálfy–Pudlák, Feit, Köhler, Basile, DeMeo's
   `L7` analysis, Lucchini–Moscatiello–Palcoux–Spiga).  The module also proves
   the note's Lemma 3.1, exposes the vacuity theorem
   `not-representable→IE`, and repairs `minIE` as `MinimallyIE`; the survey note
   is `docs/notes/flrp-rp2-catalog.md`.

+  [FLRP.Hunt][]: the RP-3 **constraint dossier** for the hunt for an
   empty-intersection family: the degenerate enforcements of the one- and
   two-element chains (triviality and nontriviality), a concrete core-free
   representation of the one-element chain, the machine-checked refutation of
   statement (C) as the note prints it (`unguarded-statement-C-refuted`, the
   erratum-grade finding behind the per-canopy guard of the repaired
   `Statement-C`), the refutation of the unrestricted pair statement and its
   repaired form `PairQuestion`, the closure of the two-element corner of the
   RP-4 reduction (outright on chains, by padding under statement (C)
   otherwise), the theorem that families of two-element chains have inhabited
   intersection, and the wreath-richness of two-element-chain classes; the
   survey note is `docs/notes/flrp-rp3-hunt.md`.

**Planned submodules** (per § 6 of the roadmap).

+  `FLRP.Intervals` (intervals in subgroup lattices and core-free normalization).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP where

open import FLRP.Problem        public
open import FLRP.Enforceable    public
open import FLRP.Parachute      public
open import FLRP.Parachute.Representation public
open import FLRP.Parachute.Theorems       public
open import FLRP.Reductions     public
open import FLRP.Bridge         public
open import FLRP.Representable  public
open import FLRP.Assumptions    public
open import FLRP.Closure        public
open import FLRP.KurzweilNetter public
open import FLRP.LayerBridge    public
open import FLRP.WreathNoGo     public
open import FLRP.Hunt           public
open import FLRP.Certificates   public
open import FLRP.L7EqSix        public
```
