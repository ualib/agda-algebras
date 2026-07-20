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
congruence lattice of a *finite* algebra?  The program's plan (the state of the art,
the primary avenue of attack via interval-enforceable properties, and the breakdown
into work packages) lives in `docs/notes/flrp-research-roadmap.md`; this tree holds
only problem-specific formal content, while reusable mathematics developed along the
way (group actions, subgroup lattices, closure combinatorics) lands in the `Setoid/`,
`Classical/`, and `Order/` trees proper.

Two standing warnings apply to everything under this namespace.

+  **Research-track separation**.  The FLRP is distinct from the algebraic-complexity
   / finite-CSP track and from the Maltsev and interpretability infrastructure, even
   where they share modules; do not conflate them (see `CLAUDE.md` and
   `docs/GITHUB_PROJECT.md`).
+  **Experimental status**.  FLRP modules are research material and are exempt from
   the stable-API deprecation discipline until their results stabilize.

**Current submodules**.

+  [FLRP.Problem][] — the representability predicate `Representable`, the
   formal statement of the problem, the first worked instance (the one-element
   chain), and the constructive no-go theorem for the two-element chain.
+  [FLRP.Enforceable][] — group representability of a lattice, the
   interval-enforceability classification (IE, cf-IE, min-IE), the fattening
   isomorphism `[H × K, G × K] ≅ [H, G]`, the no-contradictory-IE theorem
   (the note's Lemma 3.2), and hypothesis-parameterized statements of Lemma 3.1
   and the parachute meta-theorem.
+  [FLRP.Bridge][] — the easy (constructive) direction of the Pálfy–Pudlák
   correspondence at **Layer S**: the order isomorphism `Con (𝒢 ↷ 𝒢/H) ≅ [H, 𝒢]`
   between the *semantic* congruence lattice of the transitive coset G-set and the
   respecting upper interval in the subgroup lattice, with the representability
   corollary.  The Layer D (`DecCon`) restatement required by issue #454's updated
   criteria lands with the WP-7 decidable layer.
+  [FLRP.Representable][] — the Layer-D reformulation of the problem:
   decidable representability `Representableᵈ`, the statement
   `FLRP-Statementᵈ`, and the constructive two-element-chain representation
   `chain₂-Representableᵈ` (the object the no-go theorem forbids at Layer S,
   attained here with no postulate).

**Planned submodules** (per § 6 of the roadmap).

+  `FLRP.Closure` (closure properties of the representable class);
+  `FLRP.Intervals` (intervals in subgroup lattices and core-free normalization);
+  `FLRP.Reductions` (the catalog of reduction theorems);
+  `FLRP.Certificates` (machine-checked representation certificates);
+  `FLRP.Assumptions` (the registry of classical theorems imported as explicit
   hypotheses, keeping the tree honest under `--safe`).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP where

open import FLRP.Problem public
open import FLRP.Enforceable public
open import FLRP.Bridge public
open import FLRP.Representable public
```
