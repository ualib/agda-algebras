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

**Planned submodules** (per § 6 of the roadmap).

+  `FLRP.Closure` (closure properties of the representable class);
+  `FLRP.Intervals` (intervals in subgroup lattices and core-free normalization);
+  `FLRP.Enforceable` (interval-enforceable properties);
+  `FLRP.Reductions` (the catalog of reduction theorems);
+  `FLRP.Certificates` (machine-checked representation certificates);
+  `FLRP.Assumptions` (the registry of classical theorems imported as explicit
   hypotheses, keeping the tree honest under `--safe`).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP where

open import FLRP.Problem public
```
