---
name: scaffolding-a-module
description: Create a new Agda module in agda-algebras with the correct canonical path, literate .lagda.md structure, OPTIONS pragma, header, and documentation, ready to type-check. Use when adding a new module, especially the classical-structure modules in M3 (semigroups, groups, lattices, rings).
---

# Creating a new module in agda-algebras

## Where it goes

+  New work goes in `Setoid/`.  Specific theories (semigroups, groups, lattices, rings) go in `Classical/`.  Never add new modules under `Legacy/Base/`.

## Literate structure

A module is `.lagda.md`: Markdown prose interleaved with Agda code fences, with inline Agda names written as kramdown spans, e.g. `` `Semigroup`{.AgdaRecord} ``.  Lead with a prose statement of why the module exists and how it fits the development.  Write section headings as plain Markdown ATX headings (`### Title`); do not wrap them in HTML `<a id="…">…</a>` anchors — MkDocs slugifies heading text automatically (see `docs/STYLE_GUIDE.md` § Section headings).

## Skeleton

State the purpose in prose, then open the code block:

This module <one-line statement of purpose>.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.<Area>.<Name> where

-- open import ...   -- canonical Setoid/ imports only; no Legacy.Base.*

-- Definitions follow; give each an explicit type signature.
```

Continue with prose explaining each definition.

## Classical/ structures specifically

+  Define the structure with a Σ-type at the core for mathematical economy.
+  Provide a record-typed "bundle view" for agda-stdlib interop.
+  Isolate the underlying equality/equivalence so it can be mechanically substituted on the Cubical port (v4.0).

## Wiring and checking

+  No manual registration: `make` regenerates the `Everything*.agda` aggregator by scanning the tree, so a new module is picked up automatically.
+  Type-check per-file, then `make check`.
+  Gate quality: explicit type signatures, small named lemmas, one canonical name per concept, prose paired with each formal statement.


