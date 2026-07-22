---
layout: default
file: "src/Setoid/Congruences/Certificates.lagda.md"
title: "Setoid.Congruences.Certificates module (The Agda Universal Algebra Library)"
date: "2026-07-22"
author: "the agda-algebras development team"
---

### Congruence certificates

This is the [Setoid.Congruences.Certificates][] module of the [Agda Universal Algebra Library][].

Machine-checked import of externally computed congruence-lattice facts: the
certificate schema (normal-form parent vectors and Freese traces) and the
search-free checkers that turn a certificate into a theorem.  The design is fixed
in `docs/notes/flrp-wp6-freese-certificates.md`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Congruences.Certificates where

open import Setoid.Congruences.Certificates.Schema      public
open import Setoid.Congruences.Certificates.Congruence  public
```
