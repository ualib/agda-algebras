---
layout: default
file: "src/FLRP/KurzweilNetter/Invariance.lagda.md"
title: "FLRP.KurzweilNetter.Invariance module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### Invariant partitions

This is the [FLRP.KurzweilNetter.Invariance][] module of the [Agda Universal Algebra Library][].

A partition `π` of `Fin n` is **invariant** under a map `t : Fin n → Fin n` when
`t` carries blocks into blocks: indices in one block of `π` have their `t`-images
in one block of `π`.  This is the pivotal notion of the Kurzweil–Netter expansion
step (issue #502): on the algebra side, the congruences of a finite algebra `𝑨`
indexed by `Fin n` correspond exactly to the partitions invariant under `𝑨`'s
basic translations ([FLRP.KurzweilNetter.Translations][]); on the group side, the
congruences of the expanded coset algebra on `Sⁿ/D` correspond exactly to the
partition subgroups `K_π` with `π` invariant under the lifted maps
([FLRP.KurzweilNetter.Expansion][]).  The two sides meet in this definition,
which is why it lives in its own small module, free of both the algebra and the
group.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter.Invariance where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base   using ( Fin )
open import Data.Nat.Base   using ( ℕ )
open import Data.Product    using ( _,_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Partitions  using ( SameBlock ; _≈ᵖ_ )
open import Setoid.Congruences.Certificates.Schema   using ( ParentVec )

private variable n : ℕ
```
-->

#### The invariance predicate

`Inv t pv` says the kernel of `pv` is preserved by `t`: a block relation of the
partition is carried to a block relation.

```agda
-- The partition pv is invariant under the index map t.
Inv : (Fin n → Fin n) → ParentVec n → Type
Inv t pv = ∀ {i j} → SameBlock pv i j → SameBlock pv (t i) (t j)
```

Invariance is a property of the *kernel*, so it transports along partition
equality (mutual refinement) — the lemma every round trip below needs when a
construction returns a merely `≈ᵖ`-equal presentation of a partition.

```agda
-- Invariance respects kernel equality of the partitions.
Inv-resp-≈ᵖ : (t : Fin n → Fin n) {pu pw : ParentVec n}
  → pu ≈ᵖ pw → Inv t pu → Inv t pw
Inv-resp-≈ᵖ t (u⊑w , w⊑u) invᵤ sb = u⊑w (invᵤ (w⊑u sb))
```

--------------------------------------
