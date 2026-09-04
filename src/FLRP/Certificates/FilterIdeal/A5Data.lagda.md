---
layout: default
file: "src/FLRP/Certificates/FilterIdeal/A5Data.lagda.md"
title: "FLRP.Certificates.FilterIdeal.A5Data module (The Agda Universal Algebra Library)"
date: "2026-08-17"
author: "the agda-algebras development team (emitted by scripts/python/flrp/filter_ideal_certs.py)"
---

### Certificate data: A5, its L16 subgroups, and their escalation words

This is the [FLRP.Certificates.FilterIdeal.A5Data][] module of the [Agda Universal Algebra Library][].

**This module was emitted by `scripts/python/flrp/filter_ideal_certs.py`.
Do not edit it by hand; rerun the emitter instead.**

Pure data, no proofs: the alternating group `A5` as 60 permutation
image-vectors on 5 points with its multiplication and inverse tables, the
characteristic vectors of the seven subgroups `1 , C3 , C5 , S3 , A4 , A4' ,
A5` that carry the census lattice `L16` as a filter-ideal union, and the
escalation certificates (generators, ranks, step targets, step words,
expansion words) for the two interval families `[C3 , A5]` (five
members) and `[1 , C5]` (two members), in the schema of
[Classical.Structures.Group.SubgroupClassification][].  Element `0` is the
identity; elements are the even permutations of `{0..4}` in lexicographic
order of their image vectors.  Every table below is re-verified by decision
in [FLRP.Certificates.FilterIdeal.L16SubA5][]: a wrong entry or word makes a
decidable check compute to `no`{.AgdaInductiveConstructor} and breaks
compilation, so nothing is believed on this emitter's authority.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Certificates.FilterIdeal.A5Data where

open import Data.Bool.Base      using ( Bool ; true ; false )
open import Data.Fin.Base       using ( Fin ; suc )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F ; 7F ; 8F ; 9F )
open import Data.List.Base      using ( List ; [] ; _∷_ )
open import Data.Nat.Base       using ( ℕ )
open import Data.Vec.Base       using ( Vec ; [] ; _∷_ )
```
-->

`Data.Fin.Patterns` stops at `9F`; the larger literals this module needs are
declared as pattern synonyms once here.

```agda
pattern 10F = suc 9F
pattern 11F = suc 10F
pattern 12F = suc 11F
pattern 13F = suc 12F
pattern 14F = suc 13F
pattern 15F = suc 14F
pattern 16F = suc 15F
pattern 17F = suc 16F
pattern 18F = suc 17F
pattern 19F = suc 18F
pattern 20F = suc 19F
pattern 21F = suc 20F
pattern 22F = suc 21F
pattern 23F = suc 22F
pattern 24F = suc 23F
pattern 25F = suc 24F
pattern 26F = suc 25F
pattern 27F = suc 26F
pattern 28F = suc 27F
pattern 29F = suc 28F
pattern 30F = suc 29F
pattern 31F = suc 30F
pattern 32F = suc 31F
pattern 33F = suc 32F
pattern 34F = suc 33F
pattern 35F = suc 34F
pattern 36F = suc 35F
pattern 37F = suc 36F
pattern 38F = suc 37F
pattern 39F = suc 38F
pattern 40F = suc 39F
pattern 41F = suc 40F
pattern 42F = suc 41F
pattern 43F = suc 42F
pattern 44F = suc 43F
pattern 45F = suc 44F
pattern 46F = suc 45F
pattern 47F = suc 46F
pattern 48F = suc 47F
pattern 49F = suc 48F
pattern 50F = suc 49F
pattern 51F = suc 50F
pattern 52F = suc 51F
pattern 53F = suc 52F
pattern 54F = suc 53F
pattern 55F = suc 54F
pattern 56F = suc 55F
pattern 57F = suc 56F
pattern 58F = suc 57F
pattern 59F = suc 58F
```

#### The group tables

```agda
permVecs : Vec (Vec (Fin 5) 5) 60
permVecs =
  (    (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ [])
     ∷ (0F ∷ 1F ∷ 3F ∷ 4F ∷ 2F ∷ [])
     ∷ (0F ∷ 1F ∷ 4F ∷ 2F ∷ 3F ∷ [])
     ∷ (0F ∷ 2F ∷ 1F ∷ 4F ∷ 3F ∷ [])
     ∷ (0F ∷ 2F ∷ 3F ∷ 1F ∷ 4F ∷ [])
     ∷ (0F ∷ 2F ∷ 4F ∷ 3F ∷ 1F ∷ [])
     ∷ (0F ∷ 3F ∷ 1F ∷ 2F ∷ 4F ∷ [])
     ∷ (0F ∷ 3F ∷ 2F ∷ 4F ∷ 1F ∷ [])
     ∷ (0F ∷ 3F ∷ 4F ∷ 1F ∷ 2F ∷ [])
     ∷ (0F ∷ 4F ∷ 1F ∷ 3F ∷ 2F ∷ [])
     ∷ (0F ∷ 4F ∷ 2F ∷ 1F ∷ 3F ∷ [])
     ∷ (0F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ [])
     ∷ (1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ [])
     ∷ (1F ∷ 0F ∷ 3F ∷ 2F ∷ 4F ∷ [])
     ∷ (1F ∷ 0F ∷ 4F ∷ 3F ∷ 2F ∷ [])
     ∷ (1F ∷ 2F ∷ 0F ∷ 3F ∷ 4F ∷ [])
     ∷ (1F ∷ 2F ∷ 3F ∷ 4F ∷ 0F ∷ [])
     ∷ (1F ∷ 2F ∷ 4F ∷ 0F ∷ 3F ∷ [])
     ∷ (1F ∷ 3F ∷ 0F ∷ 4F ∷ 2F ∷ [])
     ∷ (1F ∷ 3F ∷ 2F ∷ 0F ∷ 4F ∷ [])
     ∷ (1F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ [])
     ∷ (1F ∷ 4F ∷ 0F ∷ 2F ∷ 3F ∷ [])
     ∷ (1F ∷ 4F ∷ 2F ∷ 3F ∷ 0F ∷ [])
     ∷ (1F ∷ 4F ∷ 3F ∷ 0F ∷ 2F ∷ [])
     ∷ (2F ∷ 0F ∷ 1F ∷ 3F ∷ 4F ∷ [])
     ∷ (2F ∷ 0F ∷ 3F ∷ 4F ∷ 1F ∷ [])
     ∷ (2F ∷ 0F ∷ 4F ∷ 1F ∷ 3F ∷ [])
     ∷ (2F ∷ 1F ∷ 0F ∷ 4F ∷ 3F ∷ [])
     ∷ (2F ∷ 1F ∷ 3F ∷ 0F ∷ 4F ∷ [])
     ∷ (2F ∷ 1F ∷ 4F ∷ 3F ∷ 0F ∷ [])
     ∷ (2F ∷ 3F ∷ 0F ∷ 1F ∷ 4F ∷ [])
     ∷ (2F ∷ 3F ∷ 1F ∷ 4F ∷ 0F ∷ [])
     ∷ (2F ∷ 3F ∷ 4F ∷ 0F ∷ 1F ∷ [])
     ∷ (2F ∷ 4F ∷ 0F ∷ 3F ∷ 1F ∷ [])
     ∷ (2F ∷ 4F ∷ 1F ∷ 0F ∷ 3F ∷ [])
     ∷ (2F ∷ 4F ∷ 3F ∷ 1F ∷ 0F ∷ [])
     ∷ (3F ∷ 0F ∷ 1F ∷ 4F ∷ 2F ∷ [])
     ∷ (3F ∷ 0F ∷ 2F ∷ 1F ∷ 4F ∷ [])
     ∷ (3F ∷ 0F ∷ 4F ∷ 2F ∷ 1F ∷ [])
     ∷ (3F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ [])
     ∷ (3F ∷ 1F ∷ 2F ∷ 4F ∷ 0F ∷ [])
     ∷ (3F ∷ 1F ∷ 4F ∷ 0F ∷ 2F ∷ [])
     ∷ (3F ∷ 2F ∷ 0F ∷ 4F ∷ 1F ∷ [])
     ∷ (3F ∷ 2F ∷ 1F ∷ 0F ∷ 4F ∷ [])
     ∷ (3F ∷ 2F ∷ 4F ∷ 1F ∷ 0F ∷ [])
     ∷ (3F ∷ 4F ∷ 0F ∷ 1F ∷ 2F ∷ [])
     ∷ (3F ∷ 4F ∷ 1F ∷ 2F ∷ 0F ∷ [])
     ∷ (3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ [])
     ∷ (4F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ [])
     ∷ (4F ∷ 0F ∷ 2F ∷ 3F ∷ 1F ∷ [])
     ∷ (4F ∷ 0F ∷ 3F ∷ 1F ∷ 2F ∷ [])
     ∷ (4F ∷ 1F ∷ 0F ∷ 3F ∷ 2F ∷ [])
     ∷ (4F ∷ 1F ∷ 2F ∷ 0F ∷ 3F ∷ [])
     ∷ (4F ∷ 1F ∷ 3F ∷ 2F ∷ 0F ∷ [])
     ∷ (4F ∷ 2F ∷ 0F ∷ 1F ∷ 3F ∷ [])
     ∷ (4F ∷ 2F ∷ 1F ∷ 3F ∷ 0F ∷ [])
     ∷ (4F ∷ 2F ∷ 3F ∷ 0F ∷ 1F ∷ [])
     ∷ (4F ∷ 3F ∷ 0F ∷ 2F ∷ 1F ∷ [])
     ∷ (4F ∷ 3F ∷ 1F ∷ 0F ∷ 2F ∷ [])
     ∷ (4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ [])
     ∷ [])

mulVecs : Vec (Vec (Fin 60) 60) 60
mulVecs =
  (    (  0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ 7F ∷ 8F ∷ 9F ∷ 10F ∷ 11F ∷ 12F ∷ 13F ∷ 14F ∷ 15F ∷ 16F ∷ 17F ∷ 18F ∷ 19F
        ∷ 20F ∷ 21F ∷ 22F ∷ 23F ∷ 24F ∷ 25F ∷ 26F ∷ 27F ∷ 28F ∷ 29F ∷ 30F ∷ 31F ∷ 32F ∷ 33F ∷ 34F ∷ 35F ∷ 36F ∷ 37F ∷ 38F ∷ 39F
        ∷ 40F ∷ 41F ∷ 42F ∷ 43F ∷ 44F ∷ 45F ∷ 46F ∷ 47F ∷ 48F ∷ 49F ∷ 50F ∷ 51F ∷ 52F ∷ 53F ∷ 54F ∷ 55F ∷ 56F ∷ 57F ∷ 58F ∷ 59F
        ∷ [])
     ∷ (  1F ∷ 2F ∷ 0F ∷ 6F ∷ 8F ∷ 7F ∷ 9F ∷ 11F ∷ 10F ∷ 3F ∷ 4F ∷ 5F ∷ 13F ∷ 14F ∷ 12F ∷ 18F ∷ 20F ∷ 19F ∷ 21F ∷ 23F
        ∷ 22F ∷ 15F ∷ 16F ∷ 17F ∷ 36F ∷ 38F ∷ 37F ∷ 39F ∷ 41F ∷ 40F ∷ 45F ∷ 46F ∷ 47F ∷ 42F ∷ 43F ∷ 44F ∷ 48F ∷ 50F ∷ 49F ∷ 51F
        ∷ 53F ∷ 52F ∷ 57F ∷ 58F ∷ 59F ∷ 54F ∷ 55F ∷ 56F ∷ 24F ∷ 25F ∷ 26F ∷ 27F ∷ 28F ∷ 29F ∷ 30F ∷ 31F ∷ 32F ∷ 33F ∷ 34F ∷ 35F
        ∷ [])
     ∷ (  2F ∷ 0F ∷ 1F ∷ 9F ∷ 10F ∷ 11F ∷ 3F ∷ 5F ∷ 4F ∷ 6F ∷ 8F ∷ 7F ∷ 14F ∷ 12F ∷ 13F ∷ 21F ∷ 22F ∷ 23F ∷ 15F ∷ 17F
        ∷ 16F ∷ 18F ∷ 20F ∷ 19F ∷ 48F ∷ 49F ∷ 50F ∷ 51F ∷ 52F ∷ 53F ∷ 54F ∷ 55F ∷ 56F ∷ 57F ∷ 58F ∷ 59F ∷ 24F ∷ 26F ∷ 25F ∷ 27F
        ∷ 29F ∷ 28F ∷ 33F ∷ 34F ∷ 35F ∷ 30F ∷ 31F ∷ 32F ∷ 36F ∷ 38F ∷ 37F ∷ 39F ∷ 41F ∷ 40F ∷ 45F ∷ 46F ∷ 47F ∷ 42F ∷ 43F ∷ 44F
        ∷ [])
     ∷ (  3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ 10F ∷ 9F ∷ 11F ∷ 7F ∷ 6F ∷ 8F ∷ 24F ∷ 26F ∷ 25F ∷ 27F ∷ 29F ∷ 28F ∷ 33F ∷ 34F
        ∷ 35F ∷ 30F ∷ 31F ∷ 32F ∷ 12F ∷ 14F ∷ 13F ∷ 15F ∷ 17F ∷ 16F ∷ 21F ∷ 22F ∷ 23F ∷ 18F ∷ 19F ∷ 20F ∷ 49F ∷ 48F ∷ 50F ∷ 54F
        ∷ 55F ∷ 56F ∷ 51F ∷ 52F ∷ 53F ∷ 57F ∷ 59F ∷ 58F ∷ 37F ∷ 36F ∷ 38F ∷ 42F ∷ 43F ∷ 44F ∷ 39F ∷ 40F ∷ 41F ∷ 45F ∷ 47F ∷ 46F
        ∷ [])
     ∷ (  4F ∷ 3F ∷ 5F ∷ 7F ∷ 6F ∷ 8F ∷ 0F ∷ 1F ∷ 2F ∷ 10F ∷ 11F ∷ 9F ∷ 25F ∷ 24F ∷ 26F ∷ 30F ∷ 31F ∷ 32F ∷ 27F ∷ 28F
        ∷ 29F ∷ 33F ∷ 35F ∷ 34F ∷ 37F ∷ 36F ∷ 38F ∷ 42F ∷ 43F ∷ 44F ∷ 39F ∷ 40F ∷ 41F ∷ 45F ∷ 47F ∷ 46F ∷ 12F ∷ 13F ∷ 14F ∷ 15F
        ∷ 16F ∷ 17F ∷ 18F ∷ 19F ∷ 20F ∷ 21F ∷ 22F ∷ 23F ∷ 49F ∷ 50F ∷ 48F ∷ 54F ∷ 56F ∷ 55F ∷ 57F ∷ 59F ∷ 58F ∷ 51F ∷ 52F ∷ 53F
        ∷ [])
     ∷ (  5F ∷ 4F ∷ 3F ∷ 10F ∷ 11F ∷ 9F ∷ 7F ∷ 8F ∷ 6F ∷ 0F ∷ 2F ∷ 1F ∷ 26F ∷ 25F ∷ 24F ∷ 33F ∷ 35F ∷ 34F ∷ 30F ∷ 32F
        ∷ 31F ∷ 27F ∷ 29F ∷ 28F ∷ 49F ∷ 50F ∷ 48F ∷ 54F ∷ 56F ∷ 55F ∷ 57F ∷ 59F ∷ 58F ∷ 51F ∷ 52F ∷ 53F ∷ 37F ∷ 38F ∷ 36F ∷ 42F
        ∷ 44F ∷ 43F ∷ 45F ∷ 47F ∷ 46F ∷ 39F ∷ 40F ∷ 41F ∷ 12F ∷ 14F ∷ 13F ∷ 15F ∷ 17F ∷ 16F ∷ 21F ∷ 22F ∷ 23F ∷ 18F ∷ 19F ∷ 20F
        ∷ [])
     ∷ (  6F ∷ 7F ∷ 8F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ 5F ∷ 11F ∷ 9F ∷ 10F ∷ 36F ∷ 37F ∷ 38F ∷ 39F ∷ 40F ∷ 41F ∷ 42F ∷ 43F
        ∷ 44F ∷ 45F ∷ 46F ∷ 47F ∷ 13F ∷ 12F ∷ 14F ∷ 18F ∷ 19F ∷ 20F ∷ 15F ∷ 16F ∷ 17F ∷ 21F ∷ 23F ∷ 22F ∷ 25F ∷ 24F ∷ 26F ∷ 30F
        ∷ 31F ∷ 32F ∷ 27F ∷ 28F ∷ 29F ∷ 33F ∷ 35F ∷ 34F ∷ 50F ∷ 48F ∷ 49F ∷ 57F ∷ 58F ∷ 59F ∷ 51F ∷ 53F ∷ 52F ∷ 54F ∷ 56F ∷ 55F
        ∷ [])
     ∷ (  7F ∷ 8F ∷ 6F ∷ 4F ∷ 5F ∷ 3F ∷ 11F ∷ 10F ∷ 9F ∷ 1F ∷ 0F ∷ 2F ∷ 37F ∷ 38F ∷ 36F ∷ 42F ∷ 44F ∷ 43F ∷ 45F ∷ 47F
        ∷ 46F ∷ 39F ∷ 40F ∷ 41F ∷ 25F ∷ 26F ∷ 24F ∷ 30F ∷ 32F ∷ 31F ∷ 33F ∷ 35F ∷ 34F ∷ 27F ∷ 28F ∷ 29F ∷ 50F ∷ 49F ∷ 48F ∷ 57F
        ∷ 59F ∷ 58F ∷ 54F ∷ 56F ∷ 55F ∷ 51F ∷ 53F ∷ 52F ∷ 13F ∷ 12F ∷ 14F ∷ 18F ∷ 19F ∷ 20F ∷ 15F ∷ 16F ∷ 17F ∷ 21F ∷ 23F ∷ 22F
        ∷ [])
     ∷ (  8F ∷ 6F ∷ 7F ∷ 11F ∷ 9F ∷ 10F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F ∷ 38F ∷ 36F ∷ 37F ∷ 45F ∷ 46F ∷ 47F ∷ 39F ∷ 41F
        ∷ 40F ∷ 42F ∷ 44F ∷ 43F ∷ 50F ∷ 48F ∷ 49F ∷ 57F ∷ 58F ∷ 59F ∷ 51F ∷ 53F ∷ 52F ∷ 54F ∷ 56F ∷ 55F ∷ 13F ∷ 14F ∷ 12F ∷ 18F
        ∷ 20F ∷ 19F ∷ 21F ∷ 23F ∷ 22F ∷ 15F ∷ 16F ∷ 17F ∷ 25F ∷ 26F ∷ 24F ∷ 30F ∷ 32F ∷ 31F ∷ 33F ∷ 35F ∷ 34F ∷ 27F ∷ 28F ∷ 29F
        ∷ [])
     ∷ (  9F ∷ 11F ∷ 10F ∷ 2F ∷ 1F ∷ 0F ∷ 8F ∷ 6F ∷ 7F ∷ 5F ∷ 3F ∷ 4F ∷ 48F ∷ 50F ∷ 49F ∷ 51F ∷ 53F ∷ 52F ∷ 57F ∷ 58F
        ∷ 59F ∷ 54F ∷ 55F ∷ 56F ∷ 14F ∷ 13F ∷ 12F ∷ 21F ∷ 23F ∷ 22F ∷ 18F ∷ 20F ∷ 19F ∷ 15F ∷ 17F ∷ 16F ∷ 38F ∷ 36F ∷ 37F ∷ 45F
        ∷ 46F ∷ 47F ∷ 39F ∷ 41F ∷ 40F ∷ 42F ∷ 44F ∷ 43F ∷ 26F ∷ 24F ∷ 25F ∷ 33F ∷ 34F ∷ 35F ∷ 27F ∷ 29F ∷ 28F ∷ 30F ∷ 32F ∷ 31F
        ∷ [])
     ∷ (  10F ∷ 9F ∷ 11F ∷ 5F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ 8F ∷ 7F ∷ 6F ∷ 49F ∷ 48F ∷ 50F ∷ 54F ∷ 55F ∷ 56F ∷ 51F ∷ 52F
        ∷ 53F ∷ 57F ∷ 59F ∷ 58F ∷ 26F ∷ 24F ∷ 25F ∷ 33F ∷ 34F ∷ 35F ∷ 27F ∷ 29F ∷ 28F ∷ 30F ∷ 32F ∷ 31F ∷ 14F ∷ 12F ∷ 13F ∷ 21F
        ∷ 22F ∷ 23F ∷ 15F ∷ 17F ∷ 16F ∷ 18F ∷ 20F ∷ 19F ∷ 38F ∷ 37F ∷ 36F ∷ 45F ∷ 47F ∷ 46F ∷ 42F ∷ 44F ∷ 43F ∷ 39F ∷ 41F ∷ 40F
        ∷ [])
     ∷ (  11F ∷ 10F ∷ 9F ∷ 8F ∷ 7F ∷ 6F ∷ 5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ 50F ∷ 49F ∷ 48F ∷ 57F ∷ 59F ∷ 58F ∷ 54F ∷ 56F
        ∷ 55F ∷ 51F ∷ 53F ∷ 52F ∷ 38F ∷ 37F ∷ 36F ∷ 45F ∷ 47F ∷ 46F ∷ 42F ∷ 44F ∷ 43F ∷ 39F ∷ 41F ∷ 40F ∷ 26F ∷ 25F ∷ 24F ∷ 33F
        ∷ 35F ∷ 34F ∷ 30F ∷ 32F ∷ 31F ∷ 27F ∷ 29F ∷ 28F ∷ 14F ∷ 13F ∷ 12F ∷ 21F ∷ 23F ∷ 22F ∷ 18F ∷ 20F ∷ 19F ∷ 15F ∷ 17F ∷ 16F
        ∷ [])
     ∷ (  12F ∷ 14F ∷ 13F ∷ 15F ∷ 17F ∷ 16F ∷ 21F ∷ 22F ∷ 23F ∷ 18F ∷ 19F ∷ 20F ∷ 0F ∷ 2F ∷ 1F ∷ 3F ∷ 5F ∷ 4F ∷ 9F ∷ 10F
        ∷ 11F ∷ 6F ∷ 7F ∷ 8F ∷ 27F ∷ 29F ∷ 28F ∷ 24F ∷ 26F ∷ 25F ∷ 34F ∷ 33F ∷ 35F ∷ 31F ∷ 30F ∷ 32F ∷ 51F ∷ 52F ∷ 53F ∷ 48F
        ∷ 49F ∷ 50F ∷ 55F ∷ 54F ∷ 56F ∷ 58F ∷ 57F ∷ 59F ∷ 39F ∷ 40F ∷ 41F ∷ 36F ∷ 37F ∷ 38F ∷ 43F ∷ 42F ∷ 44F ∷ 46F ∷ 45F ∷ 47F
        ∷ [])
     ∷ (  13F ∷ 12F ∷ 14F ∷ 18F ∷ 19F ∷ 20F ∷ 15F ∷ 16F ∷ 17F ∷ 21F ∷ 23F ∷ 22F ∷ 1F ∷ 0F ∷ 2F ∷ 6F ∷ 7F ∷ 8F ∷ 3F ∷ 4F
        ∷ 5F ∷ 9F ∷ 11F ∷ 10F ∷ 39F ∷ 40F ∷ 41F ∷ 36F ∷ 37F ∷ 38F ∷ 43F ∷ 42F ∷ 44F ∷ 46F ∷ 45F ∷ 47F ∷ 27F ∷ 28F ∷ 29F ∷ 24F
        ∷ 25F ∷ 26F ∷ 31F ∷ 30F ∷ 32F ∷ 34F ∷ 33F ∷ 35F ∷ 51F ∷ 53F ∷ 52F ∷ 48F ∷ 50F ∷ 49F ∷ 58F ∷ 57F ∷ 59F ∷ 55F ∷ 54F ∷ 56F
        ∷ [])
     ∷ (  14F ∷ 13F ∷ 12F ∷ 21F ∷ 23F ∷ 22F ∷ 18F ∷ 20F ∷ 19F ∷ 15F ∷ 17F ∷ 16F ∷ 2F ∷ 1F ∷ 0F ∷ 9F ∷ 11F ∷ 10F ∷ 6F ∷ 8F
        ∷ 7F ∷ 3F ∷ 5F ∷ 4F ∷ 51F ∷ 53F ∷ 52F ∷ 48F ∷ 50F ∷ 49F ∷ 58F ∷ 57F ∷ 59F ∷ 55F ∷ 54F ∷ 56F ∷ 39F ∷ 41F ∷ 40F ∷ 36F
        ∷ 38F ∷ 37F ∷ 46F ∷ 45F ∷ 47F ∷ 43F ∷ 42F ∷ 44F ∷ 27F ∷ 29F ∷ 28F ∷ 24F ∷ 26F ∷ 25F ∷ 34F ∷ 33F ∷ 35F ∷ 31F ∷ 30F ∷ 32F
        ∷ [])
     ∷ (  15F ∷ 16F ∷ 17F ∷ 12F ∷ 13F ∷ 14F ∷ 19F ∷ 18F ∷ 20F ∷ 22F ∷ 21F ∷ 23F ∷ 27F ∷ 28F ∷ 29F ∷ 24F ∷ 25F ∷ 26F ∷ 31F ∷ 30F
        ∷ 32F ∷ 34F ∷ 33F ∷ 35F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ 7F ∷ 8F ∷ 9F ∷ 10F ∷ 11F ∷ 40F ∷ 39F ∷ 41F ∷ 43F
        ∷ 42F ∷ 44F ∷ 36F ∷ 37F ∷ 38F ∷ 46F ∷ 47F ∷ 45F ∷ 52F ∷ 51F ∷ 53F ∷ 55F ∷ 54F ∷ 56F ∷ 48F ∷ 49F ∷ 50F ∷ 58F ∷ 59F ∷ 57F
        ∷ [])
     ∷ (  16F ∷ 17F ∷ 15F ∷ 19F ∷ 20F ∷ 18F ∷ 22F ∷ 23F ∷ 21F ∷ 12F ∷ 13F ∷ 14F ∷ 28F ∷ 29F ∷ 27F ∷ 31F ∷ 32F ∷ 30F ∷ 34F ∷ 35F
        ∷ 33F ∷ 24F ∷ 25F ∷ 26F ∷ 40F ∷ 41F ∷ 39F ∷ 43F ∷ 44F ∷ 42F ∷ 46F ∷ 47F ∷ 45F ∷ 36F ∷ 37F ∷ 38F ∷ 52F ∷ 53F ∷ 51F ∷ 55F
        ∷ 56F ∷ 54F ∷ 58F ∷ 59F ∷ 57F ∷ 48F ∷ 49F ∷ 50F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ 7F ∷ 8F ∷ 9F ∷ 10F ∷ 11F
        ∷ [])
     ∷ (  17F ∷ 15F ∷ 16F ∷ 22F ∷ 21F ∷ 23F ∷ 12F ∷ 14F ∷ 13F ∷ 19F ∷ 20F ∷ 18F ∷ 29F ∷ 27F ∷ 28F ∷ 34F ∷ 33F ∷ 35F ∷ 24F ∷ 26F
        ∷ 25F ∷ 31F ∷ 32F ∷ 30F ∷ 52F ∷ 51F ∷ 53F ∷ 55F ∷ 54F ∷ 56F ∷ 48F ∷ 49F ∷ 50F ∷ 58F ∷ 59F ∷ 57F ∷ 0F ∷ 2F ∷ 1F ∷ 3F
        ∷ 5F ∷ 4F ∷ 9F ∷ 10F ∷ 11F ∷ 6F ∷ 7F ∷ 8F ∷ 40F ∷ 41F ∷ 39F ∷ 43F ∷ 44F ∷ 42F ∷ 46F ∷ 47F ∷ 45F ∷ 36F ∷ 37F ∷ 38F
        ∷ [])
     ∷ (  18F ∷ 20F ∷ 19F ∷ 13F ∷ 14F ∷ 12F ∷ 23F ∷ 21F ∷ 22F ∷ 16F ∷ 15F ∷ 17F ∷ 39F ∷ 41F ∷ 40F ∷ 36F ∷ 38F ∷ 37F ∷ 46F ∷ 45F
        ∷ 47F ∷ 43F ∷ 42F ∷ 44F ∷ 1F ∷ 2F ∷ 0F ∷ 6F ∷ 8F ∷ 7F ∷ 9F ∷ 11F ∷ 10F ∷ 3F ∷ 4F ∷ 5F ∷ 53F ∷ 51F ∷ 52F ∷ 58F
        ∷ 57F ∷ 59F ∷ 48F ∷ 50F ∷ 49F ∷ 55F ∷ 56F ∷ 54F ∷ 28F ∷ 27F ∷ 29F ∷ 31F ∷ 30F ∷ 32F ∷ 24F ∷ 25F ∷ 26F ∷ 34F ∷ 35F ∷ 33F
        ∷ [])
     ∷ (  19F ∷ 18F ∷ 20F ∷ 16F ∷ 15F ∷ 17F ∷ 13F ∷ 12F ∷ 14F ∷ 23F ∷ 22F ∷ 21F ∷ 40F ∷ 39F ∷ 41F ∷ 43F ∷ 42F ∷ 44F ∷ 36F ∷ 37F
        ∷ 38F ∷ 46F ∷ 47F ∷ 45F ∷ 28F ∷ 27F ∷ 29F ∷ 31F ∷ 30F ∷ 32F ∷ 24F ∷ 25F ∷ 26F ∷ 34F ∷ 35F ∷ 33F ∷ 1F ∷ 0F ∷ 2F ∷ 6F
        ∷ 7F ∷ 8F ∷ 3F ∷ 4F ∷ 5F ∷ 9F ∷ 11F ∷ 10F ∷ 53F ∷ 52F ∷ 51F ∷ 58F ∷ 59F ∷ 57F ∷ 55F ∷ 56F ∷ 54F ∷ 48F ∷ 50F ∷ 49F
        ∷ [])
     ∷ (  20F ∷ 19F ∷ 18F ∷ 23F ∷ 22F ∷ 21F ∷ 16F ∷ 17F ∷ 15F ∷ 13F ∷ 14F ∷ 12F ∷ 41F ∷ 40F ∷ 39F ∷ 46F ∷ 47F ∷ 45F ∷ 43F ∷ 44F
        ∷ 42F ∷ 36F ∷ 38F ∷ 37F ∷ 53F ∷ 52F ∷ 51F ∷ 58F ∷ 59F ∷ 57F ∷ 55F ∷ 56F ∷ 54F ∷ 48F ∷ 50F ∷ 49F ∷ 28F ∷ 29F ∷ 27F ∷ 31F
        ∷ 32F ∷ 30F ∷ 34F ∷ 35F ∷ 33F ∷ 24F ∷ 25F ∷ 26F ∷ 1F ∷ 2F ∷ 0F ∷ 6F ∷ 8F ∷ 7F ∷ 9F ∷ 11F ∷ 10F ∷ 3F ∷ 4F ∷ 5F
        ∷ [])
     ∷ (  21F ∷ 22F ∷ 23F ∷ 14F ∷ 12F ∷ 13F ∷ 17F ∷ 15F ∷ 16F ∷ 20F ∷ 18F ∷ 19F ∷ 51F ∷ 52F ∷ 53F ∷ 48F ∷ 49F ∷ 50F ∷ 55F ∷ 54F
        ∷ 56F ∷ 58F ∷ 57F ∷ 59F ∷ 2F ∷ 0F ∷ 1F ∷ 9F ∷ 10F ∷ 11F ∷ 3F ∷ 5F ∷ 4F ∷ 6F ∷ 8F ∷ 7F ∷ 29F ∷ 27F ∷ 28F ∷ 34F
        ∷ 33F ∷ 35F ∷ 24F ∷ 26F ∷ 25F ∷ 31F ∷ 32F ∷ 30F ∷ 41F ∷ 39F ∷ 40F ∷ 46F ∷ 45F ∷ 47F ∷ 36F ∷ 38F ∷ 37F ∷ 43F ∷ 44F ∷ 42F
        ∷ [])
     ∷ (  22F ∷ 23F ∷ 21F ∷ 17F ∷ 16F ∷ 15F ∷ 20F ∷ 19F ∷ 18F ∷ 14F ∷ 12F ∷ 13F ∷ 52F ∷ 53F ∷ 51F ∷ 55F ∷ 56F ∷ 54F ∷ 58F ∷ 59F
        ∷ 57F ∷ 48F ∷ 49F ∷ 50F ∷ 29F ∷ 28F ∷ 27F ∷ 34F ∷ 35F ∷ 33F ∷ 31F ∷ 32F ∷ 30F ∷ 24F ∷ 26F ∷ 25F ∷ 41F ∷ 40F ∷ 39F ∷ 46F
        ∷ 47F ∷ 45F ∷ 43F ∷ 44F ∷ 42F ∷ 36F ∷ 38F ∷ 37F ∷ 2F ∷ 0F ∷ 1F ∷ 9F ∷ 10F ∷ 11F ∷ 3F ∷ 5F ∷ 4F ∷ 6F ∷ 8F ∷ 7F
        ∷ [])
     ∷ (  23F ∷ 21F ∷ 22F ∷ 20F ∷ 18F ∷ 19F ∷ 14F ∷ 13F ∷ 12F ∷ 17F ∷ 16F ∷ 15F ∷ 53F ∷ 51F ∷ 52F ∷ 58F ∷ 57F ∷ 59F ∷ 48F ∷ 50F
        ∷ 49F ∷ 55F ∷ 56F ∷ 54F ∷ 41F ∷ 39F ∷ 40F ∷ 46F ∷ 45F ∷ 47F ∷ 36F ∷ 38F ∷ 37F ∷ 43F ∷ 44F ∷ 42F ∷ 2F ∷ 1F ∷ 0F ∷ 9F
        ∷ 11F ∷ 10F ∷ 6F ∷ 8F ∷ 7F ∷ 3F ∷ 5F ∷ 4F ∷ 29F ∷ 28F ∷ 27F ∷ 34F ∷ 35F ∷ 33F ∷ 31F ∷ 32F ∷ 30F ∷ 24F ∷ 26F ∷ 25F
        ∷ [])
     ∷ (  24F ∷ 25F ∷ 26F ∷ 27F ∷ 28F ∷ 29F ∷ 30F ∷ 31F ∷ 32F ∷ 33F ∷ 34F ∷ 35F ∷ 3F ∷ 4F ∷ 5F ∷ 0F ∷ 1F ∷ 2F ∷ 7F ∷ 6F
        ∷ 8F ∷ 10F ∷ 9F ∷ 11F ∷ 15F ∷ 16F ∷ 17F ∷ 12F ∷ 13F ∷ 14F ∷ 19F ∷ 18F ∷ 20F ∷ 22F ∷ 21F ∷ 23F ∷ 42F ∷ 43F ∷ 44F ∷ 37F
        ∷ 36F ∷ 38F ∷ 40F ∷ 39F ∷ 41F ∷ 47F ∷ 45F ∷ 46F ∷ 54F ∷ 55F ∷ 56F ∷ 49F ∷ 48F ∷ 50F ∷ 52F ∷ 51F ∷ 53F ∷ 59F ∷ 57F ∷ 58F
        ∷ [])
     ∷ (  25F ∷ 26F ∷ 24F ∷ 30F ∷ 32F ∷ 31F ∷ 33F ∷ 35F ∷ 34F ∷ 27F ∷ 28F ∷ 29F ∷ 4F ∷ 5F ∷ 3F ∷ 7F ∷ 8F ∷ 6F ∷ 10F ∷ 11F
        ∷ 9F ∷ 0F ∷ 1F ∷ 2F ∷ 42F ∷ 44F ∷ 43F ∷ 37F ∷ 38F ∷ 36F ∷ 47F ∷ 45F ∷ 46F ∷ 40F ∷ 39F ∷ 41F ∷ 54F ∷ 56F ∷ 55F ∷ 49F
        ∷ 50F ∷ 48F ∷ 59F ∷ 57F ∷ 58F ∷ 52F ∷ 51F ∷ 53F ∷ 15F ∷ 16F ∷ 17F ∷ 12F ∷ 13F ∷ 14F ∷ 19F ∷ 18F ∷ 20F ∷ 22F ∷ 21F ∷ 23F
        ∷ [])
     ∷ (  26F ∷ 24F ∷ 25F ∷ 33F ∷ 34F ∷ 35F ∷ 27F ∷ 29F ∷ 28F ∷ 30F ∷ 32F ∷ 31F ∷ 5F ∷ 3F ∷ 4F ∷ 10F ∷ 9F ∷ 11F ∷ 0F ∷ 2F
        ∷ 1F ∷ 7F ∷ 8F ∷ 6F ∷ 54F ∷ 55F ∷ 56F ∷ 49F ∷ 48F ∷ 50F ∷ 52F ∷ 51F ∷ 53F ∷ 59F ∷ 57F ∷ 58F ∷ 15F ∷ 17F ∷ 16F ∷ 12F
        ∷ 14F ∷ 13F ∷ 22F ∷ 21F ∷ 23F ∷ 19F ∷ 18F ∷ 20F ∷ 42F ∷ 44F ∷ 43F ∷ 37F ∷ 38F ∷ 36F ∷ 47F ∷ 45F ∷ 46F ∷ 40F ∷ 39F ∷ 41F
        ∷ [])
     ∷ (  27F ∷ 29F ∷ 28F ∷ 24F ∷ 26F ∷ 25F ∷ 34F ∷ 33F ∷ 35F ∷ 31F ∷ 30F ∷ 32F ∷ 15F ∷ 17F ∷ 16F ∷ 12F ∷ 14F ∷ 13F ∷ 22F ∷ 21F
        ∷ 23F ∷ 19F ∷ 18F ∷ 20F ∷ 3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ 10F ∷ 9F ∷ 11F ∷ 7F ∷ 6F ∷ 8F ∷ 55F ∷ 54F ∷ 56F ∷ 52F
        ∷ 51F ∷ 53F ∷ 49F ∷ 48F ∷ 50F ∷ 59F ∷ 58F ∷ 57F ∷ 43F ∷ 42F ∷ 44F ∷ 40F ∷ 39F ∷ 41F ∷ 37F ∷ 36F ∷ 38F ∷ 47F ∷ 46F ∷ 45F
        ∷ [])
     ∷ (  28F ∷ 27F ∷ 29F ∷ 31F ∷ 30F ∷ 32F ∷ 24F ∷ 25F ∷ 26F ∷ 34F ∷ 35F ∷ 33F ∷ 16F ∷ 15F ∷ 17F ∷ 19F ∷ 18F ∷ 20F ∷ 12F ∷ 13F
        ∷ 14F ∷ 22F ∷ 23F ∷ 21F ∷ 43F ∷ 42F ∷ 44F ∷ 40F ∷ 39F ∷ 41F ∷ 37F ∷ 36F ∷ 38F ∷ 47F ∷ 46F ∷ 45F ∷ 3F ∷ 4F ∷ 5F ∷ 0F
        ∷ 1F ∷ 2F ∷ 7F ∷ 6F ∷ 8F ∷ 10F ∷ 9F ∷ 11F ∷ 55F ∷ 56F ∷ 54F ∷ 52F ∷ 53F ∷ 51F ∷ 59F ∷ 58F ∷ 57F ∷ 49F ∷ 48F ∷ 50F
        ∷ [])
     ∷ (  29F ∷ 28F ∷ 27F ∷ 34F ∷ 35F ∷ 33F ∷ 31F ∷ 32F ∷ 30F ∷ 24F ∷ 26F ∷ 25F ∷ 17F ∷ 16F ∷ 15F ∷ 22F ∷ 23F ∷ 21F ∷ 19F ∷ 20F
        ∷ 18F ∷ 12F ∷ 14F ∷ 13F ∷ 55F ∷ 56F ∷ 54F ∷ 52F ∷ 53F ∷ 51F ∷ 59F ∷ 58F ∷ 57F ∷ 49F ∷ 48F ∷ 50F ∷ 43F ∷ 44F ∷ 42F ∷ 40F
        ∷ 41F ∷ 39F ∷ 47F ∷ 46F ∷ 45F ∷ 37F ∷ 36F ∷ 38F ∷ 3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ 10F ∷ 9F ∷ 11F ∷ 7F ∷ 6F ∷ 8F
        ∷ [])
     ∷ (  30F ∷ 31F ∷ 32F ∷ 25F ∷ 24F ∷ 26F ∷ 28F ∷ 27F ∷ 29F ∷ 35F ∷ 33F ∷ 34F ∷ 42F ∷ 43F ∷ 44F ∷ 37F ∷ 36F ∷ 38F ∷ 40F ∷ 39F
        ∷ 41F ∷ 47F ∷ 45F ∷ 46F ∷ 4F ∷ 3F ∷ 5F ∷ 7F ∷ 6F ∷ 8F ∷ 0F ∷ 1F ∷ 2F ∷ 10F ∷ 11F ∷ 9F ∷ 16F ∷ 15F ∷ 17F ∷ 19F
        ∷ 18F ∷ 20F ∷ 12F ∷ 13F ∷ 14F ∷ 22F ∷ 23F ∷ 21F ∷ 56F ∷ 54F ∷ 55F ∷ 59F ∷ 57F ∷ 58F ∷ 49F ∷ 50F ∷ 48F ∷ 52F ∷ 53F ∷ 51F
        ∷ [])
     ∷ (  31F ∷ 32F ∷ 30F ∷ 28F ∷ 29F ∷ 27F ∷ 35F ∷ 34F ∷ 33F ∷ 25F ∷ 24F ∷ 26F ∷ 43F ∷ 44F ∷ 42F ∷ 40F ∷ 41F ∷ 39F ∷ 47F ∷ 46F
        ∷ 45F ∷ 37F ∷ 36F ∷ 38F ∷ 16F ∷ 17F ∷ 15F ∷ 19F ∷ 20F ∷ 18F ∷ 22F ∷ 23F ∷ 21F ∷ 12F ∷ 13F ∷ 14F ∷ 56F ∷ 55F ∷ 54F ∷ 59F
        ∷ 58F ∷ 57F ∷ 52F ∷ 53F ∷ 51F ∷ 49F ∷ 50F ∷ 48F ∷ 4F ∷ 3F ∷ 5F ∷ 7F ∷ 6F ∷ 8F ∷ 0F ∷ 1F ∷ 2F ∷ 10F ∷ 11F ∷ 9F
        ∷ [])
     ∷ (  32F ∷ 30F ∷ 31F ∷ 35F ∷ 33F ∷ 34F ∷ 25F ∷ 26F ∷ 24F ∷ 28F ∷ 29F ∷ 27F ∷ 44F ∷ 42F ∷ 43F ∷ 47F ∷ 45F ∷ 46F ∷ 37F ∷ 38F
        ∷ 36F ∷ 40F ∷ 41F ∷ 39F ∷ 56F ∷ 54F ∷ 55F ∷ 59F ∷ 57F ∷ 58F ∷ 49F ∷ 50F ∷ 48F ∷ 52F ∷ 53F ∷ 51F ∷ 4F ∷ 5F ∷ 3F ∷ 7F
        ∷ 8F ∷ 6F ∷ 10F ∷ 11F ∷ 9F ∷ 0F ∷ 1F ∷ 2F ∷ 16F ∷ 17F ∷ 15F ∷ 19F ∷ 20F ∷ 18F ∷ 22F ∷ 23F ∷ 21F ∷ 12F ∷ 13F ∷ 14F
        ∷ [])
     ∷ (  33F ∷ 35F ∷ 34F ∷ 26F ∷ 25F ∷ 24F ∷ 32F ∷ 30F ∷ 31F ∷ 29F ∷ 27F ∷ 28F ∷ 54F ∷ 56F ∷ 55F ∷ 49F ∷ 50F ∷ 48F ∷ 59F ∷ 57F
        ∷ 58F ∷ 52F ∷ 51F ∷ 53F ∷ 5F ∷ 4F ∷ 3F ∷ 10F ∷ 11F ∷ 9F ∷ 7F ∷ 8F ∷ 6F ∷ 0F ∷ 2F ∷ 1F ∷ 44F ∷ 42F ∷ 43F ∷ 47F
        ∷ 45F ∷ 46F ∷ 37F ∷ 38F ∷ 36F ∷ 40F ∷ 41F ∷ 39F ∷ 17F ∷ 15F ∷ 16F ∷ 22F ∷ 21F ∷ 23F ∷ 12F ∷ 14F ∷ 13F ∷ 19F ∷ 20F ∷ 18F
        ∷ [])
     ∷ (  34F ∷ 33F ∷ 35F ∷ 29F ∷ 27F ∷ 28F ∷ 26F ∷ 24F ∷ 25F ∷ 32F ∷ 31F ∷ 30F ∷ 55F ∷ 54F ∷ 56F ∷ 52F ∷ 51F ∷ 53F ∷ 49F ∷ 48F
        ∷ 50F ∷ 59F ∷ 58F ∷ 57F ∷ 17F ∷ 15F ∷ 16F ∷ 22F ∷ 21F ∷ 23F ∷ 12F ∷ 14F ∷ 13F ∷ 19F ∷ 20F ∷ 18F ∷ 5F ∷ 3F ∷ 4F ∷ 10F
        ∷ 9F ∷ 11F ∷ 0F ∷ 2F ∷ 1F ∷ 7F ∷ 8F ∷ 6F ∷ 44F ∷ 43F ∷ 42F ∷ 47F ∷ 46F ∷ 45F ∷ 40F ∷ 41F ∷ 39F ∷ 37F ∷ 38F ∷ 36F
        ∷ [])
     ∷ (  35F ∷ 34F ∷ 33F ∷ 32F ∷ 31F ∷ 30F ∷ 29F ∷ 28F ∷ 27F ∷ 26F ∷ 25F ∷ 24F ∷ 56F ∷ 55F ∷ 54F ∷ 59F ∷ 58F ∷ 57F ∷ 52F ∷ 53F
        ∷ 51F ∷ 49F ∷ 50F ∷ 48F ∷ 44F ∷ 43F ∷ 42F ∷ 47F ∷ 46F ∷ 45F ∷ 40F ∷ 41F ∷ 39F ∷ 37F ∷ 38F ∷ 36F ∷ 17F ∷ 16F ∷ 15F ∷ 22F
        ∷ 23F ∷ 21F ∷ 19F ∷ 20F ∷ 18F ∷ 12F ∷ 14F ∷ 13F ∷ 5F ∷ 4F ∷ 3F ∷ 10F ∷ 11F ∷ 9F ∷ 7F ∷ 8F ∷ 6F ∷ 0F ∷ 2F ∷ 1F
        ∷ [])
     ∷ (  36F ∷ 38F ∷ 37F ∷ 39F ∷ 41F ∷ 40F ∷ 45F ∷ 46F ∷ 47F ∷ 42F ∷ 43F ∷ 44F ∷ 6F ∷ 8F ∷ 7F ∷ 1F ∷ 2F ∷ 0F ∷ 11F ∷ 9F
        ∷ 10F ∷ 4F ∷ 3F ∷ 5F ∷ 18F ∷ 20F ∷ 19F ∷ 13F ∷ 14F ∷ 12F ∷ 23F ∷ 21F ∷ 22F ∷ 16F ∷ 15F ∷ 17F ∷ 57F ∷ 58F ∷ 59F ∷ 50F
        ∷ 48F ∷ 49F ∷ 53F ∷ 51F ∷ 52F ∷ 56F ∷ 54F ∷ 55F ∷ 30F ∷ 31F ∷ 32F ∷ 25F ∷ 24F ∷ 26F ∷ 28F ∷ 27F ∷ 29F ∷ 35F ∷ 33F ∷ 34F
        ∷ [])
     ∷ (  37F ∷ 36F ∷ 38F ∷ 42F ∷ 43F ∷ 44F ∷ 39F ∷ 40F ∷ 41F ∷ 45F ∷ 47F ∷ 46F ∷ 7F ∷ 6F ∷ 8F ∷ 4F ∷ 3F ∷ 5F ∷ 1F ∷ 0F
        ∷ 2F ∷ 11F ∷ 10F ∷ 9F ∷ 30F ∷ 31F ∷ 32F ∷ 25F ∷ 24F ∷ 26F ∷ 28F ∷ 27F ∷ 29F ∷ 35F ∷ 33F ∷ 34F ∷ 18F ∷ 19F ∷ 20F ∷ 13F
        ∷ 12F ∷ 14F ∷ 16F ∷ 15F ∷ 17F ∷ 23F ∷ 21F ∷ 22F ∷ 57F ∷ 59F ∷ 58F ∷ 50F ∷ 49F ∷ 48F ∷ 56F ∷ 54F ∷ 55F ∷ 53F ∷ 51F ∷ 52F
        ∷ [])
     ∷ (  38F ∷ 37F ∷ 36F ∷ 45F ∷ 47F ∷ 46F ∷ 42F ∷ 44F ∷ 43F ∷ 39F ∷ 41F ∷ 40F ∷ 8F ∷ 7F ∷ 6F ∷ 11F ∷ 10F ∷ 9F ∷ 4F ∷ 5F
        ∷ 3F ∷ 1F ∷ 2F ∷ 0F ∷ 57F ∷ 59F ∷ 58F ∷ 50F ∷ 49F ∷ 48F ∷ 56F ∷ 54F ∷ 55F ∷ 53F ∷ 51F ∷ 52F ∷ 30F ∷ 32F ∷ 31F ∷ 25F
        ∷ 26F ∷ 24F ∷ 35F ∷ 33F ∷ 34F ∷ 28F ∷ 27F ∷ 29F ∷ 18F ∷ 20F ∷ 19F ∷ 13F ∷ 14F ∷ 12F ∷ 23F ∷ 21F ∷ 22F ∷ 16F ∷ 15F ∷ 17F
        ∷ [])
     ∷ (  39F ∷ 40F ∷ 41F ∷ 36F ∷ 37F ∷ 38F ∷ 43F ∷ 42F ∷ 44F ∷ 46F ∷ 45F ∷ 47F ∷ 18F ∷ 19F ∷ 20F ∷ 13F ∷ 12F ∷ 14F ∷ 16F ∷ 15F
        ∷ 17F ∷ 23F ∷ 21F ∷ 22F ∷ 6F ∷ 7F ∷ 8F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ 5F ∷ 11F ∷ 9F ∷ 10F ∷ 31F ∷ 30F ∷ 32F ∷ 28F
        ∷ 27F ∷ 29F ∷ 25F ∷ 24F ∷ 26F ∷ 35F ∷ 34F ∷ 33F ∷ 58F ∷ 57F ∷ 59F ∷ 53F ∷ 51F ∷ 52F ∷ 50F ∷ 48F ∷ 49F ∷ 56F ∷ 55F ∷ 54F
        ∷ [])
     ∷ (  40F ∷ 41F ∷ 39F ∷ 43F ∷ 44F ∷ 42F ∷ 46F ∷ 47F ∷ 45F ∷ 36F ∷ 37F ∷ 38F ∷ 19F ∷ 20F ∷ 18F ∷ 16F ∷ 17F ∷ 15F ∷ 23F ∷ 22F
        ∷ 21F ∷ 13F ∷ 12F ∷ 14F ∷ 31F ∷ 32F ∷ 30F ∷ 28F ∷ 29F ∷ 27F ∷ 35F ∷ 34F ∷ 33F ∷ 25F ∷ 24F ∷ 26F ∷ 58F ∷ 59F ∷ 57F ∷ 53F
        ∷ 52F ∷ 51F ∷ 56F ∷ 55F ∷ 54F ∷ 50F ∷ 48F ∷ 49F ∷ 6F ∷ 7F ∷ 8F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ 5F ∷ 11F ∷ 9F ∷ 10F
        ∷ [])
     ∷ (  41F ∷ 39F ∷ 40F ∷ 46F ∷ 45F ∷ 47F ∷ 36F ∷ 38F ∷ 37F ∷ 43F ∷ 44F ∷ 42F ∷ 20F ∷ 18F ∷ 19F ∷ 23F ∷ 21F ∷ 22F ∷ 13F ∷ 14F
        ∷ 12F ∷ 16F ∷ 17F ∷ 15F ∷ 58F ∷ 57F ∷ 59F ∷ 53F ∷ 51F ∷ 52F ∷ 50F ∷ 48F ∷ 49F ∷ 56F ∷ 55F ∷ 54F ∷ 6F ∷ 8F ∷ 7F ∷ 1F
        ∷ 2F ∷ 0F ∷ 11F ∷ 9F ∷ 10F ∷ 4F ∷ 3F ∷ 5F ∷ 31F ∷ 32F ∷ 30F ∷ 28F ∷ 29F ∷ 27F ∷ 35F ∷ 34F ∷ 33F ∷ 25F ∷ 24F ∷ 26F
        ∷ [])
     ∷ (  42F ∷ 44F ∷ 43F ∷ 37F ∷ 38F ∷ 36F ∷ 47F ∷ 45F ∷ 46F ∷ 40F ∷ 39F ∷ 41F ∷ 30F ∷ 32F ∷ 31F ∷ 25F ∷ 26F ∷ 24F ∷ 35F ∷ 33F
        ∷ 34F ∷ 28F ∷ 27F ∷ 29F ∷ 7F ∷ 8F ∷ 6F ∷ 4F ∷ 5F ∷ 3F ∷ 11F ∷ 10F ∷ 9F ∷ 1F ∷ 0F ∷ 2F ∷ 59F ∷ 57F ∷ 58F ∷ 56F
        ∷ 54F ∷ 55F ∷ 50F ∷ 49F ∷ 48F ∷ 53F ∷ 52F ∷ 51F ∷ 19F ∷ 18F ∷ 20F ∷ 16F ∷ 15F ∷ 17F ∷ 13F ∷ 12F ∷ 14F ∷ 23F ∷ 22F ∷ 21F
        ∷ [])
     ∷ (  43F ∷ 42F ∷ 44F ∷ 40F ∷ 39F ∷ 41F ∷ 37F ∷ 36F ∷ 38F ∷ 47F ∷ 46F ∷ 45F ∷ 31F ∷ 30F ∷ 32F ∷ 28F ∷ 27F ∷ 29F ∷ 25F ∷ 24F
        ∷ 26F ∷ 35F ∷ 34F ∷ 33F ∷ 19F ∷ 18F ∷ 20F ∷ 16F ∷ 15F ∷ 17F ∷ 13F ∷ 12F ∷ 14F ∷ 23F ∷ 22F ∷ 21F ∷ 7F ∷ 6F ∷ 8F ∷ 4F
        ∷ 3F ∷ 5F ∷ 1F ∷ 0F ∷ 2F ∷ 11F ∷ 10F ∷ 9F ∷ 59F ∷ 58F ∷ 57F ∷ 56F ∷ 55F ∷ 54F ∷ 53F ∷ 52F ∷ 51F ∷ 50F ∷ 49F ∷ 48F
        ∷ [])
     ∷ (  44F ∷ 43F ∷ 42F ∷ 47F ∷ 46F ∷ 45F ∷ 40F ∷ 41F ∷ 39F ∷ 37F ∷ 38F ∷ 36F ∷ 32F ∷ 31F ∷ 30F ∷ 35F ∷ 34F ∷ 33F ∷ 28F ∷ 29F
        ∷ 27F ∷ 25F ∷ 26F ∷ 24F ∷ 59F ∷ 58F ∷ 57F ∷ 56F ∷ 55F ∷ 54F ∷ 53F ∷ 52F ∷ 51F ∷ 50F ∷ 49F ∷ 48F ∷ 19F ∷ 20F ∷ 18F ∷ 16F
        ∷ 17F ∷ 15F ∷ 23F ∷ 22F ∷ 21F ∷ 13F ∷ 12F ∷ 14F ∷ 7F ∷ 8F ∷ 6F ∷ 4F ∷ 5F ∷ 3F ∷ 11F ∷ 10F ∷ 9F ∷ 1F ∷ 0F ∷ 2F
        ∷ [])
     ∷ (  45F ∷ 46F ∷ 47F ∷ 38F ∷ 36F ∷ 37F ∷ 41F ∷ 39F ∷ 40F ∷ 44F ∷ 42F ∷ 43F ∷ 57F ∷ 58F ∷ 59F ∷ 50F ∷ 48F ∷ 49F ∷ 53F ∷ 51F
        ∷ 52F ∷ 56F ∷ 54F ∷ 55F ∷ 8F ∷ 6F ∷ 7F ∷ 11F ∷ 9F ∷ 10F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F ∷ 20F ∷ 18F ∷ 19F ∷ 23F
        ∷ 21F ∷ 22F ∷ 13F ∷ 14F ∷ 12F ∷ 16F ∷ 17F ∷ 15F ∷ 32F ∷ 30F ∷ 31F ∷ 35F ∷ 33F ∷ 34F ∷ 25F ∷ 26F ∷ 24F ∷ 28F ∷ 29F ∷ 27F
        ∷ [])
     ∷ (  46F ∷ 47F ∷ 45F ∷ 41F ∷ 40F ∷ 39F ∷ 44F ∷ 43F ∷ 42F ∷ 38F ∷ 36F ∷ 37F ∷ 58F ∷ 59F ∷ 57F ∷ 53F ∷ 52F ∷ 51F ∷ 56F ∷ 55F
        ∷ 54F ∷ 50F ∷ 48F ∷ 49F ∷ 20F ∷ 19F ∷ 18F ∷ 23F ∷ 22F ∷ 21F ∷ 16F ∷ 17F ∷ 15F ∷ 13F ∷ 14F ∷ 12F ∷ 32F ∷ 31F ∷ 30F ∷ 35F
        ∷ 34F ∷ 33F ∷ 28F ∷ 29F ∷ 27F ∷ 25F ∷ 26F ∷ 24F ∷ 8F ∷ 6F ∷ 7F ∷ 11F ∷ 9F ∷ 10F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F
        ∷ [])
     ∷ (  47F ∷ 45F ∷ 46F ∷ 44F ∷ 42F ∷ 43F ∷ 38F ∷ 37F ∷ 36F ∷ 41F ∷ 40F ∷ 39F ∷ 59F ∷ 57F ∷ 58F ∷ 56F ∷ 54F ∷ 55F ∷ 50F ∷ 49F
        ∷ 48F ∷ 53F ∷ 52F ∷ 51F ∷ 32F ∷ 30F ∷ 31F ∷ 35F ∷ 33F ∷ 34F ∷ 25F ∷ 26F ∷ 24F ∷ 28F ∷ 29F ∷ 27F ∷ 8F ∷ 7F ∷ 6F ∷ 11F
        ∷ 10F ∷ 9F ∷ 4F ∷ 5F ∷ 3F ∷ 1F ∷ 2F ∷ 0F ∷ 20F ∷ 19F ∷ 18F ∷ 23F ∷ 22F ∷ 21F ∷ 16F ∷ 17F ∷ 15F ∷ 13F ∷ 14F ∷ 12F
        ∷ [])
     ∷ (  48F ∷ 49F ∷ 50F ∷ 51F ∷ 52F ∷ 53F ∷ 54F ∷ 55F ∷ 56F ∷ 57F ∷ 58F ∷ 59F ∷ 9F ∷ 10F ∷ 11F ∷ 2F ∷ 0F ∷ 1F ∷ 5F ∷ 3F
        ∷ 4F ∷ 8F ∷ 6F ∷ 7F ∷ 21F ∷ 22F ∷ 23F ∷ 14F ∷ 12F ∷ 13F ∷ 17F ∷ 15F ∷ 16F ∷ 20F ∷ 18F ∷ 19F ∷ 33F ∷ 34F ∷ 35F ∷ 26F
        ∷ 24F ∷ 25F ∷ 29F ∷ 27F ∷ 28F ∷ 32F ∷ 30F ∷ 31F ∷ 45F ∷ 46F ∷ 47F ∷ 38F ∷ 36F ∷ 37F ∷ 41F ∷ 39F ∷ 40F ∷ 44F ∷ 42F ∷ 43F
        ∷ [])
     ∷ (  49F ∷ 50F ∷ 48F ∷ 54F ∷ 56F ∷ 55F ∷ 57F ∷ 59F ∷ 58F ∷ 51F ∷ 52F ∷ 53F ∷ 10F ∷ 11F ∷ 9F ∷ 5F ∷ 4F ∷ 3F ∷ 8F ∷ 7F
        ∷ 6F ∷ 2F ∷ 0F ∷ 1F ∷ 33F ∷ 35F ∷ 34F ∷ 26F ∷ 25F ∷ 24F ∷ 32F ∷ 30F ∷ 31F ∷ 29F ∷ 27F ∷ 28F ∷ 45F ∷ 47F ∷ 46F ∷ 38F
        ∷ 37F ∷ 36F ∷ 44F ∷ 42F ∷ 43F ∷ 41F ∷ 39F ∷ 40F ∷ 21F ∷ 22F ∷ 23F ∷ 14F ∷ 12F ∷ 13F ∷ 17F ∷ 15F ∷ 16F ∷ 20F ∷ 18F ∷ 19F
        ∷ [])
     ∷ (  50F ∷ 48F ∷ 49F ∷ 57F ∷ 58F ∷ 59F ∷ 51F ∷ 53F ∷ 52F ∷ 54F ∷ 56F ∷ 55F ∷ 11F ∷ 9F ∷ 10F ∷ 8F ∷ 6F ∷ 7F ∷ 2F ∷ 1F
        ∷ 0F ∷ 5F ∷ 4F ∷ 3F ∷ 45F ∷ 46F ∷ 47F ∷ 38F ∷ 36F ∷ 37F ∷ 41F ∷ 39F ∷ 40F ∷ 44F ∷ 42F ∷ 43F ∷ 21F ∷ 23F ∷ 22F ∷ 14F
        ∷ 13F ∷ 12F ∷ 20F ∷ 18F ∷ 19F ∷ 17F ∷ 15F ∷ 16F ∷ 33F ∷ 35F ∷ 34F ∷ 26F ∷ 25F ∷ 24F ∷ 32F ∷ 30F ∷ 31F ∷ 29F ∷ 27F ∷ 28F
        ∷ [])
     ∷ (  51F ∷ 53F ∷ 52F ∷ 48F ∷ 50F ∷ 49F ∷ 58F ∷ 57F ∷ 59F ∷ 55F ∷ 54F ∷ 56F ∷ 21F ∷ 23F ∷ 22F ∷ 14F ∷ 13F ∷ 12F ∷ 20F ∷ 18F
        ∷ 19F ∷ 17F ∷ 15F ∷ 16F ∷ 9F ∷ 11F ∷ 10F ∷ 2F ∷ 1F ∷ 0F ∷ 8F ∷ 6F ∷ 7F ∷ 5F ∷ 3F ∷ 4F ∷ 46F ∷ 45F ∷ 47F ∷ 41F
        ∷ 39F ∷ 40F ∷ 38F ∷ 36F ∷ 37F ∷ 44F ∷ 43F ∷ 42F ∷ 34F ∷ 33F ∷ 35F ∷ 29F ∷ 27F ∷ 28F ∷ 26F ∷ 24F ∷ 25F ∷ 32F ∷ 31F ∷ 30F
        ∷ [])
     ∷ (  52F ∷ 51F ∷ 53F ∷ 55F ∷ 54F ∷ 56F ∷ 48F ∷ 49F ∷ 50F ∷ 58F ∷ 59F ∷ 57F ∷ 22F ∷ 21F ∷ 23F ∷ 17F ∷ 15F ∷ 16F ∷ 14F ∷ 12F
        ∷ 13F ∷ 20F ∷ 19F ∷ 18F ∷ 34F ∷ 33F ∷ 35F ∷ 29F ∷ 27F ∷ 28F ∷ 26F ∷ 24F ∷ 25F ∷ 32F ∷ 31F ∷ 30F ∷ 9F ∷ 10F ∷ 11F ∷ 2F
        ∷ 0F ∷ 1F ∷ 5F ∷ 3F ∷ 4F ∷ 8F ∷ 6F ∷ 7F ∷ 46F ∷ 47F ∷ 45F ∷ 41F ∷ 40F ∷ 39F ∷ 44F ∷ 43F ∷ 42F ∷ 38F ∷ 36F ∷ 37F
        ∷ [])
     ∷ (  53F ∷ 52F ∷ 51F ∷ 58F ∷ 59F ∷ 57F ∷ 55F ∷ 56F ∷ 54F ∷ 48F ∷ 50F ∷ 49F ∷ 23F ∷ 22F ∷ 21F ∷ 20F ∷ 19F ∷ 18F ∷ 17F ∷ 16F
        ∷ 15F ∷ 14F ∷ 13F ∷ 12F ∷ 46F ∷ 47F ∷ 45F ∷ 41F ∷ 40F ∷ 39F ∷ 44F ∷ 43F ∷ 42F ∷ 38F ∷ 36F ∷ 37F ∷ 34F ∷ 35F ∷ 33F ∷ 29F
        ∷ 28F ∷ 27F ∷ 32F ∷ 31F ∷ 30F ∷ 26F ∷ 24F ∷ 25F ∷ 9F ∷ 11F ∷ 10F ∷ 2F ∷ 1F ∷ 0F ∷ 8F ∷ 6F ∷ 7F ∷ 5F ∷ 3F ∷ 4F
        ∷ [])
     ∷ (  54F ∷ 55F ∷ 56F ∷ 49F ∷ 48F ∷ 50F ∷ 52F ∷ 51F ∷ 53F ∷ 59F ∷ 57F ∷ 58F ∷ 33F ∷ 34F ∷ 35F ∷ 26F ∷ 24F ∷ 25F ∷ 29F ∷ 27F
        ∷ 28F ∷ 32F ∷ 30F ∷ 31F ∷ 10F ∷ 9F ∷ 11F ∷ 5F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ 8F ∷ 7F ∷ 6F ∷ 22F ∷ 21F ∷ 23F ∷ 17F
        ∷ 15F ∷ 16F ∷ 14F ∷ 12F ∷ 13F ∷ 20F ∷ 19F ∷ 18F ∷ 47F ∷ 45F ∷ 46F ∷ 44F ∷ 42F ∷ 43F ∷ 38F ∷ 37F ∷ 36F ∷ 41F ∷ 40F ∷ 39F
        ∷ [])
     ∷ (  55F ∷ 56F ∷ 54F ∷ 52F ∷ 53F ∷ 51F ∷ 59F ∷ 58F ∷ 57F ∷ 49F ∷ 48F ∷ 50F ∷ 34F ∷ 35F ∷ 33F ∷ 29F ∷ 28F ∷ 27F ∷ 32F ∷ 31F
        ∷ 30F ∷ 26F ∷ 24F ∷ 25F ∷ 22F ∷ 23F ∷ 21F ∷ 17F ∷ 16F ∷ 15F ∷ 20F ∷ 19F ∷ 18F ∷ 14F ∷ 12F ∷ 13F ∷ 47F ∷ 46F ∷ 45F ∷ 44F
        ∷ 43F ∷ 42F ∷ 41F ∷ 40F ∷ 39F ∷ 38F ∷ 37F ∷ 36F ∷ 10F ∷ 9F ∷ 11F ∷ 5F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ 8F ∷ 7F ∷ 6F
        ∷ [])
     ∷ (  56F ∷ 54F ∷ 55F ∷ 59F ∷ 57F ∷ 58F ∷ 49F ∷ 50F ∷ 48F ∷ 52F ∷ 53F ∷ 51F ∷ 35F ∷ 33F ∷ 34F ∷ 32F ∷ 30F ∷ 31F ∷ 26F ∷ 25F
        ∷ 24F ∷ 29F ∷ 28F ∷ 27F ∷ 47F ∷ 45F ∷ 46F ∷ 44F ∷ 42F ∷ 43F ∷ 38F ∷ 37F ∷ 36F ∷ 41F ∷ 40F ∷ 39F ∷ 10F ∷ 11F ∷ 9F ∷ 5F
        ∷ 4F ∷ 3F ∷ 8F ∷ 7F ∷ 6F ∷ 2F ∷ 0F ∷ 1F ∷ 22F ∷ 23F ∷ 21F ∷ 17F ∷ 16F ∷ 15F ∷ 20F ∷ 19F ∷ 18F ∷ 14F ∷ 12F ∷ 13F
        ∷ [])
     ∷ (  57F ∷ 59F ∷ 58F ∷ 50F ∷ 49F ∷ 48F ∷ 56F ∷ 54F ∷ 55F ∷ 53F ∷ 51F ∷ 52F ∷ 45F ∷ 47F ∷ 46F ∷ 38F ∷ 37F ∷ 36F ∷ 44F ∷ 42F
        ∷ 43F ∷ 41F ∷ 39F ∷ 40F ∷ 11F ∷ 10F ∷ 9F ∷ 8F ∷ 7F ∷ 6F ∷ 5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ 35F ∷ 33F ∷ 34F ∷ 32F
        ∷ 30F ∷ 31F ∷ 26F ∷ 25F ∷ 24F ∷ 29F ∷ 28F ∷ 27F ∷ 23F ∷ 21F ∷ 22F ∷ 20F ∷ 18F ∷ 19F ∷ 14F ∷ 13F ∷ 12F ∷ 17F ∷ 16F ∷ 15F
        ∷ [])
     ∷ (  58F ∷ 57F ∷ 59F ∷ 53F ∷ 51F ∷ 52F ∷ 50F ∷ 48F ∷ 49F ∷ 56F ∷ 55F ∷ 54F ∷ 46F ∷ 45F ∷ 47F ∷ 41F ∷ 39F ∷ 40F ∷ 38F ∷ 36F
        ∷ 37F ∷ 44F ∷ 43F ∷ 42F ∷ 23F ∷ 21F ∷ 22F ∷ 20F ∷ 18F ∷ 19F ∷ 14F ∷ 13F ∷ 12F ∷ 17F ∷ 16F ∷ 15F ∷ 11F ∷ 9F ∷ 10F ∷ 8F
        ∷ 6F ∷ 7F ∷ 2F ∷ 1F ∷ 0F ∷ 5F ∷ 4F ∷ 3F ∷ 35F ∷ 34F ∷ 33F ∷ 32F ∷ 31F ∷ 30F ∷ 29F ∷ 28F ∷ 27F ∷ 26F ∷ 25F ∷ 24F
        ∷ [])
     ∷ (  59F ∷ 58F ∷ 57F ∷ 56F ∷ 55F ∷ 54F ∷ 53F ∷ 52F ∷ 51F ∷ 50F ∷ 49F ∷ 48F ∷ 47F ∷ 46F ∷ 45F ∷ 44F ∷ 43F ∷ 42F ∷ 41F ∷ 40F
        ∷ 39F ∷ 38F ∷ 37F ∷ 36F ∷ 35F ∷ 34F ∷ 33F ∷ 32F ∷ 31F ∷ 30F ∷ 29F ∷ 28F ∷ 27F ∷ 26F ∷ 25F ∷ 24F ∷ 23F ∷ 22F ∷ 21F ∷ 20F
        ∷ 19F ∷ 18F ∷ 17F ∷ 16F ∷ 15F ∷ 14F ∷ 13F ∷ 12F ∷ 11F ∷ 10F ∷ 9F ∷ 8F ∷ 7F ∷ 6F ∷ 5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F
        ∷ [])
     ∷ [])

invVec : Vec (Fin 60) 60
invVec =
  (  0F ∷ 2F ∷ 1F ∷ 3F ∷ 6F ∷ 9F ∷ 4F ∷ 10F ∷ 8F ∷ 5F ∷ 7F ∷ 11F ∷ 12F ∷ 13F ∷ 14F ∷ 24F ∷ 48F ∷ 36F ∷ 26F ∷ 37F
        ∷ 50F ∷ 25F ∷ 49F ∷ 38F ∷ 15F ∷ 21F ∷ 18F ∷ 27F ∷ 39F ∷ 51F ∷ 30F ∷ 54F ∷ 45F ∷ 33F ∷ 42F ∷ 57F ∷ 17F ∷ 19F ∷ 23F ∷ 28F
        ∷ 52F ∷ 41F ∷ 34F ∷ 43F ∷ 58F ∷ 32F ∷ 56F ∷ 47F ∷ 16F ∷ 22F ∷ 20F ∷ 29F ∷ 40F ∷ 53F ∷ 31F ∷ 55F ∷ 46F ∷ 35F ∷ 44F ∷ 59F
        ∷ [])
```

#### The seven subgroups, as characteristic vectors

```agda
chi1 : Vec Bool 60
chi1 =
  (  true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ [])

chiC3 : Vec Bool 60
chiC3 =
  (  true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ [])

chiC5 : Vec Bool 60
chiC5 =
  (  true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ [])

chiS3 : Vec Bool 60
chiS3 =
  (  true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ [])

chiA4 : Vec Bool 60
chiA4 =
  (  true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true
        ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ true
        ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ [])

chiA4' : Vec Bool 60
chiA4' =
  (  true ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ true ∷ true ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false
        ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false
        ∷ [])

chiA5 : Vec Bool 60
chiA5 =
  (  true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true
        ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true
        ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true
        ∷ [])
```

#### The filter family [C3 , A5]: C3 , S3 , A4 , A4' , A5

```agda
filterGens : Vec (List (Fin 60)) 5
filterGens =
  (    (15F ∷ [])
     ∷ (15F ∷ 12F ∷ [])
     ∷ (15F ∷ 13F ∷ [])
     ∷ (15F ∷ 14F ∷ [])
     ∷ (15F ∷ 16F ∷ [])
     ∷ [])

filterRank : Vec ℕ 5
filterRank =
  (    0
     ∷ 1
     ∷ 1
     ∷ 1
     ∷ 2
     ∷ [])

filterStepNext : Vec (Vec (Fin 5) 60) 5
filterStepNext =
  (    (  0F ∷ 4F ∷ 4F ∷ 1F ∷ 2F ∷ 3F ∷ 2F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 1F ∷ 2F ∷ 3F ∷ 0F ∷ 4F ∷ 4F ∷ 4F ∷ 2F
        ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 0F ∷ 4F ∷ 4F ∷ 1F ∷ 2F ∷ 3F ∷ 2F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 2F
        ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ [])
     ∷ (  1F ∷ 4F ∷ 4F ∷ 1F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 1F ∷ 4F ∷ 4F ∷ 1F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 1F ∷ 4F ∷ 4F ∷ 1F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ [])
     ∷ (  2F ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 2F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 2F ∷ 4F ∷ 4F ∷ 4F ∷ 2F
        ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 2F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 2F
        ∷ 4F ∷ 4F ∷ 4F ∷ 2F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ [])
     ∷ (  3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 3F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ [])
     ∷ (  4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F ∷ 4F
        ∷ [])
     ∷ [])

filterStepWords : Vec (Vec (List (List (Fin 60))) 60) 5
filterStepWords =
  (    (  [] ∷ ((15F ∷ []) ∷ (15F ∷ 1F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 2F ∷ 2F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 3F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 4F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 5F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (6F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 7F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (8F ∷ 15F ∷ 8F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (9F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 10F ∷ 10F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (11F ∷ 15F ∷ 15F ∷ 11F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (13F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (14F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (16F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (17F ∷ 15F ∷ 15F ∷ 17F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 18F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (19F ∷ 15F ∷ 15F ∷ 19F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 20F ∷ 20F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (21F ∷ 21F ∷ 15F ∷ 21F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (22F ∷ 15F ∷ 15F ∷ 22F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (23F ∷ 23F ∷ 23F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 25F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 26F ∷ 15F ∷ 26F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (27F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (28F ∷ 28F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (29F ∷ 29F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 30F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (31F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (32F ∷ 32F ∷ 32F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 33F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (34F ∷ 15F ∷ 34F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 35F ∷ 35F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 36F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (37F ∷ 15F ∷ 37F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (38F ∷ 38F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (39F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (40F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (41F ∷ 15F ∷ 41F ∷ 15F ∷ 41F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 42F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 43F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 44F ∷ 44F ∷ 44F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (45F ∷ 45F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 46F ∷ 46F ∷ 46F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 47F ∷ 15F ∷ 47F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (48F ∷ 48F ∷ 48F ∷ 48F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (49F ∷ 15F ∷ 49F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (50F ∷ 15F ∷ 15F ∷ 50F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (51F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (52F ∷ 52F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 53F ∷ 15F ∷ 53F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (54F ∷ 15F ∷ 54F ∷ 54F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 55F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 56F ∷ 56F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (57F ∷ 15F ∷ 57F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 58F ∷ 58F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 59F ∷ 15F ∷ 15F ∷ 59F ∷ []) ∷ [])
        ∷ [])
     ∷ (  [] ∷ ((15F ∷ []) ∷ (15F ∷ 1F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 2F ∷ 2F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 4F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 5F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 6F ∷ 12F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (7F ∷ 12F ∷ 7F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (8F ∷ 15F ∷ 8F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 9F ∷ 9F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 10F ∷ 12F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (11F ∷ 15F ∷ 15F ∷ 11F ∷ 15F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 13F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 12F ∷ 14F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (16F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (17F ∷ 15F ∷ 15F ∷ 17F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (18F ∷ 12F ∷ 18F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (19F ∷ 12F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (20F ∷ 15F ∷ 20F ∷ 20F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (21F ∷ 21F ∷ 15F ∷ 21F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 22F ∷ 22F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (23F ∷ 23F ∷ 23F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 25F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 26F ∷ 12F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (28F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 15F ∷ 29F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (30F ∷ 15F ∷ 30F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (31F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (32F ∷ 32F ∷ 32F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 33F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (34F ∷ 34F ∷ 15F ∷ 12F ∷ 34F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 35F ∷ 35F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 36F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (37F ∷ 37F ∷ 12F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (38F ∷ 38F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (39F ∷ 39F ∷ 12F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (40F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (41F ∷ 15F ∷ 41F ∷ 15F ∷ 41F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (42F ∷ 12F ∷ 15F ∷ 42F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (43F ∷ 15F ∷ 12F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (44F ∷ 44F ∷ 15F ∷ 44F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (45F ∷ 45F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 46F ∷ 46F ∷ 12F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 47F ∷ 15F ∷ 47F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (48F ∷ 48F ∷ 48F ∷ 48F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 49F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (50F ∷ 15F ∷ 15F ∷ 50F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 12F ∷ 51F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (52F ∷ 52F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (53F ∷ 12F ∷ 53F ∷ 15F ∷ 15F ∷ 53F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (54F ∷ 15F ∷ 54F ∷ 54F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (12F ∷ 15F ∷ 55F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (56F ∷ 56F ∷ 12F ∷ 56F ∷ 56F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (57F ∷ 15F ∷ 57F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 58F ∷ 58F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 59F ∷ 15F ∷ 15F ∷ 59F ∷ []) ∷ [])
        ∷ [])
     ∷ (  [] ∷ ((15F ∷ []) ∷ (15F ∷ 1F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 2F ∷ 2F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 13F ∷ 15F ∷ 3F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 5F ∷ 13F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (13F ∷ 7F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (8F ∷ 15F ∷ 8F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (9F ∷ 9F ∷ 15F ∷ 9F ∷ 13F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (13F ∷ 10F ∷ 10F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (11F ∷ 15F ∷ 15F ∷ 11F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 13F ∷ 12F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 14F ∷ 13F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (16F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (17F ∷ 15F ∷ 15F ∷ 17F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 18F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (20F ∷ 13F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (21F ∷ 21F ∷ 15F ∷ 21F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (22F ∷ 15F ∷ 15F ∷ 13F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (23F ∷ 13F ∷ 23F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 25F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (26F ∷ 15F ∷ 15F ∷ 13F ∷ 26F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 13F ∷ 27F ∷ 15F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (29F ∷ 13F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (31F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (32F ∷ 32F ∷ 32F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (33F ∷ 15F ∷ 33F ∷ 13F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (34F ∷ 34F ∷ 13F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (35F ∷ 13F ∷ 15F ∷ 13F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 36F ∷ 15F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (13F ∷ 38F ∷ 13F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (40F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (41F ∷ 15F ∷ 41F ∷ 15F ∷ 41F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 42F ∷ 15F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (44F ∷ 13F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (45F ∷ 45F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (46F ∷ 15F ∷ 15F ∷ 13F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 47F ∷ 15F ∷ 47F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (48F ∷ 48F ∷ 48F ∷ 48F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (49F ∷ 15F ∷ 13F ∷ 49F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 50F ∷ 15F ∷ 13F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (51F ∷ 51F ∷ 13F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (52F ∷ 52F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (53F ∷ 15F ∷ 13F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (54F ∷ 15F ∷ 54F ∷ 54F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (55F ∷ 15F ∷ 13F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (56F ∷ 13F ∷ 15F ∷ 56F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (57F ∷ 15F ∷ 57F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (58F ∷ 13F ∷ 58F ∷ 13F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (59F ∷ 15F ∷ 13F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ [])
     ∷ (  [] ∷ ((15F ∷ []) ∷ (15F ∷ 1F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 2F ∷ 2F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (3F ∷ 15F ∷ 14F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 14F ∷ 15F ∷ 4F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (6F ∷ 15F ∷ 14F ∷ 6F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 7F ∷ 14F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (8F ∷ 15F ∷ 8F ∷ 15F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 10F ∷ 10F ∷ 14F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (14F ∷ 11F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 12F ∷ 14F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 14F ∷ 13F ∷ []) ∷ []) ∷ [] ∷ []
        ∷ ((15F ∷ []) ∷ (16F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (17F ∷ 15F ∷ 15F ∷ 17F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (18F ∷ 14F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 19F ∷ 14F ∷ 15F ∷ 19F ∷ 19F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (20F ∷ 20F ∷ 14F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (21F ∷ 21F ∷ 15F ∷ 21F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (14F ∷ 15F ∷ 15F ∷ 23F ∷ []) ∷ [])
        ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 25F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (26F ∷ 26F ∷ 14F ∷ 26F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (27F ∷ 14F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 14F ∷ 28F ∷ 28F ∷ 15F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (30F ∷ 14F ∷ 15F ∷ 30F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (31F ∷ 15F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (32F ∷ 32F ∷ 32F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (34F ∷ 14F ∷ 34F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (14F ∷ 15F ∷ 35F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (15F ∷ 36F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 14F ∷ 37F ∷ 15F ∷ 37F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (14F ∷ 38F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 14F ∷ 39F ∷ 15F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (40F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (41F ∷ 15F ∷ 41F ∷ 15F ∷ 41F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (42F ∷ 14F ∷ 15F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (14F ∷ 43F ∷ 14F ∷ 43F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (14F ∷ 15F ∷ 44F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (45F ∷ 45F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (46F ∷ 46F ∷ 46F ∷ 14F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 47F ∷ 15F ∷ 47F ∷ []) ∷ [])
        ∷ ((15F ∷ []) ∷ (14F ∷ 48F ∷ 14F ∷ []) ∷ []) ∷ [] ∷ ((15F ∷ []) ∷ (15F ∷ 50F ∷ 14F ∷ 50F ∷ 15F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (52F ∷ 52F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 14F ∷ 53F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (54F ∷ 15F ∷ 54F ∷ 54F ∷ []) ∷ []) ∷ []
        ∷ ((15F ∷ []) ∷ (56F ∷ 56F ∷ 14F ∷ 15F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (57F ∷ 15F ∷ 57F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (15F ∷ 15F ∷ 58F ∷ 58F ∷ []) ∷ []) ∷ ((15F ∷ []) ∷ (59F ∷ 14F ∷ 59F ∷ 14F ∷ []) ∷ [])
        ∷ [])
     ∷ (  [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ [])

filterExpWords : Vec (Vec (List (Fin 60)) 60) 5
filterExpWords =
  (    (  [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ (15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ (15F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ (  [] ∷ [] ∷ [] ∷ (12F ∷ 15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ (12F ∷ []) ∷ [] ∷ [] ∷ (15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ (15F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ (15F ∷ 12F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ (  [] ∷ [] ∷ [] ∷ [] ∷ (15F ∷ 15F ∷ 13F ∷ []) ∷ []
        ∷ (13F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ (13F ∷ []) ∷ [] ∷ (15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ (15F ∷ 13F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ []
        ∷ (15F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ (15F ∷ 13F ∷ []) ∷ []
        ∷ (15F ∷ 15F ∷ 13F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ (13F ∷ 15F ∷ 13F ∷ []) ∷ [] ∷ (13F ∷ 15F ∷ 15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ (15F ∷ 13F ∷ 15F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ (  [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ (15F ∷ 15F ∷ 14F ∷ [])
        ∷ [] ∷ [] ∷ [] ∷ (14F ∷ 15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ (14F ∷ []) ∷ (15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ (15F ∷ 14F ∷ 15F ∷ []) ∷ []
        ∷ (15F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ [] ∷ (15F ∷ 14F ∷ [])
        ∷ [] ∷ [] ∷ [] ∷ (15F ∷ 15F ∷ 14F ∷ 15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ (14F ∷ 15F ∷ 14F ∷ []) ∷ [] ∷ (14F ∷ 15F ∷ 15F ∷ []) ∷ [] ∷ []
        ∷ [] ∷ (15F ∷ 14F ∷ 15F ∷ 15F ∷ []) ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ (  [] ∷ (15F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ [])
        ∷ (16F ∷ 16F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ []) ∷ (15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 15F ∷ [])
        ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ []) ∷ (15F ∷ []) ∷ (16F ∷ []) ∷ (16F ∷ 15F ∷ 15F ∷ 16F ∷ [])
        ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ []) ∷ (15F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ [])
        ∷ (15F ∷ 15F ∷ []) ∷ (15F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ [])
        ∷ (16F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ []) ∷ (16F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 15F ∷ [])
        ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 15F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ [])
        ∷ (15F ∷ 16F ∷ 15F ∷ 15F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 16F ∷ 15F ∷ [])
        ∷ (16F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 16F ∷ 16F ∷ 15F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (15F ∷ 16F ∷ 16F ∷ 16F ∷ 15F ∷ [])
        ∷ (16F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (15F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ (16F ∷ 16F ∷ 15F ∷ 15F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ 16F ∷ []) ∷ (16F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ []) ∷ (15F ∷ 16F ∷ 15F ∷ 16F ∷ 15F ∷ 15F ∷ [])
        ∷ [])
     ∷ [])
```

#### The ideal family [1 , C5]: 1 , C5

```agda
idealGens : Vec (List (Fin 60)) 2
idealGens =
  (    []
     ∷ (16F ∷ [])
     ∷ [])

idealRank : Vec ℕ 2
idealRank =
  (    0
     ∷ 1
     ∷ [])

idealStepNext : Vec (Vec (Fin 2) 60) 2
idealStepNext =
  (    (  0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 1F ∷ 0F ∷ 0F ∷ 0F
        ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 1F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F
        ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 1F ∷ 0F ∷ 0F ∷ 1F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F
        ∷ [])
     ∷ (  1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F
        ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F
        ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ 1F
        ∷ [])
     ∷ [])

idealStepWords : Vec (Vec (List (List (Fin 60))) 60) 2
idealStepWords =
  (    (  [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ ((16F ∷ []) ∷ []) ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ ((32F ∷ 32F ∷ 32F ∷ []) ∷ []) ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ ((45F ∷ 45F ∷ []) ∷ []) ∷ [] ∷ []
        ∷ ((48F ∷ 48F ∷ 48F ∷ 48F ∷ []) ∷ []) ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ (  [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ [])

idealExpWords : Vec (Vec (List (Fin 60)) 60) 2
idealExpWords =
  (    (  [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ (  [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ (16F ∷ []) ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ (16F ∷ 16F ∷ []) ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ (16F ∷ 16F ∷ 16F ∷ []) ∷ [] ∷ []
        ∷ (16F ∷ 16F ∷ 16F ∷ 16F ∷ []) ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ []
        ∷ [])
     ∷ [])
```

--------------------------------------
