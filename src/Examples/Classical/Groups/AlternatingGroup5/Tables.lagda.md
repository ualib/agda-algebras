---
layout: default
file: "src/Examples/Classical/Groups/AlternatingGroup5/Tables.lagda.md"
title: "Examples.Classical.Groups.AlternatingGroup5.Tables module"
date: "2026-08-30"
author: "the agda-algebras development team"
---

### Generated tables for the alternating group `A₅`

This is the [Examples.Classical.Groups.AlternatingGroup5.Tables][] module of the [Agda Universal Algebra Library][].

**Generated file: do not edit by hand.**  Regenerate with

    python3 scripts/python/flrp/a5_simple_cert.py

The module carries the raw data for the certified `A₅` of
[Examples.Classical.Groups.AlternatingGroup5][]: the Cayley table, inverse
vector, and point action of the 60 even permutations of five points in
lexicographic order (index 0 is the identity), the indices of the generators
`s = (0 1 2 3 4)` and `t = (0 1 2)`, and the simplicity certificate in the
closure-term language of [Classical.Structures.Group.NormalClosure][]: for the
`i`-th non-identity element `x`, `a5-seed-words-s`{.AgdaFunction} and
`a5-seed-words-t`{.AgdaFunction} express the generators as products of
conjugates of `x` and of its inverse, and `a5-gen-words`{.AgdaFunction}
expresses every element as a word in the generators.  Every claim in this data
is replayed by decision procedures in the consuming module; nothing rests on
the generator's authority.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups.AlternatingGroup5.Tables where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin.Base      using ( Fin ; suc )
open import Data.Fin.Patterns  using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F ; 7F ; 8F ; 9F )
open import Data.Vec.Base      using ( Vec ; _∷_ ; [] )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                           using ( Table )
open import Classical.Structures.Group.NormalClosure  using ( ClosureTerm ; one
                                                            ; seed ; inv ; mul ; cnj )

-- Data.Fin.Patterns stops at 9F; the larger literals this module needs are
-- pattern synonyms in the same style.
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
-->

#### The Cayley table, inverse vector, and point action

```agda
-- The A₅ multiplication table on the lexicographic even-permutation encoding.
a5-mul-table : Table 60
a5-mul-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ 7F ∷ 8F ∷ 9F ∷ 10F ∷ 11F ∷ 12F ∷ 13F ∷ 14F ∷ 15F ∷ 16F ∷ 17F ∷ 18F ∷ 19F ∷ 20F ∷ 21F ∷ 22F ∷ 23F ∷ 24F ∷ 25F ∷ 26F ∷ 27F ∷ 28F ∷ 29F ∷ 30F ∷ 31F ∷ 32F ∷ 33F ∷ 34F ∷ 35F ∷ 36F ∷ 37F ∷ 38F ∷ 39F ∷ 40F ∷ 41F ∷ 42F ∷ 43F ∷ 44F ∷ 45F ∷ 46F ∷ 47F ∷ 48F ∷ 49F ∷ 50F ∷ 51F ∷ 52F ∷ 53F ∷ 54F ∷ 55F ∷ 56F ∷ 57F ∷ 58F ∷ 59F ∷ [])
             ∷ (1F ∷ 2F ∷ 0F ∷ 6F ∷ 8F ∷ 7F ∷ 9F ∷ 11F ∷ 10F ∷ 3F ∷ 4F ∷ 5F ∷ 13F ∷ 14F ∷ 12F ∷ 18F ∷ 20F ∷ 19F ∷ 21F ∷ 23F ∷ 22F ∷ 15F ∷ 16F ∷ 17F ∷ 36F ∷ 38F ∷ 37F ∷ 39F ∷ 41F ∷ 40F ∷ 45F ∷ 46F ∷ 47F ∷ 42F ∷ 43F ∷ 44F ∷ 48F ∷ 50F ∷ 49F ∷ 51F ∷ 53F ∷ 52F ∷ 57F ∷ 58F ∷ 59F ∷ 54F ∷ 55F ∷ 56F ∷ 24F ∷ 25F ∷ 26F ∷ 27F ∷ 28F ∷ 29F ∷ 30F ∷ 31F ∷ 32F ∷ 33F ∷ 34F ∷ 35F ∷ [])
             ∷ (2F ∷ 0F ∷ 1F ∷ 9F ∷ 10F ∷ 11F ∷ 3F ∷ 5F ∷ 4F ∷ 6F ∷ 8F ∷ 7F ∷ 14F ∷ 12F ∷ 13F ∷ 21F ∷ 22F ∷ 23F ∷ 15F ∷ 17F ∷ 16F ∷ 18F ∷ 20F ∷ 19F ∷ 48F ∷ 49F ∷ 50F ∷ 51F ∷ 52F ∷ 53F ∷ 54F ∷ 55F ∷ 56F ∷ 57F ∷ 58F ∷ 59F ∷ 24F ∷ 26F ∷ 25F ∷ 27F ∷ 29F ∷ 28F ∷ 33F ∷ 34F ∷ 35F ∷ 30F ∷ 31F ∷ 32F ∷ 36F ∷ 38F ∷ 37F ∷ 39F ∷ 41F ∷ 40F ∷ 45F ∷ 46F ∷ 47F ∷ 42F ∷ 43F ∷ 44F ∷ [])
             ∷ (3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ 10F ∷ 9F ∷ 11F ∷ 7F ∷ 6F ∷ 8F ∷ 24F ∷ 26F ∷ 25F ∷ 27F ∷ 29F ∷ 28F ∷ 33F ∷ 34F ∷ 35F ∷ 30F ∷ 31F ∷ 32F ∷ 12F ∷ 14F ∷ 13F ∷ 15F ∷ 17F ∷ 16F ∷ 21F ∷ 22F ∷ 23F ∷ 18F ∷ 19F ∷ 20F ∷ 49F ∷ 48F ∷ 50F ∷ 54F ∷ 55F ∷ 56F ∷ 51F ∷ 52F ∷ 53F ∷ 57F ∷ 59F ∷ 58F ∷ 37F ∷ 36F ∷ 38F ∷ 42F ∷ 43F ∷ 44F ∷ 39F ∷ 40F ∷ 41F ∷ 45F ∷ 47F ∷ 46F ∷ [])
             ∷ (4F ∷ 3F ∷ 5F ∷ 7F ∷ 6F ∷ 8F ∷ 0F ∷ 1F ∷ 2F ∷ 10F ∷ 11F ∷ 9F ∷ 25F ∷ 24F ∷ 26F ∷ 30F ∷ 31F ∷ 32F ∷ 27F ∷ 28F ∷ 29F ∷ 33F ∷ 35F ∷ 34F ∷ 37F ∷ 36F ∷ 38F ∷ 42F ∷ 43F ∷ 44F ∷ 39F ∷ 40F ∷ 41F ∷ 45F ∷ 47F ∷ 46F ∷ 12F ∷ 13F ∷ 14F ∷ 15F ∷ 16F ∷ 17F ∷ 18F ∷ 19F ∷ 20F ∷ 21F ∷ 22F ∷ 23F ∷ 49F ∷ 50F ∷ 48F ∷ 54F ∷ 56F ∷ 55F ∷ 57F ∷ 59F ∷ 58F ∷ 51F ∷ 52F ∷ 53F ∷ [])
             ∷ (5F ∷ 4F ∷ 3F ∷ 10F ∷ 11F ∷ 9F ∷ 7F ∷ 8F ∷ 6F ∷ 0F ∷ 2F ∷ 1F ∷ 26F ∷ 25F ∷ 24F ∷ 33F ∷ 35F ∷ 34F ∷ 30F ∷ 32F ∷ 31F ∷ 27F ∷ 29F ∷ 28F ∷ 49F ∷ 50F ∷ 48F ∷ 54F ∷ 56F ∷ 55F ∷ 57F ∷ 59F ∷ 58F ∷ 51F ∷ 52F ∷ 53F ∷ 37F ∷ 38F ∷ 36F ∷ 42F ∷ 44F ∷ 43F ∷ 45F ∷ 47F ∷ 46F ∷ 39F ∷ 40F ∷ 41F ∷ 12F ∷ 14F ∷ 13F ∷ 15F ∷ 17F ∷ 16F ∷ 21F ∷ 22F ∷ 23F ∷ 18F ∷ 19F ∷ 20F ∷ [])
             ∷ (6F ∷ 7F ∷ 8F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ 5F ∷ 11F ∷ 9F ∷ 10F ∷ 36F ∷ 37F ∷ 38F ∷ 39F ∷ 40F ∷ 41F ∷ 42F ∷ 43F ∷ 44F ∷ 45F ∷ 46F ∷ 47F ∷ 13F ∷ 12F ∷ 14F ∷ 18F ∷ 19F ∷ 20F ∷ 15F ∷ 16F ∷ 17F ∷ 21F ∷ 23F ∷ 22F ∷ 25F ∷ 24F ∷ 26F ∷ 30F ∷ 31F ∷ 32F ∷ 27F ∷ 28F ∷ 29F ∷ 33F ∷ 35F ∷ 34F ∷ 50F ∷ 48F ∷ 49F ∷ 57F ∷ 58F ∷ 59F ∷ 51F ∷ 53F ∷ 52F ∷ 54F ∷ 56F ∷ 55F ∷ [])
             ∷ (7F ∷ 8F ∷ 6F ∷ 4F ∷ 5F ∷ 3F ∷ 11F ∷ 10F ∷ 9F ∷ 1F ∷ 0F ∷ 2F ∷ 37F ∷ 38F ∷ 36F ∷ 42F ∷ 44F ∷ 43F ∷ 45F ∷ 47F ∷ 46F ∷ 39F ∷ 40F ∷ 41F ∷ 25F ∷ 26F ∷ 24F ∷ 30F ∷ 32F ∷ 31F ∷ 33F ∷ 35F ∷ 34F ∷ 27F ∷ 28F ∷ 29F ∷ 50F ∷ 49F ∷ 48F ∷ 57F ∷ 59F ∷ 58F ∷ 54F ∷ 56F ∷ 55F ∷ 51F ∷ 53F ∷ 52F ∷ 13F ∷ 12F ∷ 14F ∷ 18F ∷ 19F ∷ 20F ∷ 15F ∷ 16F ∷ 17F ∷ 21F ∷ 23F ∷ 22F ∷ [])
             ∷ (8F ∷ 6F ∷ 7F ∷ 11F ∷ 9F ∷ 10F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F ∷ 38F ∷ 36F ∷ 37F ∷ 45F ∷ 46F ∷ 47F ∷ 39F ∷ 41F ∷ 40F ∷ 42F ∷ 44F ∷ 43F ∷ 50F ∷ 48F ∷ 49F ∷ 57F ∷ 58F ∷ 59F ∷ 51F ∷ 53F ∷ 52F ∷ 54F ∷ 56F ∷ 55F ∷ 13F ∷ 14F ∷ 12F ∷ 18F ∷ 20F ∷ 19F ∷ 21F ∷ 23F ∷ 22F ∷ 15F ∷ 16F ∷ 17F ∷ 25F ∷ 26F ∷ 24F ∷ 30F ∷ 32F ∷ 31F ∷ 33F ∷ 35F ∷ 34F ∷ 27F ∷ 28F ∷ 29F ∷ [])
             ∷ (9F ∷ 11F ∷ 10F ∷ 2F ∷ 1F ∷ 0F ∷ 8F ∷ 6F ∷ 7F ∷ 5F ∷ 3F ∷ 4F ∷ 48F ∷ 50F ∷ 49F ∷ 51F ∷ 53F ∷ 52F ∷ 57F ∷ 58F ∷ 59F ∷ 54F ∷ 55F ∷ 56F ∷ 14F ∷ 13F ∷ 12F ∷ 21F ∷ 23F ∷ 22F ∷ 18F ∷ 20F ∷ 19F ∷ 15F ∷ 17F ∷ 16F ∷ 38F ∷ 36F ∷ 37F ∷ 45F ∷ 46F ∷ 47F ∷ 39F ∷ 41F ∷ 40F ∷ 42F ∷ 44F ∷ 43F ∷ 26F ∷ 24F ∷ 25F ∷ 33F ∷ 34F ∷ 35F ∷ 27F ∷ 29F ∷ 28F ∷ 30F ∷ 32F ∷ 31F ∷ [])
             ∷ (10F ∷ 9F ∷ 11F ∷ 5F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ 8F ∷ 7F ∷ 6F ∷ 49F ∷ 48F ∷ 50F ∷ 54F ∷ 55F ∷ 56F ∷ 51F ∷ 52F ∷ 53F ∷ 57F ∷ 59F ∷ 58F ∷ 26F ∷ 24F ∷ 25F ∷ 33F ∷ 34F ∷ 35F ∷ 27F ∷ 29F ∷ 28F ∷ 30F ∷ 32F ∷ 31F ∷ 14F ∷ 12F ∷ 13F ∷ 21F ∷ 22F ∷ 23F ∷ 15F ∷ 17F ∷ 16F ∷ 18F ∷ 20F ∷ 19F ∷ 38F ∷ 37F ∷ 36F ∷ 45F ∷ 47F ∷ 46F ∷ 42F ∷ 44F ∷ 43F ∷ 39F ∷ 41F ∷ 40F ∷ [])
             ∷ (11F ∷ 10F ∷ 9F ∷ 8F ∷ 7F ∷ 6F ∷ 5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ 50F ∷ 49F ∷ 48F ∷ 57F ∷ 59F ∷ 58F ∷ 54F ∷ 56F ∷ 55F ∷ 51F ∷ 53F ∷ 52F ∷ 38F ∷ 37F ∷ 36F ∷ 45F ∷ 47F ∷ 46F ∷ 42F ∷ 44F ∷ 43F ∷ 39F ∷ 41F ∷ 40F ∷ 26F ∷ 25F ∷ 24F ∷ 33F ∷ 35F ∷ 34F ∷ 30F ∷ 32F ∷ 31F ∷ 27F ∷ 29F ∷ 28F ∷ 14F ∷ 13F ∷ 12F ∷ 21F ∷ 23F ∷ 22F ∷ 18F ∷ 20F ∷ 19F ∷ 15F ∷ 17F ∷ 16F ∷ [])
             ∷ (12F ∷ 14F ∷ 13F ∷ 15F ∷ 17F ∷ 16F ∷ 21F ∷ 22F ∷ 23F ∷ 18F ∷ 19F ∷ 20F ∷ 0F ∷ 2F ∷ 1F ∷ 3F ∷ 5F ∷ 4F ∷ 9F ∷ 10F ∷ 11F ∷ 6F ∷ 7F ∷ 8F ∷ 27F ∷ 29F ∷ 28F ∷ 24F ∷ 26F ∷ 25F ∷ 34F ∷ 33F ∷ 35F ∷ 31F ∷ 30F ∷ 32F ∷ 51F ∷ 52F ∷ 53F ∷ 48F ∷ 49F ∷ 50F ∷ 55F ∷ 54F ∷ 56F ∷ 58F ∷ 57F ∷ 59F ∷ 39F ∷ 40F ∷ 41F ∷ 36F ∷ 37F ∷ 38F ∷ 43F ∷ 42F ∷ 44F ∷ 46F ∷ 45F ∷ 47F ∷ [])
             ∷ (13F ∷ 12F ∷ 14F ∷ 18F ∷ 19F ∷ 20F ∷ 15F ∷ 16F ∷ 17F ∷ 21F ∷ 23F ∷ 22F ∷ 1F ∷ 0F ∷ 2F ∷ 6F ∷ 7F ∷ 8F ∷ 3F ∷ 4F ∷ 5F ∷ 9F ∷ 11F ∷ 10F ∷ 39F ∷ 40F ∷ 41F ∷ 36F ∷ 37F ∷ 38F ∷ 43F ∷ 42F ∷ 44F ∷ 46F ∷ 45F ∷ 47F ∷ 27F ∷ 28F ∷ 29F ∷ 24F ∷ 25F ∷ 26F ∷ 31F ∷ 30F ∷ 32F ∷ 34F ∷ 33F ∷ 35F ∷ 51F ∷ 53F ∷ 52F ∷ 48F ∷ 50F ∷ 49F ∷ 58F ∷ 57F ∷ 59F ∷ 55F ∷ 54F ∷ 56F ∷ [])
             ∷ (14F ∷ 13F ∷ 12F ∷ 21F ∷ 23F ∷ 22F ∷ 18F ∷ 20F ∷ 19F ∷ 15F ∷ 17F ∷ 16F ∷ 2F ∷ 1F ∷ 0F ∷ 9F ∷ 11F ∷ 10F ∷ 6F ∷ 8F ∷ 7F ∷ 3F ∷ 5F ∷ 4F ∷ 51F ∷ 53F ∷ 52F ∷ 48F ∷ 50F ∷ 49F ∷ 58F ∷ 57F ∷ 59F ∷ 55F ∷ 54F ∷ 56F ∷ 39F ∷ 41F ∷ 40F ∷ 36F ∷ 38F ∷ 37F ∷ 46F ∷ 45F ∷ 47F ∷ 43F ∷ 42F ∷ 44F ∷ 27F ∷ 29F ∷ 28F ∷ 24F ∷ 26F ∷ 25F ∷ 34F ∷ 33F ∷ 35F ∷ 31F ∷ 30F ∷ 32F ∷ [])
             ∷ (15F ∷ 16F ∷ 17F ∷ 12F ∷ 13F ∷ 14F ∷ 19F ∷ 18F ∷ 20F ∷ 22F ∷ 21F ∷ 23F ∷ 27F ∷ 28F ∷ 29F ∷ 24F ∷ 25F ∷ 26F ∷ 31F ∷ 30F ∷ 32F ∷ 34F ∷ 33F ∷ 35F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ 7F ∷ 8F ∷ 9F ∷ 10F ∷ 11F ∷ 40F ∷ 39F ∷ 41F ∷ 43F ∷ 42F ∷ 44F ∷ 36F ∷ 37F ∷ 38F ∷ 46F ∷ 47F ∷ 45F ∷ 52F ∷ 51F ∷ 53F ∷ 55F ∷ 54F ∷ 56F ∷ 48F ∷ 49F ∷ 50F ∷ 58F ∷ 59F ∷ 57F ∷ [])
             ∷ (16F ∷ 17F ∷ 15F ∷ 19F ∷ 20F ∷ 18F ∷ 22F ∷ 23F ∷ 21F ∷ 12F ∷ 13F ∷ 14F ∷ 28F ∷ 29F ∷ 27F ∷ 31F ∷ 32F ∷ 30F ∷ 34F ∷ 35F ∷ 33F ∷ 24F ∷ 25F ∷ 26F ∷ 40F ∷ 41F ∷ 39F ∷ 43F ∷ 44F ∷ 42F ∷ 46F ∷ 47F ∷ 45F ∷ 36F ∷ 37F ∷ 38F ∷ 52F ∷ 53F ∷ 51F ∷ 55F ∷ 56F ∷ 54F ∷ 58F ∷ 59F ∷ 57F ∷ 48F ∷ 49F ∷ 50F ∷ 0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ 7F ∷ 8F ∷ 9F ∷ 10F ∷ 11F ∷ [])
             ∷ (17F ∷ 15F ∷ 16F ∷ 22F ∷ 21F ∷ 23F ∷ 12F ∷ 14F ∷ 13F ∷ 19F ∷ 20F ∷ 18F ∷ 29F ∷ 27F ∷ 28F ∷ 34F ∷ 33F ∷ 35F ∷ 24F ∷ 26F ∷ 25F ∷ 31F ∷ 32F ∷ 30F ∷ 52F ∷ 51F ∷ 53F ∷ 55F ∷ 54F ∷ 56F ∷ 48F ∷ 49F ∷ 50F ∷ 58F ∷ 59F ∷ 57F ∷ 0F ∷ 2F ∷ 1F ∷ 3F ∷ 5F ∷ 4F ∷ 9F ∷ 10F ∷ 11F ∷ 6F ∷ 7F ∷ 8F ∷ 40F ∷ 41F ∷ 39F ∷ 43F ∷ 44F ∷ 42F ∷ 46F ∷ 47F ∷ 45F ∷ 36F ∷ 37F ∷ 38F ∷ [])
             ∷ (18F ∷ 20F ∷ 19F ∷ 13F ∷ 14F ∷ 12F ∷ 23F ∷ 21F ∷ 22F ∷ 16F ∷ 15F ∷ 17F ∷ 39F ∷ 41F ∷ 40F ∷ 36F ∷ 38F ∷ 37F ∷ 46F ∷ 45F ∷ 47F ∷ 43F ∷ 42F ∷ 44F ∷ 1F ∷ 2F ∷ 0F ∷ 6F ∷ 8F ∷ 7F ∷ 9F ∷ 11F ∷ 10F ∷ 3F ∷ 4F ∷ 5F ∷ 53F ∷ 51F ∷ 52F ∷ 58F ∷ 57F ∷ 59F ∷ 48F ∷ 50F ∷ 49F ∷ 55F ∷ 56F ∷ 54F ∷ 28F ∷ 27F ∷ 29F ∷ 31F ∷ 30F ∷ 32F ∷ 24F ∷ 25F ∷ 26F ∷ 34F ∷ 35F ∷ 33F ∷ [])
             ∷ (19F ∷ 18F ∷ 20F ∷ 16F ∷ 15F ∷ 17F ∷ 13F ∷ 12F ∷ 14F ∷ 23F ∷ 22F ∷ 21F ∷ 40F ∷ 39F ∷ 41F ∷ 43F ∷ 42F ∷ 44F ∷ 36F ∷ 37F ∷ 38F ∷ 46F ∷ 47F ∷ 45F ∷ 28F ∷ 27F ∷ 29F ∷ 31F ∷ 30F ∷ 32F ∷ 24F ∷ 25F ∷ 26F ∷ 34F ∷ 35F ∷ 33F ∷ 1F ∷ 0F ∷ 2F ∷ 6F ∷ 7F ∷ 8F ∷ 3F ∷ 4F ∷ 5F ∷ 9F ∷ 11F ∷ 10F ∷ 53F ∷ 52F ∷ 51F ∷ 58F ∷ 59F ∷ 57F ∷ 55F ∷ 56F ∷ 54F ∷ 48F ∷ 50F ∷ 49F ∷ [])
             ∷ (20F ∷ 19F ∷ 18F ∷ 23F ∷ 22F ∷ 21F ∷ 16F ∷ 17F ∷ 15F ∷ 13F ∷ 14F ∷ 12F ∷ 41F ∷ 40F ∷ 39F ∷ 46F ∷ 47F ∷ 45F ∷ 43F ∷ 44F ∷ 42F ∷ 36F ∷ 38F ∷ 37F ∷ 53F ∷ 52F ∷ 51F ∷ 58F ∷ 59F ∷ 57F ∷ 55F ∷ 56F ∷ 54F ∷ 48F ∷ 50F ∷ 49F ∷ 28F ∷ 29F ∷ 27F ∷ 31F ∷ 32F ∷ 30F ∷ 34F ∷ 35F ∷ 33F ∷ 24F ∷ 25F ∷ 26F ∷ 1F ∷ 2F ∷ 0F ∷ 6F ∷ 8F ∷ 7F ∷ 9F ∷ 11F ∷ 10F ∷ 3F ∷ 4F ∷ 5F ∷ [])
             ∷ (21F ∷ 22F ∷ 23F ∷ 14F ∷ 12F ∷ 13F ∷ 17F ∷ 15F ∷ 16F ∷ 20F ∷ 18F ∷ 19F ∷ 51F ∷ 52F ∷ 53F ∷ 48F ∷ 49F ∷ 50F ∷ 55F ∷ 54F ∷ 56F ∷ 58F ∷ 57F ∷ 59F ∷ 2F ∷ 0F ∷ 1F ∷ 9F ∷ 10F ∷ 11F ∷ 3F ∷ 5F ∷ 4F ∷ 6F ∷ 8F ∷ 7F ∷ 29F ∷ 27F ∷ 28F ∷ 34F ∷ 33F ∷ 35F ∷ 24F ∷ 26F ∷ 25F ∷ 31F ∷ 32F ∷ 30F ∷ 41F ∷ 39F ∷ 40F ∷ 46F ∷ 45F ∷ 47F ∷ 36F ∷ 38F ∷ 37F ∷ 43F ∷ 44F ∷ 42F ∷ [])
             ∷ (22F ∷ 23F ∷ 21F ∷ 17F ∷ 16F ∷ 15F ∷ 20F ∷ 19F ∷ 18F ∷ 14F ∷ 12F ∷ 13F ∷ 52F ∷ 53F ∷ 51F ∷ 55F ∷ 56F ∷ 54F ∷ 58F ∷ 59F ∷ 57F ∷ 48F ∷ 49F ∷ 50F ∷ 29F ∷ 28F ∷ 27F ∷ 34F ∷ 35F ∷ 33F ∷ 31F ∷ 32F ∷ 30F ∷ 24F ∷ 26F ∷ 25F ∷ 41F ∷ 40F ∷ 39F ∷ 46F ∷ 47F ∷ 45F ∷ 43F ∷ 44F ∷ 42F ∷ 36F ∷ 38F ∷ 37F ∷ 2F ∷ 0F ∷ 1F ∷ 9F ∷ 10F ∷ 11F ∷ 3F ∷ 5F ∷ 4F ∷ 6F ∷ 8F ∷ 7F ∷ [])
             ∷ (23F ∷ 21F ∷ 22F ∷ 20F ∷ 18F ∷ 19F ∷ 14F ∷ 13F ∷ 12F ∷ 17F ∷ 16F ∷ 15F ∷ 53F ∷ 51F ∷ 52F ∷ 58F ∷ 57F ∷ 59F ∷ 48F ∷ 50F ∷ 49F ∷ 55F ∷ 56F ∷ 54F ∷ 41F ∷ 39F ∷ 40F ∷ 46F ∷ 45F ∷ 47F ∷ 36F ∷ 38F ∷ 37F ∷ 43F ∷ 44F ∷ 42F ∷ 2F ∷ 1F ∷ 0F ∷ 9F ∷ 11F ∷ 10F ∷ 6F ∷ 8F ∷ 7F ∷ 3F ∷ 5F ∷ 4F ∷ 29F ∷ 28F ∷ 27F ∷ 34F ∷ 35F ∷ 33F ∷ 31F ∷ 32F ∷ 30F ∷ 24F ∷ 26F ∷ 25F ∷ [])
             ∷ (24F ∷ 25F ∷ 26F ∷ 27F ∷ 28F ∷ 29F ∷ 30F ∷ 31F ∷ 32F ∷ 33F ∷ 34F ∷ 35F ∷ 3F ∷ 4F ∷ 5F ∷ 0F ∷ 1F ∷ 2F ∷ 7F ∷ 6F ∷ 8F ∷ 10F ∷ 9F ∷ 11F ∷ 15F ∷ 16F ∷ 17F ∷ 12F ∷ 13F ∷ 14F ∷ 19F ∷ 18F ∷ 20F ∷ 22F ∷ 21F ∷ 23F ∷ 42F ∷ 43F ∷ 44F ∷ 37F ∷ 36F ∷ 38F ∷ 40F ∷ 39F ∷ 41F ∷ 47F ∷ 45F ∷ 46F ∷ 54F ∷ 55F ∷ 56F ∷ 49F ∷ 48F ∷ 50F ∷ 52F ∷ 51F ∷ 53F ∷ 59F ∷ 57F ∷ 58F ∷ [])
             ∷ (25F ∷ 26F ∷ 24F ∷ 30F ∷ 32F ∷ 31F ∷ 33F ∷ 35F ∷ 34F ∷ 27F ∷ 28F ∷ 29F ∷ 4F ∷ 5F ∷ 3F ∷ 7F ∷ 8F ∷ 6F ∷ 10F ∷ 11F ∷ 9F ∷ 0F ∷ 1F ∷ 2F ∷ 42F ∷ 44F ∷ 43F ∷ 37F ∷ 38F ∷ 36F ∷ 47F ∷ 45F ∷ 46F ∷ 40F ∷ 39F ∷ 41F ∷ 54F ∷ 56F ∷ 55F ∷ 49F ∷ 50F ∷ 48F ∷ 59F ∷ 57F ∷ 58F ∷ 52F ∷ 51F ∷ 53F ∷ 15F ∷ 16F ∷ 17F ∷ 12F ∷ 13F ∷ 14F ∷ 19F ∷ 18F ∷ 20F ∷ 22F ∷ 21F ∷ 23F ∷ [])
             ∷ (26F ∷ 24F ∷ 25F ∷ 33F ∷ 34F ∷ 35F ∷ 27F ∷ 29F ∷ 28F ∷ 30F ∷ 32F ∷ 31F ∷ 5F ∷ 3F ∷ 4F ∷ 10F ∷ 9F ∷ 11F ∷ 0F ∷ 2F ∷ 1F ∷ 7F ∷ 8F ∷ 6F ∷ 54F ∷ 55F ∷ 56F ∷ 49F ∷ 48F ∷ 50F ∷ 52F ∷ 51F ∷ 53F ∷ 59F ∷ 57F ∷ 58F ∷ 15F ∷ 17F ∷ 16F ∷ 12F ∷ 14F ∷ 13F ∷ 22F ∷ 21F ∷ 23F ∷ 19F ∷ 18F ∷ 20F ∷ 42F ∷ 44F ∷ 43F ∷ 37F ∷ 38F ∷ 36F ∷ 47F ∷ 45F ∷ 46F ∷ 40F ∷ 39F ∷ 41F ∷ [])
             ∷ (27F ∷ 29F ∷ 28F ∷ 24F ∷ 26F ∷ 25F ∷ 34F ∷ 33F ∷ 35F ∷ 31F ∷ 30F ∷ 32F ∷ 15F ∷ 17F ∷ 16F ∷ 12F ∷ 14F ∷ 13F ∷ 22F ∷ 21F ∷ 23F ∷ 19F ∷ 18F ∷ 20F ∷ 3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ 10F ∷ 9F ∷ 11F ∷ 7F ∷ 6F ∷ 8F ∷ 55F ∷ 54F ∷ 56F ∷ 52F ∷ 51F ∷ 53F ∷ 49F ∷ 48F ∷ 50F ∷ 59F ∷ 58F ∷ 57F ∷ 43F ∷ 42F ∷ 44F ∷ 40F ∷ 39F ∷ 41F ∷ 37F ∷ 36F ∷ 38F ∷ 47F ∷ 46F ∷ 45F ∷ [])
             ∷ (28F ∷ 27F ∷ 29F ∷ 31F ∷ 30F ∷ 32F ∷ 24F ∷ 25F ∷ 26F ∷ 34F ∷ 35F ∷ 33F ∷ 16F ∷ 15F ∷ 17F ∷ 19F ∷ 18F ∷ 20F ∷ 12F ∷ 13F ∷ 14F ∷ 22F ∷ 23F ∷ 21F ∷ 43F ∷ 42F ∷ 44F ∷ 40F ∷ 39F ∷ 41F ∷ 37F ∷ 36F ∷ 38F ∷ 47F ∷ 46F ∷ 45F ∷ 3F ∷ 4F ∷ 5F ∷ 0F ∷ 1F ∷ 2F ∷ 7F ∷ 6F ∷ 8F ∷ 10F ∷ 9F ∷ 11F ∷ 55F ∷ 56F ∷ 54F ∷ 52F ∷ 53F ∷ 51F ∷ 59F ∷ 58F ∷ 57F ∷ 49F ∷ 48F ∷ 50F ∷ [])
             ∷ (29F ∷ 28F ∷ 27F ∷ 34F ∷ 35F ∷ 33F ∷ 31F ∷ 32F ∷ 30F ∷ 24F ∷ 26F ∷ 25F ∷ 17F ∷ 16F ∷ 15F ∷ 22F ∷ 23F ∷ 21F ∷ 19F ∷ 20F ∷ 18F ∷ 12F ∷ 14F ∷ 13F ∷ 55F ∷ 56F ∷ 54F ∷ 52F ∷ 53F ∷ 51F ∷ 59F ∷ 58F ∷ 57F ∷ 49F ∷ 48F ∷ 50F ∷ 43F ∷ 44F ∷ 42F ∷ 40F ∷ 41F ∷ 39F ∷ 47F ∷ 46F ∷ 45F ∷ 37F ∷ 36F ∷ 38F ∷ 3F ∷ 5F ∷ 4F ∷ 0F ∷ 2F ∷ 1F ∷ 10F ∷ 9F ∷ 11F ∷ 7F ∷ 6F ∷ 8F ∷ [])
             ∷ (30F ∷ 31F ∷ 32F ∷ 25F ∷ 24F ∷ 26F ∷ 28F ∷ 27F ∷ 29F ∷ 35F ∷ 33F ∷ 34F ∷ 42F ∷ 43F ∷ 44F ∷ 37F ∷ 36F ∷ 38F ∷ 40F ∷ 39F ∷ 41F ∷ 47F ∷ 45F ∷ 46F ∷ 4F ∷ 3F ∷ 5F ∷ 7F ∷ 6F ∷ 8F ∷ 0F ∷ 1F ∷ 2F ∷ 10F ∷ 11F ∷ 9F ∷ 16F ∷ 15F ∷ 17F ∷ 19F ∷ 18F ∷ 20F ∷ 12F ∷ 13F ∷ 14F ∷ 22F ∷ 23F ∷ 21F ∷ 56F ∷ 54F ∷ 55F ∷ 59F ∷ 57F ∷ 58F ∷ 49F ∷ 50F ∷ 48F ∷ 52F ∷ 53F ∷ 51F ∷ [])
             ∷ (31F ∷ 32F ∷ 30F ∷ 28F ∷ 29F ∷ 27F ∷ 35F ∷ 34F ∷ 33F ∷ 25F ∷ 24F ∷ 26F ∷ 43F ∷ 44F ∷ 42F ∷ 40F ∷ 41F ∷ 39F ∷ 47F ∷ 46F ∷ 45F ∷ 37F ∷ 36F ∷ 38F ∷ 16F ∷ 17F ∷ 15F ∷ 19F ∷ 20F ∷ 18F ∷ 22F ∷ 23F ∷ 21F ∷ 12F ∷ 13F ∷ 14F ∷ 56F ∷ 55F ∷ 54F ∷ 59F ∷ 58F ∷ 57F ∷ 52F ∷ 53F ∷ 51F ∷ 49F ∷ 50F ∷ 48F ∷ 4F ∷ 3F ∷ 5F ∷ 7F ∷ 6F ∷ 8F ∷ 0F ∷ 1F ∷ 2F ∷ 10F ∷ 11F ∷ 9F ∷ [])
             ∷ (32F ∷ 30F ∷ 31F ∷ 35F ∷ 33F ∷ 34F ∷ 25F ∷ 26F ∷ 24F ∷ 28F ∷ 29F ∷ 27F ∷ 44F ∷ 42F ∷ 43F ∷ 47F ∷ 45F ∷ 46F ∷ 37F ∷ 38F ∷ 36F ∷ 40F ∷ 41F ∷ 39F ∷ 56F ∷ 54F ∷ 55F ∷ 59F ∷ 57F ∷ 58F ∷ 49F ∷ 50F ∷ 48F ∷ 52F ∷ 53F ∷ 51F ∷ 4F ∷ 5F ∷ 3F ∷ 7F ∷ 8F ∷ 6F ∷ 10F ∷ 11F ∷ 9F ∷ 0F ∷ 1F ∷ 2F ∷ 16F ∷ 17F ∷ 15F ∷ 19F ∷ 20F ∷ 18F ∷ 22F ∷ 23F ∷ 21F ∷ 12F ∷ 13F ∷ 14F ∷ [])
             ∷ (33F ∷ 35F ∷ 34F ∷ 26F ∷ 25F ∷ 24F ∷ 32F ∷ 30F ∷ 31F ∷ 29F ∷ 27F ∷ 28F ∷ 54F ∷ 56F ∷ 55F ∷ 49F ∷ 50F ∷ 48F ∷ 59F ∷ 57F ∷ 58F ∷ 52F ∷ 51F ∷ 53F ∷ 5F ∷ 4F ∷ 3F ∷ 10F ∷ 11F ∷ 9F ∷ 7F ∷ 8F ∷ 6F ∷ 0F ∷ 2F ∷ 1F ∷ 44F ∷ 42F ∷ 43F ∷ 47F ∷ 45F ∷ 46F ∷ 37F ∷ 38F ∷ 36F ∷ 40F ∷ 41F ∷ 39F ∷ 17F ∷ 15F ∷ 16F ∷ 22F ∷ 21F ∷ 23F ∷ 12F ∷ 14F ∷ 13F ∷ 19F ∷ 20F ∷ 18F ∷ [])
             ∷ (34F ∷ 33F ∷ 35F ∷ 29F ∷ 27F ∷ 28F ∷ 26F ∷ 24F ∷ 25F ∷ 32F ∷ 31F ∷ 30F ∷ 55F ∷ 54F ∷ 56F ∷ 52F ∷ 51F ∷ 53F ∷ 49F ∷ 48F ∷ 50F ∷ 59F ∷ 58F ∷ 57F ∷ 17F ∷ 15F ∷ 16F ∷ 22F ∷ 21F ∷ 23F ∷ 12F ∷ 14F ∷ 13F ∷ 19F ∷ 20F ∷ 18F ∷ 5F ∷ 3F ∷ 4F ∷ 10F ∷ 9F ∷ 11F ∷ 0F ∷ 2F ∷ 1F ∷ 7F ∷ 8F ∷ 6F ∷ 44F ∷ 43F ∷ 42F ∷ 47F ∷ 46F ∷ 45F ∷ 40F ∷ 41F ∷ 39F ∷ 37F ∷ 38F ∷ 36F ∷ [])
             ∷ (35F ∷ 34F ∷ 33F ∷ 32F ∷ 31F ∷ 30F ∷ 29F ∷ 28F ∷ 27F ∷ 26F ∷ 25F ∷ 24F ∷ 56F ∷ 55F ∷ 54F ∷ 59F ∷ 58F ∷ 57F ∷ 52F ∷ 53F ∷ 51F ∷ 49F ∷ 50F ∷ 48F ∷ 44F ∷ 43F ∷ 42F ∷ 47F ∷ 46F ∷ 45F ∷ 40F ∷ 41F ∷ 39F ∷ 37F ∷ 38F ∷ 36F ∷ 17F ∷ 16F ∷ 15F ∷ 22F ∷ 23F ∷ 21F ∷ 19F ∷ 20F ∷ 18F ∷ 12F ∷ 14F ∷ 13F ∷ 5F ∷ 4F ∷ 3F ∷ 10F ∷ 11F ∷ 9F ∷ 7F ∷ 8F ∷ 6F ∷ 0F ∷ 2F ∷ 1F ∷ [])
             ∷ (36F ∷ 38F ∷ 37F ∷ 39F ∷ 41F ∷ 40F ∷ 45F ∷ 46F ∷ 47F ∷ 42F ∷ 43F ∷ 44F ∷ 6F ∷ 8F ∷ 7F ∷ 1F ∷ 2F ∷ 0F ∷ 11F ∷ 9F ∷ 10F ∷ 4F ∷ 3F ∷ 5F ∷ 18F ∷ 20F ∷ 19F ∷ 13F ∷ 14F ∷ 12F ∷ 23F ∷ 21F ∷ 22F ∷ 16F ∷ 15F ∷ 17F ∷ 57F ∷ 58F ∷ 59F ∷ 50F ∷ 48F ∷ 49F ∷ 53F ∷ 51F ∷ 52F ∷ 56F ∷ 54F ∷ 55F ∷ 30F ∷ 31F ∷ 32F ∷ 25F ∷ 24F ∷ 26F ∷ 28F ∷ 27F ∷ 29F ∷ 35F ∷ 33F ∷ 34F ∷ [])
             ∷ (37F ∷ 36F ∷ 38F ∷ 42F ∷ 43F ∷ 44F ∷ 39F ∷ 40F ∷ 41F ∷ 45F ∷ 47F ∷ 46F ∷ 7F ∷ 6F ∷ 8F ∷ 4F ∷ 3F ∷ 5F ∷ 1F ∷ 0F ∷ 2F ∷ 11F ∷ 10F ∷ 9F ∷ 30F ∷ 31F ∷ 32F ∷ 25F ∷ 24F ∷ 26F ∷ 28F ∷ 27F ∷ 29F ∷ 35F ∷ 33F ∷ 34F ∷ 18F ∷ 19F ∷ 20F ∷ 13F ∷ 12F ∷ 14F ∷ 16F ∷ 15F ∷ 17F ∷ 23F ∷ 21F ∷ 22F ∷ 57F ∷ 59F ∷ 58F ∷ 50F ∷ 49F ∷ 48F ∷ 56F ∷ 54F ∷ 55F ∷ 53F ∷ 51F ∷ 52F ∷ [])
             ∷ (38F ∷ 37F ∷ 36F ∷ 45F ∷ 47F ∷ 46F ∷ 42F ∷ 44F ∷ 43F ∷ 39F ∷ 41F ∷ 40F ∷ 8F ∷ 7F ∷ 6F ∷ 11F ∷ 10F ∷ 9F ∷ 4F ∷ 5F ∷ 3F ∷ 1F ∷ 2F ∷ 0F ∷ 57F ∷ 59F ∷ 58F ∷ 50F ∷ 49F ∷ 48F ∷ 56F ∷ 54F ∷ 55F ∷ 53F ∷ 51F ∷ 52F ∷ 30F ∷ 32F ∷ 31F ∷ 25F ∷ 26F ∷ 24F ∷ 35F ∷ 33F ∷ 34F ∷ 28F ∷ 27F ∷ 29F ∷ 18F ∷ 20F ∷ 19F ∷ 13F ∷ 14F ∷ 12F ∷ 23F ∷ 21F ∷ 22F ∷ 16F ∷ 15F ∷ 17F ∷ [])
             ∷ (39F ∷ 40F ∷ 41F ∷ 36F ∷ 37F ∷ 38F ∷ 43F ∷ 42F ∷ 44F ∷ 46F ∷ 45F ∷ 47F ∷ 18F ∷ 19F ∷ 20F ∷ 13F ∷ 12F ∷ 14F ∷ 16F ∷ 15F ∷ 17F ∷ 23F ∷ 21F ∷ 22F ∷ 6F ∷ 7F ∷ 8F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ 5F ∷ 11F ∷ 9F ∷ 10F ∷ 31F ∷ 30F ∷ 32F ∷ 28F ∷ 27F ∷ 29F ∷ 25F ∷ 24F ∷ 26F ∷ 35F ∷ 34F ∷ 33F ∷ 58F ∷ 57F ∷ 59F ∷ 53F ∷ 51F ∷ 52F ∷ 50F ∷ 48F ∷ 49F ∷ 56F ∷ 55F ∷ 54F ∷ [])
             ∷ (40F ∷ 41F ∷ 39F ∷ 43F ∷ 44F ∷ 42F ∷ 46F ∷ 47F ∷ 45F ∷ 36F ∷ 37F ∷ 38F ∷ 19F ∷ 20F ∷ 18F ∷ 16F ∷ 17F ∷ 15F ∷ 23F ∷ 22F ∷ 21F ∷ 13F ∷ 12F ∷ 14F ∷ 31F ∷ 32F ∷ 30F ∷ 28F ∷ 29F ∷ 27F ∷ 35F ∷ 34F ∷ 33F ∷ 25F ∷ 24F ∷ 26F ∷ 58F ∷ 59F ∷ 57F ∷ 53F ∷ 52F ∷ 51F ∷ 56F ∷ 55F ∷ 54F ∷ 50F ∷ 48F ∷ 49F ∷ 6F ∷ 7F ∷ 8F ∷ 1F ∷ 0F ∷ 2F ∷ 4F ∷ 3F ∷ 5F ∷ 11F ∷ 9F ∷ 10F ∷ [])
             ∷ (41F ∷ 39F ∷ 40F ∷ 46F ∷ 45F ∷ 47F ∷ 36F ∷ 38F ∷ 37F ∷ 43F ∷ 44F ∷ 42F ∷ 20F ∷ 18F ∷ 19F ∷ 23F ∷ 21F ∷ 22F ∷ 13F ∷ 14F ∷ 12F ∷ 16F ∷ 17F ∷ 15F ∷ 58F ∷ 57F ∷ 59F ∷ 53F ∷ 51F ∷ 52F ∷ 50F ∷ 48F ∷ 49F ∷ 56F ∷ 55F ∷ 54F ∷ 6F ∷ 8F ∷ 7F ∷ 1F ∷ 2F ∷ 0F ∷ 11F ∷ 9F ∷ 10F ∷ 4F ∷ 3F ∷ 5F ∷ 31F ∷ 32F ∷ 30F ∷ 28F ∷ 29F ∷ 27F ∷ 35F ∷ 34F ∷ 33F ∷ 25F ∷ 24F ∷ 26F ∷ [])
             ∷ (42F ∷ 44F ∷ 43F ∷ 37F ∷ 38F ∷ 36F ∷ 47F ∷ 45F ∷ 46F ∷ 40F ∷ 39F ∷ 41F ∷ 30F ∷ 32F ∷ 31F ∷ 25F ∷ 26F ∷ 24F ∷ 35F ∷ 33F ∷ 34F ∷ 28F ∷ 27F ∷ 29F ∷ 7F ∷ 8F ∷ 6F ∷ 4F ∷ 5F ∷ 3F ∷ 11F ∷ 10F ∷ 9F ∷ 1F ∷ 0F ∷ 2F ∷ 59F ∷ 57F ∷ 58F ∷ 56F ∷ 54F ∷ 55F ∷ 50F ∷ 49F ∷ 48F ∷ 53F ∷ 52F ∷ 51F ∷ 19F ∷ 18F ∷ 20F ∷ 16F ∷ 15F ∷ 17F ∷ 13F ∷ 12F ∷ 14F ∷ 23F ∷ 22F ∷ 21F ∷ [])
             ∷ (43F ∷ 42F ∷ 44F ∷ 40F ∷ 39F ∷ 41F ∷ 37F ∷ 36F ∷ 38F ∷ 47F ∷ 46F ∷ 45F ∷ 31F ∷ 30F ∷ 32F ∷ 28F ∷ 27F ∷ 29F ∷ 25F ∷ 24F ∷ 26F ∷ 35F ∷ 34F ∷ 33F ∷ 19F ∷ 18F ∷ 20F ∷ 16F ∷ 15F ∷ 17F ∷ 13F ∷ 12F ∷ 14F ∷ 23F ∷ 22F ∷ 21F ∷ 7F ∷ 6F ∷ 8F ∷ 4F ∷ 3F ∷ 5F ∷ 1F ∷ 0F ∷ 2F ∷ 11F ∷ 10F ∷ 9F ∷ 59F ∷ 58F ∷ 57F ∷ 56F ∷ 55F ∷ 54F ∷ 53F ∷ 52F ∷ 51F ∷ 50F ∷ 49F ∷ 48F ∷ [])
             ∷ (44F ∷ 43F ∷ 42F ∷ 47F ∷ 46F ∷ 45F ∷ 40F ∷ 41F ∷ 39F ∷ 37F ∷ 38F ∷ 36F ∷ 32F ∷ 31F ∷ 30F ∷ 35F ∷ 34F ∷ 33F ∷ 28F ∷ 29F ∷ 27F ∷ 25F ∷ 26F ∷ 24F ∷ 59F ∷ 58F ∷ 57F ∷ 56F ∷ 55F ∷ 54F ∷ 53F ∷ 52F ∷ 51F ∷ 50F ∷ 49F ∷ 48F ∷ 19F ∷ 20F ∷ 18F ∷ 16F ∷ 17F ∷ 15F ∷ 23F ∷ 22F ∷ 21F ∷ 13F ∷ 12F ∷ 14F ∷ 7F ∷ 8F ∷ 6F ∷ 4F ∷ 5F ∷ 3F ∷ 11F ∷ 10F ∷ 9F ∷ 1F ∷ 0F ∷ 2F ∷ [])
             ∷ (45F ∷ 46F ∷ 47F ∷ 38F ∷ 36F ∷ 37F ∷ 41F ∷ 39F ∷ 40F ∷ 44F ∷ 42F ∷ 43F ∷ 57F ∷ 58F ∷ 59F ∷ 50F ∷ 48F ∷ 49F ∷ 53F ∷ 51F ∷ 52F ∷ 56F ∷ 54F ∷ 55F ∷ 8F ∷ 6F ∷ 7F ∷ 11F ∷ 9F ∷ 10F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F ∷ 20F ∷ 18F ∷ 19F ∷ 23F ∷ 21F ∷ 22F ∷ 13F ∷ 14F ∷ 12F ∷ 16F ∷ 17F ∷ 15F ∷ 32F ∷ 30F ∷ 31F ∷ 35F ∷ 33F ∷ 34F ∷ 25F ∷ 26F ∷ 24F ∷ 28F ∷ 29F ∷ 27F ∷ [])
             ∷ (46F ∷ 47F ∷ 45F ∷ 41F ∷ 40F ∷ 39F ∷ 44F ∷ 43F ∷ 42F ∷ 38F ∷ 36F ∷ 37F ∷ 58F ∷ 59F ∷ 57F ∷ 53F ∷ 52F ∷ 51F ∷ 56F ∷ 55F ∷ 54F ∷ 50F ∷ 48F ∷ 49F ∷ 20F ∷ 19F ∷ 18F ∷ 23F ∷ 22F ∷ 21F ∷ 16F ∷ 17F ∷ 15F ∷ 13F ∷ 14F ∷ 12F ∷ 32F ∷ 31F ∷ 30F ∷ 35F ∷ 34F ∷ 33F ∷ 28F ∷ 29F ∷ 27F ∷ 25F ∷ 26F ∷ 24F ∷ 8F ∷ 6F ∷ 7F ∷ 11F ∷ 9F ∷ 10F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 5F ∷ 3F ∷ [])
             ∷ (47F ∷ 45F ∷ 46F ∷ 44F ∷ 42F ∷ 43F ∷ 38F ∷ 37F ∷ 36F ∷ 41F ∷ 40F ∷ 39F ∷ 59F ∷ 57F ∷ 58F ∷ 56F ∷ 54F ∷ 55F ∷ 50F ∷ 49F ∷ 48F ∷ 53F ∷ 52F ∷ 51F ∷ 32F ∷ 30F ∷ 31F ∷ 35F ∷ 33F ∷ 34F ∷ 25F ∷ 26F ∷ 24F ∷ 28F ∷ 29F ∷ 27F ∷ 8F ∷ 7F ∷ 6F ∷ 11F ∷ 10F ∷ 9F ∷ 4F ∷ 5F ∷ 3F ∷ 1F ∷ 2F ∷ 0F ∷ 20F ∷ 19F ∷ 18F ∷ 23F ∷ 22F ∷ 21F ∷ 16F ∷ 17F ∷ 15F ∷ 13F ∷ 14F ∷ 12F ∷ [])
             ∷ (48F ∷ 49F ∷ 50F ∷ 51F ∷ 52F ∷ 53F ∷ 54F ∷ 55F ∷ 56F ∷ 57F ∷ 58F ∷ 59F ∷ 9F ∷ 10F ∷ 11F ∷ 2F ∷ 0F ∷ 1F ∷ 5F ∷ 3F ∷ 4F ∷ 8F ∷ 6F ∷ 7F ∷ 21F ∷ 22F ∷ 23F ∷ 14F ∷ 12F ∷ 13F ∷ 17F ∷ 15F ∷ 16F ∷ 20F ∷ 18F ∷ 19F ∷ 33F ∷ 34F ∷ 35F ∷ 26F ∷ 24F ∷ 25F ∷ 29F ∷ 27F ∷ 28F ∷ 32F ∷ 30F ∷ 31F ∷ 45F ∷ 46F ∷ 47F ∷ 38F ∷ 36F ∷ 37F ∷ 41F ∷ 39F ∷ 40F ∷ 44F ∷ 42F ∷ 43F ∷ [])
             ∷ (49F ∷ 50F ∷ 48F ∷ 54F ∷ 56F ∷ 55F ∷ 57F ∷ 59F ∷ 58F ∷ 51F ∷ 52F ∷ 53F ∷ 10F ∷ 11F ∷ 9F ∷ 5F ∷ 4F ∷ 3F ∷ 8F ∷ 7F ∷ 6F ∷ 2F ∷ 0F ∷ 1F ∷ 33F ∷ 35F ∷ 34F ∷ 26F ∷ 25F ∷ 24F ∷ 32F ∷ 30F ∷ 31F ∷ 29F ∷ 27F ∷ 28F ∷ 45F ∷ 47F ∷ 46F ∷ 38F ∷ 37F ∷ 36F ∷ 44F ∷ 42F ∷ 43F ∷ 41F ∷ 39F ∷ 40F ∷ 21F ∷ 22F ∷ 23F ∷ 14F ∷ 12F ∷ 13F ∷ 17F ∷ 15F ∷ 16F ∷ 20F ∷ 18F ∷ 19F ∷ [])
             ∷ (50F ∷ 48F ∷ 49F ∷ 57F ∷ 58F ∷ 59F ∷ 51F ∷ 53F ∷ 52F ∷ 54F ∷ 56F ∷ 55F ∷ 11F ∷ 9F ∷ 10F ∷ 8F ∷ 6F ∷ 7F ∷ 2F ∷ 1F ∷ 0F ∷ 5F ∷ 4F ∷ 3F ∷ 45F ∷ 46F ∷ 47F ∷ 38F ∷ 36F ∷ 37F ∷ 41F ∷ 39F ∷ 40F ∷ 44F ∷ 42F ∷ 43F ∷ 21F ∷ 23F ∷ 22F ∷ 14F ∷ 13F ∷ 12F ∷ 20F ∷ 18F ∷ 19F ∷ 17F ∷ 15F ∷ 16F ∷ 33F ∷ 35F ∷ 34F ∷ 26F ∷ 25F ∷ 24F ∷ 32F ∷ 30F ∷ 31F ∷ 29F ∷ 27F ∷ 28F ∷ [])
             ∷ (51F ∷ 53F ∷ 52F ∷ 48F ∷ 50F ∷ 49F ∷ 58F ∷ 57F ∷ 59F ∷ 55F ∷ 54F ∷ 56F ∷ 21F ∷ 23F ∷ 22F ∷ 14F ∷ 13F ∷ 12F ∷ 20F ∷ 18F ∷ 19F ∷ 17F ∷ 15F ∷ 16F ∷ 9F ∷ 11F ∷ 10F ∷ 2F ∷ 1F ∷ 0F ∷ 8F ∷ 6F ∷ 7F ∷ 5F ∷ 3F ∷ 4F ∷ 46F ∷ 45F ∷ 47F ∷ 41F ∷ 39F ∷ 40F ∷ 38F ∷ 36F ∷ 37F ∷ 44F ∷ 43F ∷ 42F ∷ 34F ∷ 33F ∷ 35F ∷ 29F ∷ 27F ∷ 28F ∷ 26F ∷ 24F ∷ 25F ∷ 32F ∷ 31F ∷ 30F ∷ [])
             ∷ (52F ∷ 51F ∷ 53F ∷ 55F ∷ 54F ∷ 56F ∷ 48F ∷ 49F ∷ 50F ∷ 58F ∷ 59F ∷ 57F ∷ 22F ∷ 21F ∷ 23F ∷ 17F ∷ 15F ∷ 16F ∷ 14F ∷ 12F ∷ 13F ∷ 20F ∷ 19F ∷ 18F ∷ 34F ∷ 33F ∷ 35F ∷ 29F ∷ 27F ∷ 28F ∷ 26F ∷ 24F ∷ 25F ∷ 32F ∷ 31F ∷ 30F ∷ 9F ∷ 10F ∷ 11F ∷ 2F ∷ 0F ∷ 1F ∷ 5F ∷ 3F ∷ 4F ∷ 8F ∷ 6F ∷ 7F ∷ 46F ∷ 47F ∷ 45F ∷ 41F ∷ 40F ∷ 39F ∷ 44F ∷ 43F ∷ 42F ∷ 38F ∷ 36F ∷ 37F ∷ [])
             ∷ (53F ∷ 52F ∷ 51F ∷ 58F ∷ 59F ∷ 57F ∷ 55F ∷ 56F ∷ 54F ∷ 48F ∷ 50F ∷ 49F ∷ 23F ∷ 22F ∷ 21F ∷ 20F ∷ 19F ∷ 18F ∷ 17F ∷ 16F ∷ 15F ∷ 14F ∷ 13F ∷ 12F ∷ 46F ∷ 47F ∷ 45F ∷ 41F ∷ 40F ∷ 39F ∷ 44F ∷ 43F ∷ 42F ∷ 38F ∷ 36F ∷ 37F ∷ 34F ∷ 35F ∷ 33F ∷ 29F ∷ 28F ∷ 27F ∷ 32F ∷ 31F ∷ 30F ∷ 26F ∷ 24F ∷ 25F ∷ 9F ∷ 11F ∷ 10F ∷ 2F ∷ 1F ∷ 0F ∷ 8F ∷ 6F ∷ 7F ∷ 5F ∷ 3F ∷ 4F ∷ [])
             ∷ (54F ∷ 55F ∷ 56F ∷ 49F ∷ 48F ∷ 50F ∷ 52F ∷ 51F ∷ 53F ∷ 59F ∷ 57F ∷ 58F ∷ 33F ∷ 34F ∷ 35F ∷ 26F ∷ 24F ∷ 25F ∷ 29F ∷ 27F ∷ 28F ∷ 32F ∷ 30F ∷ 31F ∷ 10F ∷ 9F ∷ 11F ∷ 5F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ 8F ∷ 7F ∷ 6F ∷ 22F ∷ 21F ∷ 23F ∷ 17F ∷ 15F ∷ 16F ∷ 14F ∷ 12F ∷ 13F ∷ 20F ∷ 19F ∷ 18F ∷ 47F ∷ 45F ∷ 46F ∷ 44F ∷ 42F ∷ 43F ∷ 38F ∷ 37F ∷ 36F ∷ 41F ∷ 40F ∷ 39F ∷ [])
             ∷ (55F ∷ 56F ∷ 54F ∷ 52F ∷ 53F ∷ 51F ∷ 59F ∷ 58F ∷ 57F ∷ 49F ∷ 48F ∷ 50F ∷ 34F ∷ 35F ∷ 33F ∷ 29F ∷ 28F ∷ 27F ∷ 32F ∷ 31F ∷ 30F ∷ 26F ∷ 24F ∷ 25F ∷ 22F ∷ 23F ∷ 21F ∷ 17F ∷ 16F ∷ 15F ∷ 20F ∷ 19F ∷ 18F ∷ 14F ∷ 12F ∷ 13F ∷ 47F ∷ 46F ∷ 45F ∷ 44F ∷ 43F ∷ 42F ∷ 41F ∷ 40F ∷ 39F ∷ 38F ∷ 37F ∷ 36F ∷ 10F ∷ 9F ∷ 11F ∷ 5F ∷ 3F ∷ 4F ∷ 2F ∷ 0F ∷ 1F ∷ 8F ∷ 7F ∷ 6F ∷ [])
             ∷ (56F ∷ 54F ∷ 55F ∷ 59F ∷ 57F ∷ 58F ∷ 49F ∷ 50F ∷ 48F ∷ 52F ∷ 53F ∷ 51F ∷ 35F ∷ 33F ∷ 34F ∷ 32F ∷ 30F ∷ 31F ∷ 26F ∷ 25F ∷ 24F ∷ 29F ∷ 28F ∷ 27F ∷ 47F ∷ 45F ∷ 46F ∷ 44F ∷ 42F ∷ 43F ∷ 38F ∷ 37F ∷ 36F ∷ 41F ∷ 40F ∷ 39F ∷ 10F ∷ 11F ∷ 9F ∷ 5F ∷ 4F ∷ 3F ∷ 8F ∷ 7F ∷ 6F ∷ 2F ∷ 0F ∷ 1F ∷ 22F ∷ 23F ∷ 21F ∷ 17F ∷ 16F ∷ 15F ∷ 20F ∷ 19F ∷ 18F ∷ 14F ∷ 12F ∷ 13F ∷ [])
             ∷ (57F ∷ 59F ∷ 58F ∷ 50F ∷ 49F ∷ 48F ∷ 56F ∷ 54F ∷ 55F ∷ 53F ∷ 51F ∷ 52F ∷ 45F ∷ 47F ∷ 46F ∷ 38F ∷ 37F ∷ 36F ∷ 44F ∷ 42F ∷ 43F ∷ 41F ∷ 39F ∷ 40F ∷ 11F ∷ 10F ∷ 9F ∷ 8F ∷ 7F ∷ 6F ∷ 5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ 35F ∷ 33F ∷ 34F ∷ 32F ∷ 30F ∷ 31F ∷ 26F ∷ 25F ∷ 24F ∷ 29F ∷ 28F ∷ 27F ∷ 23F ∷ 21F ∷ 22F ∷ 20F ∷ 18F ∷ 19F ∷ 14F ∷ 13F ∷ 12F ∷ 17F ∷ 16F ∷ 15F ∷ [])
             ∷ (58F ∷ 57F ∷ 59F ∷ 53F ∷ 51F ∷ 52F ∷ 50F ∷ 48F ∷ 49F ∷ 56F ∷ 55F ∷ 54F ∷ 46F ∷ 45F ∷ 47F ∷ 41F ∷ 39F ∷ 40F ∷ 38F ∷ 36F ∷ 37F ∷ 44F ∷ 43F ∷ 42F ∷ 23F ∷ 21F ∷ 22F ∷ 20F ∷ 18F ∷ 19F ∷ 14F ∷ 13F ∷ 12F ∷ 17F ∷ 16F ∷ 15F ∷ 11F ∷ 9F ∷ 10F ∷ 8F ∷ 6F ∷ 7F ∷ 2F ∷ 1F ∷ 0F ∷ 5F ∷ 4F ∷ 3F ∷ 35F ∷ 34F ∷ 33F ∷ 32F ∷ 31F ∷ 30F ∷ 29F ∷ 28F ∷ 27F ∷ 26F ∷ 25F ∷ 24F ∷ [])
             ∷ (59F ∷ 58F ∷ 57F ∷ 56F ∷ 55F ∷ 54F ∷ 53F ∷ 52F ∷ 51F ∷ 50F ∷ 49F ∷ 48F ∷ 47F ∷ 46F ∷ 45F ∷ 44F ∷ 43F ∷ 42F ∷ 41F ∷ 40F ∷ 39F ∷ 38F ∷ 37F ∷ 36F ∷ 35F ∷ 34F ∷ 33F ∷ 32F ∷ 31F ∷ 30F ∷ 29F ∷ 28F ∷ 27F ∷ 26F ∷ 25F ∷ 24F ∷ 23F ∷ 22F ∷ 21F ∷ 20F ∷ 19F ∷ 18F ∷ 17F ∷ 16F ∷ 15F ∷ 14F ∷ 13F ∷ 12F ∷ 11F ∷ 10F ∷ 9F ∷ 8F ∷ 7F ∷ 6F ∷ 5F ∷ 4F ∷ 3F ∷ 2F ∷ 1F ∷ 0F ∷ [])
             ∷ []

-- The inverse of each element.
a5-inv-vec : Vec (Fin 60) 60
a5-inv-vec = 0F
           ∷ 2F
           ∷ 1F
           ∷ 3F
           ∷ 6F
           ∷ 9F
           ∷ 4F
           ∷ 10F
           ∷ 8F
           ∷ 5F
           ∷ 7F
           ∷ 11F
           ∷ 12F
           ∷ 13F
           ∷ 14F
           ∷ 24F
           ∷ 48F
           ∷ 36F
           ∷ 26F
           ∷ 37F
           ∷ 50F
           ∷ 25F
           ∷ 49F
           ∷ 38F
           ∷ 15F
           ∷ 21F
           ∷ 18F
           ∷ 27F
           ∷ 39F
           ∷ 51F
           ∷ 30F
           ∷ 54F
           ∷ 45F
           ∷ 33F
           ∷ 42F
           ∷ 57F
           ∷ 17F
           ∷ 19F
           ∷ 23F
           ∷ 28F
           ∷ 52F
           ∷ 41F
           ∷ 34F
           ∷ 43F
           ∷ 58F
           ∷ 32F
           ∷ 56F
           ∷ 47F
           ∷ 16F
           ∷ 22F
           ∷ 20F
           ∷ 29F
           ∷ 40F
           ∷ 53F
           ∷ 31F
           ∷ 55F
           ∷ 46F
           ∷ 35F
           ∷ 44F
           ∷ 59F
           ∷ []

-- The action on the five points: row a is the one-line notation of element a.
a5-act-table : Vec (Vec (Fin 5) 5) 60
a5-act-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ [])
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
             ∷ []
```

#### The generators

```agda
-- The 5-cycle (0 1 2 3 4).
a5-gen-s : Fin 60
a5-gen-s = 16F

-- The 3-cycle (0 1 2).
a5-gen-t : Fin 60
a5-gen-t = 15F
```

#### The simplicity certificate

```agda
-- Every element as a word in the generators: seed 0 is s, seed 1 is t.
a5-gen-words : Vec (ClosureTerm (Fin 60) 2) 60
a5-gen-words = one
             ∷ mul (inv (seed 1F)) (seed 0F)
             ∷ mul (inv (seed 0F)) (seed 1F)
             ∷ mul (mul (mul (mul (seed 0F) (seed 1F)) (inv (seed 0F))) (inv (seed 1F))) (seed 0F)
             ∷ mul (mul (seed 0F) (seed 1F)) (inv (seed 0F))
             ∷ mul (mul (mul (inv (seed 0F)) (inv (seed 1F))) (seed 0F)) (seed 1F)
             ∷ mul (mul (seed 0F) (inv (seed 1F))) (inv (seed 0F))
             ∷ mul (mul (seed 1F) (seed 0F)) (seed 1F)
             ∷ mul (mul (inv (seed 0F)) (inv (seed 0F))) (inv (seed 1F))
             ∷ mul (mul (mul (inv (seed 1F)) (inv (seed 0F))) (seed 1F)) (seed 0F)
             ∷ mul (mul (inv (seed 1F)) (inv (seed 0F))) (inv (seed 1F))
             ∷ mul (mul (mul (mul (inv (seed 1F)) (seed 0F)) (seed 1F)) (seed 0F)) (seed 1F)
             ∷ mul (mul (mul (mul (seed 0F) (inv (seed 1F))) (inv (seed 0F))) (seed 1F)) (seed 0F)
             ∷ mul (mul (mul (seed 0F) (inv (seed 1F))) (inv (seed 0F))) (inv (seed 1F))
             ∷ mul (mul (mul (mul (seed 1F) (inv (seed 0F))) (inv (seed 1F))) (seed 0F)) (seed 1F)
             ∷ seed 1F
             ∷ seed 0F
             ∷ mul (mul (seed 0F) (inv (seed 1F))) (seed 0F)
             ∷ mul (mul (inv (seed 1F)) (seed 0F)) (seed 1F)
             ∷ mul (mul (mul (seed 1F) (seed 0F)) (inv (seed 1F))) (inv (seed 0F))
             ∷ mul (mul (inv (seed 1F)) (seed 0F)) (seed 0F)
             ∷ mul (inv (seed 0F)) (inv (seed 1F))
             ∷ mul (mul (inv (seed 0F)) (seed 1F)) (seed 0F)
             ∷ mul (mul (mul (seed 0F) (seed 1F)) (seed 0F)) (seed 1F)
             ∷ inv (seed 1F)
             ∷ mul (seed 1F) (seed 0F)
             ∷ mul (mul (inv (seed 1F)) (inv (seed 0F))) (seed 1F)
             ∷ mul (mul (mul (mul (mul (seed 0F) (seed 1F)) (inv (seed 0F))) (inv (seed 1F))) (seed 0F)) (seed 1F)
             ∷ mul (mul (mul (inv (seed 1F)) (seed 0F)) (seed 1F)) (inv (seed 0F))
             ∷ mul (mul (mul (inv (seed 0F)) (seed 1F)) (seed 0F)) (inv (seed 1F))
             ∷ mul (mul (mul (seed 0F) (seed 0F)) (inv (seed 1F))) (seed 0F)
             ∷ mul (seed 0F) (seed 1F)
             ∷ mul (seed 0F) (seed 0F)
             ∷ mul (mul (mul (seed 0F) (inv (seed 1F))) (seed 0F)) (seed 0F)
             ∷ mul (mul (seed 1F) (inv (seed 0F))) (inv (seed 1F))
             ∷ mul (mul (mul (mul (seed 0F) (seed 1F)) (seed 0F)) (inv (seed 1F))) (inv (seed 0F))
             ∷ mul (mul (inv (seed 0F)) (seed 1F)) (inv (seed 0F))
             ∷ mul (mul (mul (seed 0F) (seed 1F)) (inv (seed 0F))) (inv (seed 1F))
             ∷ mul (mul (mul (inv (seed 1F)) (seed 0F)) (seed 1F)) (seed 0F)
             ∷ mul (mul (mul (seed 0F) (inv (seed 1F))) (inv (seed 0F))) (seed 1F)
             ∷ mul (seed 0F) (inv (seed 1F))
             ∷ mul (mul (seed 0F) (seed 1F)) (seed 0F)
             ∷ mul (mul (seed 1F) (seed 0F)) (inv (seed 1F))
             ∷ mul (mul (mul (mul (seed 1F) (seed 0F)) (inv (seed 1F))) (inv (seed 0F))) (seed 1F)
             ∷ mul (mul (mul (seed 1F) (seed 0F)) (seed 1F)) (seed 0F)
             ∷ mul (inv (seed 0F)) (inv (seed 0F))
             ∷ mul (mul (seed 1F) (inv (seed 0F))) (inv (seed 0F))
             ∷ mul (mul (seed 0F) (seed 0F)) (seed 1F)
             ∷ inv (seed 0F)
             ∷ mul (mul (inv (seed 0F)) (inv (seed 1F))) (seed 0F)
             ∷ mul (mul (inv (seed 0F)) (inv (seed 0F))) (seed 1F)
             ∷ mul (mul (mul (seed 1F) (inv (seed 0F))) (inv (seed 1F))) (seed 0F)
             ∷ mul (seed 1F) (inv (seed 0F))
             ∷ mul (mul (mul (seed 1F) (inv (seed 0F))) (inv (seed 0F))) (seed 1F)
             ∷ mul (inv (seed 1F)) (inv (seed 0F))
             ∷ mul (mul (mul (inv (seed 0F)) (seed 1F)) (seed 0F)) (seed 1F)
             ∷ mul (mul (seed 0F) (seed 0F)) (inv (seed 1F))
             ∷ mul (mul (mul (mul (seed 0F) (seed 1F)) (seed 0F)) (seed 1F)) (seed 0F)
             ∷ mul (mul (mul (seed 0F) (seed 1F)) (seed 0F)) (inv (seed 1F))
             ∷ mul (mul (mul (mul (seed 1F) (seed 0F)) (seed 1F)) (seed 0F)) (inv (seed 1F))
             ∷ []

-- For the i-th non-identity element x, the generator s as a product of
-- conjugates of x and of its inverse (the one seed is x).
a5-seed-words-s : Vec (ClosureTerm (Fin 60) 1) 59
a5-seed-words-s = mul (cnj 0F (seed 0F)) (cnj 30F (seed 0F))
                ∷ mul (cnj 0F (inv (seed 0F))) (cnj 30F (inv (seed 0F)))
                ∷ mul (cnj 2F (seed 0F)) (cnj 26F (seed 0F))
                ∷ mul (cnj 5F (inv (seed 0F))) (cnj 26F (inv (seed 0F)))
                ∷ mul (cnj 4F (seed 0F)) (cnj 24F (seed 0F))
                ∷ mul (cnj 5F (seed 0F)) (cnj 26F (seed 0F))
                ∷ mul (cnj 3F (inv (seed 0F))) (cnj 25F (inv (seed 0F)))
                ∷ mul (cnj 1F (seed 0F)) (cnj 25F (seed 0F))
                ∷ mul (cnj 4F (inv (seed 0F))) (cnj 24F (inv (seed 0F)))
                ∷ mul (cnj 3F (seed 0F)) (cnj 25F (seed 0F))
                ∷ mul (cnj 0F (seed 0F)) (cnj 24F (seed 0F))
                ∷ mul (cnj 21F (seed 0F)) (cnj 10F (seed 0F))
                ∷ mul (cnj 22F (seed 0F)) (cnj 9F (seed 0F))
                ∷ mul (cnj 23F (seed 0F)) (cnj 11F (seed 0F))
                ∷ mul (cnj 32F (seed 0F)) (cnj 2F (seed 0F))
                ∷ cnj 0F (seed 0F)
                ∷ mul (cnj 5F (inv (seed 0F))) (cnj 5F (inv (seed 0F)))
                ∷ cnj 2F (seed 0F)
                ∷ mul (cnj 31F (seed 0F)) (cnj 1F (seed 0F))
                ∷ mul (cnj 3F (inv (seed 0F))) (cnj 3F (inv (seed 0F)))
                ∷ mul (cnj 4F (inv (seed 0F))) (cnj 4F (inv (seed 0F)))
                ∷ mul (cnj 30F (seed 0F)) (cnj 0F (seed 0F))
                ∷ cnj 1F (seed 0F)
                ∷ mul (cnj 32F (inv (seed 0F))) (cnj 2F (inv (seed 0F)))
                ∷ mul (cnj 4F (seed 0F)) (cnj 4F (seed 0F))
                ∷ cnj 2F (inv (seed 0F))
                ∷ mul (cnj 14F (seed 0F)) (cnj 5F (seed 0F))
                ∷ mul (cnj 25F (seed 0F)) (cnj 3F (seed 0F))
                ∷ mul (cnj 26F (inv (seed 0F))) (cnj 5F (inv (seed 0F)))
                ∷ mul (cnj 20F (seed 0F)) (cnj 8F (seed 0F))
                ∷ mul (cnj 1F (seed 0F)) (cnj 1F (seed 0F))
                ∷ mul (cnj 0F (inv (seed 0F))) (cnj 0F (inv (seed 0F)))
                ∷ mul (cnj 17F (seed 0F)) (cnj 2F (seed 0F))
                ∷ cnj 3F (seed 0F)
                ∷ cnj 5F (inv (seed 0F))
                ∷ mul (cnj 5F (seed 0F)) (cnj 5F (seed 0F))
                ∷ mul (cnj 31F (inv (seed 0F))) (cnj 1F (inv (seed 0F)))
                ∷ cnj 1F (inv (seed 0F))
                ∷ mul (cnj 25F (inv (seed 0F))) (cnj 3F (inv (seed 0F)))
                ∷ mul (cnj 24F (seed 0F)) (cnj 4F (seed 0F))
                ∷ mul (cnj 12F (seed 0F)) (cnj 3F (seed 0F))
                ∷ cnj 3F (inv (seed 0F))
                ∷ mul (cnj 16F (seed 0F)) (cnj 1F (seed 0F))
                ∷ cnj 4F (seed 0F)
                ∷ mul (cnj 0F (seed 0F)) (cnj 0F (seed 0F))
                ∷ mul (cnj 2F (inv (seed 0F))) (cnj 2F (inv (seed 0F)))
                ∷ mul (cnj 18F (seed 0F)) (cnj 7F (seed 0F))
                ∷ cnj 0F (inv (seed 0F))
                ∷ mul (cnj 30F (inv (seed 0F))) (cnj 0F (inv (seed 0F)))
                ∷ mul (cnj 3F (seed 0F)) (cnj 3F (seed 0F))
                ∷ mul (cnj 26F (seed 0F)) (cnj 5F (seed 0F))
                ∷ mul (cnj 24F (inv (seed 0F))) (cnj 4F (inv (seed 0F)))
                ∷ mul (cnj 13F (seed 0F)) (cnj 4F (seed 0F))
                ∷ mul (cnj 1F (inv (seed 0F))) (cnj 1F (inv (seed 0F)))
                ∷ mul (cnj 19F (seed 0F)) (cnj 6F (seed 0F))
                ∷ mul (cnj 2F (seed 0F)) (cnj 2F (seed 0F))
                ∷ cnj 5F (seed 0F)
                ∷ cnj 4F (inv (seed 0F))
                ∷ mul (cnj 15F (seed 0F)) (cnj 0F (seed 0F))
                ∷ []

-- The same for the generator t.
a5-seed-words-t : Vec (ClosureTerm (Fin 60) 1) 59
a5-seed-words-t = cnj 45F (seed 0F)
                ∷ cnj 45F (inv (seed 0F))
                ∷ mul (cnj 0F (seed 0F)) (cnj 12F (seed 0F))
                ∷ cnj 37F (inv (seed 0F))
                ∷ cnj 36F (seed 0F)
                ∷ cnj 37F (seed 0F)
                ∷ cnj 38F (inv (seed 0F))
                ∷ mul (cnj 2F (seed 0F)) (cnj 13F (seed 0F))
                ∷ cnj 36F (inv (seed 0F))
                ∷ cnj 38F (seed 0F)
                ∷ mul (cnj 1F (seed 0F)) (cnj 14F (seed 0F))
                ∷ mul (cnj 15F (seed 0F)) (cnj 3F (seed 0F))
                ∷ mul (cnj 16F (seed 0F)) (cnj 5F (seed 0F))
                ∷ mul (cnj 17F (seed 0F)) (cnj 4F (seed 0F))
                ∷ cnj 0F (seed 0F)
                ∷ mul (cnj 4F (seed 0F)) (cnj 2F (inv (seed 0F)))
                ∷ mul (cnj 5F (seed 0F)) (cnj 1F (inv (seed 0F)))
                ∷ mul (cnj 5F (seed 0F)) (cnj 1F (inv (seed 0F)))
                ∷ cnj 2F (seed 0F)
                ∷ mul (cnj 3F (seed 0F)) (cnj 0F (inv (seed 0F)))
                ∷ mul (cnj 4F (seed 0F)) (cnj 2F (inv (seed 0F)))
                ∷ cnj 1F (seed 0F)
                ∷ mul (cnj 3F (seed 0F)) (cnj 0F (inv (seed 0F)))
                ∷ cnj 0F (inv (seed 0F))
                ∷ mul (cnj 4F (inv (seed 0F))) (cnj 2F (seed 0F))
                ∷ mul (cnj 5F (inv (seed 0F))) (cnj 1F (seed 0F))
                ∷ mul (cnj 12F (seed 0F)) (cnj 0F (seed 0F))
                ∷ cnj 6F (seed 0F)
                ∷ cnj 7F (inv (seed 0F))
                ∷ mul (cnj 22F (seed 0F)) (cnj 7F (seed 0F))
                ∷ mul (cnj 1F (inv (seed 0F))) (cnj 5F (seed 0F))
                ∷ mul (cnj 0F (seed 0F)) (cnj 3F (inv (seed 0F)))
                ∷ mul (cnj 19F (seed 0F)) (cnj 10F (seed 0F))
                ∷ mul (cnj 2F (inv (seed 0F))) (cnj 4F (seed 0F))
                ∷ mul (cnj 0F (seed 0F)) (cnj 3F (inv (seed 0F)))
                ∷ mul (cnj 5F (inv (seed 0F))) (cnj 1F (seed 0F))
                ∷ cnj 2F (inv (seed 0F))
                ∷ mul (cnj 3F (inv (seed 0F))) (cnj 0F (seed 0F))
                ∷ cnj 6F (inv (seed 0F))
                ∷ cnj 8F (seed 0F)
                ∷ mul (cnj 13F (seed 0F)) (cnj 2F (seed 0F))
                ∷ mul (cnj 2F (seed 0F)) (cnj 4F (inv (seed 0F)))
                ∷ mul (cnj 20F (seed 0F)) (cnj 11F (seed 0F))
                ∷ mul (cnj 1F (inv (seed 0F))) (cnj 5F (seed 0F))
                ∷ mul (cnj 0F (inv (seed 0F))) (cnj 3F (seed 0F))
                ∷ mul (cnj 2F (seed 0F)) (cnj 4F (inv (seed 0F)))
                ∷ mul (cnj 21F (seed 0F)) (cnj 6F (seed 0F))
                ∷ mul (cnj 4F (inv (seed 0F))) (cnj 2F (seed 0F))
                ∷ cnj 1F (inv (seed 0F))
                ∷ mul (cnj 3F (inv (seed 0F))) (cnj 0F (seed 0F))
                ∷ cnj 7F (seed 0F)
                ∷ cnj 8F (inv (seed 0F))
                ∷ mul (cnj 14F (seed 0F)) (cnj 1F (seed 0F))
                ∷ mul (cnj 1F (seed 0F)) (cnj 5F (inv (seed 0F)))
                ∷ mul (cnj 23F (seed 0F)) (cnj 8F (seed 0F))
                ∷ mul (cnj 2F (inv (seed 0F))) (cnj 4F (seed 0F))
                ∷ mul (cnj 0F (inv (seed 0F))) (cnj 3F (seed 0F))
                ∷ mul (cnj 1F (seed 0F)) (cnj 5F (inv (seed 0F)))
                ∷ mul (cnj 18F (seed 0F)) (cnj 9F (seed 0F))
                ∷ []
```
