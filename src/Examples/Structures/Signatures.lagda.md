---
layout: default
title : "Examples.Structures.Signatures module (Agda Universal Algebra Library)"
date : "2021-07-16"
author: "agda-algebras development team"
---

### Example signatures for general structures

This is the [Examples.Structures.Signatures][] module of the [Agda Universal Algebra Library][].

Eight tiny signatures for the general `structure` type of the frozen `Legacy.Base`
tree, named by an arity-counting convention: position `k` of the digit string
counts the symbols of arity `k`, so `S001` has one binary symbol and `S111` has one
nullary, one unary, and one binary.  They give the structure examples of
[Examples.Structures.Basic][] and the finite-CSP exercises of
[Exercises.Complexity.FiniteCSP][] something concrete to instantiate.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Structures.Signatures where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Empty                    using () renaming ( ⊥ to 𝟘 )
open import Data.Unit.Base                using () renaming ( ⊤ to 𝟙 ; tt to 𝟎 )
open import Level                         using () renaming ( 0ℓ to ℓ₀ )

open import Overture                      using ( 𝟚 ; 𝟛 )
open import Legacy.Base.Structures.Basic  using ( signature )
```
-->


#### Examples of finite signatures

Each is a `signature` record whose `symbol` type is `𝟘`, `𝟙`, `𝟚`, or `𝟛` and
whose arity map sends a symbol to the finite type of its argument positions: `S∅`
(no symbols, so bare sets), `S1` (one constant, pointed sets), `S01` (one unary),
`S001` (one binary, magmas and their kin), `S0001` (one ternary, the NAE-3-SAT
relation), `S021` (two unary and one binary), `S101` (one constant and one binary,
monoids), and `S111` (one constant, one unary, and one binary, groups).

```agda
-- The signature with...

-- ... no symbols  (e.g., sets)
S∅ : signature ℓ₀ ℓ₀
S∅ = record { symbol = 𝟘 ; arity = λ () }

-- ... one nullary symbol (e.g., pointed sets)
S1 : signature ℓ₀ ℓ₀
S1 = record { symbol = 𝟙 ; arity = λ _ → 𝟘 }

S01 : signature ℓ₀ ℓ₀ -- ...one unary
S01 = record { symbol = 𝟙 ; arity = λ _ → 𝟙 }

-- ...one binary symbol (e.g., magmas, semigroups, semilattices)
S001 : signature ℓ₀ ℓ₀
S001 = record { symbol = 𝟙 ; arity = λ _ → 𝟚 }

-- ...one ternary symbol (e.g., boolean NAE-3-SAT relational structure)
S0001 : signature ℓ₀ ℓ₀
S0001 = record { symbol = 𝟙 ; arity = λ _ → 𝟛 }

-- ...0 nullary, 2 unary, and 1 binary
S021 : signature ℓ₀ ℓ₀
S021 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟚 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟙 } }

-- ...one nullary and one binary (e.g., monoids)
S101 : signature ℓ₀ ℓ₀
S101 = record { symbol = 𝟚 ; arity = λ{ 𝟚.𝟎 → 𝟘 ; 𝟚.𝟏 → 𝟚 } }

-- ...one nullary, one unary, and one binary (e.g., groups)
S111 : signature ℓ₀ ℓ₀
S111 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟘 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟚 } }
```
