---
layout: default
file: "src/Setoid/Algebras/Products/Finite.lagda.md"
title: "Setoid.Algebras.Products.Finite module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### Finiteness of finite powers

This is the [Setoid.Algebras.Products.Finite][] module of the [Agda Universal Algebra Library][].

A finite power of a finite algebra is finite.  This module discharges the
`FiniteAlgebra`{.AgdaRecord} interface of [Setoid.Algebras.Finite][] for the
constant-family product `⨅ (λ (_ : Fin n) → 𝑨)`{.AgdaFunction} of
[Setoid.Algebras.Products][] — the *power* `𝑨ⁿ` — from a finiteness witness for
the base algebra `𝑨`{.AgdaBound}:

+  **decidable equality** is decided coordinatewise, by a finite conjunction of
   base-level decisions (`all?`{.AgdaFunction});
+  **the enumeration** of the `cardⁿ` tuples is the standard library's positional
   base-`card` encoding `finToFun`{.AgdaFunction}, composed with the base
   enumeration coordinatewise;
+  **surjectivity** holds *pointwise up to `≈`* — which is exactly the setoid
   equality of the product — with no appeal to function extensionality: the
   round-trip law `finToFun-funToFin`{.AgdaFunction} is itself pointwise.

The first consumer is the Kurzweil–Netter duality proof (issue #502), which
needs the power `Sᵐ` of a finite group to be a finite algebra so that the coset
algebra on `Sᵐ/D` inherits finiteness through
`cosetAlgebra-FiniteAlgebra`{.AgdaFunction} of
[Classical.Structures.Group.GSet][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Products.Finite where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base        using ( Fin ; finToFun ; funToFin )
open import Data.Fin.Properties  using ( all? ; finToFun-funToFin )
open import Data.Nat.Base        using ( ℕ ; _^_ )
open import Data.Product         using ( _,_ ; proj₁ ; proj₂ )
open import Level                using ( Level )
open import Relation.Binary      using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( cong )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture                  using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic     using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite    using ( FiniteAlgebra )
open import Setoid.Algebras.Products  using ( ⨅ )

private variable α ρ : Level
```
-->

#### The finiteness witness for a power

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} {n : ℕ}
         (𝑭 : FiniteAlgebra 𝑨) where

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; trans ) renaming ( reflexive to ≈-reflexive )
  open FiniteAlgebra 𝑭 using ( _≟_ ; card ; enum ; enum-sur )

  private
    𝑷 : Algebra {𝑆 = 𝑆} α ρ
    𝑷 = ⨅ {I = Fin n} (λ _ → 𝑨)

    -- The tuple encoded by an index: base enumeration after digit extraction.
    penum : Fin (card ^ n) → 𝕌[ 𝑷 ]
    penum ν i = enum (finToFun ν i)

    -- The index encoding a tuple: the digits are the base indices of its values.
    pidx : 𝕌[ 𝑷 ] → Fin (card ^ n)
    pidx x = funToFin (λ i → proj₁ (enum-sur (x i)))

    -- The round trip hits the tuple coordinatewise, up to ≈.
    penum-pidx : (x : 𝕌[ 𝑷 ]) (i : Fin n) → penum (pidx x) i ≈ x i
    penum-pidx x i = trans
      (≈-reflexive (cong enum (finToFun-funToFin (λ j → proj₁ (enum-sur (x j))) i)))
      (proj₂ (enum-sur (x i)))

  -- A finite power of a finite algebra is finite.
  power-FiniteAlgebra : FiniteAlgebra 𝑷
  power-FiniteAlgebra = record
    { _≟_       = λ x y → all? (λ i → x i ≟ y i)
    ; card      = card ^ n
    ; enum      = penum
    ; enum-sur  = λ x → pidx x , penum-pidx x
    }
```

--------------------------------------
