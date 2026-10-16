---
layout: default
file: "src/Setoid/Algebras/Finite.lagda.md"
title: "Setoid.Algebras.Finite module (The Agda Universal Algebra Library)"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Finite setoid algebras

This is the [Setoid.Algebras.Finite][] module of the [Agda Universal Algebra Library][].

This module defines the finiteness interface for setoid algebras.  The record
`FiniteAlgebra`{.AgdaRecord} `𝑨` bundles decidable setoid equality on the carrier of
`𝑨` with a finite, surjective enumeration of that carrier.  (It says nothing about
the congruences of `𝑨`; it is carrier-level data only.)

Two design points deserve comment.

+  **The enumeration is surjective, not bijective**.  A map `Fin card → 𝕌[ 𝑨 ]`
   hitting every element up to `≈` is exactly what downstream constructions need in
   order to *search* the carrier and to *count*; e.g., counting the pairs related by a
   congruence in [Setoid.Subalgebras.Subdirect.Finite][].  Demanding injectivity as
   well would burden every instance with distinctness proofs that no consumer uses,
   so `card`{.AgdaField} is an upper bound on, not the exact size of, the carrier.

+  **Decidable `≈` is a separate field**.  Surjective enumerability of a setoid
   carrier does not imply decidability of its equality, so the interface must ask
   for both.

The name `FiniteAlgebra`{.AgdaRecord} is deliberately reserved for this bare
interface.  Finite-algebra theorems about the *congruence lattice* — for instance
Birkhoff's subdirect representation theorem for finite algebras — need strictly more
than carrier finiteness: a complete, decidable enumeration of the congruences, which
carrier finiteness cannot supply constructively.  That stronger, logically
independent interface is `FiniteCongruences`{.AgdaRecord}, defined in
[Setoid.Congruences.Finite][]; the two are consumed together in
[Setoid.Subalgebras.Subdirect.Finite][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Algebras.Finite  where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Base         using ( Fin ; zero )
open import Data.Fin.Properties   using ( all? ; any? )
open import Data.Nat.Base         using ( ℕ )
open import Data.Product          using ( _,_  ; ∃-syntax ; proj₁ ; proj₂ )
open import Data.Unit.Base        using ( ⊤ ; tt )
open import Function              using ( Func )
open import Level                 using ( Level ; _⊔_ ; 0ℓ )
open import Relation.Binary       using ( Setoid )
open import Relation.Nullary      using ( Dec ; yes )
open import Relation.Nullary.Decidable.Core  using ( map′ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture               using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic  using ( Algebra ; 𝕌[_] ; 𝔻[_] )

open Algebra  using ( Domain ; Interp )
open Func     using ( cong ) renaming ( to to _⟨$⟩_ )
open Relation.Binary.IsEquivalence

private variable α ρ ℓ : Level
```
-->

#### The bare finiteness interface

A **finite algebra** is an algebra together with a decision procedure for its setoid
equality and a surjective enumeration of its carrier by a finite index type.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
  record FiniteAlgebra (𝑨 : Algebra {𝑆 = 𝑆} α ρ) : Type (α ⊔ ρ) where
    open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
    field
      _≟_       : ∀ x y → Dec (x ≈ y)      -- decidable setoid equality carrier of 𝑨
      card      : ℕ
      enum      : Fin card → 𝕌[ 𝑨 ]       -- finite enumeration of the carrier
      enum-sur  : ∀ x → ∃[ i ] enum i ≈ x  -- that hits every element, up to ≈
  open FiniteAlgebra
```

#### Non-vacuity: the one-element algebra is finite

The record is genuine, computational data, so we exhibit an inhabitant.  The
one-element algebra `𝟏`{.AgdaFunction} over the ambient signature has carrier `⊤`,
trivial setoid equality, and each operation constantly `tt`; its finiteness witness
is immediate.[^1]

```agda
-- The one-element algebra over the signature 𝑆.
  open Setoid

  𝟏 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ
  𝟏 .Domain .Carrier        = ⊤
  𝟏 .Domain ._≈_            = λ _ _ → ⊤
  𝟏 .Domain .isEquivalence  = record  { refl   = tt
                                      ; sym    = λ _ → tt
                                      ; trans  = λ _ _ → tt }
  𝟏 .Interp ⟨$⟩ _           = tt
  𝟏 .Interp .cong _         = tt

  -- The one-element algebra is a finite algebra.
  𝟏-FiniteAlgebra : FiniteAlgebra 𝟏
  𝟏-FiniteAlgebra ._≟_       = λ _ _ → yes tt
  𝟏-FiniteAlgebra .card      = 1
  𝟏-FiniteAlgebra .enum      = λ _ → tt
  𝟏-FiniteAlgebra .enum-sur  = λ _ → zero , tt
```

#### Deciding a universal statement by sweeping the enumeration

The enumeration is what turns a universally quantified property of a finite algebra
into a finite computation.  Let `P`{.AgdaBound} be a property of triples of elements
that *respects* `≈`: whenever `a ≈ a'`, `b ≈ b'`, and `c ≈ c'`, the instance
`P a b c` implies `P a' b' c'`.  If `P`{.AgdaBound} holds at every triple of
enumerated elements, then it holds at every triple, since every element is equal
to an enumerated one (`enum-all³`{.AgdaFunction}).  Conversely, a property that
holds everywhere holds at the enumerated elements.  So when each instance of
`P`{.AgdaBound} is decidable, the universal statement is decided by a sweep of
`card³` instances (`all³?`{.AgdaFunction}), three nested calls of the standard
library's `all?`{.AgdaFunction} on `Fin card`, whose answer is transported along
the two implications.  The binary form `all²?`{.AgdaFunction} decides a
universal statement about pairs, and `exists?`{.AgdaFunction} decides an
existential one, `∃ a, P a`, by the standard library's `any?`{.AgdaFunction}:
a witness among the enumerated elements is a witness, and any witness `a` has an
enumerated stand-in `enum i ≈ a`.  The quadruple forms `enum-all⁴`{.AgdaFunction} and
`all⁴?`{.AgdaFunction} are the same with one more quantifier; they decide, for
instance, Whitman's condition on a finite lattice (in a separate repository,
which builds on this library).  Because
surjectivity is all the sweep uses, an enumeration that repeats elements only
repeats work.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑭 : FiniteAlgebra 𝑨) where
  open FiniteAlgebra 𝑭  using ( card ; enum ; enum-sur )
  open Setoid 𝔻[ 𝑨 ]    using ( _≈_ ) renaming ( sym to ≈sym )

  enum-all² : (P : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ)
    → (∀ {a a' b b'} → a ≈ a' → b ≈ b' → P a b → P a' b')
    → (∀ i j → P (enum i) (enum j)) → ∀ a b → P a b
  enum-all² P resp h a b =
    resp (proj₂ (enum-sur a)) (proj₂ (enum-sur b)) (h (proj₁ (enum-sur a)) (proj₁ (enum-sur b)))

  all²? : (P : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ)
    → (∀ {a a' b b'} → a ≈ a' → b ≈ b' → P a b → P a' b')
    → (∀ a b → Dec (P a b)) → Dec (∀ a b → P a b)
  all²? P resp P? =
    map′ (enum-all² P resp) (λ h i j → h (enum i) (enum j)) (all? λ i → all? λ j → P? (enum i) (enum j))

  exists? : (P : 𝕌[ 𝑨 ] → Type ℓ) → (∀ {a a'} → a ≈ a' → P a → P a')
    → (∀ a → Dec (P a)) → Dec (∃[ a ] P a)
  exists? P resp P? =
    map′ (λ (i , p) → enum i , p) (λ (a , p) → proj₁ (enum-sur a) , resp (≈sym (proj₂ (enum-sur a))) p)
         (any? λ i → P? (enum i))

  enum-all³ : (P : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ)
    → (∀ {a a' b b' c c'} → a ≈ a' → b ≈ b' → c ≈ c' → P a b c → P a' b' c')
    → (∀ i j k → P (enum i) (enum j) (enum k)) → ∀ a b c → P a b c
  enum-all³ P resp h a b c =
    resp (proj₂ (enum-sur a)) (proj₂ (enum-sur b)) (proj₂ (enum-sur c))
         (h (proj₁ (enum-sur a)) (proj₁ (enum-sur b)) (proj₁ (enum-sur c)))

  all³? : (P : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ)
    → (∀ {a a' b b' c c'} → a ≈ a' → b ≈ b' → c ≈ c' → P a b c → P a' b' c')
    → (∀ a b c → Dec (P a b c)) → Dec (∀ a b c → P a b c)
  all³? P resp P? =
    map′ (enum-all³ P resp) (λ h i j k → h (enum i) (enum j) (enum k))
         (all? λ i → all? λ j → all? λ k → P? (enum i) (enum j) (enum k))

  enum-all⁴ : (P : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ)
    → (∀ {a a' b b' c c' d d'} → a ≈ a' → b ≈ b' → c ≈ c' → d ≈ d' → P a b c d → P a' b' c' d')
    → (∀ i j k l → P (enum i) (enum j) (enum k) (enum l)) → ∀ a b c d → P a b c d
  enum-all⁴ P resp h a b c d =
    resp (proj₂ (enum-sur a)) (proj₂ (enum-sur b)) (proj₂ (enum-sur c)) (proj₂ (enum-sur d))
         (h (proj₁ (enum-sur a)) (proj₁ (enum-sur b)) (proj₁ (enum-sur c)) (proj₁ (enum-sur d)))

  all⁴? : (P : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ)
    → (∀ {a a' b b' c c' d d'} → a ≈ a' → b ≈ b' → c ≈ c' → d ≈ d' → P a b c d → P a' b' c' d')
    → (∀ a b c d → Dec (P a b c d)) → Dec (∀ a b c d → P a b c d)
  all⁴? P resp P? =
    map′ (enum-all⁴ P resp) (λ h i j k l → h (enum i) (enum j) (enum k) (enum l))
         (all? λ i → all? λ j → all? λ k → all? λ l → P? (enum i) (enum j) (enum k) (enum l))
```

--------------------------------------

[^1]:  The finiteness witness of the congruence lattice of 𝟏 is
       `𝟏-FiniteCongruences`{.AgdaFunction} in [Setoid.Congruences.Finite][] which,
       together with the witness `𝟏-FiniteAlgebra`{.AgdaFunction}, is consumed by
       Birkhoff's theorem for finite algebras in [Setoid.Subalgebras.Subdirect.Finite][].
