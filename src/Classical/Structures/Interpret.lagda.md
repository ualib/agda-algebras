---
layout: default
file: "src/Classical/Structures/Interpret.lagda.md"
title: "Classical.Structures.Interpret module"
date: "2026-05-22"
author: "the agda-algebras development team"
---

### Interpretation congruence — the one shared η-bridge primitive {#classical-structures-interpret}

This is the [Classical.Structures.Interpret][] module of the [Agda Universal Algebra Library][].

Every `<Structure>-Op` module must bridge two views of an operation applied to
arguments: the *term-interpretation* form `⟦ node f args ⟧ ⟨$⟩ η`, in which the
arguments arrive as a tuple `ArityOf 𝑆 f → 𝕌`, and the *curried* form
`(⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)`, in which they arrive one at a time.  Under
`--cubical-compatible` the two argument-tuples agree pointwise but not
definitionally (no η on `Fin n`-pattern lambdas), so the bridge is a `cong` over
the interpretation function with a pointwise witness.

The *only* signature-generic content of that bridge is the congruence step itself:
`interp-cong` below.  It is symbol-agnostic and arity-agnostic, takes no arity
proof, and carries no `subst`.  It is the common core of `∙-cong` (binary
congruence) and of every `interp-nodeₙ` lemma.

**Per-structure convention (normative).**  Each `<Structure>-Op` module defines its
own named `interp-nodeₙ` family — `interp-node∙` (binary), `interp-node₀`
(nullary, for an identity element `ε-Op`), `interp-node⁻¹` (unary, for an inverse
`⁻¹-Op`) — over *its own* signature's terms, each a one-liner delegating to
`interp-cong`.  These cannot be pulled into this module: their statements mention
the concrete operation symbols of a particular signature, and `node f (pair s t)`
only type-checks when `ArityOf 𝑆 f` reduces definitionally to `Fin 2`, which holds
only at a concrete signature.  Stating the binary case generically would force a
`refl`-match of the neutral `ArityOf 𝑆 f` against `Fin 2`, rejected by the
without-K unifier.  Hence: the *congruence* is shared here; the *family* is named
per signature.  See [ADR-002 v2 §1, §5](../../docs/adr/002-classical-layer-design.md).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Interpret where

-- Imports from the Agda Standard Library -----------------------------------------
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Data.Product                           using ( _,_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Overture                using ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Signatures     using ( OperationSymbolsOf ; ArityOf )
open import Setoid.Algebras.Basic   using ( Algebra ; 𝔻[_] ; 𝕌[_] ; _^_ )

open Func renaming ( to to _⟨$⟩_ )
open Algebra using ( Interp )

private variable α ρ : Level
```
-->

`interp-cong 𝑨 f u≈v` says: applying the `𝑨`-interpretation of `f` to two
argument-tuples that agree pointwise yields setoid-equal results.  The proof is
`Func.cong (Interp 𝑨)` fed the `⟨ 𝑆 ⟩`-equivalence `(≡.refl , u≈v)` — a `refl` on
the operation-symbol component (same symbol) paired with the pointwise argument
witness.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra α ρ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

  interp-cong : (f : OperationSymbolsOf 𝑆) {u v : ArityOf 𝑆 f → 𝕌[ 𝑨 ]}
              → (∀ i → u i ≈ v i) → (f ^ 𝑨) u ≈ (f ^ 𝑨) v
  interp-cong f u≈v = cong (Interp 𝑨) (refl , u≈v)
```
