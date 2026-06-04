---
layout: default
file: "src/Classical/Operations.lagda.md"
title: "Classical.Operations module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Operations on classical structures — curry/uncurry between tuple-indexed and curried form

This is the [Classical.Operations][] module of the [Agda Universal Algebra Library][].

The foundational layer of `agda-algebras` represents an `I`-ary operation on a carrier `A` as a function `(I → A) → A`.  This tuple-indexed form is non-negotiable in the universal-algebra meta-theory: variety closure operators, the term algebra as a W-type, Birkhoff's HSP theorem, and the equational-logic substrate (`Modᵗ`) all recurse on arity and require operations in this form.

The user-facing layer of `Classical/` — every accessor that consumers of a classical structure actually read at use sites — exposes operations in *curried* form: a binary operation as `A → A → A`, a nullary operation as `A`, a unary operation as `A → A`.  This is the form working algebraists write (`x ∙ y`, not `pair x y 0F · pair x y 1F`) and the form that supports straightforward partial application, sectioning, and infix syntax.

This module provides the bridge: per-arity `Curry`/`Uncurry` helpers that translate between the two forms.  They are written once here and reused by every per-structure file across the `Classical/` tree.  The Fin n η-failure under `--cubical-compatible` is contained inside `Uncurry₂` / `Curry₂` and similar — per-structure files never write `pair`-style argument wrappers inline; the wrapping is the responsibility of this module alone.

See [ADR-002 v2 §1](../../docs/adr/002-classical-layer-design.md) for the design rationale.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Operations where

-- Imports from Agda and the Agda Standard Library ----------------------
open import Agda.Primitive    using ()             renaming ( Set to Type )
open import Data.Fin.Base     using ( Fin )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Level             using ( Level )

private variable
  α : Level
  A : Type α
```

#### Operation types

The type `Op I A` of `I`-ary operations on `A`, in tuple-indexed form.  Arity first, carrier second: this orders parameters from "less likely to vary" to "more likely to vary," which is the right convention for partial application — `Op (Fin 2)` partially applies as "binary operation," independent of any carrier.

```agda
Op : {𝓥 : Level} → Type 𝓥 → Type α → Type _
Op I A = (I → A) → A
```

#### Two-element argument tuple

The canonical `Fin 2 → A` constructed from two elements.  Used internally by `Uncurry₂` and as the bridge target in bundle conversion functions.  Made public for the rare per-structure use case (e.g., expressing a tuple-indexed `(∙-Op ^ 𝑨) (pair a b)` directly when the curried form is inconvenient).

```agda
pair : A → A → Fin 2 → A
pair a b 0F = a
pair a b 1F = b
```

#### Curry and Uncurry, per arity

The translation between tuple-indexed and curried operations.  Each pair is a two-line definition; the obligation that they form a definitional inverse on the curried side (`Curry₂ (Uncurry₂ f) ≡ f` as functions `A → A → A → A`) holds by `refl`.  The reverse direction (`Uncurry₂ (Curry₂ f) ≡ f` as `(Fin 2 → A) → A`) holds *pointwise* but not definitionally as functions, because the lack of η on `Fin 2`-pattern lambdas under `--cubical-compatible` prevents the lambda repackaging from collapsing.  This asymmetry is contained here and surfaced as the pointwise round-trip statement in per-structure bundle bridges (per [ADR-002 v2 §6](docs/adr/002-classical-layer-design.md)).

```agda
-- Nullary
Curry₀ : Op (Fin 0) A → A
Curry₀ f = f λ ()

Uncurry₀ : A → Op (Fin 0) A
Uncurry₀ a _ = a

-- Unary.  Note: Fin 1 has a single inhabitant 0F, and `Curry₁ f a` ignores
-- the index argument because there is only one possible value.
Curry₁ : Op (Fin 1) A → (A → A)
Curry₁ f a = f λ _ → a

Uncurry₁ : (A → A) → Op (Fin 1) A
Uncurry₁ f args = f (args 0F)

-- Binary
Curry₂ : Op (Fin 2) A → (A → A → A)
Curry₂ f a b = f (pair a b)

Uncurry₂ : (A → A → A) → Op (Fin 2) A
Uncurry₂ _·_ args = args 0F · args 1F
```

Higher arities (`Curry₃` / `Uncurry₃` for ternary, etc.) are added as concrete structures require them.  Lattice's absorption law (in M3-7) may want `Curry₃`; deferred until then.

--------------------------------------

<span style="float:left;">[← Classical](Classical.html)</span>
<span style="float:right;">[Classical.Equations →](Classical.Equations.html)</span>

{% include UALib.Links.md %}
