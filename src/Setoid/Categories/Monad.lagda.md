---
layout: default
file: "src/Setoid/Categories/Monad.lagda.md"
title: "Setoid.Categories.Monad module"
date: "2026-06-12"
author: "the agda-algebras development team"
---

### Monads on a minimal category

This is the [Setoid.Categories.Monad][] module of the [Agda Universal Algebra Library][].

A *monad* is the categorical abstraction of the notion of

> a formal expression that can be nested and then flattened.

It consists of an endofunctor `T : 𝐂 → 𝐂` — read `T A` as "formal expressions over `A`"
— together with two natural transformations:

+  the **unit** `η : Id ⟹ T`, which regards a plain `A` as a trivial expression
   (a variable is already a term; an element is already a `just`-value);
+  the **multiplication** `μ : T ∘ T ⟹ T`, which flattens an expression
   *whose leaves are themselves expressions* into a single expression (substituting
   terms for variables; collapsing `Maybe (Maybe A)` to `Maybe A`).

Three laws make the metaphor exact, and each says something a working algebraist
already believes about substitution.  Writing `μ_A : T (T A) → T A` for the
component at `A`:

```text
            T η_A                  η_{T A}                     T μ_A
      T A ────────→ T (T A)    T A ────────→ T (T A)    T³ A ─────────→ T² A

          ╲         │             ╲          │          │               │
           ╲        │ μ_A          ╲         │ μ_A      │ μ_{T A}       │ μ_A
        id  ╲       │            id ╲        │          │               │
             ╲      │                ╲       │          │               │
              ╲     │                 ╲      │          │               │
               ╲    │                  ╲     │          │               │
                ↘   ↓                  ↘     ↓          ↓               ↓
                 T A                      T A         T² A ─────────→  T A
                                                               μ_A
```

+  `identityˡ` (left triangle): wrapping every *leaf* as a trivial expression and then
   flattening changes nothing — substituting the variable `x` for each variable `x` is
   the identity substitution.
+  `identityʳ` (right triangle): wrapping the *whole expression* as a trivial
   expression-of-expressions and flattening changes nothing.
+  `assoc` (the square): given three layers of nesting, flattening the inner two layers
   first or the outer two layers first yields the same result — exactly the
   associativity of substitution composition.

The slogan "a monad is a monoid in the category of endofunctors" is visible in the
field names: `μ` is the multiplication, `η` the unit, and the laws are the monoid
laws, written with `∘` because the elements being multiplied are functors.

This record is the M4-5e extension of the self-contained ADR-006 vocabulary, built on
[`NaturalTransformation`][Setoid.Categories.NaturalTransformation] exactly as
promised by the footnote of [Setoid.Categories.Adjunction][]: the unit and
multiplication are *bundled* natural transformations (so their naturality squares come
packaged), while the three monad laws are stated componentwise against `𝐂`'s
hom-equality — the same convention as `Adjunction`'s componentwise fields, and for the
same reason: componentwise statements are what instances can prove pointwise under
`--safe`, with no function extensionality.

Two instances anchor the abstraction in this library:

+  **From an adjunction.**  Every adjunction `L ⊣ R` induces a monad on the domain of
   `L`, with `T = R ∘F L`, unit the adjunction's unit, and multiplication obtained by
   running the counit inside `R`.  This is proved in general below
   (`adjunction→monad`{.AgdaFunction}) and instantiated in
   [Classical.Categories.AdjoinUnit][]: adjoining a unit to a semigroup and then
   forgetting down again is a monad on the category of semigroups (the "`Maybe` monad
   on semigroups").
+  **The term monad** — the motivating example, where `T X` is the type of terms over
   variables `X`, `η` is the generator injection `ℊ`, and `μ` is substitution.  In a
   predicative universe hierarchy `Term` *raises levels* (`Term X : Type (ov χ)` for
   `X : Type χ`), so it is not an endofunctor of any one category `Setoid α ρ` and
   cannot inhabit this record; it is a *relative* monad, and its laws are stated in
   the equivalent Kleisli form in [Setoid.Terms.Monad][].  See
   `docs/notes/m4-5e-term-monad.md` for why this is a fact about predicativity, not a
   defect of the formalization.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.Monad where

open import Agda.Primitive  using ( _⊔_ ) renaming ( Set to Type )
open import Level           using ( Level )

open import Setoid.Categories.Category               using ( Category )
open import Setoid.Categories.Functor                using ( Functor ; idF ; _∘F_ )
open import Setoid.Categories.NaturalTransformation  using ( NaturalTransformation )
open import Setoid.Categories.Adjunction             using ( Adjunction )

private variable o ℓ e o′ ℓ′ e′ : Level
```
-->

#### The record

```agda
record Monad (𝐂 : Category o ℓ e) : Type (o ⊔ ℓ ⊔ e) where
  open Category 𝐂 using (_≈_ ; _∘_ ) renaming (Hom to 𝐂[_,_]; id to idC; Obj to 𝐂₀)

  field
    T     : Functor 𝐂 𝐂
    unit  : NaturalTransformation (idF {𝐂 = 𝐂}) T
    mult  : NaturalTransformation (T ∘F T) T

  -- Component shorthands: η_A : A ⟶ T A and μ_A : T (T A) ⟶ T A.
  open Functor T renaming ( F₀ to T₀ ; F₁ to T₁ ) public

  η : (A : 𝐂₀) → 𝐂[ A , T₀ A ]
  η = NaturalTransformation.component unit

  μ : (A : 𝐂₀) → 𝐂[ T₀ (T₀ A) , T₀ A ]
  μ = NaturalTransformation.component mult

  field
    -- Flattening three layers from the inside or from the outside agrees.
    assoc : (A : 𝐂₀) → μ A ∘ T₁ (μ A) ≈ μ A ∘ μ (T₀ A)

    -- Wrapping each leaf trivially, then flattening, is the identity.
    identityˡ : (A : 𝐂₀) → μ A ∘ T₁ (η A) ≈ idC

    -- Wrapping the whole expression trivially, then flattening, is the identity.
    identityʳ : (A : 𝐂₀) → μ A ∘ η (T₀ A) ≈ idC
```

#### Every adjunction induces a monad

This is the classical Huber/Eilenberg–Moore observation, and it is the bridge from
the free-expansion adjunction of M4-5d to the monad vocabulary of M4-5e.  Given
`L ⊣ R` with unit `η` and counit `ε`, the composite `T = R ∘F L` is a monad on `𝐂`:

+  the monad unit is the adjunction unit `η_A : A ⟶ R (L A)`;
+  the multiplication is the counit, transported into `𝐂` by `R`:
   `μ_A = R₁ (ε_{L A}) : R (L (R (L A))) ⟶ R (L A)` — flattening means "evaluate the
   inner formal layer with the counit."

The intuition for the proof obligations: everything about `μ` is a statement about
`ε` wearing an `R₁` coat.  Each proof below therefore has the same three moves —
collect the two `R₁`s into one (`homomorphism`, read right to left), rewrite inside
`R₁` using a fact about the counit (its naturality, or a triangle identity), and
redistribute.  The monad's right unit law needs no moves at all: it *is* the `zag`
triangle identity, on the nose.

```agda
module _
  {𝐂 : Category o ℓ e} {𝐃 : Category o′ ℓ′ e′}
  {L : Functor 𝐂 𝐃} {R : Functor 𝐃 𝐂}
  (adj : Adjunction L R)
  where
  open Category 𝐂 using ( ≈-sym ; ≈-trans )
  open Functor L using () renaming ( F₀ to L₀ ; F₁ to L₁ )
  open Functor R using ( F-resp-≈ ; identity ; homomorphism ) renaming ( F₁ to R₁ )
  open Adjunction adj

  adjunction→monad : Monad 𝐂
  adjunction→monad = record
    { T     = R ∘F L
    ; unit  = record  { component = unit ; natural = unit-natural }
    ; mult  = record  { component = λ A → R₁ (ε (L₀ A))

                        -- Naturality of μ: push both R₁s together, apply the counit's
                        -- naturality square inside R₁, and split them apart again.
                      ; natural = λ f → ≈-trans  (≈-sym homomorphism)
                                                 (≈-trans  (F-resp-≈ (counit-natural (L₁ f)))
                                                           homomorphism)
                      }

    -- In R₁, the two flattenings differ by the counit's naturality square taken at ε itself.
    ; assoc = λ A → ≈-trans  (≈-sym homomorphism)
                             (≈-trans  (F-resp-≈ (counit-natural (counit (L₀ A))))
                                       homomorphism)

    -- In R₁, the composite is the zig triangle, which collapses to the id; R₁ id is id.
    ; identityˡ  = λ A → ≈-trans (≈-sym homomorphism) (≈-trans (F-resp-≈ (zig A)) identity)

    -- This is literally the zag triangle identity at L₀ A.
    ; identityʳ  = λ A → zag (L₀ A)
    }
```

For the reader meeting this for the first time, it is worth unwinding `identityʳ` by
hand once: the law asks for

    μ_A ∘ η_{T A} ≈ id

i.e. `R₁ (ε_{L A}) ∘ η_{R (L A)} ≈ id`, and that is *exactly* the `zag` field of the
adjunction at the object `L₀ A` — the triangle identities of an adjunction are the
unit laws of its monad; this is no accident and is the historical origin of both.
