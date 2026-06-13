---
layout: default
file: "src/Setoid/Terms/Translation.lagda.md"
title: "Setoid.Terms.Translation module"
date: "2026-06-12"
author: "the agda-algebras development team"
---

#### Laws of term translation

This is the [Setoid.Terms.Translation][] module of the [Agda Universal Algebra Library][].

The translation `φ ✶ t` of terms along a signature morphism is defined in
[Overture.Terms.Translation][], where it needs nothing but the signatures.
Its laws, proved here, compare functions on node positions (`λ i → …`) and therefore
live at the level of the equality-of-terms relation `_≐_` of [Setoid.Terms.Basic][]
— the same division of labor as `Term` (Overture) versus `𝑻 X` and `_≐_` (Setoid).
None of the laws below can be strengthened to propositional `_≡_` under `--safe`:
each compares position functions that agree pointwise but are not definitionally
equal, which is exactly the situation `_≐_` exists for.

Together the laws say that `_✶_` is as well-behaved as it could possibly be — it is
a *functorial family of monad morphisms*:

+  `✶-cong`{.AgdaFunction} — translation respects term equality, so `φ ✶_` is a
   setoid function between term setoids (`✶-func`{.AgdaFunction} packages it as a
   `Func`).
+  `✶-id`{.AgdaFunction} and `✶-∘`{.AgdaFunction} — translating along the identity
   morphism changes nothing, and translating along a composite is translating twice:
   the assignment `φ ↦ φ ✶_` is a functor from the category `Sig` of signatures
   ([Overture.Signatures.Morphisms][]) to term-setoid endomaps.  This lifts the
   functoriality of `⟦_⟧` (single applications, [Setoid.Signatures.Functor][])
   from one operation deep to arbitrarily deep terms.
+  `✶-sub`{.AgdaFunction} — the *monad morphism* square: translating after
   substituting is substituting after translating,

   ```text
                       _[ σ ]
        Term₁ Y ──────────────────────→ Term₁ X

           │                             │
      φ ✶_ │                             │ φ ✶_
           ↓                             ↓
        Term₂ Y ──────────────────────→ Term₂ X
                 _[ (λ y → φ ✶ σ y) ]
   ```

   where the bottom edge substitutes the *translated* terms.  In monad vocabulary
   ([Setoid.Terms.Monad][]), `φ ✶_` commutes with the units (definitionally —
   `φ ✶ ℊ x` is `ℊ x`) and with the multiplications (this square), which is the
   definition of a morphism between the term monads of `𝑆₁` and `𝑆₂`.  Equivalently,
   it is a functor between their Kleisli categories that is the identity on objects.

Looking one subissue ahead: M4-5f's *theory interpretations* replace the
symbol-to-symbol `ι` by a symbol-to-derived-term assignment, and `✶-sub` is the law
that makes interpretations compose — substitute first or interpret first, same
result.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Terms.Translation where

open import Agda.Primitive                 using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Function                       using ( Func )
open import Level                          using ( Level )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Signatures.Morphisms  using ( SigMorphism ; ι ; κ ; id-morphism ; _∘ₛ_ )
open import Overture.Terms                 using ( Term ; ℊ ; node )
open import Overture.Terms.Translation     using ( _✶_ )
open import Setoid.Terms.Basic             using ( _≐_ ; ≐-isRefl ; Sub ; _[_] ; TermSetoid )

open _≐_ using ( rfl ; gnl )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  χ : Level
  X Y : Type χ
```

##### Congruence: translation is a setoid function

Equal terms translate to equal terms.  The leaf case is immediate (translation fixes
variables); at a node, the inductive hypotheses are consulted at the *reindexed*
positions, mirroring the `node` clause of `_✶_` itself.

```agda
module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} {φ : SigMorphism 𝑆₁ 𝑆₂} where

  ✶-cong : {s t : Term {𝑆 = 𝑆₁} X} → s ≐ t → (φ ✶ s) ≐ (φ ✶ t)
  ✶-cong (rfl x≡y) = rfl x≡y
  ✶-cong (gnl {f = f} ps) = gnl (λ j → ✶-cong (ps (κ φ f j)))

  -- The packaged form: translation as a map of term setoids.
  ✶-func : (X : Type χ) → Func (TermSetoid {𝑆 = 𝑆₁} X) (TermSetoid {𝑆 = 𝑆₂} X)
  ✶-func X ⟨$⟩ t = φ ✶ t
  ✶-func X .cong = ✶-cong
```

##### The monad-morphism square

Translation commutes with substitution.  (It commutes with the units by definition:
`φ ✶ ℊ x` reduces to `ℊ x`.)

```agda
  ✶-sub : (t : Term {𝑆 = 𝑆₁} Y) (σ : Sub {𝑆 = 𝑆₁} X Y)
    → φ ✶ t [ σ ] ≐ (φ ✶ t) [ (λ y → φ ✶ σ y) ]
  ✶-sub (ℊ y) σ = ≐-isRefl
  ✶-sub (node f ts) σ = gnl (λ j → ✶-sub (ts (κ φ f j)) σ)
```

##### Functoriality in the signature morphism

Translating along the identity signature morphism is the identity (up to `_≐_` — the
node clause rebuilds the position function, so the two sides are pointwise, not
definitionally, equal), and translating along a composite is the composite of the
translations.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where

  ✶-id : (t : Term {𝑆 = 𝑆} X) → (id-morphism ✶ t) ≐ t
  ✶-id (ℊ x) = ≐-isRefl
  ✶-id (node f ts) = gnl (λ i → ✶-id (ts i))


module _ {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥} {φ : SigMorphism 𝑆₁ 𝑆₂} {ψ : SigMorphism 𝑆₂ 𝑆₃} where

  ✶-∘ : (t : Term {𝑆 = 𝑆₁} X) → ψ ∘ₛ φ ✶ t ≐ ψ ✶ (φ ✶ t)
  ✶-∘ (ℊ x) = ≐-isRefl
  ✶-∘ (node f ts) = gnl (λ i → ✶-∘ (ts (κ φ f (κ ψ (ι φ f) i))))
```

--------------------------------------

{% include UALib.Links.md %}
