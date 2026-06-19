---
layout: default
file: "src/Setoid/Varieties/FreeSubstitution.lagda.md"
title: "Setoid.Varieties.FreeSubstitution module"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### A substitution kit for derivable equality

This is the [Setoid.Varieties.FreeSubstitution][] module of the [Agda Universal Algebra Library][].

Substitution `_[_]` ([Setoid.Terms.Basic][]) pushes into a node *pointwise*,

    (node f ts) [ σ ] = node f (λ i → ts i [ σ ]).

When `ts` is a finite tuple written as a pattern-matching lambda, say,
`λ { 0F → s ; 1F → t }`, the natural way to write a binary term is, e.g.,
`s · t = node ∙-Op (λ { 0F → s ; 1F → t })`.

Unfortunately, the result `node f (λ i → ts i [ σ ])` is not definitionally equal to
a freshly *rebuilt* term

    s [ σ ] · t [ σ ] = node ∙-Op (λ { 0F → s [ σ ] ; 1F → t [ σ ] }),

since a pattern-matching lambda does not reduce under a variable index `i`, and
bridging the two position functions needs function extensionality, which is
unavailable under `--safe` / `--cubical-compatible`.[^1]

The practical bite is that the obvious way to instantiate an equation at *compound*
terms fails: `sub (hyp i) σ` produces a goal in `_[ σ ]`-form that will not match a
readable, rebuilt term, so a multi-step rewrite like a four-fold reassociation cannot
be written directly.

The fix is small, because the bookkeeping half of the kit is already proved: the
`_≐_`-level laws `[]-unitˡ` (left unit, the issue's `[]-ℊ`), `[]-unitʳ`, `[]-assoc`,
and `[]-cong` live in [Setoid.Terms.Monad][] and are re-exported here so the kit
reads from one place.  What is added here is the bridge between the two equalities on
terms — the inductive equality `_≐_` of [Setoid.Terms.Basic][] and the *derivable*
equality `_⊢_▹_≈_` of [Setoid.Varieties.SoundAndComplete][]:

+  `≐→⊢`{.AgdaFunction} — every `_≐_`-equality is derivable.  Two terms that are
   `_≐_` (same shape, equal variables at the leaves) are equal in *every* equational
   theory, by `refl` at the leaves and the congruence rule `app` at the nodes.  This
   is exactly the tool for rewriting a `_[ σ ]`-form into the rebuilt term it agrees
   with pointwise: the rebuild is a `_≐_`-fact (a finite, mechanical `gnl` /
   `≐-isRefl` match), and `≐→⊢` turns it into a derivation step.
+  `sub▹`{.AgdaFunction} — instantiate a derivation at a substitution and land on
   *readable* end terms.  It packages `sub` between two `≐→⊢` bridges, so a consumer
   writes `sub▹ d σ l≐pσ qσ≐r` and gets `E ⊢ Γ ▹ l ≈ r` directly.

The worked four-fold reassociation that motivated the substitution kit is in
[Examples.Setoid.FreeSemigroup][], built from one application of `sub▹` (a generic
`assoc▹` that instantiates associativity at arbitrary subterms) plus the congruence rule.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.FreeSubstitution {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )

import Relation.Binary.PropositionalEquality as ≡

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Terms                      {𝑆 = 𝑆} using ( Term )
open import Setoid.Terms.Basic                  {𝑆 = 𝑆} using ( _≐_ ; Sub ; _[_] )
open import Setoid.Varieties.SoundAndComplete   {𝑆 = 𝑆} using ( Eq ; _⊢_▹_≈_ )

-- The bookkeeping laws (proved in Setoid.Terms.Monad) re-exported for one-stop access.
-- The issue's `[]-ℊ` is `[]-unitˡ`; its `[]-∘` is `[]-assoc`.
open import Setoid.Terms.Monad {𝑆 = 𝑆}
  using ( _⊙ˢ_ ; []-unitˡ ; []-unitˡ-ptw ; []-unitʳ ; []-assoc ; []-cong ) public

open _≐_         using ( rfl ; gnl )
open _⊢_▹_≈_     using ( app ; sub ; refl ; trans )

private variable
  χ ι : Level
  Γ Δ : Type χ
  I   : Type ι
```

#### Derivable equality refines term equality

Every `_≐_`-equality is derivable in any theory `E`.  The leaf case is the reflexivity
rule (the variables are equal, so the terms are literally equal); the node case is the
congruence rule `app` applied to the inductive hypotheses at the positions.  No clause
inspects the equation set `E`, so this holds uniformly.

```agda
≐→⊢ : {E : I → Eq} {s t : Term Γ} → s ≐ t → E ⊢ Γ ▹ s ≈ t
≐→⊢ (rfl ≡.refl)  = refl
≐→⊢ (gnl ps)      = app (λ i → ≐→⊢ (ps i))
```

#### Instantiating a derivation at compound terms

`sub▹ d σ` substitutes `σ` into a derivation `d : E ⊢ Δ ▹ p ≈ q` and rewrites both ends
to readable terms supplied by the caller: given `l ≐ p [ σ ]` and `q [ σ ] ≐ r`, it
returns `E ⊢ Γ ▹ l ≈ r`.  This is the clean way to use an equation at compound terms —
the `_≐_` arguments are the mechanical "rebuild" bridges, and `sub▹` hides the
`_[ σ ]`-form behind them.

```agda
sub▹ : {E : I → Eq} {p q : Term Δ} (d : E ⊢ Δ ▹ p ≈ q) (σ : Sub Γ Δ)
       {l r : Term Γ} → l ≐ p [ σ ] → q [ σ ] ≐ r → E ⊢ Γ ▹ l ≈ r
sub▹ d σ l≐pσ qσ≐r = trans (≐→⊢ l≐pσ) (trans (sub d σ) (≐→⊢ qσ≐r))
```

--------------------------------------

[^1]: This is the same `Fin n` η-gap that the M4-5 development meets repeatedly; see [ADR-002][] §6.


[M4-10]: https://github.com/ualib/agda-algebras/issues/362

{% include UALib.Links.md %}
