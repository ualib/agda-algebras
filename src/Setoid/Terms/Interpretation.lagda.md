---
layout: default
file: "src/Setoid/Terms/Interpretation.lagda.md"
title: "Setoid.Terms.Interpretation module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

#### Laws of the interpretation action

This is the [Setoid.Terms.Interpretation][] module of the [Agda Universal Algebra Library][].

The interpretation action `I ✦ t` of a theory interpretation on terms is defined in
[Overture.Terms.Interpretation][], where it needs nothing but the signatures.  Its
laws, proved here, compare functions on node positions (`λ i → …`) and so live at the
level of the equality-of-terms relation `_≐_` of [Setoid.Terms.Basic][] — the same
division of labour as `Term` (Overture) versus `𝑻 X` and `_≐_` (Setoid), and exactly as
for the signature-morphism translation `_✶_` ([Setoid.Terms.Translation][]).  None can
be strengthened to propositional `_≡_` under `--safe`: each compares position functions
that agree pointwise but not definitionally.

The laws come in two layers.  First, three facts about `graft`{.AgdaFunction} — the
heterogeneous-level substitution `I ✦_` is built from — that mirror the term monad's
own laws ([Setoid.Terms.Monad][]):

+  `graft-cong`{.AgdaFunction} — grafting respects pointwise term equality of the
   substitution.
+  `graft-assoc`{.AgdaFunction} — grafting in two stages equals grafting once by the
   composite (associativity of bind).
+  `graft-sub`{.AgdaFunction} — grafting commutes with substitution `_[_]`.

Then the laws of `_✦_`{.AgdaFunction} proper, which say it is a *functorial family of
monad morphisms*, exactly as `_✶_`'s laws do — only now the functor runs over the
larger *clone category* of interpretations rather than the signature category `Sig`:

+  `✦-cong`{.AgdaFunction} — the action respects term equality, so `I ✦_` is a setoid
   function between term setoids (`✦-func`{.AgdaFunction} packages it as a `Func`).
+  `✦-id`{.AgdaFunction} and `✦-∘`{.AgdaFunction} — the identity interpretation acts as
   the identity, and a composite interpretation acts as the composite of the actions:
   `I ↦ I ✦_` is functorial.  This is the composability law the milestone calls for —
   the interpretation-level analogue of `✶-∘`, and what makes the interpretability
   quasi-order transitive ([Setoid.Varieties.Interpretation][]).
+  `✦-sub`{.AgdaFunction} — the *monad-morphism* square: interpreting after substituting
   is substituting (the interpreted terms) after interpreting.  This is the direct
   generalization of `✶-sub`, and it is what lets an interpretation carry a *derivation*
   (which uses the substitution rule of equational logic), not merely an equation.
+  `✦-⟨⟩`{.AgdaFunction} — the interpretation `⟨ φ ⟩ᴵ` induced by a signature morphism
   acts exactly as `φ ✶_`, confirming that interpretations strictly generalize signature
   morphisms.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Terms.Interpretation where

open import Agda.Primitive                 using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Function                       using ( Func )
open import Level                          using ( Level )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Signatures.Morphisms  using ( SigMorphism ; ι ; κ )
open import Overture.Terms                  using ( Term ; ℊ ; node )
open import Overture.Terms.Translation      using ( _✶_ )
open import Overture.Terms.Interpretation   using ( Interpretation ; graft ; _✦_
                                                  ; idᴵ ; _∘ᴵ_ ; ⟨_⟩ᴵ )
open import Setoid.Terms.Basic             using ( _≐_ ; ≐-isRefl ; ≐-isSym ; ≐-isTrans
                                                 ; Sub ; _[_] ; TermSetoid )

open _≐_ using ( rfl ; gnl )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  χ ξ ζ : Level
  X Y : Type χ      -- a same-level pair, for the homogeneous Sub / _[_]
  U : Type ξ        -- an independent-level variable type (positions of a symbol)
  V : Type ζ
  𝑆 𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥
```

##### Laws of `graft`

Grafting respects pointwise term equality of the substitution: replacing each leaf by
an equal term gives an equal result.

```agda
graft-cong : (u : Term {𝑆 = 𝑆} U) {σ τ : U → Term {𝑆 = 𝑆} X}
  → (∀ y → σ y ≐ τ y) → graft u σ ≐ graft u τ
graft-cong (ℊ y)       p = p y
graft-cong (node f ts) p = gnl (λ i → graft-cong (ts i) p)
```

Grafting in two stages is grafting once by the composite — associativity of the bind.
The leaf case is definitional (a single lookup either way); the node case recurses.

```agda
graft-assoc : (u : Term {𝑆 = 𝑆} V) (α : V → Term {𝑆 = 𝑆} U) (β : U → Term {𝑆 = 𝑆} X)
  → graft (graft u α) β ≐ graft u (λ z → graft (α z) β)
graft-assoc (ℊ z)       α β = ≐-isRefl
graft-assoc (node f ts) α β = gnl (λ i → graft-assoc (ts i) α β)
```

Grafting commutes with substitution: substituting `β` into a graft equals grafting the
`β`-substituted terms.  (Both are instances of associativity, with one side a
same-level substitution `_[_]`; we state it separately because `_✦_`'s monad-morphism
square consumes exactly this form.)

```agda
graft-sub : (u : Term {𝑆 = 𝑆} U) (ρ : U → Term {𝑆 = 𝑆} X) (β : Sub {𝑆 = 𝑆} Y X)
  → graft u (λ y → (ρ y) [ β ]) ≐ (graft u ρ) [ β ]
graft-sub (ℊ y)       ρ β = ≐-isRefl
graft-sub (node f ts) ρ β = gnl (λ i → graft-sub (ts i) ρ β)
```

##### Functoriality at the identity

Interpreting along the identity interpretation changes nothing (up to `_≐_` — the node
clause rebuilds the position function).

```agda
✦-id : (t : Term {𝑆 = 𝑆} X) → (idᴵ ✦ t) ≐ t
✦-id (ℊ x)       = ≐-isRefl
✦-id (node f ts) = gnl (λ i → ✦-id (ts i))
```

##### Congruence and the monad-morphism square

Everything from here fixes an interpretation `I`.  Congruence makes `I ✦_` a setoid
function; the leaf case fixes variables, the node case consults the inductive
hypotheses at the grafted positions.

```agda
module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (I : Interpretation 𝑆₁ 𝑆₂) where

  ✦-cong : {s t : Term {𝑆 = 𝑆₁} X} → s ≐ t → (I ✦ s) ≐ (I ✦ t)
  ✦-cong (rfl x≡y)        = rfl x≡y
  ✦-cong (gnl {f = f} ps) = graft-cong (I f) (λ i → ✦-cong (ps i))

  -- The packaged form: the interpretation action as a map of term setoids.
  ✦-func : (X : Type χ) → Func (TermSetoid {𝑆 = 𝑆₁} X) (TermSetoid {𝑆 = 𝑆₂} X)
  ✦-func X ⟨$⟩ t = I ✦ t
  ✦-func X .cong = ✦-cong
```

Translation commutes with substitution: interpreting `t [ σ ]` equals substituting the
*interpreted* assignment `λ y → I ✦ σ y` into `I ✦ t`.  (It commutes with the units by
definition, since `I ✦ ℊ x` reduces to `ℊ x`.)  This is the monad-morphism square — the
generalization of `✶-sub` — proved by reducing the node case to `graft-sub`.

```text
                    _[ σ ]
     Term₁ Y ──────────────────────→ Term₁ X

        │                             │
   I ✦_ │                             │ I ✦_
        ↓                             ↓
     Term₂ Y ──────────────────────→ Term₂ X
              _[ (λ y → I ✦ σ y) ]
```

```agda
  ✦-sub : (t : Term {𝑆 = 𝑆₁} Y) (σ : Sub {𝑆 = 𝑆₁} X Y)
    → I ✦ (t [ σ ]) ≐ (I ✦ t) [ (λ y → I ✦ σ y) ]
  ✦-sub (ℊ y)       σ = ≐-isRefl
  ✦-sub (node f ts) σ =
    ≐-isTrans (graft-cong (I f) (λ i → ✦-sub (ts i) σ))
              (graft-sub  (I f) (λ i → I ✦ ts i) (λ y → I ✦ σ y))
```

##### Interpreting a graft

The action of an interpretation `J` is itself a graft homomorphism — it commutes with
grafting.  This is the lemma the composition law turns on, and its node case is a
`graft-assoc` rearrangement.

```agda
module _ {𝑆₂ 𝑆₃ : Signature 𝓞 𝓥} (J : Interpretation 𝑆₂ 𝑆₃) where

  ✦-graft : (u : Term {𝑆 = 𝑆₂} U) (ρ : U → Term {𝑆 = 𝑆₂} X)
    → J ✦ (graft u ρ) ≐ graft (J ✦ u) (λ y → J ✦ ρ y)
  ✦-graft (ℊ y)       ρ = ≐-isRefl
  ✦-graft (node f us) ρ =
    ≐-isTrans (graft-cong (J f) (λ i → ✦-graft (us i) ρ))
              (≐-isSym (graft-assoc (J f) (λ i → J ✦ us i) (λ y → J ✦ ρ y)))
```

##### Functoriality at a composite

Interpreting along a composite `J ∘ᴵ I` is interpreting twice.  This is the
composability law: together with `✦-id` it makes `I ↦ I ✦_` a functor from the clone
category to term-setoid endomaps, and it underwrites transitivity of the
interpretability quasi-order.

```agda
module _ {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥}
         (J : Interpretation 𝑆₂ 𝑆₃) (I : Interpretation 𝑆₁ 𝑆₂) where

  ✦-∘ : (t : Term {𝑆 = 𝑆₁} X) → ((J ∘ᴵ I) ✦ t) ≐ (J ✦ (I ✦ t))
  ✦-∘ (ℊ x)       = ≐-isRefl
  ✦-∘ (node f ts) =
    ≐-isTrans (graft-cong (J ✦ I f) (λ i → ✦-∘ (ts i)))
              (≐-isSym (✦-graft J (I f) (λ i → I ✦ ts i)))
```

##### Signature morphisms as interpretations

The interpretation `⟨ φ ⟩ᴵ` induced by a signature morphism acts on terms exactly as
the translation `φ ✶_` does.  So `_✦_` genuinely subsumes `_✶_`, and the
interpretability quasi-order below extends the reduct/satisfaction story of
[Setoid.Varieties.Invariance][] to derived operations.

```agda
module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) where

  ✦-⟨⟩ : (t : Term {𝑆 = 𝑆₁} X) → (⟨ φ ⟩ᴵ ✦ t) ≐ (φ ✶ t)
  ✦-⟨⟩ (ℊ x)       = ≐-isRefl
  ✦-⟨⟩ (node f ts) = gnl (λ j → ✦-⟨⟩ (ts (κ φ f j)))
```

--------------------------------------

{% include UALib.Links.md %}
