---
layout: default
file: "src/Overture/Terms/Interpretation.lagda.md"
title: "Overture.Terms.Interpretation module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

### Theory interpretations: sending operation symbols to derived terms

This is the [Overture.Terms.Interpretation][] module of the [Agda Universal Algebra Library][].

A signature morphism `φ : SigMorphism 𝑆₁ 𝑆₂` ([Overture.Signatures.Morphisms][])
relabels each operation symbol of `𝑆₁` to an operation symbol of `𝑆₂`.
A *theory interpretation* generalizes this one decisive step: it sends each
operation symbol `o` of `𝑆₁` to a *term* of `𝑆₂` — a *derived operation* of `𝑆₂`, an
`𝑆₂`-term in the argument positions `ArityOf 𝑆₁ o` of `o`.

This is the term-valued generalization of a signature morphism, and it is exactly the
data with which universal algebra defines one variety's operations inside another
(Garcia–Taylor's "definitions"[^1]): a Maltsev term, a majority term, or a
near-unanimity term is such an assignment of one fresh symbol to a derived term.

    signature morphism φ :   o ↦ ι φ o                            (one symbol)
    interpretation     I :   o ↦ (an 𝑆₂-term over ArityOf 𝑆₁ o)   (a derived operation)

Like the signature-morphism translation `φ ✶_` ([Overture.Terms.Translation][]), an
interpretation acts on whole terms: `I ✦ t` rewrites an `𝑆₁`-term `t` into an
`𝑆₂`-term over the same variables.  The leaf clause fixes variables; the node clause
is where the generalization lives — where `φ ✶_` *relabels* the node `node f ts` to
`node (ι φ f) …`, the interpretation *substitutes* the translated subterms into the
chosen derived term `I f`.

Substitution into a term — grafting one tree onto the leaves of another — is the
operation we call `graft`{.AgdaFunction} below; it is the term monad's bind, stated
at heterogeneous variable levels (the positions `ArityOf 𝑆₁ f` live at level `𝓥`, the
term's variables at an arbitrary level `χ`), which the level-homogeneous
`Sub`{.AgdaFunction} / `_[_]`{.AgdaFunction} of [Setoid.Terms.Basic][] cannot
express.

Everything here presupposes only the signatures — no setoid, no equality on any
carrier — so it lives in `Overture/`, exactly as `Term`{.AgdaDatatype} and `φ ✶_` do.
The laws of `_✦_`{.AgdaFunction} (congruence, functoriality, the substitution square)
compare functions on positions and so require the equality-of-terms relation `_≐_`;
they are proved in [Setoid.Terms.Interpretation][].  The *equation-preserving* half
of a theory interpretation — that it carries one theory's laws into another's — needs
satisfaction and lives in [Setoid.Varieties.Interpretation][], the analogue of
[Setoid.Varieties.Invariance][] for `reduct`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Terms.Interpretation where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level ; suc ; _⊔_ )
open import Function        using ( _∘_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using  ( 𝓞 ; 𝓥 ; Signature
                                                  ; OperationSymbolsOf ; ArityOf )
open import Overture.Signatures.Morphisms  using  ( SigMorphism ; ι ; κ )
open import Overture.Terms.Basic           using  ( Term ; ℊ ; node )

private variable
  χ ξ : Level
  X : Type χ
  Y : Type ξ
  𝑆 𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥
```
-->

#### Interpretations

An `Interpretation 𝑆₁ 𝑆₂` assigns to each operation symbol `o` in `𝑆₁` an `𝑆₂`-term
over argument positions `ArityOf 𝑆₁ o`.  Reading position `i : ArityOf 𝑆₁ o` as the
variable "the `i`-th argument of `o`", the assigned term `I o` is the recipe for
computing `o` from its arguments using only `𝑆₂`-operations.

```agda
Interpretation : (𝑆₁ 𝑆₂ : Signature 𝓞 𝓥) → Type (𝓞 ⊔ suc 𝓥)
Interpretation 𝑆₁ 𝑆₂ = (o : OperationSymbolsOf 𝑆₁) → Term {𝑆 = 𝑆₂} (ArityOf 𝑆₁ o)
```

#### Grafting: substitution at heterogeneous levels

Given a term `t` and a map `σ : Y → Term {𝑆 = 𝑆} X`, the application `graft t σ`
replaces each leaf `ℊ y` of the term `t` by the term `σ y`, recursing through nodes
(the term monad's bind).  This is `_[_]`{.AgdaFunction} of [Setoid.Terms.Basic][],
but stated for variable types `Y` and `X` at independent universe levels, which is
what the interpretation action below needs: it grafts an `𝑆₂`-term over the positions
`ArityOf 𝑆₁ f` (level `𝓥`) into one over the term's own variables.

```agda
graft : Term {𝑆 = 𝑆} Y → (Y → Term {𝑆 = 𝑆} X) → Term {𝑆 = 𝑆} X
graft (ℊ y) σ = σ y
graft (node f ts) σ = node f (λ i → graft (ts i) σ)
```

#### The interpretation action on terms

Given an `𝑆₁`-`𝑆₂`-interpretation `I`, and an `𝑆₁`-term `t`,  `I ✦ t` translates `t`
to an `𝑆₂`-term over the same variables.[^2]

Variables are fixed points (`I ✦ ℊ x` is `ℊ x`, definitionally), so environments
transfer across the action unchanged.  At a node, the subterms are translated and then
grafted into the chosen derived term `I f`.

```agda
infix 15 _✦_

_✦_ : Interpretation 𝑆₁ 𝑆₂ → Term {𝑆 = 𝑆₁} X → Term {𝑆 = 𝑆₂} X
I ✦ ℊ x = ℊ x
I ✦ node f ts = graft (I f) (λ i → I ✦ ts i)
```

#### Identity, composition, and the embedding of signature morphisms

Interpretations are the morphisms of a category whose objects are signatures — the
*clone category* of algebraic theories.  The identity interpretation sends each symbol
to itself, applied to its own argument variables; composition runs an interpretation's
derived terms through a second interpretation.  (That these satisfy the category laws —
`I ✦_` is functorial in `I` — is the content of `✦-id`{.AgdaFunction} and
`✦-∘`{.AgdaFunction} in [Setoid.Terms.Interpretation][].)

```agda
idᴵ : Interpretation 𝑆 𝑆
idᴵ o = node o ℊ

infixr 9 _∘ᴵ_

_∘ᴵ_ : Interpretation 𝑆₂ 𝑆₃ → Interpretation 𝑆₁ 𝑆₂ → Interpretation 𝑆₁ 𝑆₃
(J ∘ᴵ I) o = J ✦ I o
```

Every signature morphism is an interpretation: send `o` to the single-application
derived term `node (ι φ o) (λ j → ℊ (κ φ o j))` — apply the relabelled symbol `ι φ o`
to its arguments, reindexed back through `κ φ o`.  This is the inclusion of `Sig`
([Overture.Signatures.Morphisms][]) into the clone category, and `✦-⟨⟩`{.AgdaFunction}
([Setoid.Terms.Interpretation][]) checks that the embedded interpretation acts on terms
exactly as `φ ✶_` does, so theory interpretations strictly generalize signature
morphisms.

```agda
⟨_⟩ᴵ : SigMorphism 𝑆₁ 𝑆₂ → Interpretation 𝑆₁ 𝑆₂
⟨ φ ⟩ᴵ o = node (ι φ o) (ℊ ∘ (κ φ o))
```

--------------------------------------

[^1]: W. D. Neumann; O. C. García and W. Taylor, *The Lattice of Interpretability Types of Varieties*, Mem. Amer. Math. Soc. **50** (1984), no. 305.

[^2]: **Unicode tip**.  Type `\st` and select `✦` to get the four-pointed star; it is the `_✶_` of [Overture.Terms.Translation][] "thickened", since `_✦_` generalizes `_✶_` from one application to an arbitrary derived term.
