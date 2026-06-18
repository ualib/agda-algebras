---
layout: default
file: "src/Overture/Terms/Translation.lagda.md"
title: "Overture.Terms.Translation module"
date: "2026-06-12"
author: "the agda-algebras development team"
---

### Translating terms along a signature morphism

This is the [Overture.Terms.Translation][] module of the [Agda Universal Algebra Library][].

A signature morphism `φ : SigMorphism 𝑆₁ 𝑆₂` ([Overture.Signatures.Morphisms][])
relabels operation symbols (`ι φ`, covariantly) and reindexes argument positions
(`κ φ`, contravariantly).  This module extends that relabelling from single symbols
to whole *terms*: the translation `φ ✶ t` rewrites an `𝑆₁`-term `t` into an
`𝑆₂`-term over the same variables, leaf by leaf and node by node.

The definition is exactly the structural recursion one would guess, and it is worth
reading the `node` clause slowly because the contravariance of `κ` is where all the
content lives.  A node `node f ts` of an `𝑆₁`-term carries one subterm `ts i` for
each position `i : ArityOf 𝑆₁ f`.  Its translation is a node labelled `ι φ f`, which
must carry one subterm for each position `j : ArityOf 𝑆₂ (ι φ f)` — a position of
the *target* symbol.  The position map `κ φ f` converts such a `j` back into a
source position `κ φ f j`, and the translated subterm at `j` is the translation of
`ts (κ φ f j)`:

```text
   𝑆₁-term:        node f ts          with subterms   ts i ,        i : ArityOf 𝑆₁ f
                      │
                      │  φ ✶_
                      ↓
   𝑆₂-term:   node (ι φ f) ts′        with subterms   ts′ j = φ ✶ ts (κ φ f j) ,
                                                                j : ArityOf 𝑆₂ (ι φ f)
```

In the typical case of a signature *inclusion* — `ι` injective, each `κ φ f` the
identity, as in `Sig-Magma ↪ Sig-Monoid` — the translation simply re-reads a magma
term such as `(x ∙ y) ∙ z` as the same expression in the monoid signature.  That
"same expression, richer signature" reading is what makes the translation the
syntactic half of the *reduct*: `reduct φ` moves algebras from `𝑆₂` to `𝑆₁`
([Setoid.Algebras.Reduct][]), `φ ✶_` moves terms from `𝑆₁` to `𝑆₂`, and the
two are adjoint in the logical sense that satisfaction is invariant —
`reduct φ 𝑨 ⊧ s ≈ t` iff `𝑨 ⊧ φ ✶ s ≈ φ ✶ t` ([Setoid.Varieties.Invariance][]).
In the vocabulary of M4-5b, `φ ✶_` is the unique extension of the natural
transformation `⟦ φ ⟧ : ⟨ 𝑆₁ ⟩ ⟹ ⟨ 𝑆₂ ⟩` from single applications to free
`P_{𝑆₁}`-algebras; in monad vocabulary it is a *morphism of term monads*, a fact
recorded (up to `_≐_`) in [Setoid.Terms.Translation][].

Like `Term` itself, the translation presupposes only the signatures — no setoid, no
equality on any carrier — so it lives in `Overture/`.  Its laws (functoriality in
`φ`, congruence, and the substitution square) require the equality-of-terms relation
`_≐_` and are therefore stated in [Setoid.Terms.Translation][], mirroring the
`Overture.Terms` / `Setoid.Terms.Basic` split.  M4-5f will generalize precisely this
definition: a *theory interpretation* sends operation symbols to derived operations
(terms) rather than to symbols, and its action on terms replaces the `node` clause's
relabelling by substitution into the chosen derived term.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Terms.Translation where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                 using () renaming ( Set to Type )
open import Level                          using ( Level )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Signatures.Morphisms  using ( SigMorphism ; ι ; κ )

import Overture.Terms.Basic as Terms

private variable
  χ : Level
  X : Type χ
```

#### The translation

The two signatures are instantiated by module application; `Term₁ X` and
`Term₂ X` are the term types over the same variable type `X`.[^1]

```agda
module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} where
  open Terms {𝑆 = 𝑆₁} using () renaming (ℊ to ℊ₁; node to node₁; Term to Term₁)
  open Terms {𝑆 = 𝑆₂} using () renaming (ℊ to ℊ₂; node to node₂; Term to Term₂)
  infix 15 _✶_

  _✶_ : SigMorphism 𝑆₁ 𝑆₂ → Term₁ X → Term₂ X
  φ ✶ ℊ₁ x = ℊ₂ x
  φ ✶ node₁ f ts = node₂ (ι φ f) (λ j → φ ✶ ts (κ φ f j))
```

Variables are fixed points of the translation (`φ ✶ ℊ x` is `ℊ x`, definitionally),
which is what lets environments transfer across it unchanged: interpreting `φ ✶ t`
needs values for exactly the variables that interpreting `t` needs.  The
reduct-invariance theorem leans on this directly.

--------------------------------------

[^1]: **Unicode tip**.  Type `\st` and select `✶` to get the star.


{% include UALib.Links.md %}
