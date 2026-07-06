---
layout: default
file: "src/Setoid/Varieties/Maltsev/Basic.lagda.md"
title: "Setoid.Varieties.Maltsev.Basic module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

### The Maltsev condition as a theory interpretation

This is the [Setoid.Varieties.Maltsev.Basic][] module of the [Agda Universal Algebra Library][].

A **Maltsev condition** is a property of a variety equivalent to the existence of
terms satisfying prescribed identities.  The three most basic concern the shape of
the congruence lattices of the algebras in the variety:

+  **congruence permutability** (CP) — composition of congruences is commutative;
+  **congruence distributivity** (CD) — every congruence lattice is distributive;
+  **congruence modularity** (CM) — every congruence lattice is modular.

A **Maltsev term** for a variety `𝒱` is a ternary term `m` satisfying

    m(x, x, y) ≈ y      and      m(x, y, y) ≈ x,

and a variety has such a term exactly when it is CP.

This is the original *Maltsev condition* and it is quintessential universal algebra —
a property of an arbitrary variety, phrased over an arbitrary signature, with no
commitment to any particular structure.

This module fixes the abstract data of the condition and frames it as a theory
interpretation ([Setoid.Varieties.Interpretation][]): the one-ternary-symbol
signature `Sig-Maltsev`, the two-equation theory `Th-Maltsev`, and the predicate
`HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ`.  "`ℰ` admits a Maltsev term" is exactly
"the Maltsev theory interprets into `ℰ`".

A *worked* example — that `x ∙ (y ⁻¹ ∙ z)` is a Maltsev term for the variety
of groups — is structure-specific (it consumes the group operations and laws), so it
lives one layer up, in [Classical.Interpretations.Maltsev][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev.Basic where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Bool.Base     using ( Bool ; true ; not )
open import Data.Fin.Base      using ( Fin )
open import Data.Fin.Patterns  using ( 0F ; 1F ; 2F )
open import Data.Nat.Base      using ( ℕ ; zero ; suc )
open import Data.Product       using ( _×_ ; _,_ ; proj₂ )
open import Level              using ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures              using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic            using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic         using ( Con ; is-compatible )
open import Setoid.Terms.Basic               using ( _[_] ; module Environment )
open import Setoid.Varieties.Interpretation  using ( module Interpret )
import Overture.Terms as Terms

open import Function using ( Func )
open Func using () renaming ( to to _⟨$⟩_ )

private variable α ρ χ ℓ : Level
```
-->

#### The Maltsev signature and theory

`Sig-Maltsev` has a single ternary operation symbol; `Th-Maltsev` carries the two
Maltsev equations over the variable carrier `Fin 3` (`0F` for `x`, `1F` for `y`).

```agda
data Op-Maltsev : Type where
  m-Op : Op-Maltsev

ar-Maltsev : Op-Maltsev → Type
ar-Maltsev m-Op = Fin 3

Sig-Maltsev : Signature 0ℓ 0ℓ
Sig-Maltsev = Op-Maltsev , ar-Maltsev

-- The canonical 3-element tuple, as a *named* function (not an extended lambda),
-- so the worked-instance proofs can refer to it definitionally.
tri : {ℓ : Level} {A : Type ℓ} → A → A → A → Fin 3 → A
tri a b c 0F = a
tri a b c 1F = b
tri a b c 2F = c

module _ where
  open Terms {𝑆 = Sig-Maltsev} using ( Term ; ℊ ; node )
  -- the ternary application m(a, b, c) as a Sig-Maltsev term
  m : {X : Type} → Term X → Term X → Term X → Term X
  m a b c = node m-Op (tri a b c)

  private
    x y z : Term (Fin 3)
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F

  data Eq-Maltsev : Type where
    mxxy≈y mxyy≈x : Eq-Maltsev

  Th-Maltsev : Eq-Maltsev → Term (Fin 3) × Term (Fin 3)
  Th-Maltsev mxxy≈y = m x x y , y   -- m(x, x, y) ≈ y
  Th-Maltsev mxyy≈x = m x y y , x   -- m(x, y, y) ≈ x
```

#### The Maltsev condition

A theory `ℰ` (equivalently, its variety) *has a Maltsev term* (equivalently, is
congruence-permutable) exactly when the Maltsev theory interprets into it.  This is
the clean, signature-agnostic statement of the condition; a concrete variety
satisfies it by exhibiting an interpretation `Th-Maltsev ≼ ℰ`, that is, an `ℰ`-term
witnessing the two Maltsev equations.

The target theory's signature is fixed at `(0ℓ , 0ℓ)`, matching `Sig-Maltsev` (the
interpretability relation `≼` relates theories over a common level pair); this is
no restriction for the finitary algebraic theories the Maltsev condition concerns.

```agda
module _
  {α ρ χ ι  : Level}
  {𝑆        : Signature 0ℓ 0ℓ}
  {X        : Type χ}
  {Idx      : Type ι}
  where
  open Terms {𝑆 = 𝑆} using (Term)

  HasMaltsevTerm : (Idx → Term X × Term X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
  HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ
    where open Interpret α ρ
```

#### Miscellaneous prerequisites

Maltsev arguments rely on the fact that the chosen Maltsev *term operation*
respects every congruence.  This is an instance of a fundamental fact, which we prove
once in full generality: Given an algebra `𝑩` and a term `t` in the signature of `𝑩`,
every congruence `ψ` of `𝑩` is compatible with the evaluation of `t` — if two
environments are pointwise `ψ`-related at the leaves, the values of `t` are
`ψ`-related.  The proof is the obvious structural induction.

```agda
module _
  {𝑆 : Signature 𝓞 𝓥}
  {𝑩 : Algebra {𝑆 = 𝑆} α ρ}
  where
  open Environment 𝑩 using ( ⟦_⟧ )
  open Terms {𝑆 = 𝑆} using (Term ; ℊ ; node)

  term-compatible : {V : Type χ } ((_ψ_ , _) : Con 𝑩 ℓ )
    (t : Term V ) {η η′     : V → 𝕌[ 𝑩 ] }
    → (∀ v → (η v) ψ (η′ v)) → (⟦ t ⟧ ⟨$⟩ η) ψ (⟦ t ⟧ ⟨$⟩ η′)
  term-compatible _ (ℊ v) h = h v
  term-compatible ψ (node f ts) h = is-compatible (ψ .proj₂) f (λ i → term-compatible ψ (ts i) h)
```

Finally, a function indicating the parity of a natural number is needed to split the
Jónsson/Day "fork" identities by index in [Setoid.Varieties.Maltsev.Distributivity][]
and [Setoid.Varieties.Maltsev.Modularity][].

```agda
even? : ℕ → Bool
even? zero = true
even? (suc m) = not (even? m)
```
