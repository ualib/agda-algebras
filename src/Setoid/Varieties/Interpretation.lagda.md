---
layout: default
file: "src/Setoid/Varieties/Interpretation.lagda.md"
title: "Setoid.Varieties.Interpretation module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

### Theory interpretations and the interpretability quasi-order

This is the [Setoid.Varieties.Interpretation][] module of the [Agda Universal Algebra Library][].

This module is to a theory interpretation what [Setoid.Varieties.Invariance][] is to
a signature morphism.  Where the latter packages a `SigMorphism` as a `reduct` with
respect to which satisfaction is an invariant, here we package an *interpretation*
([Overture.Terms.Interpretation][]) as a `reductᴵ`{.AgdaFunction} and prove the
generalized satisfaction condition; we then use it to define the
**interpretability quasi-order** on equational theories and to record its reflexivity
and transitivity.

#### The interpretation reduct

For an interpretation `I : 𝑆₁ → 𝑆₂` and an `𝑆₂`-algebra `𝑩`, the
*interpretation reduct* `reductᴵ I 𝑩` is the `𝑆₁`-algebra on the same carrier in
which each operation symbol `o` of `𝑆₁` is interpreted by the **derived operation**
`I o` — that is, by evaluating the `𝑆₂`-term `I o` in `𝑩`, reading the arguments as
the values of the argument positions of `o`.

When `I = ⟨ φ ⟩ᴵ` comes from a signature morphism, `reductᴵ I 𝑩` is the ordinary
`reduct φ 𝑩` (`reductᴵ-⟨⟩`{.AgdaFunction} below, by `refl`), so this is the
term-valued generalization of [`reduct`][Setoid.Algebras.Reduct].

#### The satisfaction condition

The pay-off is the generalized satisfaction condition: for `𝑆₁`-terms `s , t`,

    reductᴵ I 𝑩 ⊧ s ≈ t   if and only if   𝑩 ⊧ (I ✦ s) ≈ (I ✦ t).

To check an `𝑆₁`-equation against the derived view of `𝑩` is to check the
*interpreted* equation against `𝑩` itself.  It is the shadow of one commuting
triangle of interpretation maps — naturality of the fold along the interpretation —
exactly as in [Setoid.Varieties.Invariance][], only now the node step
*grafts a derived term* rather than relabelling a symbol, and the proof leans on the
heterogeneous evaluation lemma `graft-eval`{.AgdaFunction} (evaluation commutes with
`graft`) in place of the definitional `reduct` step.  (As there, no clause matches a
concrete `Fin n`, so the without-K unifier is never asked to invert anything.)

#### The quasi-order

An equational theory `ℰ₁` of `𝑆₁` is *interpretable in* a theory `ℰ₂` of `𝑆₂`,
written `ℰ₁ ≼ ℰ₂`, when some interpretation carries every model of `ℰ₂` (via its
reduct) to a model of `ℰ₁`.  By the satisfaction condition this is the same as asking
that every `ℰ₁`-equation, *interpreted*, be a consequence of `ℰ₂`.

This is the universal algebraist's notion of one variety interpreting another, whose
order-reflection is the Garcia–Taylor lattice of interpretability types.[^1]

Reflexivity is the identity interpretation and transitivity is composition `_∘ᴵ_`;
the proofs are short *because* `✦-id` and `✦-∘` ([Setoid.Terms.Interpretation][])
already did the work, fed through the satisfaction condition.

This connects forward to planned formalizing work related to the Bodirsky–Pinsker
program, where interpretability between (infinite-domain) clones is the governing
relation.[^2]

A worked Maltsev-term instance is in [Classical.Interpretations.Maltsev][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Interpretation where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                 using () renaming ( Set to Type )
open import Data.Product                   using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Function                       using ( Func )
open import Level                          using ( Level )
open import Relation.Binary                using ( Setoid )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using  ( 𝓞 ; 𝓥 ; Signature
                                                  ; OperationSymbolsOf )
open import Overture.Signatures.Morphisms  using  ( SigMorphism )
open import Overture.Terms                 using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation  using  ( Interpretation ; graft ; _✦_
                                                  ; idᴵ ; _∘ᴵ_ ; ⟨_⟩ᴵ )
open import Setoid.Algebras.Basic          using  ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Reduct         using  ( reduct )
open import Setoid.Terms.Basic             using  ( _≐_ ; ≐-isSym ; module Environment )
open import Setoid.Terms.Interpretation    using  ( ✦-id ; ✦-∘ )

import Setoid.Varieties.EquationalLogic as EqLogic

open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  α ρ χ ι : Level
  X : Type χ
  𝑆 𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥
  χ₁ χ₂ χ₃ ι₁ ι₂ ι₃ : Level
```

#### Two single-algebra lemmas

Everything in this block fixes one algebra `𝑨`.  First, satisfaction respects the
term equality `_≐_` on both sides.  (This is the convenience lemma we anticipated
consumers would want; the interpretability proofs are that consumer.)

```agda
module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra {𝑆 = 𝑆} α ρ) where
  open Environment 𝑨 using ( ⟦_⟧ ; ≐→Equal )
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open EqLogic {𝑆 = 𝑆} using ( _⊧_≈_ )

  ⊧-≐ : {s s′ t t′ : Term {𝑆 = 𝑆} X}
    → s ≐ s′ → t ≐ t′ → 𝑨 ⊧ s ≈ t → 𝑨 ⊧ s′ ≈ t′
  ⊧-≐ {s = s} {s′} {t} {t′} s≐s′ t≐t′ A⊧ η =
    ≈trans (≈sym (≐→Equal s s′ s≐s′ η)) (≈trans (A⊧ η) (≐→Equal t t′ t≐t′ η))
```

Second, term evaluation commutes with `graft`: evaluating a grafted term is
evaluating the host term in the environment that first evaluates each grafted
subtree.  This is the heterogeneous-level analogue of the `substitution` lemma of
[Setoid.Terms.Basic][], and it is the node step of the interpretation triangle below.

```agda
  graft-eval : {ξ : Level} {U : Type ξ}
    (u : Term {𝑆 = 𝑆} U) (σ : U → Term {𝑆 = 𝑆} X) (η : X → 𝕌[ 𝑨 ])
    → ⟦ graft u σ ⟧ ⟨$⟩ η ≈ ⟦ u ⟧ ⟨$⟩ (λ y → ⟦ σ y ⟧ ⟨$⟩ η)
  graft-eval (ℊ y)       σ η = ≈refl
  graft-eval (node f us) σ η = cong (Algebra.Interp 𝑨) (refl , λ i → graft-eval (us i) σ η)
```

#### The interpretation reduct and the satisfaction condition

Now fix an interpretation `I` and an `𝑆₂`-algebra `𝑩`.  The reduct keeps the carrier
and interprets each `𝑆₁`-symbol `o` by evaluating `I o` (a derived operation), so its
`cong` is the congruence of that evaluation.

```agda
module _
  {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥}
  (𝑩 : Algebra {𝑆 = 𝑆₂} α ρ)
  where
  module _
    (I : Interpretation 𝑆₁ 𝑆₂)
    where
    private module EnvB = Environment 𝑩
    open EnvB using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
    open Algebra using (Domain ; Interp)

    reductᴵ : Algebra {𝑆 = 𝑆₁} α ρ
    reductᴵ .Domain = 𝔻[ 𝑩 ]
    reductᴵ .Interp ⟨$⟩ (o , args) = ⟦ I o ⟧₂ ⟨$⟩ args
    reductᴵ .Interp .cong {o , u} {.o , v} (refl , u≈v) = cong ⟦ I o ⟧₂ u≈v

    open Environment {𝑆 = 𝑆₁} reductᴵ using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
    open Setoid 𝔻[ 𝑩 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
    open EqLogic {𝑆 = 𝑆₁} using () renaming ( _⊧_≈_ to _⊧₁_≈_ )
    open EqLogic {𝑆 = 𝑆₂} using () renaming ( _⊧_≈_ to _⊧₂_≈_ )
```

The interpretation triangle: evaluating an `𝑆₁`-term in the reduct equals evaluating its
interpretation in `𝑩`.  At a leaf both sides look up the variable.  At a node, the
reduct's interpretation *is* "evaluate the derived term `I f`", and the translation's
node clause grafts the interpreted subterms into `I f`; `graft-eval` says those agree,
and the inductive hypotheses match the arguments through `cong`.

```agda
    reductᴵ-interp : (t : Term {𝑆 = 𝑆₁} X) (η : X → 𝕌[ 𝑩 ]) → ⟦ t ⟧₁ ⟨$⟩ η ≈ ⟦ I ✦ t ⟧₂ ⟨$⟩ η
    reductᴵ-interp (ℊ x) η = ≈refl
    reductᴵ-interp (node f ts) η =
      ≈trans  (cong ⟦ I f ⟧₂ (λ i → reductᴵ-interp (ts i) η))
              (≈sym (graft-eval 𝑩 (I f) (λ i → I ✦ ts i) η))
```

Satisfaction is the triangle quantified over environments, so each direction is a
`trans`-sandwich around the given satisfaction proof — verbatim the shape of
`⊧-reduct` / `⊧-expand`.  The equation sides are pinned (`{s}`/`{t}`), as the handoff
records, since `s` is not recoverable from `I ✦ s`.

```agda
    ⊧-interp : {s t : Term {𝑆 = 𝑆₁} X} → 𝑩 ⊧₂ (I ✦ s) ≈ (I ✦ t) → reductᴵ ⊧₁ s ≈ t
    ⊧-interp {s = s} {t} B⊧ η =
      ≈trans (reductᴵ-interp s η) (≈trans (B⊧ η) (≈sym (reductᴵ-interp t η)))

    ⊧-uninterp : {s t : Term {𝑆 = 𝑆₁} X} → reductᴵ ⊧₁ s ≈ t → 𝑩 ⊧₂ (I ✦ s) ≈ (I ✦ t)
    ⊧-uninterp {s = s} {t} R⊧ η =
      ≈trans (≈sym (reductᴵ-interp s η)) (≈trans (R⊧ η) (reductᴵ-interp t η))
```

#### `reductᴵ` generalizes `reduct`

When the interpretation is the one induced by a signature morphism, its reduct *is*
the ordinary signature reduct, operation by operation, by `refl` — the algebra-level
witness that `_✦_` (and hence this whole development) extends to derived operations.

```agda
  reductᴵ-⟨⟩ : {φ : SigMorphism 𝑆₁ 𝑆₂} {o : OperationSymbolsOf 𝑆₁}
    → o ^ reductᴵ ⟨ φ ⟩ᴵ ≡ o ^ reduct φ 𝑩
  reductᴵ-⟨⟩ = refl
```

#### The interpretability quasi-order

A *theory* is an indexed family of equations.  `𝑨 ⊨ₑ ℰ` is the assertion that `𝑨`
models every equation in `ℰ`.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
  open EqLogic {𝑆 = 𝑆} using ( _⊧_≈_ )

  infix 4 _⊨ₑ_
  _⊨ₑ_ : {Idx : Type ι} → Algebra α ρ → (Idx → Term X × Term X) → Type _
  𝑨 ⊨ₑ ℰ = ∀ k → 𝑨 ⊧ proj₁ (ℰ k) ≈ proj₂ (ℰ k)
```

Composition of interpretations carries through satisfaction.  This is the
reduct-level shadow of `✦-∘`: a `(J ∘ᴵ I)`-reduct satisfies exactly what the iterated
reduct `reductᴵ I (reductᴵ J 𝑪)` satisfies, by two applications of the satisfaction
condition and one `✦-∘` rewrite.  It is the engine of transitivity below.

```agda
module _
  {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥}
  (I : Interpretation 𝑆₁ 𝑆₂)
  (J : Interpretation 𝑆₂ 𝑆₃)
  (𝑪 : Algebra {𝑆 = 𝑆₃} α ρ)
  where
  open EqLogic {𝑆 = 𝑆₁} using ( _⊧_≈_ )

  reductᴵ-∘-⊧ : {s t : Term {𝑆 = 𝑆₁} X}
    → reductᴵ (reductᴵ 𝑪 J) I ⊧ s ≈ t → reductᴵ 𝑪 (J ∘ᴵ I) ⊧ s ≈ t
  reductᴵ-∘-⊧ {s = s} {t} hyp =
    ⊧-interp 𝑪 (J ∘ᴵ I) {s = s} {t}
      (⊧-≐ 𝑪 (≐-isSym (✦-∘ s)) (≐-isSym (✦-∘ t))
        (⊧-uninterp 𝑪 J {s = I ✦ s} {t = I ✦ t}
          (⊧-uninterp (reductᴵ 𝑪 J) I {s = s} {t = t} hyp)))
```

`ℰ₁ ≼ ℰ₂` says `ℰ₁` (a theory of `𝑆₁`) is interpretable in `ℰ₂` (a theory of `𝑆₂`):
some interpretation's reduct sends every `ℰ₂`-model to an `ℰ₁`-model.  The relation is
indexed by the algebra-level pair `(α , ρ)` at which models are tested, exactly as the
satisfaction relations are.

```agda
module Interpret (α ρ : Level) where

  _≼_ : {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥}
    {X₁ : Type χ₁} {X₂ : Type χ₂} {Idx₁ : Type ι₁} {Idx₂ : Type ι₂}
    → (Idx₁ → Term {𝑆 = 𝑆₁} X₁ × Term {𝑆 = 𝑆₁} X₁)
    → (Idx₂ → Term {𝑆 = 𝑆₂} X₂ × Term {𝑆 = 𝑆₂} X₂) → Type _
  _≼_ {𝑆₁ = 𝑆₁} {𝑆₂ = 𝑆₂} ℰ₁ ℰ₂ =
    Σ[ I ∈ Interpretation 𝑆₁ 𝑆₂ ]
      ((𝑩 : Algebra {𝑆 = 𝑆₂} α ρ) → 𝑩 ⊨ₑ ℰ₂ → reductᴵ 𝑩 I ⊨ₑ ℰ₁)

  infix 4 _≼_
```

Reflexivity: the identity interpretation works, because `idᴵ ✦_` is the identity up
to `_≐_` (`✦-id`) and satisfaction respects `_≐_`.

```agda
module _ α ρ where

  open Interpret α ρ

  ≼-refl : {𝑆 : Signature 𝓞 𝓥} {X : Type χ} {Idx : Type ι}
    (ℰ : Idx → Term X × Term X) → ℰ ≼ ℰ
  ≼-refl {𝑆 = 𝑆} ℰ = idᴵ , red
    where
    red : (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ → reductᴵ 𝑩 idᴵ ⊨ₑ ℰ
    red 𝑩 B⊨ k =
      ⊧-interp 𝑩 idᴵ {s = proj₁ (ℰ k)} {t = proj₂ (ℰ k)}
        (⊧-≐ 𝑩 (≐-isSym (✦-id (ℰ k .proj₁))) (≐-isSym (✦-id (ℰ k .proj₂))) (B⊨ k))
```

Transitivity: compose the interpretations with `_∘ᴵ_`, chain the two reduct
implications, and re-fold the iterated reduct into the composite reduct with
`reductᴵ-∘-⊧`.

```agda
  ≼-trans : {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥}
    {X₁ : Type χ₁} {X₂ : Type χ₂} {X₃ : Type χ₃}
    {Idx₁ : Type ι₁} {Idx₂ : Type ι₂} {Idx₃ : Type ι₃}
    (ℰ₁ : Idx₁ → Term {𝑆 = 𝑆₁} X₁ × Term {𝑆 = 𝑆₁} X₁)
    (ℰ₂ : Idx₂ → Term {𝑆 = 𝑆₂} X₂ × Term {𝑆 = 𝑆₂} X₂)
    (ℰ₃ : Idx₃ → Term {𝑆 = 𝑆₃} X₃ × Term {𝑆 = 𝑆₃} X₃)
    → ℰ₁ ≼ ℰ₂ → ℰ₂ ≼ ℰ₃ → ℰ₁ ≼ ℰ₃

  ≼-trans {𝑆₃ = 𝑆₃} ℰ₁ ℰ₂ ℰ₃ (I , Ihyp) (J , Jhyp) = J ∘ᴵ I , red
    where
    red : (𝑪 : Algebra {𝑆 = 𝑆₃} α ρ) → 𝑪 ⊨ₑ ℰ₃ → reductᴵ 𝑪 (J ∘ᴵ I) ⊨ₑ ℰ₁
    red 𝑪 C⊨ k =
      reductᴵ-∘-⊧ I J 𝑪 {s = proj₁ (ℰ₁ k)} {t = proj₂ (ℰ₁ k)}
        (Ihyp (reductᴵ 𝑪 J) (Jhyp 𝑪 C⊨) k)
```

--------------------------------------

[^1]: O. C. García and W. Taylor, *The Lattice of Interpretability Types of Varieties*, Mem. Amer. Math. Soc. **50** (1984), no. 305.

[^2]: Infinitary CSP over ω-categorical templates.
