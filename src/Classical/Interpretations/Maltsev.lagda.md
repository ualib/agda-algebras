---
layout: default
file: "src/Classical/Interpretations/Maltsev.lagda.md"
title: "Classical.Interpretations.Maltsev module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

### A Maltsev condition as a theory interpretation

This is the [Classical.Interpretations.Maltsev][] module of the [Agda Universal Algebra Library][].

This module is the worked instance for M4-5f: a *Maltsev condition*, presented as a
theory interpretation ([Setoid.Varieties.Interpretation][]).

A **Maltsev term** for a variety `𝒱` is a ternary term `m` satisfying

    m(x, x, y) ≈ y      and      m(x, y, y) ≈ x.

A variety has a Maltsev term exactly when it is congruence-permutable — the original,
and still the paradigmatic, *Maltsev condition*.  Such a condition is precisely a theory
interpretation of a small abstract theory into `𝒱`: take the signature `Sig-Maltsev`
with one ternary symbol `m-Op`, and the theory `Th-Maltsev` with the two equations
above; an interpretation `Th-Maltsev → Th-𝒱` is then nothing but a choice of `𝒱`-term
witnessing those equations.  In the order-theoretic language of
[Setoid.Varieties.Interpretation][], `Th-Maltsev ≼ Th-𝒱` says "𝒱 is congruence-permutable
via the chosen term."

We make this concrete for the variety of **groups**: in any group, `m(x, y, z) = x ∙
(y ⁻¹ ∙ z)` is a Maltsev term, since `x ∙ (x ⁻¹ ∙ z) = z` and `x ∙ (y ⁻¹ ∙ y) = x`.
The interpretation `I-grp` sends `m-Op` to that derived term, and the milestone's
satisfaction condition (`⊧-interp`) reduces the obligation `Th-Maltsev ≼ Th-Group` to
the two curried group identities — which are three-line group calculations.

This sits on the clone/CSP side of the library and points forward to M9-2
(Bodirsky–Pinsker); it is **not** FLRP work.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Interpretations.Maltsev where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Fin.Base     using ( Fin )
open import Data.Fin.Patterns using ( 0F ; 1F ; 2F )
open import Data.Product      using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level             using ( Level ; 0ℓ )
open import Relation.Binary   using ( Setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using ( Signature )
open import Overture.Terms                 using ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation  using ( Interpretation ; _✦_ )
open import Setoid.Algebras.Basic          using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms.Basic             using ( module Environment )
open import Setoid.Varieties.Interpretation
  using ( reductᴵ ; ⊧-interp ; graft-eval ; _⊨ₑ_ ; _≼_ )
open import Classical.Operations           using ( pair )
open import Classical.Signatures.Group     using ( Sig-Group ; ∙-Op ; ⁻¹-Op )
open import Classical.Structures.Group     using ( Group ; module Group-Op )
open import Classical.Theories.Group       using ( Th-Group )

open import Function using ( Func )
open Func renaming ( to to _⟨$⟩_ )

private variable α ρ : Level
```

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
-- so the interpretation proofs below can refer to it definitionally.
tri : {ℓ : Level} {A : Type ℓ} → A → A → A → Fin 3 → A
tri a b c 0F = a
tri a b c 1F = b
tri a b c 2F = c

-- the ternary application m(a, b, c) as a Sig-Maltsev term
mlt : {X : Type} → Term {𝑆 = Sig-Maltsev} X → Term {𝑆 = Sig-Maltsev} X
  → Term {𝑆 = Sig-Maltsev} X → Term {𝑆 = Sig-Maltsev} X
mlt a b c = node m-Op (tri a b c)

data Eq-Maltsev : Type where
  malˡ malʳ : Eq-Maltsev

Th-Maltsev : Eq-Maltsev → Term {𝑆 = Sig-Maltsev} (Fin 3) × Term {𝑆 = Sig-Maltsev} (Fin 3)
Th-Maltsev malˡ = mlt (ℊ 0F) (ℊ 0F) (ℊ 1F) , ℊ 1F   -- m(x, x, y) ≈ y
Th-Maltsev malʳ = mlt (ℊ 0F) (ℊ 1F) (ℊ 1F) , ℊ 0F   -- m(x, y, y) ≈ x
```

#### The interpretation into the group theory

`I-grp` sends `m-Op` to the derived group term `x ∙ (y ⁻¹ ∙ z)`, whose argument
positions `0F , 1F , 2F` are `x , y , z`.  (The binary nodes use `pair` so the
group's own node bridges apply when we evaluate.)

```agda
I-grp : Interpretation Sig-Maltsev Sig-Group
I-grp m-Op =
  node ∙-Op (pair (ℊ 0F) (node ∙-Op (pair (node ⁻¹-Op (λ _ → ℊ 1F)) (ℊ 2F))))
```

#### Groups are congruence-permutable, via that term

The obligation `Th-Maltsev ≼ Th-Group` is: for every group `𝑩`, the `I-grp`-reduct
satisfies `Th-Maltsev`.  By `⊧-interp` this is equivalent to `𝑩` satisfying the two
*interpreted* equations, and those follow from the curried group laws via two evaluation
lemmas — `eval-m`, which unfolds the chosen derived term to `x ∙ (y ⁻¹ ∙ z)`, and
`eval-node`, which evaluates the interpretation of a Maltsev application through
`graft-eval` — and the two Maltsev identities (`mal-lhsᵍ`, `mal-rhsᵍ`).

```agda
maltsev-≼-group : ∀ {α ρ} → _≼_ {α = α} {ρ = ρ} Th-Maltsev Th-Group
maltsev-≼-group {α} {ρ} = I-grp , red
  where
  red : (𝑩 : Algebra {𝑆 = Sig-Group} α ρ) → 𝑩 ⊨ₑ Th-Group → reductᴵ I-grp 𝑩 ⊨ₑ Th-Maltsev
  red 𝑩 g = λ  { malˡ → ⊧-interp I-grp 𝑩 {s = proj₁ (Th-Maltsev malˡ)} {t = proj₂ (Th-Maltsev malˡ)} pfˡ
               ; malʳ → ⊧-interp I-grp 𝑩 {s = proj₁ (Th-Maltsev malʳ)} {t = proj₂ (Th-Maltsev malʳ)} pfʳ }
    where
    𝒢 : Group α ρ
    𝒢 = 𝑩 , g
    open Group-Op 𝒢 using ( _∙_ ; _⁻¹ ; ε ; ∙-cong ; assoc-law ; idˡ-law ; idʳ-law
                          ; invˡ-law ; invʳ-law ; interp-node-∙ ; interp-node-⁻¹ )
    open Environment 𝑩 using ( ⟦_⟧ )
    open Setoid 𝔻[ 𝑩 ] using ( _≈_ ) renaming ( refl to ≈refl )
    open SetoidReasoning 𝔻[ 𝑩 ]

    -- Evaluate the chosen derived term to its curried group form, once.
    eval-m : (ν : Fin 3 → 𝕌[ 𝑩 ]) → ⟦ I-grp m-Op ⟧ ⟨$⟩ ν ≈ ν 0F ∙ (ν 1F ⁻¹ ∙ ν 2F)
    eval-m ν = begin
      ⟦ I-grp m-Op ⟧ ⟨$⟩ ν
        ≈⟨ interp-node-∙ (ℊ 0F) (node ∙-Op (pair (node ⁻¹-Op (λ _ → ℊ 1F)) (ℊ 2F))) {ν} ⟩
      ν 0F ∙ ⟦ node ∙-Op (pair (node ⁻¹-Op (λ _ → ℊ 1F)) (ℊ 2F)) ⟧ ⟨$⟩ ν
        ≈⟨ ∙-cong ≈refl (interp-node-∙ (node ⁻¹-Op (λ _ → ℊ 1F)) (ℊ 2F) {ν}) ⟩
      ν 0F ∙ (⟦ node ⁻¹-Op (λ _ → ℊ 1F) ⟧ ⟨$⟩ ν ∙ ν 2F)
        ≈⟨ ∙-cong ≈refl (∙-cong (interp-node-⁻¹ (ℊ 1F) {ν}) ≈refl) ⟩
      ν 0F ∙ (ν 1F ⁻¹ ∙ ν 2F)  ∎

    -- The two Maltsev identities, curried, from the group axioms.
    mal-lhsᵍ : ∀ a b → a ∙ (a ⁻¹ ∙ b) ≈ b
    mal-lhsᵍ a b = begin
      a ∙ (a ⁻¹ ∙ b)  ≈˘⟨ assoc-law a (a ⁻¹) b ⟩
      a ∙ a ⁻¹ ∙ b    ≈⟨ ∙-cong (invʳ-law a) ≈refl ⟩
      ε ∙ b           ≈⟨ idˡ-law b ⟩
      b               ∎

    mal-rhsᵍ : ∀ a b → a ∙ (b ⁻¹ ∙ b) ≈ a
    mal-rhsᵍ a b = begin
      a ∙ (b ⁻¹ ∙ b)  ≈⟨ ∙-cong ≈refl (invˡ-law b) ⟩
      a ∙ ε           ≈⟨ idʳ-law a ⟩
      a               ∎

    -- Evaluate the interpretation of a Maltsev application: graft the three
    -- interpreted subterms into the derived term, then evaluate it via eval-m.
    -- The substitution handed to graft-eval references the named `tri a b c`, so
    -- it is the very one `I-grp ✦ mlt a b c` reduces to (no fresh-lambda gap).
    eval-node : (a b c : Term {𝑆 = Sig-Maltsev} (Fin 3)) (η : Fin 3 → 𝕌[ 𝑩 ])
      → ⟦ I-grp ✦ mlt a b c ⟧ ⟨$⟩ η
        ≈ ⟦ I-grp ✦ a ⟧ ⟨$⟩ η ∙ (⟦ I-grp ✦ b ⟧ ⟨$⟩ η ⁻¹ ∙ ⟦ I-grp ✦ c ⟧ ⟨$⟩ η)
    eval-node a b c η = begin
      ⟦ I-grp ✦ mlt a b c ⟧ ⟨$⟩ η
        ≈⟨ graft-eval 𝑩 (I-grp m-Op) (λ i → I-grp ✦ tri a b c i) η ⟩
      ⟦ I-grp m-Op ⟧ ⟨$⟩ (λ y → ⟦ I-grp ✦ tri a b c y ⟧ ⟨$⟩ η)
        ≈⟨ eval-m _ ⟩
      ⟦ I-grp ✦ a ⟧ ⟨$⟩ η ∙ (⟦ I-grp ✦ b ⟧ ⟨$⟩ η ⁻¹ ∙ ⟦ I-grp ✦ c ⟧ ⟨$⟩ η)  ∎

    -- 𝑩 satisfies each interpreted Maltsev equation.
    pfˡ : (η : Fin 3 → 𝕌[ 𝑩 ])
      → ⟦ I-grp ✦ proj₁ (Th-Maltsev malˡ) ⟧ ⟨$⟩ η ≈ ⟦ I-grp ✦ proj₂ (Th-Maltsev malˡ) ⟧ ⟨$⟩ η
    pfˡ η = begin
      ⟦ I-grp ✦ proj₁ (Th-Maltsev malˡ) ⟧ ⟨$⟩ η  ≈⟨ eval-node (ℊ 0F) (ℊ 0F) (ℊ 1F) η ⟩
      η 0F ∙ (η 0F ⁻¹ ∙ η 1F)                     ≈⟨ mal-lhsᵍ (η 0F) (η 1F) ⟩
      η 1F                                        ∎

    pfʳ : (η : Fin 3 → 𝕌[ 𝑩 ])
      → ⟦ I-grp ✦ proj₁ (Th-Maltsev malʳ) ⟧ ⟨$⟩ η ≈ ⟦ I-grp ✦ proj₂ (Th-Maltsev malʳ) ⟧ ⟨$⟩ η
    pfʳ η = begin
      ⟦ I-grp ✦ proj₁ (Th-Maltsev malʳ) ⟧ ⟨$⟩ η  ≈⟨ eval-node (ℊ 0F) (ℊ 1F) (ℊ 1F) η ⟩
      η 0F ∙ (η 1F ⁻¹ ∙ η 1F)                     ≈⟨ mal-rhsᵍ (η 0F) (η 1F) ⟩
      η 0F                                        ∎
```

--------------------------------------

{% include UALib.Links.md %}
