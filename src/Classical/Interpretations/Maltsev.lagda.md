---
layout: default
file: "src/Classical/Interpretations/Maltsev.lagda.md"
title: "Classical.Interpretations.Maltsev module"
date: "2026-06-15"
author: "the agda-algebras development team"
---

### Groups have a Maltsev term

This is the [Classical.Interpretations.Maltsev][] module of the [Agda Universal Algebra Library][].

In [Setoid.Varieties.Maltsev][] a Maltsev condition is formalized by defining the
abstract one-ternary-symbol theory `Th-Maltsev`.  The predicate
`HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ` tells us when a theory `ℰ` (equivalently, its
variety) has a Maltsev term.

The present module supplies a worked example for one concrete variety — the variety
of **groups**.  Because the proof consumes the group operations and laws
(`Classical.Structures.Group`), it is structure-specific and so belongs in
`Classical/`, one layer above the general theory.

In a group, `m x y z = x ∙ (y ⁻¹ ∙ z)` is a Maltsev term, since `x ∙ (x ⁻¹ ∙ z) = z`
and `x ∙ (y ⁻¹ ∙ y) = x`.  The interpretation `I-grp` sends `m-Op` to that derived
term, and the satisfaction condition (`⊧-interp`) reduces the obligation
`HasMaltsevTerm Th-Group` to the two curried group identities.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Interpretations.Maltsev where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin.Base     using ( Fin )
open import Data.Fin.Patterns using ( 0F ; 1F ; 2F )
open import Data.Product      using ( _,_ ; proj₁ ; proj₂ )
open import Level             using ( Level ; 0ℓ )
open import Relation.Binary   using ( Setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Operations             using  ( pair )
open import Classical.Signatures.Group       using  ( Sig-Group ; ∙-Op ; ⁻¹-Op )
open import Classical.Structures.Group       using  ( Group ; module Group-Op )
open import Classical.Theories.Group         using  ( Th-Group )
open import Overture.Terms                   using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation    using  ( Interpretation ; _✦_ )
open import Setoid.Algebras.Basic            using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms.Basic               using  ( module Environment )
open import Setoid.Varieties.Interpretation  using  ( reductᴵ ; ⊧-interp
                                                    ; graft-eval ; _⊨ₑ_ )
open import Setoid.Varieties.Maltsev         using  ( Sig-Maltsev ; m-Op ; tri
                                                    ; m ; mxxy≈y ; mxyy≈x
                                                    ; Th-Maltsev ; HasMaltsevTerm )
open import Function using ( Func )
open Func renaming ( to to _⟨$⟩_ )

private variable α ρ : Level
```

#### The interpretation into the group theory

`I-grp` sends `m-Op` to the derived group term `x ∙ (y ⁻¹ ∙ z)`, whose argument
positions `0F , 1F , 2F` are `x , y , z`.  (The binary nodes use `pair` so the
group's own node bridges apply when we evaluate.)

```agda
I-grp : Interpretation Sig-Maltsev Sig-Group
I-grp m-Op = node ∙-Op (pair (ℊ 0F) (node ∙-Op (pair (node ⁻¹-Op (λ _ → ℊ 1F)) (ℊ 2F))))
```

#### Groups are congruence-permutable

The obligation `HasMaltsevTerm Th-Group` unfolds to `Th-Maltsev ≼ Th-Group`: for every
group `𝑩`, the `I-grp`-reduct satisfies `Th-Maltsev`.  By `⊧-interp` this is equivalent to
`𝑩` satisfying the two *interpreted* equations, and those follow from the curried group
laws via two evaluation lemmas — `eval-m`, which unfolds the chosen derived term to
`x ∙ (y ⁻¹ ∙ z)`, and `eval-node`, which evaluates the interpretation of a Maltsev
application through `graft-eval` — and the two Maltsev identities (`mal-lhsᵍ`, `mal-rhsᵍ`).

```agda
red : (𝑩 : Algebra 0ℓ 0ℓ) → 𝑩 ⊨ₑ Th-Group → reductᴵ I-grp 𝑩 ⊨ₑ Th-Maltsev
red 𝑩 g = λ  { mxxy≈y → ⊧-interp I-grp 𝑩 {s = proj₁ (Th-Maltsev mxxy≈y)} {t = proj₂ (Th-Maltsev mxxy≈y)} pfˡ
             ; mxyy≈x → ⊧-interp I-grp 𝑩 {s = proj₁ (Th-Maltsev mxyy≈x)} {t = proj₂ (Th-Maltsev mxyy≈x)} pfʳ }
  where
  𝒢 : Group 0ℓ 0ℓ
  𝒢 = 𝑩 , g
  open Group-Op 𝒢
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
  -- it is the very one `I-grp ✦ m a b c` reduces to (no fresh-lambda gap).
  eval-node : (a b c : Term {𝑆 = Sig-Maltsev} (Fin 3)) (η : Fin 3 → 𝕌[ 𝑩 ])
    → ⟦ I-grp ✦ m a b c ⟧ ⟨$⟩ η
      ≈ ⟦ I-grp ✦ a ⟧ ⟨$⟩ η ∙ (⟦ I-grp ✦ b ⟧ ⟨$⟩ η ⁻¹ ∙ ⟦ I-grp ✦ c ⟧ ⟨$⟩ η)
  eval-node a b c η = begin
    ⟦ I-grp ✦ m a b c ⟧ ⟨$⟩ η
      ≈⟨ graft-eval 𝑩 (I-grp m-Op) (λ i → I-grp ✦ tri a b c i) η ⟩
    ⟦ I-grp m-Op ⟧ ⟨$⟩ (λ y → ⟦ I-grp ✦ tri a b c y ⟧ ⟨$⟩ η)
      ≈⟨ eval-m _ ⟩
    ⟦ I-grp ✦ a ⟧ ⟨$⟩ η ∙ (⟦ I-grp ✦ b ⟧ ⟨$⟩ η ⁻¹ ∙ ⟦ I-grp ✦ c ⟧ ⟨$⟩ η)  ∎

  -- 𝑩 satisfies each interpreted Maltsev equation.
  pfˡ : (η : Fin 3 → 𝕌[ 𝑩 ])
    → ⟦ I-grp ✦ proj₁ (Th-Maltsev mxxy≈y) ⟧ ⟨$⟩ η ≈ ⟦ I-grp ✦ proj₂ (Th-Maltsev mxxy≈y) ⟧ ⟨$⟩ η
  pfˡ η = begin
    ⟦ I-grp ✦ proj₁ (Th-Maltsev mxxy≈y) ⟧ ⟨$⟩ η  ≈⟨ eval-node (ℊ 0F) (ℊ 0F) (ℊ 1F) η ⟩
    η 0F ∙ (η 0F ⁻¹ ∙ η 1F)                     ≈⟨ mal-lhsᵍ (η 0F) (η 1F) ⟩
    η 1F                                        ∎

  pfʳ : (η : Fin 3 → 𝕌[ 𝑩 ])
    → ⟦ I-grp ✦ proj₁ (Th-Maltsev mxyy≈x) ⟧ ⟨$⟩ η ≈ ⟦ I-grp ✦ proj₂ (Th-Maltsev mxyy≈x) ⟧ ⟨$⟩ η
  pfʳ η = begin
    ⟦ I-grp ✦ proj₁ (Th-Maltsev mxyy≈x) ⟧ ⟨$⟩ η  ≈⟨ eval-node (ℊ 0F) (ℊ 1F) (ℊ 1F) η ⟩
    η 0F ∙ (η 1F ⁻¹ ∙ η 1F)                     ≈⟨ mal-rhsᵍ (η 0F) (η 1F) ⟩
    η 0F                                        ∎

maltsev-≼-group : HasMaltsevTerm Th-Group
maltsev-≼-group = I-grp , red
```

--------------------------------------

{% include UALib.Links.md %}
