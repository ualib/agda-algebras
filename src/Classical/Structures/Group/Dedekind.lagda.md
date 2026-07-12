---
layout: default
file: "src/Classical/Structures/Group/Dedekind.lagda.md"
title: "Classical.Structures.Group.Dedekind module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### Dedekind's rule

This is the [Classical.Structures.Group.Dedekind][] module of the [Agda Universal Algebra Library][].

**Dedekind's rule** (the modular law for complex products): if `H`, `C`, `K` are
subgroups of a group with `H ≤ K`, then

    H (C ∩ K) = H C ∩ K        and        (C ∩ K) H = C H ∩ K.

Both statements are proved here, as the mutual inclusions `dedekindˡ`{.AgdaFunction}
and `dedekindʳ`{.AgdaFunction} over the complex product `_∙ᶜ_`{.AgdaFunction} of
[Classical.Structures.Group.Complexes][].

The hypotheses are minimal: only `K` needs to be a subgroup — `H` and `C` are
arbitrary subsets with `H ⊆ K` — which is exactly the generality the interval
arguments need.  The heart of both proofs is the observation that if `x ≈ h ∙ c` with
`h , x ∈ K`, then `c ≈ h ⁻¹ ∙ x` lies in `K` as well.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Dedekind where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product    using ( _,_ ; proj₁ ; proj₂ )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid )
open import Relation.Unary  using ( Pred ; _∈_ ; _⊆_ ; _∩_ ; _≐_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Group             using ( Sig-Group )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup )
open import Classical.Structures.Group.Complexes   using ( module Complex )

open import Setoid.Algebras.Basic {𝑆 = Sig-Group}  using ( Algebra ; 𝕌[_] ; 𝔻[_] )

private variable ℓʰ ℓᶜ ℓᵏ : Level
```
-->

#### The rule

```agda
module _ {α ρ : Level} (𝒢 : Group α ρ) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢 using ( _∙_ ; _⁻¹ ; ∙-cong )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using ( \\-leftDividesʳ ; //-rightDividesʳ )
  open Complex 𝒢 using ( _∙ᶜ_ )

  -- Dedekind's rule, left version: for H ⊆ K with K a subgroup,
  -- H (C ∩ K) = H C ∩ K.
  dedekindˡ : {H : Pred G ℓʰ} {C : Pred G ℓᶜ} {K : Pred G ℓᵏ}
    →  IsSubgroup 𝒢 K  →  H ⊆ K →  H ∙ᶜ (C ∩ K) ≐ (H ∙ᶜ C) ∩ K
  dedekindˡ {H = H} {C} {K} K-isSubgroup H⊆K = below , above
    where
    open IsSubgroup K-isSubgroup
      using ( ∙-closed ; ⁻¹-closed ) renaming ( respects to K-respects )

    -- Forward: a product h ∙ c with c ∈ K lands in K because h ∈ H ⊆ K.
    below : H ∙ᶜ (C ∩ K) ⊆ (H ∙ᶜ C) ∩ K
    below (h , c , h∈H , (c∈C , c∈K) , x≈hc) =
      (h , c , h∈H , c∈C , x≈hc) , K-respects (≈sym x≈hc) (∙-closed (H⊆K h∈H) c∈K)

    -- Backward: from x ≈ h ∙ c with x ∈ K and h ∈ H ⊆ K, the cofactor
    -- c ≈ h ⁻¹ ∙ x lies in K, so c ∈ C ∩ K.
    above : (H ∙ᶜ C) ∩ K ⊆ H ∙ᶜ (C ∩ K)
    above {x} ((h , c , h∈H , c∈C , x≈hc) , x∈K) =
      h , c , h∈H , (c∈C , c∈K) , x≈hc
      where
      cofactor : h ⁻¹ ∙ x ≈ c
      cofactor = begin
        h ⁻¹ ∙ x        ≈⟨ ∙-cong ≈refl x≈hc ⟩
        h ⁻¹ ∙ (h ∙ c)  ≈⟨ \\-leftDividesʳ h c ⟩
        c               ∎

      c∈K : c ∈ K
      c∈K = K-respects cofactor (∙-closed (⁻¹-closed (H⊆K h∈H)) x∈K)

  -- Dedekind's rule (right version):
  --   for H ⊆ K with K a subgroup, (C ∩ K) H = C H ∩ K.
  dedekindʳ : {H : Pred G ℓʰ} {C : Pred G ℓᶜ} {K : Pred G ℓᵏ}
    →  IsSubgroup 𝒢 K  →  H ⊆ K
    →  (C ∩ K) ∙ᶜ H ≐ (C ∙ᶜ H) ∩ K
  dedekindʳ {H = H} {C} {K} K-isSubgroup H⊆K = below , above
    where
    open IsSubgroup K-isSubgroup
      using ( ∙-closed ; ⁻¹-closed ) renaming ( respects to K-respects )

    below : (C ∩ K) ∙ᶜ H ⊆ (C ∙ᶜ H) ∩ K
    below (c , h , (c∈C , c∈K) , h∈H , x≈ch) =
      (c , h , c∈C , h∈H , x≈ch) , K-respects (≈sym x≈ch) (∙-closed c∈K (H⊆K h∈H))

    above : (C ∙ᶜ H) ∩ K ⊆ (C ∩ K) ∙ᶜ H
    above {x} ((c , h , c∈C , h∈H , x≈ch) , x∈K) =
      c , h , (c∈C , c∈K) , h∈H , x≈ch
      where
      cofactor : x ∙ h ⁻¹ ≈ c
      cofactor = begin
        x ∙ h ⁻¹        ≈⟨ ∙-cong x≈ch ≈refl ⟩
        c ∙ h ∙ h ⁻¹    ≈⟨ //-rightDividesʳ h c ⟩
        c               ∎

      c∈K : c ∈ K
      c∈K = K-respects cofactor (∙-closed x∈K (⁻¹-closed (H⊆K h∈H)))
```

---

[^1]: In the FLRP program (`docs/papers/flrp/ieprops/`, § 3.2) Dedekind's rule drives the
      antichain lemma for permuting complements and, through it, the parachute theorems;
      those corollaries are the first RP-1 targets and will build directly on this
      module.
