---
layout: default
file: "src/Classical/Structures/Group/Centralizer.lagda.md"
title: "Classical.Structures.Group.Centralizer module"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Centralizers

This is the [Classical.Structures.Group.Centralizer][] module of the [Agda Universal Algebra Library][].

The **centralizer** `C_G(N)` of a subset `N` of a group `G` is the set of elements
that commute with every member of `N`.  It is a subgroup, it is antitone in `N`,
and it is *normal* whenever `N` is.[^1]

This module also proves the small commutator fact that drives subdirect
irreducibility: *two normal subgroups that meet trivially centralize each other*.

For `m ∈ M` and `n ∈ N` the commutator `n m n⁻¹ m⁻¹` lies in `M` (read it as
`(n m n⁻¹) m⁻¹`, and use normality of `M`) and in `N` (similarly, read `n (m n⁻¹ m⁻¹)`),
hence is trivial, which is exactly `n m = m n`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Centralizer where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                 using ( proj₁ )
open import Level                        using ( Level ; _⊔_ )
open import Relation.Binary              using ( Setoid )
open import Relation.Binary.Definitions  using ( _Respects_ )
open import Relation.Unary               using ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic        using ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation  using ( module Conjugate )
open import Classical.Signatures.Group              using ( Sig-Group )
open import Classical.Structures.Group.Subgroups    using ( IsSubgroup ; mkIsSubgroup )
open import Setoid.Algebras.Basic                   using ( 𝕌[_] ; 𝔻[_] ; Algebra)

private variable ℓ ℓ' : Level
```
-->

#### The centralizer of a subset

```agda
module Centralizer {α ρ : Level} (𝒢 : Group α ρ) where
  private
    𝑮 : Algebra {𝑆 = Sig-Group} α ρ
    𝑮 = proj₁ 𝒢

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming  ( Carrier to G ; refl to ≈refl
                                               ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢     using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; assoc-law
                             ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open Conjugate 𝒢         using  ( IsNormal ; conj-cong ; conj-∙-hom
                                  ; conj-conj⁻¹ ; conj-syntax)

  -- The centralizer of N: the elements commuting with every member of N.
  C[_] : Pred G ℓ → Pred G (α ⊔ ρ ⊔ ℓ)
  C[ N ] g = ∀ x → x ∈ N → g ∙ x ≈ x ∙ g

  -- Larger subsets have smaller centralizers.
  C-isAntitone : {M : Pred G ℓ} {N : Pred G ℓ'} → M ⊆ N → C[ N ] ⊆ C[ M ]
  C-isAntitone M⊆N g∈C x x∈M = g∈C x (M⊆N x∈M)
```

The centralizer is a subgroup.  Closure under inversion is the only step with any
content: from `g x = x g` one gets `g⁻¹ x = x g⁻¹` by applying `g⁻¹` on the left
and right of both sides.

```agda
  C-isSubgroup : (N : Pred G ℓ) → IsSubgroup 𝒢 C[ N ]
  C-isSubgroup N = mkIsSubgroup 𝒢 resp ∙-c ε-c ⁻¹-c
    where
    resp : C[ N ] Respects _≈_
    resp {g} {g'} g≈g' g∈C x x∈N = begin
      g' ∙ x   ≈˘⟨ ∙-cong g≈g' ≈refl ⟩
      g ∙ x    ≈⟨ g∈C x x∈N ⟩
      x ∙ g    ≈⟨ ∙-cong ≈refl g≈g' ⟩
      x ∙ g'   ∎

    ε-c : ε ∈ C[ N ]
    ε-c x _ = ≈trans (idˡ-law x) (≈sym (idʳ-law x))

    ∙-c : ∀ {g h} → g ∈ C[ N ] → h ∈ C[ N ] → g ∙ h ∈ C[ N ]
    ∙-c {g} {h} g∈C h∈C x x∈N = begin
      g ∙ h ∙ x    ≈⟨ assoc-law g h x ⟩
      g ∙ (h ∙ x)  ≈⟨ ∙-cong ≈refl (h∈C x x∈N) ⟩
      g ∙ (x ∙ h)  ≈˘⟨ assoc-law g x h ⟩
      g ∙ x ∙ h    ≈⟨ ∙-cong (g∈C x x∈N) ≈refl ⟩
      x ∙ g ∙ h    ≈⟨ assoc-law x g h ⟩
      x ∙ (g ∙ h)  ∎

    ⁻¹-c : ∀ {g} → g ∈ C[ N ] → g ⁻¹ ∈ C[ N ]
    ⁻¹-c {g} g∈C x x∈N = begin
      g ⁻¹ ∙ x                 ≈˘⟨ ∙-cong ≈refl (idʳ-law x) ⟩
      g ⁻¹ ∙ (x ∙ ε)           ≈˘⟨ ∙-cong ≈refl (∙-cong ≈refl (invʳ-law g)) ⟩
      g ⁻¹ ∙ (x ∙ (g ∙ g ⁻¹))  ≈˘⟨ ∙-cong ≈refl (assoc-law x g (g ⁻¹)) ⟩
      g ⁻¹ ∙ (x ∙ g ∙ g ⁻¹)    ≈˘⟨ ∙-cong ≈refl (∙-cong (g∈C x x∈N) ≈refl) ⟩
      g ⁻¹ ∙ (x ^ g)           ≈⟨ ∙-cong ≈refl (assoc-law g x (g ⁻¹)) ⟩
      g ⁻¹ ∙ (g ∙ (x ∙ g ⁻¹))  ≈˘⟨ assoc-law (g ⁻¹) g (x ∙ g ⁻¹) ⟩
      (g ⁻¹ ∙ g) ∙ (x ∙ g ⁻¹)  ≈⟨ ∙-cong (invˡ-law g) ≈refl ⟩
      ε ∙ (x ∙ g ⁻¹)           ≈⟨ idˡ-law (x ∙ g ⁻¹) ⟩
      x ∙ g ⁻¹                 ∎
```

The centralizer of a *normal* subgroup is normal: conjugating a centralizing element
by `k` still centralizes, because `k⁻¹ x k` is again in `N`, so `g` commutes with it,
and conjugating that equation by `k` gives what is wanted.

```agda
  C-isNormal : {N : Pred G ℓ} → IsNormal N → IsNormal C[ N ]
  C-isNormal N-normal k {g} g∈C x x∈N = begin
    g ^ k ∙ x                ≈˘⟨ ∙-cong ≈refl (conj-conj⁻¹ k x) ⟩
    g ^ k ∙ (x ^ (k ⁻¹))^ k  ≈˘⟨ conj-∙-hom k g (x ^ (k ⁻¹)) ⟩
    (g ∙ x ^ (k ⁻¹))^ k      ≈⟨ conj-cong k (g∈C (x ^ (k ⁻¹)) (N-normal (k ⁻¹) x∈N)) ⟩
    (x ^ (k ⁻¹) ∙ g)^ k      ≈⟨ conj-∙-hom k (x ^ (k ⁻¹)) g ⟩
    (x ^ (k ⁻¹))^ k ∙ g ^ k  ≈⟨ ∙-cong (conj-conj⁻¹ k x) ≈refl ⟩
    x ∙ g ^ k                ∎
```

#### Normal subgroups meeting trivially centralize each other

Two normal subgroups with trivial intersection commute elementwise: if `M` and `N`
are normal and meet at `(ε)`, then every element of `N` centralizes `M`.

We formalize this standard fact in `normals-centralize`{.AgdaFunction};
the proof is the classical commutator argument.  Given `n ∈ N` and `m ∈ M`, the
commutator `(n m n⁻¹) m⁻¹` lies in `M` by normality of `M` and in `N` by normality
of `N`, so the trivial-intersection hypothesis forces it to be `ε`, which is exactly
`n m ≈ m n`.

```agda
  normals-centralize : {M : Pred G ℓ} {N : Pred G ℓ'}
    → IsSubgroup 𝒢 M → IsSubgroup 𝒢 N
    → IsNormal M → IsNormal N
    → (∀ {w} → w ∈ M → w ∈ N → w ≈ ε)   -- M and N meet trivially
    → N ⊆ C[ M ]
  normals-centralize {M = M} {N} M-sg N-sg M-nrm N-nrm meet {n} n∈N m m∈M = commute
    where
    open IsSubgroup M-sg using () renaming  ( ∙-closed to M∙ ; ⁻¹-closed to M⁻¹ )
    open IsSubgroup N-sg using () renaming  ( ∙-closed to N∙ ; ⁻¹-closed to N⁻¹
                                            ; respects to N-resp )

    -- The commutator, read as (n m n⁻¹) m⁻¹ ...
    w : G
    w = n ∙ m ∙ n ⁻¹ ∙ m ⁻¹

    w∈M : w ∈ M
    w∈M = M∙ (M-nrm n m∈M) (M⁻¹ m∈M)

    -- ... and as n (m n⁻¹ m⁻¹).
    w≈ : w ≈ n ∙ (n ⁻¹) ^ m
    w≈ = begin
      n ∙ m ∙ n ⁻¹ ∙ m ⁻¹    ≈⟨ ∙-cong (assoc-law n m (n ⁻¹)) ≈refl ⟩
      n ∙ (m ∙ n ⁻¹) ∙ m ⁻¹  ≈⟨ assoc-law n (m ∙ n ⁻¹) (m ⁻¹) ⟩
      n ∙ (n ⁻¹) ^ m         ∎

    w∈N : w ∈ N
    w∈N = N-resp (≈sym w≈) (N∙ n∈N (N-nrm m (N⁻¹ n∈N)))

    w≈ε : w ≈ ε
    w≈ε = meet w∈M w∈N

    -- Cancelling m⁻¹ and then n⁻¹ from n m n⁻¹ m⁻¹ ≈ ε.
    step : n ∙ m ∙ n ⁻¹ ≈ m
    step = begin
      m ^ n               ≈˘⟨ idʳ-law _ ⟩
      m ^ n ∙ ε           ≈˘⟨ ∙-cong ≈refl (invˡ-law m) ⟩
      m ^ n ∙ (m ⁻¹ ∙ m)  ≈˘⟨ assoc-law (m ^ n) (m ⁻¹) m ⟩
      m ^ n ∙ m ⁻¹ ∙ m    ≈⟨ ∙-cong w≈ε ≈refl ⟩
      ε ∙ m               ≈⟨ idˡ-law m ⟩
      m                   ∎

    commute : n ∙ m ≈ m ∙ n
    commute = begin
      n ∙ m               ≈˘⟨ idʳ-law (n ∙ m) ⟩
      n ∙ m ∙ ε           ≈˘⟨ ∙-cong ≈refl (invˡ-law n) ⟩
      n ∙ m ∙ (n ⁻¹ ∙ n)  ≈˘⟨ assoc-law (n ∙ m) (n ⁻¹) n ⟩
      m ^ n ∙ n           ≈⟨ ∙-cong step ≈refl ⟩
      m ∙ n               ∎
```

---

[^1]: The FLRP program's Lemma 3.7 (`docs/papers/flrp/ieprops/`, `lemma-wjd-5`): in a
      core-free parachute representation the centralizer of every nontrivial normal
      subgroup is trivial, whence the group is subdirectly irreducible with a
      nonabelian monolith.  See [FLRP.Parachute][].
