---
layout: default
file: "src/Classical/Structures/Group/Complexes.lagda.md"
title: "Classical.Structures.Group.Complexes module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### Complex products

This is the [Classical.Structures.Group.Complexes][] module of the [Agda Universal Algebra Library][].

For subsets `P` and `Q` of a group (also known as *complexes*), the **complex product**
is `P Q = { p ∙ q ∣ p ∈ P , q ∈ Q }`.

Over a setoid carrier we take the **≈-saturated image**, that is, an element belongs
to `P ∙ᶜ Q` when it is ≈-equal to some product `p ∙ q`.  So the complex product
respects the setoid equality by construction, exactly as the subgroup conjugate of
[Classical.Structures.Group.Conjugation][] does.

The complex product of two subgroups is generally *not* a subgroup; it is one
precisely when the two subgroups permute.  Thus, `_∙ᶜ_`{.AgdaFunction} is defined on raw
predicates.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Complexes where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                  using ( _,_ ; _×_ ; Σ-syntax ; proj₁ )
open import Level                         using ( Level ; _⊔_ )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ ; _≐_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic      using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups  using ( IsSubgroup )
open import Setoid.Algebras.Basic                 using ( 𝕌[_] ; 𝔻[_] )

private variable ℓ ℓ' : Level
```
-->

#### The complex product

```agda
module Complex {α ρ : Level} (𝒢 : Group α ρ) where
  private
    𝑮 = proj₁ 𝒢  -- the algebra
    G = 𝕌[ 𝑮 ]   -- the universe (or carrier)

  open Setoid 𝔻[ 𝑮 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢 using ( _∙_ ; ε ; idʳ-law )

  infixl 7 _∙ᶜ_

  -- The complex product: x ∈ P ∙ᶜ Q when x is ≈-equal to a product p ∙ q
  -- with p ∈ P and q ∈ Q.
  _∙ᶜ_ : Pred G ℓ → Pred G ℓ' → Pred G (α ⊔ ρ ⊔ ℓ ⊔ ℓ')
  (P ∙ᶜ Q) x = Σ[ p ∈ G ] Σ[ q ∈ G ] (p ∈ P × q ∈ Q × x ≈ p ∙ q)

  -- A literal product of members is a member of the complex product.
  mem-∙ᶜ : {P : Pred G ℓ} {Q : Pred G ℓ'} {p q : G}
    →  p ∈ P → q ∈ Q → p ∙ q ∈ P ∙ᶜ Q
  mem-∙ᶜ p∈P q∈Q = _ , _ , p∈P , q∈Q , ≈refl

  -- The complex product respects the setoid equality, with no hypotheses on P, Q.
  ∙ᶜ-respects : (P : Pred G ℓ) (Q : Pred G ℓ') → (P ∙ᶜ Q) Respects _≈_
  ∙ᶜ-respects P Q x≈y (p , q , p∈P , q∈Q , x≈pq) =
    p , q , p∈P , q∈Q , ≈trans (≈sym x≈y) x≈pq

  -- The complex product is monotone in both arguments.
  ∙ᶜ-mono : {P P' : Pred G ℓ} {Q Q' : Pred G ℓ'}
    →  P ⊆ P' → Q ⊆ Q' → P ∙ᶜ Q ⊆ P' ∙ᶜ Q'
  ∙ᶜ-mono P⊆P' Q⊆Q' (p , q , p∈P , q∈Q , x≈pq) =
    p , q , P⊆P' p∈P , Q⊆Q' q∈Q , x≈pq
```

#### Subgroups absorb their own complex square

For a subgroup `H` the complex product `H H` collapses back to `H`: one inclusion
is closure under `∙` (plus respect), the other writes `x` as `x ∙ ε`.  This is the
prototypical use of the toolkit and a lemma the interval arguments reuse.

```agda
  subgroup-∙ᶜ-idem : {H : Pred G ℓ} → IsSubgroup 𝒢 H → (H ∙ᶜ H) ≐ H
  subgroup-∙ᶜ-idem {H = H} H-isSubgroup = below , above
    where
    open IsSubgroup H-isSubgroup using ( respects ; ∙-closed ; ε-closed )

    below : H ∙ᶜ H ⊆ H
    below (p , q , p∈H , q∈H , x≈pq) = respects (≈sym x≈pq) (∙-closed p∈H q∈H)

    above : H ⊆ H ∙ᶜ H
    above {x} x∈H = x , ε , x∈H , ε-closed , ≈sym (idʳ-law x)
```

---

[^1] The role played by `_∙ᶜ_`{.AgdaFunction} in this development is as the
     vocabulary of **Dedekind's rule** (`A ≤ B → A(C ∩ B) = AC ∩ B`, in
     [Classical.Structures.Group.Dedekind][]) and, downstream, of the
     permuting-complement and parachute arguments of the FLRP research program
     (`docs/notes/flrp-research-roadmap.md` § 4).
