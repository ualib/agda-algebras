---
layout: default
file: "src/Classical/Structures/Group/Complements.lagda.md"
title: "Classical.Structures.Group.Complements module"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Permuting complements in an interval of the subgroup lattice

This is the [Classical.Structures.Group.Complements][] module of the [Agda Universal Algebra Library][].

Fix subgroups `H ≤ G` and an intermediate subgroup `A ∈ [H , G]`.  A **complement of
`A` in the interval `[H , G]`** is a subgroup `B ∈ [H , G]` with `A ∩ B = H` and
`⟨A , B⟩ = G`; the note of the FLRP program writes `A^⊥(H,G)` for the set of these.[^1]
The result this module is built for is the note's Corollary 3.5:

> if every member of a set `ℬ ⊆ A^⊥(H,G)` permutes with `A`, then `ℬ` is an antichain.

The proof is one application of Dedekind's rule
([Classical.Structures.Group.Dedekind][]): if `B₁ ≤ B₂` are two such complements then

    B₁ = B₁H = B₁(A ∩ B₂) = B₁A ∩ B₂ = G ∩ B₂ = B₂,

so no strict containment is possible.

**Complements, formalized through the complex product.**  Two of the note's
hypotheses — that `B` permutes with `A` (`AB = BA`) and that `A` and `B` join to `G`
— are used only through their conjunction, which is the single statement `BA = G`:
the *complex product* `B ∙ᶜ A` of [Classical.Structures.Group.Complexes][] exhausts
the group.  We take that statement, `Factorize`{.AgdaFunction}, as the primitive.
It is exactly equivalent to the note's pair of hypotheses — a permuting pair of
subgroups has `⟨A , B⟩ = AB` — and it keeps the argument free of the *generated*
subgroup, whose inductive presentation would otherwise have to be unfolded.  The
join hypothesis is recovered where consumers need it: a factorization of `G` is
inherited by any subgroup containing `A` and `B`
(`Factorize-least`{.AgdaFunction}), which is the universal property of the join.

The module also collects the small facts about complex products that the argument and
its FLRP consumers need: a permuting product of subgroups is a subgroup
(`permuting-∙ᶜ-isSubgroup`{.AgdaFunction}), a normal subgroup permutes with
everything (`normal-permutes`{.AgdaFunction}), and hence `NB` is a subgroup for `N`
normal (`normal-∙ᶜ-isSubgroup`{.AgdaFunction}) — the subgroup `NH` on which the
parachute theorems turn.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Complements where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using ( _,_ ; proj₁ ; proj₂ )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; _∩_ ; _≐_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group                 using ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic        using ( Group ; module Group-Op )
open import Classical.Structures.Group.Complexes    using ( module Complex )
open import Classical.Structures.Group.Conjugation  using ( module Conj )
open import Classical.Structures.Group.Dedekind     using ( dedekindˡ )
open import Classical.Structures.Group.Subgroups    using ( IsSubgroup ; mkIsSubgroup )
open import Setoid.Algebras.Basic                   using ( Algebra ; 𝕌[_] ; 𝔻[_] )

private variable ℓᵃ ℓᵇ ℓᶜ ℓʰ ℓⁿ : Level
```
-->

#### The toolkit

```agda
module Complements {α ρ : Level} (𝒢 : Group α ρ) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢  using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; assoc-law
                          ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using ( ⁻¹-involutive ; ⁻¹-anti-homo-∙ )
  open Complex 𝒢  using  ( _∙ᶜ_ ; mem-∙ᶜ ; ∙ᶜ-respects ; ∙ᶜ-mono ; subgroup-∙ᶜ-idem )
  open Conj 𝒢 using ( conj ; IsNormal )
```

A member of one factor is a member of the product, provided the *other* factor
contains the identity — the two one-sided inclusions `P ⊆ P Q` and `Q ⊆ P Q`.

```agda
  -- p ≈ p ∙ ε, so the left factor embeds when the right one contains ε.
  mem-∙ᶜˡ : {P : Pred G ℓᵃ} {Q : Pred G ℓᵇ} → ε ∈ Q → P ⊆ P ∙ᶜ Q
  mem-∙ᶜˡ {P = P} {Q} ε∈Q {x} x∈P = ∙ᶜ-respects P Q (idʳ-law x) (mem-∙ᶜ x∈P ε∈Q)

  -- q ≈ ε ∙ q, dually.
  mem-∙ᶜʳ : {P : Pred G ℓᵃ} {Q : Pred G ℓᵇ} → ε ∈ P → Q ⊆ P ∙ᶜ Q
  mem-∙ᶜʳ {P = P} {Q} ε∈P {x} x∈Q = ∙ᶜ-respects P Q (idˡ-law x) (mem-∙ᶜ ε∈P x∈Q)
```

#### Permuting subsets

Two subsets **permute** when their complex products in the two orders agree.  This
is the note's hypothesis on the members of `ℬ`, and it is what makes the product
`A B` a subgroup rather than a mere subset.

```agda
  infix 4 _permutes_

  -- P and Q permute: P Q = Q P as subsets.
  _permutes_ : Pred G ℓᵃ → Pred G ℓᵇ → Type (α ⊔ ρ ⊔ ℓᵃ ⊔ ℓᵇ)
  P permutes Q = (P ∙ᶜ Q) ≐ (Q ∙ᶜ P)
```

The product of two permuting subgroups is a subgroup.  Closure under `∙` is the one
step that consumes permutation: in `(a₁b₁)(a₂b₂)` the middle pair `b₁a₂` is
rewritten as some `a₃b₃`, after which associativity regroups the four factors.

```agda
  permuting-∙ᶜ-isSubgroup : {A : Pred G ℓᵃ} {B : Pred G ℓᵇ}
    →  IsSubgroup 𝒢 A → IsSubgroup 𝒢 B → A permutes B → IsSubgroup 𝒢 (A ∙ᶜ B)
  permuting-∙ᶜ-isSubgroup {A = A} {B} A-sg B-sg (AB⊆BA , BA⊆AB) =
    mkIsSubgroup 𝒢 (∙ᶜ-respects A B) ∙-c ε-c ⁻¹-c
    where
    open IsSubgroup A-sg using () renaming ( ∙-closed to A∙ ; ε-closed to Aε ; ⁻¹-closed to A⁻¹ )
    open IsSubgroup B-sg using () renaming ( ∙-closed to B∙ ; ε-closed to Bε ; ⁻¹-closed to B⁻¹ )

    ε-c : ε ∈ A ∙ᶜ B
    ε-c = ∙ᶜ-respects A B (idˡ-law ε) (mem-∙ᶜ Aε Bε)

    ∙-c : ∀ {x y} → x ∈ A ∙ᶜ B → y ∈ A ∙ᶜ B → x ∙ y ∈ A ∙ᶜ B
    ∙-c {x} {y} (a₁ , b₁ , a₁∈A , b₁∈B , x≈a₁b₁) (a₂ , b₂ , a₂∈A , b₂∈B , y≈a₂b₂) =
      ∙ᶜ-respects A B (≈sym regroup) (mem-∙ᶜ (A∙ a₁∈A a₃∈A) (B∙ b₃∈B b₂∈B))
      where
      -- The middle pair b₁ a₂ lies in B A = A B, so it is some a₃ b₃.
      swap : b₁ ∙ a₂ ∈ A ∙ᶜ B
      swap = BA⊆AB (mem-∙ᶜ b₁∈B a₂∈A)

      a₃ = proj₁ swap
      b₃ = proj₁ (proj₂ swap)
      a₃∈A = proj₁ (proj₂ (proj₂ swap))
      b₃∈B = proj₁ (proj₂ (proj₂ (proj₂ swap)))
      b₁a₂≈a₃b₃ = proj₂ (proj₂ (proj₂ (proj₂ swap)))

      regroup : x ∙ y ≈ (a₁ ∙ a₃) ∙ (b₃ ∙ b₂)
      regroup = begin
        x ∙ y                    ≈⟨ ∙-cong x≈a₁b₁ y≈a₂b₂ ⟩
        (a₁ ∙ b₁) ∙ (a₂ ∙ b₂)    ≈˘⟨ assoc-law (a₁ ∙ b₁) a₂ b₂ ⟩
        ((a₁ ∙ b₁) ∙ a₂) ∙ b₂    ≈⟨ ∙-cong (assoc-law a₁ b₁ a₂) ≈refl ⟩
        (a₁ ∙ (b₁ ∙ a₂)) ∙ b₂    ≈⟨ ∙-cong (∙-cong ≈refl b₁a₂≈a₃b₃) ≈refl ⟩
        (a₁ ∙ (a₃ ∙ b₃)) ∙ b₂    ≈˘⟨ ∙-cong (assoc-law a₁ a₃ b₃) ≈refl ⟩
        ((a₁ ∙ a₃) ∙ b₃) ∙ b₂    ≈⟨ assoc-law (a₁ ∙ a₃) b₃ b₂ ⟩
        (a₁ ∙ a₃) ∙ (b₃ ∙ b₂)    ∎

    ⁻¹-c : ∀ {x} → x ∈ A ∙ᶜ B → x ⁻¹ ∈ A ∙ᶜ B
    ⁻¹-c {x} (a , b , a∈A , b∈B , x≈ab) =
      BA⊆AB (∙ᶜ-respects B A (≈sym anti) (mem-∙ᶜ (B⁻¹ b∈B) (A⁻¹ a∈A)))
      where
      anti : x ⁻¹ ≈ b ⁻¹ ∙ a ⁻¹
      anti = ≈trans (⁻¹-cong x≈ab) (⁻¹-anti-homo-∙ a b)
```

#### Normal subgroups permute with everything

A normal subgroup permutes with every subset: `n b ≈ b (b⁻¹ n b)` moves a normal
element across a factor, and `(b n b⁻¹) b ≈ b n` moves it back.  Consequently `N B`
is a subgroup whenever `N` is normal and both are subgroups — this is the subgroup
`NH` of the parachute argument.

```agda
  -- Moving a conjugate across a factor, in the two directions.
  private
    swapˡ : ∀ b n → b ∙ (conj (b ⁻¹) n) ≈ n ∙ b
    swapˡ b n = begin
      b ∙ (b ⁻¹ ∙ n ∙ (b ⁻¹) ⁻¹)  ≈⟨ ∙-cong ≈refl (∙-cong ≈refl (⁻¹-involutive b)) ⟩
      b ∙ (b ⁻¹ ∙ n ∙ b)          ≈˘⟨ assoc-law b (b ⁻¹ ∙ n) b ⟩
      (b ∙ (b ⁻¹ ∙ n)) ∙ b        ≈˘⟨ ∙-cong (assoc-law b (b ⁻¹) n) ≈refl ⟩
      ((b ∙ b ⁻¹) ∙ n) ∙ b        ≈⟨ ∙-cong (∙-cong (invʳ-law b) ≈refl) ≈refl ⟩
      (ε ∙ n) ∙ b                 ≈⟨ ∙-cong (idˡ-law n) ≈refl ⟩
      n ∙ b                       ∎

    swapʳ : ∀ b n → (conj b n) ∙ b ≈ b ∙ n
    swapʳ b n = begin
      (b ∙ n ∙ b ⁻¹) ∙ b   ≈⟨ assoc-law (b ∙ n) (b ⁻¹) b ⟩
      (b ∙ n) ∙ (b ⁻¹ ∙ b) ≈⟨ ∙-cong ≈refl (invˡ-law b) ⟩
      (b ∙ n) ∙ ε          ≈⟨ idʳ-law (b ∙ n) ⟩
      b ∙ n                ∎

  -- A normal subset permutes with every subset.
  normal-permutes : {N : Pred G ℓⁿ} (B : Pred G ℓᵇ) → IsNormal N → N permutes B
  normal-permutes {N = N} B N-normal = to , from
    where
    to : N ∙ᶜ B ⊆ B ∙ᶜ N
    to {x} (n , b , n∈N , b∈B , x≈nb) =
      b , conj (b ⁻¹) n , b∈B , N-normal (b ⁻¹) n∈N , ≈trans x≈nb (≈sym (swapˡ b n))

    from : B ∙ᶜ N ⊆ N ∙ᶜ B
    from {x} (b , n , b∈B , n∈N , x≈bn) =
      conj b n , b , N-normal b n∈N , b∈B , ≈trans x≈bn (≈sym (swapʳ b n))

  -- Hence the product of a normal subgroup with any subgroup is a subgroup.
  normal-∙ᶜ-isSubgroup : {N : Pred G ℓⁿ} {B : Pred G ℓᵇ}
    →  IsNormal N → IsSubgroup 𝒢 N → IsSubgroup 𝒢 B → IsSubgroup 𝒢 (N ∙ᶜ B)
  normal-∙ᶜ-isSubgroup {B = B} N-normal N-sg B-sg =
    permuting-∙ᶜ-isSubgroup N-sg B-sg (normal-permutes B N-normal)
```

#### Factorizations of the group

`Factorize P Q` says the complex product `P Q` exhausts the group.  For subgroups
this is the note's "`P` and `Q` permute and `⟨P , Q⟩ = G`", packaged as one
statement: it is symmetric (invert a factorization elementwise), and it is inherited
by every subgroup above both factors, which is the join's universal property.

```agda
  -- Every element of the group is a product of a member of P and a member of Q.
  Factorize : Pred G ℓᵃ → Pred G ℓᵇ → Type (α ⊔ ρ ⊔ ℓᵃ ⊔ ℓᵇ)
  Factorize P Q = ∀ x → x ∈ P ∙ᶜ Q

  -- A factorization of the group by subgroups may be read in either order:
  -- x ⁻¹ ≈ p ∙ q gives x ≈ q ⁻¹ ∙ p ⁻¹.
  Factorize-sym : {P : Pred G ℓᵃ} {Q : Pred G ℓᵇ}
    →  IsSubgroup 𝒢 P → IsSubgroup 𝒢 Q → Factorize P Q → Factorize Q P
  Factorize-sym {P = P} {Q} P-sg Q-sg fact x = ∙ᶜ-respects Q P (≈sym anti) mem
    where
    open IsSubgroup P-sg using () renaming ( ⁻¹-closed to P⁻¹ )
    open IsSubgroup Q-sg using () renaming ( ⁻¹-closed to Q⁻¹ )

    p = proj₁ (fact (x ⁻¹))
    q = proj₁ (proj₂ (fact (x ⁻¹)))
    p∈P = proj₁ (proj₂ (proj₂ (fact (x ⁻¹))))
    q∈Q = proj₁ (proj₂ (proj₂ (proj₂ (fact (x ⁻¹)))))
    x⁻¹≈pq = proj₂ (proj₂ (proj₂ (proj₂ (fact (x ⁻¹)))))

    anti : x ≈ q ⁻¹ ∙ p ⁻¹
    anti = begin
      x                ≈˘⟨ ⁻¹-involutive x ⟩
      (x ⁻¹) ⁻¹        ≈⟨ ⁻¹-cong x⁻¹≈pq ⟩
      (p ∙ q) ⁻¹       ≈⟨ ⁻¹-anti-homo-∙ p q ⟩
      q ⁻¹ ∙ p ⁻¹      ∎

    mem : q ⁻¹ ∙ p ⁻¹ ∈ Q ∙ᶜ P
    mem = mem-∙ᶜ (Q⁻¹ q∈Q) (P⁻¹ p∈P)

  -- A factorization of the group is inherited by any subgroup containing both
  -- factors: this is "⟨P , Q⟩ = G" in its universal-property form.
  Factorize-least : {P : Pred G ℓᵃ} {Q : Pred G ℓᵇ} {C : Pred G ℓᶜ}
    →  IsSubgroup 𝒢 C → P ⊆ C → Q ⊆ C → Factorize P Q → (x : G) → x ∈ C
  Factorize-least {C = C} C-sg P⊆C Q⊆C fact x =
    proj₁ (subgroup-∙ᶜ-idem C-sg) (∙ᶜ-mono P⊆C Q⊆C (fact x))
```

#### Corollary 3.5: comparable permuting complements collapse

The heart of the matter, in the form the parachute argument uses: if `B₁ ≤ B₂` are
subgroups of the interval `[H , G]`, if `B₂` meets `A` in `H`, and if `B₁ A = G`,
then already `B₂ ≤ B₁`.  Reading the note's chain of equalities from the right, an
element `x ∈ B₂` lies in `B₁A ∩ B₂`, hence — by Dedekind's rule, which applies
because `B₁ ≤ B₂` and `B₂` is a subgroup — in `B₁(A ∩ B₂)`; the meet hypothesis
shrinks the second factor to `H ⊆ B₁`, and `B₁B₁ = B₁` collapses the product.

```agda
  complement-⊆-collapse :
       {H : Pred G ℓʰ} {A : Pred G ℓᵃ} {B₁ B₂ : Pred G ℓᵇ}
    →  IsSubgroup 𝒢 B₁ → IsSubgroup 𝒢 B₂
    →  H ⊆ B₁ → B₁ ⊆ B₂
    →  (A ∩ B₂) ⊆ H
    →  Factorize B₁ A
    →  B₂ ⊆ B₁
  complement-⊆-collapse {H = H} {A} {B₁} {B₂} B₁-sg B₂-sg H⊆B₁ B₁⊆B₂ meet-⊆ fact {x} x∈B₂ =
    proj₁ (subgroup-∙ᶜ-idem B₁-sg) inside
    where
    -- x lies in B₁A and in B₂ ...
    step₁ : x ∈ (B₁ ∙ᶜ A) ∩ B₂
    step₁ = fact x , x∈B₂

    -- ... hence in B₁(A ∩ B₂), by Dedekind's rule ...
    step₂ : x ∈ B₁ ∙ᶜ (A ∩ B₂)
    step₂ = proj₂ (dedekindˡ 𝒢 {H = B₁} {C = A} {K = B₂} B₂-sg B₁⊆B₂) step₁

    -- ... and A ∩ B₂ ⊆ H ⊆ B₁ turns that into a product of two members of B₁.
    inside : x ∈ B₁ ∙ᶜ B₁
    inside = ∙ᶜ-mono (λ z → z) (λ z → H⊆B₁ (meet-⊆ z)) step₂
```

An **antichain** of subgroups, indexed by a type `I`, is a family in which no member
is contained in another except when the containment reverses — the constructive
reading of "pairwise incomparable" for subsets ordered by inclusion, where equality
*is* mutual containment.

The corollary itself: a family of permuting complements of `A` in `[H , G]` is an
antichain.

```agda
  -- No strict containments: a containment between members is mutual.
  Antichain : {I : Type ℓᶜ} → (I → Pred G ℓᵇ) → Type (ℓᶜ ⊔ α ⊔ ℓᵇ)
  Antichain {I = I} ℬ = (i j : I) → ℬ i ⊆ ℬ j → ℬ j ⊆ ℬ i

  -- Corollary 3.5 (cor:dedekind1 of the note).
  complements-antichain :
       {I : Type ℓᶜ} {H : Pred G ℓʰ} {A : Pred G ℓᵃ} (ℬ : I → Pred G ℓᵇ)
    →  (∀ i → IsSubgroup 𝒢 (ℬ i))
    →  (∀ i → H ⊆ ℬ i)                    -- every member lies in the interval [H , G]
    →  (∀ i → (A ∩ ℬ i) ⊆ H)              -- every member meets A in H
    →  (∀ i → Factorize (ℬ i) A)          -- every member permutes with A and joins it to G
    →  Antichain ℬ
  complements-antichain ℬ ℬ-sg H⊆ℬ meet fact i j ℬi⊆ℬj =
    complement-⊆-collapse (ℬ-sg i) (ℬ-sg j) (H⊆ℬ i) ℬi⊆ℬj (meet j) (fact i)
```

---

[^1]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, § 3.2 (Dedekind's rule)
      and § 3.3 (parachute lattices); see also
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 4
      and the design note `docs/notes/flrp-rp1-parachutes.md`.
