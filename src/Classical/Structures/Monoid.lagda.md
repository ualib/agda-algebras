---
layout: default
file: "src/Classical/Structures/Monoid.lagda.md"
title: "Classical.Structures.Monoid module"
date: "2026-05-22"
author: "the agda-algebras development team"
---

### Monoids {#classical-structures-monoid}

This is the [Classical.Structures.Monoid][] module of the [Agda Universal Algebra Library][].

A **monoid** inhabits the Σ-typed structure `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Monoid` over `Sig-Monoid`.

Monoid is the first structure whose signature genuinely grows over its predecessor's
(`Sig-Monoid` adds `ε-Op` to `Sig-Magma`), and consequently the first whose forgetful
projection is not `proj₁` but a true *reduct*.

This module's prose is normative for every later signature-growing structure (Group,
Ring, etc.); the conventions it adds to the Semigroup template are as follows.

+  **Direct curried accessors, not inherited-through-the-forgetful**.  Where
   `Semigroup-Op` re-exported `_∙_` from `Magma-Op (semigroup→magma 𝑺)` — sound
   because that forgetful functor is `proj₁`, so the magma's `∙` *is* the semigroup's
   `∙` definitionally — `Monoid-Op` defines `_∙_ = Curry₂ (∙-Op ^ 𝑨)` and
   `ε = Curry₀ (ε-Op ^ 𝑨)` directly over `Sig-Monoid`; the reduct `monoid→magma`
   re-indexes arguments through the container morphism's position map, so the
   reduct's `∙` agrees with the monoid's only up to that map's reduction; defining
   the accessors directly keeps every downstream `refl` off that bet; each later
   signature-growing structure follows suit.

+  **Curried laws factored out above the forgetful**.  The curried associativity
   `mn-assoc` is proved once, standalone, before `monoid→semigroup`, because the
   forgetful's `Th-Semigroup` obligation consumes it; `Monoid-Op.assoc-law` then
   re-exposes the same `mn-assoc`, so there is a single proof of curried
   associativity, with a single proof; the acyclic ordering is
   `mn-assoc` → `Monoid-Op.assoc-law` (= `mn-assoc 𝑴`) → `monoid→semigroup`
   (which opens `Monoid-Op` for `assoc-law`).
+  **The forgetful is a reduct**.  `monoid→semigroup` reducts the
   `Sig-Monoid`-algebra to a `Sig-Magma`-algebra (dropping `ε-Op` via the container
   morphism `∙-incl`) and discharges `Th-Semigroup` from `mn-assoc` by the
   curried-law pivot — the monoid's curried associativity transfers to the reduct
   verbatim (reduct preserves carrier, `≈`, and `∙`), and is re-inflated to the reduct's
   `Sig-Magma` associativity terms by the reduct's own `interp-node∙`; no
   reduct-preserves-satisfaction term machinery is needed; see
   [ADR-002 v2](../../docs/adr/002-classical-layer-design.md) §5, §9.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Monoid where

open import Agda.Primitive                          using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Classical.Operations            using ( pair ; Curry₂ ; Curry₀ )
open import Classical.Signatures.Magma      using ( Sig-Magma ; Op-Magma ) renaming ( ∙-Op to ∙-Opᵐᵃ )
open import Classical.Signatures.Monoid     using ( Sig-Monoid ; Op-Monoid ; ∙-Op ; ε-Op )
open import Classical.Structures.Interpret  using ( interp-cong )
open import Classical.Structures.Magma      using ( Magma ; module Magma-Op ; opsToMagma )
open import Classical.Structures.Reduct     using ( reductBy )
open import Classical.Structures.Semigroup  using ( Semigroup ) renaming (_⊨_ to _⊨ˢᵍ_)
open import Classical.Theories.Monoid       using ( Eq-Monoid ; Th-Monoid ; assoc ; idˡ ; idʳ )
open import Classical.Theories.Semigroup    using ( Th-Semigroup ) renaming ( assoc to assocˢ )
open import Overture.Terms                  using ( Term ; ℊ ; node )
open import Overture.Signatures             using ( ArityOf ; OperationSymbolsOf)
open import Setoid.Algebras.Basic           using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms                    using ( module Environment )

open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Monoid} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### The local satisfaction predicate

```agda
infix 4 _⊨ᵐᵒ_
_⊨ᵐᵒ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-Monoid → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᵐᵒ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### The type of monoids

```agda
Monoid : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Monoid α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᵐᵒ Th-Monoid
```

#### The reduct to magmas

The container morphism `Sig-Magma ⟹ Sig-Monoid` sends the magma's `∙-Opᵐᵃ` to the
monoid's `∙-Op`; the position map is the identity (`Fin 2` to `Fin 2`).
`monoid→magma` is the induced reduct of the underlying algebra.

```agda
∙-incl : Op-Magma → Op-Monoid
∙-incl ∙-Opᵐᵃ = ∙-Op

∙-κ : (o : OperationSymbolsOf Sig-Magma)
      → ArityOf Sig-Monoid (∙-incl o)
      → ArityOf Sig-Magma o
∙-κ ∙-Opᵐᵃ = λ z → z
```

With that:

```agda
monoid→magma : Monoid α ρ → Magma α ρ
monoid→magma 𝑴 = reductBy ∙-incl ∙-κ (𝑴 .proj₁)
```

#### Curried associativity, standalone

`mn-assoc` proves `(x ∙ y) ∙ z ≈ x ∙ (y ∙ z)` for the monoid's own `∙`, from
`equations assoc`, via the local binary node-bridge `interp-node∙` built on
`IntMo.interp-cong`.  It is defined here, above the forgetful, so both
`monoid→semigroup` and `Monoid-Op.assoc-law` can consume it.  The proof is a
verbatim port of `Semigroup-Op.assoc-law` to `Sig-Monoid`.

```agda
module _ (𝑴 : Monoid α ρ) where
  private 𝑨 = proj₁ 𝑴
  open Setoid 𝔻[ 𝑨 ] using (_≈_; sym) renaming (refl to ≈refl)
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  private
    infixl 7 _∙_
    _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
    _∙_ = Curry₂ (∙-Op ^ 𝑨)

    interp-node∙ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑨 ])
      → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)
    interp-node∙ s t η = interp-cong 𝑨 ∙-Op (λ { 0F → ≈refl ; 1F → ≈refl })

  mn-assoc : ∀ x y z → x ∙ y ∙ z ≈ x ∙ (y ∙ z)
  mn-assoc x y z = begin
    x ∙ y ∙ z       ≈˘⟨ interp-cong 𝑨 ∙-Op (λ { 0F → interp-node∙ (ℊ 0F) (ℊ 1F) η ; 1F → ≈refl }) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η  ≈⟨ proj₂ 𝑴 assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η  ≈⟨ interp-cong 𝑨 ∙-Op (λ { 0F → ≈refl ; 1F → interp-node∙ (ℊ 1F) (ℊ 2F) η }) ⟩
    x ∙ (y ∙ z)     ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }

    lhsT rhsT : Term (Fin 3)
    lhsT = node ∙-Op (pair (node ∙-Op (pair (ℊ 0F) (ℊ 1F))) (ℊ 2F))
    rhsT = node ∙-Op (pair (ℊ 0F) (node ∙-Op (pair (ℊ 1F) (ℊ 2F))))
```

#### The `Monoid-Op` module

```agda
module Monoid-Op {α ρ : Level} (𝑴 : Monoid α ρ) where
  private 𝑨 = proj₁ 𝑴
  open Setoid 𝔻[ 𝑨 ] using (_≈_; trans; sym) renaming (refl to ≈refl)
  open Environment 𝑨 using ( ⟦_⟧ )

  infixl 7 _∙_
  _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _∙_ = Curry₂ (∙-Op ^ 𝑨)

  ε : 𝕌[ 𝑨 ]
  ε = Curry₀ (ε-Op ^ 𝑨)

  equations : 𝑨 ⊨ᵐᵒ Th-Monoid
  equations = proj₂ 𝑴

  ∙-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x ∙ u ≈ y ∙ v
  ∙-cong x≈y u≈v = interp-cong 𝑨 ∙-Op (λ { 0F → x≈y ; 1F → u≈v })

  interp-node-∙ : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∙ ⟦ t ⟧ ⟨$⟩ η
  interp-node-∙ s t = interp-cong 𝑨 ∙-Op (λ { 0F → ≈refl ; 1F → ≈refl })

  interp-node-ε : {η : Fin 3 → 𝕌[ 𝑨 ]} → ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η ≈ ε
  interp-node-ε = interp-cong 𝑨 ε-Op (λ ())

  assoc-law : ∀ x y z → x ∙ y ∙ z ≈ x ∙ (y ∙ z)
  assoc-law = mn-assoc 𝑴

  idˡ-law : ∀ x → ε ∙ x ≈ x
  idˡ-law x = trans (∙-cong (sym interp-node-ε) ≈refl)
                    (trans (sym (interp-node-∙ (node ε-Op (λ ())) (ℊ 0F)))
                           (equations idˡ (λ _ → x)))

  idʳ-law : ∀ x → x ∙ ε ≈ x
  idʳ-law x = trans (∙-cong ≈refl (sym (interp-node-ε)))
                    (trans (sym (interp-node-∙ (ℊ 0F) (node ε-Op (λ ()))))
                           (equations idʳ (λ _ → x)))
```

#### The forgetful projection to semigroups

```agda
monoid→semigroup : Monoid α ρ → Semigroup α ρ
monoid→semigroup ℳ@(𝑴 , _) = 𝑹 , thm
  where
  𝑹 : Magma _ _
  𝑹 = monoid→magma ℳ
  open Algebra 𝑴 using () renaming (Domain to M)
  open Algebra 𝑹 using () renaming (Domain to R)
  open Setoid M using (_≈_; sym) renaming (refl to ≈refl)
  open Setoid R using () renaming (_≈_ to _≋_ )
  open Environment 𝑹 using ( ⟦_⟧ )    -- Sig-Magma environment on 𝑹
  open SetoidReasoning M
  open Magma-Op 𝑹 using ( _∙_ )  -- 𝑹's curried ∙, over Sig-Magma

  -- 𝑹's binary node-bridge, over Sig-Magma
  interp-congᴿ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑴 ])
      → ⟦ node ∙-Opᵐᵃ (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)
  interp-congᴿ s t η = interp-cong 𝑹 ∙-Opᵐᵃ λ { 0F → ≈refl ; 1F → ≈refl }

  -- 𝑹's curried-∙ congruence
  ∙-congᴿ : ∀ {a b c d} → a ≈ b → c ≈ d → (a ∙ c) ≈ (b ∙ d)
  ∙-congᴿ a≈b c≈d = interp-cong 𝑹 ∙-Opᵐᵃ (λ { 0F → a≈b ; 1F → c≈d })

  thm : 𝑹 ⊨ˢᵍ Th-Semigroup
  thm assocˢ η = begin
    ⟦ Th-Semigroup assocˢ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-congᴿ xy (ℊ 2F) η ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∙ z                      ≈⟨ ∙-congᴿ (interp-congᴿ (ℊ 0F) (ℊ 1F) η) ≈refl ⟩
    x ∙ y ∙ z                             ≈⟨ assoc-law x y z ⟩
    x ∙ (y ∙ z)                           ≈˘⟨ ∙-congᴿ ≈refl (interp-congᴿ (ℊ 1F) (ℊ 2F) η) ⟩
    x ∙ ⟦ yz ⟧ ⟨$⟩ η                      ≈˘⟨ interp-congᴿ (ℊ 0F) yz η ⟩
    ⟦ Th-Semigroup assocˢ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    open Monoid-Op ℳ using ( assoc-law ) -- the monoid's curried associativity
    x y z : 𝕌[ 𝑴 ]
    x = η 0F ; y = η 1F ; z = η 2F
    xy yz : Term (Fin 3)
    xy = node ∙-Opᵐᵃ (pair (ℊ 0F) (ℊ 1F))   -- the subterm  x ∙ y
    yz = node ∙-Opᵐᵃ (pair (ℊ 1F) (ℊ 2F))   -- the subterm  y ∙ z
```

The statement is `𝑹 ⊧ (Sig-Magma assoc-lhs) ≈ (Sig-Magma assoc-rhs)` under every `η`,
and the proof is the curried-law pivot: unfold both `Sig-Magma` terms to the reduct's
curried `∙ᴿ` via `IntMa.interp-cong 𝑹 ∙-Opᵐᵃ`, apply `mn-assoc 𝑴` (whose `∙` is that
of the monoid, definitionally equal to `∙ᴿ` since the position map is `id`), then
refold.  Mechanically identical to `Semigroup-Op.assoc-law` but on `𝑹` and pivoting
through `mn-assoc 𝑴` in the middle.

#### Monoid Builders

`opsToBareMonoid` builds a "raw" algebra in the signature of a monoid from a carrier,
a binary operation, and an identity element.  It is `opsToMagma` followed by one
`expand-ε`, building the magma over `≡.setoid A` and adjoining `e` as the
interpretation of `ε-Op`.

```agda
opsToBareMonoid : (A : Type α) (_·_ : A → A → A) (e : A) → Algebra {𝑆 = Sig-Monoid} α α
opsToBareMonoid A _·_ e = expand-ε e

  where
  open Algebra
  𝑩 : Algebra {𝑆 = Sig-Magma} _ _
  𝑩 = opsToMagma A _·_
  -- expand-ε is the expand half of the reduct/expand dual at the Sig-Magma ↪ Sig-Monoid
  -- step, written inline; we'll construct a shared `expand` module once Group's
  -- expand-⁻¹ provides a second consumer.
  expand-ε : A → Algebra {𝑆 = Sig-Monoid} _ _
  expand-ε _ .Domain = 𝔻[ 𝑩 ]
  expand-ε _ .Interp ⟨$⟩ (∙-Op , args) = (∙-Opᵐᵃ ^ 𝑩) args
  expand-ε e .Interp ⟨$⟩ (ε-Op , _) = e
  expand-ε _ .Interp .cong {∙-Op , _} {.∙-Op , _} (refl , u≈v) = cong (𝑩 .Interp) (refl , u≈v)
  expand-ε _ .Interp .cong {ε-Op , _} {.ε-Op , _} (refl , _) = Setoid.refl 𝔻[ 𝑩 ]
```

`eqsToMonoid` builds a Monoid by first building the raw algebra via `opsToBareMonoid`,
then proving the monoid laws from the given equations.  The proof is a verbatim port
of `Semigroup-Op.assoc-law` to `Sig-Monoid` for associativity, and straightforward
for the identity laws.

```agda
eqsToMonoid : (A : Type α) (_·_ : A → A → A) (e : A)
  → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  → (·-idˡ : ∀ a → e · a ≡ a) (·-idʳ : ∀ a → a · e ≡ a)
  → Monoid α α
eqsToMonoid A _·_ e ·-assoc ·-idˡ ·-idʳ = opsToBareMonoid A _·_ e , proof
  where
  proof : opsToBareMonoid A _·_ e ⊨ᵐᵒ Th-Monoid
  proof assoc ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof idˡ ρ = ·-idˡ (ρ 0F)
  proof idʳ ρ = ·-idʳ (ρ 0F)
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Semigroup](Classical.Structures.Semigroup.html)</span>
<span style="float:right;">[Classical.Structures.Group →](Classical.Structures.Group.html)</span>

{% include UALib.Links.md %}
