---
layout: default
file: "src/Classical/Structures/Group/Basic.lagda.md"
title: "Classical.Structures.Group.Basic module"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Groups {#classical-structures-group}

This is the [Classical.Structures.Group.Basic][] module of the [Agda Universal Algebra Library][].

A **group** inhabits the Σ-typed structure `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Group` over
`Sig-Group`.  Group is the first structure whose signature grows over its
predecessor's by a *unary* symbol (`Sig-Group` adds `⁻¹-Op` to `Sig-Monoid`); its
forgetful projection `group→monoid` is therefore a reduct that drops `⁻¹-Op`,
discharging the three monoid equations on the reduct by the curried-law pivot of
the `monoid→semigroup` of [`Classical.Structures.Monoid`][Classical.Structures.Monoid] (here extended from one
law to three, the two identity laws additionally bridging the nullary `ε-Op` node).

This module follows the [Monoid][Classical.Structures.Monoid] template, adding the
following to it.

+  **Direct curried accessors for all three operations**.  `Group-Op` defines
   `_∙_ = Curry₂ (∙-Op ^ 𝑨)`, `ε = Curry₀ (ε-Op ^ 𝑨)`, and
   `_⁻¹ = Curry₁ (⁻¹-Op ^ 𝑨)` directly over `Sig-Group`, never inheriting through the
   reduct, for the reason Monoid gives: keeping the accessors direct keeps every
   downstream `refl` off the reduct's position-map reduction.
+  **A unary node-bridge**.  Alongside the binary `interp-node-∙` and nullary
   `interp-node-ε`, `Group-Op` has `interp-node-⁻¹` for the unary `⁻¹-Op`, a
   one-liner delegating to `interp-cong` exactly as the other two do.
+  **Two inverse laws**.  `invˡ-law` and `invʳ-law` join the three monoid laws in
   `Group-Op`; they are the only laws not consumed by the forgetful (which lands in
   `Monoid`, below the inverse structure), so they live in `Group-Op` rather than in
   the standalone curried-law block.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Basic where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong ; cong₂ ; setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Classical.Operations            using  ( pair ; Curry₂ ; Curry₁ ; Curry₀ )
open import Classical.Signatures.Monoid     using  ( Sig-Monoid ; Op-Monoid )
                                            renaming ( ∙-Op to ∙-Opᵐᵒ ; ε-Op to ε-Opᵐᵒ )
open import Classical.Signatures.Group      using  ( Sig-Group ; Op-Group ; ∙-Op ; ε-Op ; ⁻¹-Op ; ar-Group)
open import Classical.Structures.Interpret  using  ( interp-cong )
open import Setoid.Algebras.Reduct          using  ( reductBy )
open import Classical.Structures.Monoid     using  ( Monoid ; _⊨ᵐᵒ_ )
open import Classical.Theories.Group        using  ( Eq-Group ; Th-Group
                                                   ; assoc ; idˡ ; idʳ ; invˡ ; invʳ )
open import Classical.Theories.Monoid       using  ( Th-Monoid )
                                            renaming ( assoc to assocᵐ ; idˡ to idˡᵐ ; idʳ to idʳᵐ )
open import Overture.Terms                  using  ( Term ; ℊ ; node )
open import Overture.Signatures             using  ( ArityOf ; OperationSymbolsOf )
open import Setoid.Algebras.Basic           using  ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms                    using  ( module Environment )

open import Setoid.Varieties.EquationalLogic using ( _⊧_≈_ )

private variable α ρ : Level
```
-->

#### The local satisfaction predicate

```agda
infix 4 _⊨ᵍᵖ_
_⊨ᵍᵖ_ : (𝑨 : Algebra {𝑆 = Sig-Group} α ρ) (ℰ : Eq-Group → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᵍᵖ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### The type of groups

```agda
Group : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Group α ρ = Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Group} α ρ ] 𝑨 ⊨ᵍᵖ Th-Group
```

#### The reduct to monoids

The container morphism `Sig-Monoid ⟹ Sig-Group` sends the monoid's `∙-Opᵐᵒ` and
`ε-Opᵐᵒ` to the group's `∙-Op` and `ε-Op`; the position maps are the identity.
`group→monoidAlg` is the induced reduct of the underlying algebra.

```agda
mo-incl : Op-Monoid → Op-Group
mo-incl ∙-Opᵐᵒ = ∙-Op
mo-incl ε-Opᵐᵒ = ε-Op

mo-κ : (o : OperationSymbolsOf Sig-Monoid)
  → ArityOf Sig-Group (mo-incl o) → ArityOf Sig-Monoid o
mo-κ ∙-Opᵐᵒ = λ z → z
mo-κ ε-Opᵐᵒ = λ z → z

group→monoidAlg : Group α ρ → Algebra {𝑆 = Sig-Monoid} α ρ
group→monoidAlg 𝑮 = reductBy mo-incl mo-κ (𝑮 .proj₁)
```

#### Curried associativity, standalone

`gp-assoc` proves `(x ∙ y) ∙ z ≈ x ∙ (y ∙ z)` for the group's own `∙`, a verbatim
port of `Monoid-Op.mn-assoc` to `Sig-Group`.  It is standalone, above the forgetful,
so both `Group-Op.assoc-law` and the `group→monoid` discharge consume one proof.

```agda
module _ (𝑮 : Group α ρ) where
  private 𝑨 = proj₁ 𝑮
  open Setoid 𝔻[ 𝑨 ] using (_≈_) renaming (sym to ≈sym ; refl to ≈refl)
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  private
    infixl 7 _∙_
    _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
    _∙_ = Curry₂ (∙-Op ^ 𝑨)

    interp-node∙ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑨 ])
      → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∙ ⟦ t ⟧ ⟨$⟩ η
    interp-node∙ s t η = interp-cong 𝑨 ∙-Op λ { 0F → ≈refl ; 1F → ≈refl }

  gp-assoc : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  gp-assoc x y z = begin
    x ∙ y ∙ z                ≈˘⟨ interp-cong 𝑨 ∙-Op γ ⟩
    ⟦ node ∙-Op lhs ⟧ ⟨$⟩ η  ≈⟨ proj₂ 𝑮 assoc η ⟩
    ⟦ node ∙-Op rhs ⟧ ⟨$⟩ η  ≈⟨ interp-cong 𝑨 ∙-Op γ' ⟩
    x ∙ (y ∙ z)              ∎
    where
    g0 g1 g2 : Term (Fin 3)
    g0 = ℊ 0F; g1 = ℊ 1F; g2 = ℊ 2F

    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }

    lhs rhs : Fin 2 → Term (Fin 3)
    lhs = pair (node ∙-Op (pair g0 g1)) g2
    rhs = pair g0 (node ∙-Op (pair g1 g2))

    γ : ∀ i → ⟦ lhs i ⟧ ⟨$⟩ η ≈ pair (x ∙ y) z i
    γ = λ { 0F → interp-node∙ g0 g1 η; 1F → ≈refl }

    γ' : ∀ i → ⟦ rhs i ⟧ ⟨$⟩ η ≈ pair x (y ∙ z) i
    γ' = λ { 0F → ≈refl ; 1F → interp-node∙ g1 g2 η }
```

#### The `Group-Op` module

```agda
module Group-Op {α ρ : Level} (𝑮 : Group α ρ) where
  private 𝑨 = proj₁ 𝑮
  open Setoid 𝔻[ 𝑨 ] using (_≈_) renaming (trans to ≈trans; sym to ≈sym; refl to ≈refl)
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Environment 𝑨 using ( ⟦_⟧ )

  infixl 7 _∙_
  _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _∙_ = Curry₂ (∙-Op ^ 𝑨)

  ε : 𝕌[ 𝑨 ]
  ε = Curry₀ (ε-Op ^ 𝑨)

  infix 8 _⁻¹
  _⁻¹ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _⁻¹ = Curry₁ (⁻¹-Op ^ 𝑨)

  equations : 𝑨 ⊨ᵍᵖ Th-Group
  equations = proj₂ 𝑮

  ∙-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x ∙ u ≈ y ∙ v
  ∙-cong x≈y u≈v = interp-cong 𝑨 ∙-Op (λ { 0F → x≈y ; 1F → u≈v })

  ⁻¹-cong : ∀ {x y} → x ≈ y → x ⁻¹ ≈ y ⁻¹
  ⁻¹-cong x≈y = interp-cong 𝑨 ⁻¹-Op (λ { 0F → x≈y })

  interp-node-∙ : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∙ ⟦ t ⟧ ⟨$⟩ η
  interp-node-∙ s t = interp-cong 𝑨 ∙-Op (λ { 0F → ≈refl ; 1F → ≈refl })

  interp-node-ε : {η : Fin 3 → 𝕌[ 𝑨 ]} → ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η ≈ ε
  interp-node-ε = interp-cong 𝑨 ε-Op (λ ())

  interp-node-⁻¹ : (s : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑨 ]}
    → ⟦ node ⁻¹-Op (λ _ → s) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ⁻¹
  interp-node-⁻¹ s = interp-cong 𝑨 ⁻¹-Op (λ { 0F → ≈refl })

  assoc-law : ∀ x y z → x ∙ y ∙ z ≈ x ∙ (y ∙ z)
  assoc-law = gp-assoc 𝑮

  idˡ-law : ∀ x → ε ∙ x ≈ x
  idˡ-law x = begin
    ε ∙ x                                             ≈˘⟨ ∙-cong interp-node-ε ≈refl ⟩
    ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η ∙ ⟦ g0 ⟧ ⟨$⟩ η         ≈˘⟨ interp-node-∙ (node ε-Op (λ ())) g0 ⟩
    ⟦ node ∙-Op (pair (node ε-Op (λ ())) g0) ⟧ ⟨$⟩ η  ≈⟨ equations idˡ η ⟩
    x                                                 ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ _ → x
    g0 : Term (Fin 3)
    g0 = ℊ {X = Fin 3} 0F

  idʳ-law : ∀ x → x ∙ ε ≈ x
  idʳ-law x = begin
    x ∙ ε                                             ≈˘⟨ ∙-cong ≈refl interp-node-ε ⟩
    ⟦ g0 ⟧ ⟨$⟩ η ∙ ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η         ≈˘⟨ interp-node-∙ g0 (node ε-Op (λ ())) ⟩
    ⟦ node ∙-Op (pair g0 (node ε-Op (λ ()))) ⟧ ⟨$⟩ η  ≈⟨ equations idʳ η ⟩
    x                                                 ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ _ → x
    g0 : Term (Fin 3)
    g0 = ℊ {X = Fin 3} 0F

  invˡ-law : ∀ x → x ⁻¹ ∙ x ≈ ε
  invˡ-law x = begin
    x ⁻¹ ∙ x                                       ≈˘⟨ ∙-cong (interp-node-⁻¹ g0 {η}) ≈refl ⟩
    ⟦ node ⁻¹-Op τ ⟧ ⟨$⟩ η ∙ ⟦ g0 ⟧ ⟨$⟩ η          ≈˘⟨ interp-node-∙ (node ⁻¹-Op τ) g0 ⟩
    ⟦ node ∙-Op (pair (node ⁻¹-Op τ) g0) ⟧ ⟨$⟩ η   ≈⟨ equations invˡ η ⟩
    ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η                     ≈⟨ interp-node-ε ⟩
    ε              ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ _ → x
    τ : (_ : ar-Group ⁻¹-Op) → Term (Fin 3)
    τ = λ _ → ℊ 0F
    g0 : Term (Fin 3)
    g0 = ℊ {X = Fin 3} 0F

  invʳ-law : ∀ x → x ∙ x ⁻¹ ≈ ε
  invʳ-law x = ≈trans (∙-cong ≈refl (≈sym (interp-node-⁻¹ (ℊ 0F) {λ _ → x})))
                     (≈trans (≈sym (interp-node-∙ (ℊ 0F) (node ⁻¹-Op (λ _ → ℊ 0F)) {λ _ → x}))
                            (≈trans (equations invʳ (λ _ → x)) (interp-node-ε {λ _ → x})))
```

#### The forgetful projection to monoids

`group→monoid` takes a group to the monoid on its `(∙, ε)`-reduct: the underlying
algebra is `group→monoidAlg`, and the `Th-Monoid` satisfaction proof pivots through
`Group-Op`'s `assoc-law`, `idˡ-law`, `idʳ-law` by the curried-law-pivot pattern of
`monoid→semigroup`, the two identity laws additionally bridging the nullary `ε-Op`
node on the reduct.

```agda
group→monoid : Group α ρ → Monoid α ρ
group→monoid 𝒢@(𝑮 , _) = 𝑹 , thm
  where
  𝑹 : Algebra {𝑆 = Sig-Monoid} _ _
  𝑹 = group→monoidAlg 𝒢
  open Setoid 𝔻[ 𝑮 ] using (_≈_) renaming (refl to ≈refl)
  open Environment 𝑹 using ( ⟦_⟧ )    -- Sig-Monoid environment on 𝑹
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢 using ( _∙_ ; ε ; ∙-cong ; assoc-law ; idˡ-law ; idʳ-law )

  -- 𝑹's binary node-bridge, over Sig-Monoid, landing in the group's curried ∙
  interp-node-∙ᴿ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑮 ])
    → ⟦ node ∙-Opᵐᵒ (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∙ ⟦ t ⟧ ⟨$⟩ η
  interp-node-∙ᴿ s t η = interp-cong 𝑹 ∙-Opᵐᵒ λ { 0F → ≈refl ; 1F → ≈refl }

  -- 𝑹's nullary node-bridge, landing in the group's curried ε
  interp-node-εᴿ : (η : Fin 3 → 𝕌[ 𝑮 ]) → ⟦ node ε-Opᵐᵒ (λ ()) ⟧ ⟨$⟩ η ≈ ε
  interp-node-εᴿ η = interp-cong 𝑹 ε-Opᵐᵒ (λ ())

  thm : 𝑹 ⊨ᵐᵒ Th-Monoid
  thm assocᵐ η = begin
    ⟦ Th-Monoid assocᵐ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ interp-node-∙ᴿ xy (ℊ 2F) η ⟩
    ⟦ xy ⟧ ⟨$⟩ η ∙ z                   ≈⟨ ∙-cong (interp-node-∙ᴿ (ℊ 0F) (ℊ 1F) η) ≈refl ⟩
    x ∙ y ∙ z                          ≈⟨ assoc-law x y z ⟩
    x ∙ (y ∙ z)                        ≈˘⟨ ∙-cong ≈refl (interp-node-∙ᴿ (ℊ 1F) (ℊ 2F) η) ⟩
    x ∙ ⟦ yz ⟧ ⟨$⟩ η                   ≈˘⟨ interp-node-∙ᴿ (ℊ 0F) yz η ⟩
    ⟦ Th-Monoid assocᵐ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    x y z : 𝕌[ 𝑮 ]
    x = η 0F ; y = η 1F ; z = η 2F
    xy yz : Term (Fin 3)
    xy = node ∙-Opᵐᵒ (pair (ℊ 0F) (ℊ 1F))
    yz = node ∙-Opᵐᵒ (pair (ℊ 1F) (ℊ 2F))

  thm idˡᵐ η = begin
    ⟦ Th-Monoid idˡᵐ .proj₁ ⟧ ⟨$⟩ η   ≈⟨ interp-node-∙ᴿ (node ε-Opᵐᵒ (λ ())) (ℊ 0F) η ⟩
    ⟦ node ε-Opᵐᵒ (λ ()) ⟧ ⟨$⟩ η ∙ _  ≈⟨ ∙-cong (interp-node-εᴿ η) ≈refl ⟩
    ε ∙ _                             ≈⟨ idˡ-law _ ⟩
    _                                 ∎

  thm idʳᵐ η = begin
    ⟦ Th-Monoid idʳᵐ .proj₁ ⟧ ⟨$⟩ η   ≈⟨ interp-node-∙ᴿ (ℊ 0F) (node ε-Opᵐᵒ (λ ())) η ⟩
    _ ∙ ⟦ node ε-Opᵐᵒ (λ ()) ⟧ ⟨$⟩ η  ≈⟨ ∙-cong ≈refl (interp-node-εᴿ η) ⟩
    _ ∙ ε                             ≈⟨ idʳ-law _ ⟩
    _                                 ∎
```

#### Group builders

`opsToBareGroup` builds a "raw" `Sig-Group`-algebra from a carrier, a binary
operation, an identity element, and an inverse, over the propositional-equality
setoid `setoid A` — the empty-theory edge case of the `opsTo<family>` pattern, now
with one clause per `Sig-Group` symbol.

```agda
open Algebra

opsToBareGroup : {A : Type α}
  (_·_ : A → A → A) (e : A) (i : A → A) → Algebra {𝑆 = Sig-Group} α α
opsToBareGroup _·_ e i .Domain = setoid _
opsToBareGroup _·_ e i .Interp ⟨$⟩ (∙-Op , args) = args 0F · args 1F
opsToBareGroup _·_ e i .Interp ⟨$⟩ (ε-Op , _) = e
opsToBareGroup _·_ e i .Interp ⟨$⟩ (⁻¹-Op , args) = i (args 0F)
opsToBareGroup _·_ e i .Interp .≈cong {∙-Op , _} {.∙-Op  , _} (refl , u≈v) = cong₂ _·_ (u≈v 0F) (u≈v 1F)
opsToBareGroup _·_ e i .Interp .≈cong {ε-Op , _} {.ε-Op  , _} (refl , _) = refl
opsToBareGroup _·_ e i .Interp .≈cong {⁻¹-Op , _} {.⁻¹-Op , _} (refl , u≈v) = cong i (u≈v 0F)
```

`eqsToGroup` builds a Group from the raw algebra plus the five equation proofs.

```agda
eqsToGroup : {A : Type α} (_·_ : A → A → A) (e : A) (i : A → A)
  → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  → (·-idˡ : ∀ a → e · a ≡ a) (·-idʳ : ∀ a → a · e ≡ a)
  → (·-invˡ : ∀ a → (i a) · a ≡ e) (·-invʳ : ∀ a → a · (i a) ≡ e)
  → Group α α
eqsToGroup _·_ e i ·-assoc ·-idˡ ·-idʳ ·-invˡ ·-invʳ = opsToBareGroup _·_ e i , proof
  where
  proof : opsToBareGroup _·_ e i ⊨ᵍᵖ Th-Group
  proof assoc ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof idˡ   ρ = ·-idˡ   (ρ 0F)
  proof idʳ   ρ = ·-idʳ   (ρ 0F)
  proof invˡ  ρ = ·-invˡ  (ρ 0F)
  proof invʳ  ρ = ·-invʳ  (ρ 0F)
```
