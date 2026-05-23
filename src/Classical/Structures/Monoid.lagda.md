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
   associativity, used in both places; this is the acyclic ordering:
   `mn-assoc` → `monoid→semigroup` → `Monoid-Op`.
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
open import Relation.Binary.PropositionalEquality  as ≡ using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Classical.Operations                    using ( pair ; Curry₂ ; Curry₀ )
open import Classical.Signatures.Magma              using ( Sig-Magma ; Op-Magma )renaming ( ∙-Op to ∙-Opᵐᵃ )
open import Classical.Signatures.Monoid             using ( Sig-Monoid ; Op-Monoid ; ∙-Op ; ε-Op )
open import Classical.Structures.Magma              using ( Magma ; module Magma-Op )
open import Classical.Structures.Reduct             using ( reduct )
open import Classical.Structures.Semigroup          using ( Semigroup ) renaming (_⊨_ to _⊨ˢᵍ_)
open import Classical.Theories.Monoid               using ( Eq-Monoid ; Th-Monoid ; assoc ; id-l ; id-r )
open import Classical.Theories.Semigroup            using ( Th-Semigroup ) renaming ( assoc to assocˢ )
open import Overture.Terms {𝑆 = Sig-Monoid}         using ( Term ; ℊ ; node )
open import Overture.Signatures                     using ( ArityOf ; OperationSymbolsOf)
import Overture.Terms {𝑆 = Sig-Magma} as TmMa
import Setoid.Terms {𝑆 = Sig-Magma} as StMa

open import Setoid.Algebras.Basic {𝑆 = Sig-Monoid}  using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] ; ⟨_⟩ )
import Setoid.Algebras.Basic as Alg -- {𝑆 = Sig-Monoid}  using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] ; ⟨_⟩ )
open import Setoid.Terms {𝑆 = Sig-Monoid}           using ( module Environment )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Monoid} using ( _⊧_≈_ )

import Classical.Structures.Interpret {𝑆 = Sig-Monoid} as IntMo
import Classical.Structures.Interpret {𝑆 = Sig-Magma}  as IntMa

-- open Algebra using ( Interp )

private variable α ρ : Level
```

#### <a id="satisfaction-alias">The local satisfaction predicate</a>

```agda
infix 4 _⊨_
_⊨_ : (𝑨 : Alg.Algebra α ρ) (ℰ : Eq-Monoid → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### <a id="the-type">The type of monoids</a>

```agda
Monoid : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Monoid α ρ = Σ[ 𝑨 ∈ Alg.Algebra α ρ ] 𝑨 ⊨ Th-Monoid
```

#### <a id="forgetful-to-magma">The reduct to magmas</a>

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
monoid→magma 𝑴 = reduct ∙-incl ∙-κ (𝑴 .proj₁)
```

#### <a id="curried-associativity">Curried associativity, standalone</a>

`mn-assoc` proves `(x ∙ y) ∙ z ≈ x ∙ (y ∙ z)` for the monoid's own `∙`, from
`equations assoc`, via the local binary node-bridge `interp-node∙` built on
`IntMo.interp-cong`.  It is defined here, above the forgetful, so both
`monoid→semigroup` and `Monoid-Op.assoc-law` can consume it.  The proof is a
verbatim port of `Semigroup-Op.assoc-law` to `Sig-Monoid`.

```agda
module _ (𝑴 : Monoid α ρ) where
  -- open Alg {𝑆 = Sig-Monoid}
  private 𝑨 = proj₁ 𝑴
  open Setoid Alg.𝔻[ 𝑨 ]
  open Environment 𝑨 using ( ⟦_⟧ )
  open SetoidReasoning Alg.𝔻[ 𝑨 ]

  private
    _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
    _∙_ = Curry₂ (∙-Op ^ 𝑨)

    interp-node∙ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑨 ])
                 → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)
    interp-node∙ s t η = IntMo.interp-cong 𝑨 ∙-Op (λ { 0F → refl ; 1F → refl })

  mn-assoc : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  mn-assoc x y z = begin
    (x ∙ y) ∙ z          ≈⟨ IntMo.interp-cong 𝑨 ∙-Op (λ { 0F → sym (interp-node∙ (ℊ 0F) (ℊ 1F) η) ; 1F → refl }) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η       ≈⟨ proj₂ 𝑴 assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η       ≈⟨ IntMo.interp-cong 𝑨 ∙-Op (λ { 0F → refl ; 1F → interp-node∙ (ℊ 1F) (ℊ 2F) η }) ⟩
    x ∙ (y ∙ z)          ∎
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    lhsT = node ∙-Op (pair (node ∙-Op (pair (ℊ 0F) (ℊ 1F))) (ℊ 2F))
    rhsT = node ∙-Op (pair (ℊ 0F) (node ∙-Op (pair (ℊ 1F) (ℊ 2F))))
```

#### <a id="monoid-op">The `Monoid-Op` module</a>

```agda
module Monoid-Op {α ρ : Level} (𝑴 : Monoid α ρ) where
  private 𝑨 = proj₁ 𝑴
  open Setoid 𝔻[ 𝑨 ]
  open Environment 𝑨 using ( ⟦_⟧ )

  infixl 7 _∙_
  _∙_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ]
  _∙_ = Curry₂ (∙-Op ^ 𝑨)

  ε : 𝕌[ 𝑨 ]
  ε = Curry₀ (ε-Op ^ 𝑨)

  equations : 𝑨 ⊨ Th-Monoid
  equations = proj₂ 𝑴

  ∙-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x ∙ u) ≈ (y ∙ v)
  ∙-cong x≈y u≈v = IntMo.interp-cong 𝑨 ∙-Op (λ { 0F → x≈y ; 1F → u≈v })

  interp-node∙ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑨 ])
               → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)
  interp-node∙ s t η = IntMo.interp-cong 𝑨 ∙-Op (λ { 0F → refl ; 1F → refl })

  interp-node₀ : (η : Fin 3 → 𝕌[ 𝑨 ]) → ⟦ node ε-Op (λ ()) ⟧ ⟨$⟩ η ≈ ε
  interp-node₀ η = IntMo.interp-cong 𝑨 ε-Op (λ ())

  assoc-law : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  assoc-law = mn-assoc 𝑴

  idˡ-law : ∀ x → ε ∙ x ≈ x
  idˡ-law x = trans (∙-cong (sym (interp-node₀ η)) refl)
                    (trans (sym (interp-node∙ (node ε-Op (λ ())) (ℊ 0F) η)) (equations id-l η))
    where η : Fin 3 → 𝕌[ 𝑨 ] ; η = λ _ → x

  idʳ-law : ∀ x → x ∙ ε ≈ x
  idʳ-law x = trans (∙-cong refl (sym (interp-node₀ η)))
                    (trans (sym (interp-node∙ (ℊ 0F) (node ε-Op (λ ())) η)) (equations id-r η))
    where η : Fin 3 → 𝕌[ 𝑨 ] ; η = λ _ → x
```

#### <a id="forgetful-to-semigroup">The forgetful projection to semigroups</a>

```agda
monoid→semigroup : Monoid α ρ → Semigroup α ρ
monoid→semigroup 𝑴 = 𝑹 , thm -- thm
  where
  𝑹 = monoid→magma 𝑴
  module ℳ = Alg {𝑆 = Sig-Monoid}
  module ℛ = Alg {𝑆 = Sig-Magma}
  open ℳ.Algebra (proj₁ 𝑴) renaming (Domain to M)
  open ℛ.Algebra 𝑹 renaming (Domain to R)
  open Setoid M using (_≈_; refl; sym)
  open Setoid R using () renaming (_≈_ to _≋_ ; refl to R-refl)
  open StMa.Environment 𝑹 using ( ⟦_⟧ )          -- Sig-Magma environment on 𝑹
  open SetoidReasoning M
  open Magma-Op 𝑹 using ( _∙_ )                  -- 𝑹's curried ∙, over Sig-Magma

  -- 𝑹's binary node-bridge, over Sig-Magma (IntMa = Interpret {Sig-Magma})
  ndᴿ : (s t : TmMa.Term (Fin 3)) (η : Fin 3 → 𝕌[ proj₁ 𝑴 ])
      → ⟦ TmMa.node ∙-Opᵐᵃ (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)
  ndᴿ s t η = IntMa.interp-cong 𝑹 ∙-Opᵐᵃ (λ { 0F → refl ; 1F → refl })

  thm : 𝑹 ⊨ˢᵍ Th-Semigroup
  thm assocˢ η = Goal
    where
    open Monoid-Op 𝑴 using ( assoc-law )       -- the monoid's curried associativity

    -- 𝑹's curried-∙ congruence, in the same idiom as ndᴿ (reuses interp-cong):
    ∙-congᴿ : ∀ {a b c d} → a ≈ b → c ≈ d → (a ∙ c) ≈ (b ∙ d)
    ∙-congᴿ a≈b c≈d = IntMa.interp-cong 𝑹 ∙-Opᵐᵃ (λ { 0F → a≈b ; 1F → c≈d })

    Lt = TmMa.node ∙-Opᵐᵃ (pair (TmMa.ℊ 0F) (TmMa.ℊ 1F))   -- the subterm  x ∙ y
    Rt = TmMa.node ∙-Opᵐᵃ (pair (TmMa.ℊ 1F) (TmMa.ℊ 2F))   -- the subterm  y ∙ z

    Goal : ⟦ Th-Semigroup assocˢ .proj₁ ⟧ ⟨$⟩ η ≋ ⟦ Th-Semigroup assocˢ .proj₂ ⟧ ⟨$⟩ η
    Goal = begin
      ⟦ Th-Semigroup assocˢ .proj₁ ⟧ ⟨$⟩ η   ≈⟨ ndᴿ Lt (TmMa.ℊ 2F) η ⟩
      (⟦ Lt ⟧ ⟨$⟩ η) ∙ (η 2F)                ≈⟨ ∙-congᴿ (ndᴿ (TmMa.ℊ 0F) (TmMa.ℊ 1F) η) refl ⟩
      (η 0F) ∙ (η 1F) ∙ (η 2F)               ≈⟨ assoc-law (η 0F) (η 1F) (η 2F) ⟩
      (η 0F) ∙ ((η 1F) ∙ (η 2F))             ≈˘⟨ ∙-congᴿ refl (ndᴿ (TmMa.ℊ 1F) (TmMa.ℊ 2F) η) ⟩
      (η 0F) ∙ (⟦ Rt ⟧ ⟨$⟩ η)                ≈˘⟨ ndᴿ (TmMa.ℊ 0F) Rt η ⟩
      ⟦ Th-Semigroup assocˢ .proj₂ ⟧ ⟨$⟩ η   ∎
```

The statement is `𝑹 ⊧ (Sig-Magma assoc-lhs) ≈ (Sig-Magma assoc-rhs)` under every `η`,
and the proof is the curried-law pivot: unfold both `Sig-Magma` terms to the reduct's
curried `∙ᴿ` via `IntMa.interp-cong 𝑹 ∙-Opᵐᵃ`, apply `mn-assoc 𝑴` (whose `∙` is that
of the monoid, definitionally equal to `∙ᴿ` since the position map is `id`), then
refold.  Mechanically identical to `Semigroup-Op.assoc-law` but on `𝑹` and pivoting
through `mn-assoc 𝑴` in the middle.

#### <a id="frommonoidops">Bare-algebra builder and `fromPropEq`</a>

`fromMonoidOps` builds a `Sig-Monoid`-algebra from a carrier, a binary operation,
and an identity element — interpreting `∙-Op` and `ε-Op` directly.  This is the
expand half of the reduct/expand dual at the Magma↪Monoid step, written inline
(no generic `expand` until a second use appears, per #326).  `fromPropEq` pairs
it with the three propositional-equality proofs.

```agda
fromMonoidOps : (A : Type α) (_·_ : A → A → A) (e : A) → Algebra α α
fromMonoidOps A _·_ e = record { Domain = ≡.setoid A ; Interp = interp }
  where
  interp : Func (⟨ Sig-Monoid ⟩ _) _
  interp ⟨$⟩ (∙-Op , args) = args 0F · args 1F
  interp ⟨$⟩ (ε-Op , _)    = e
  cong interp {∙-Op , _} {.∙-Op , _} (≡.refl , a≈) = ≡.cong₂ _·_ (a≈ 0F) (a≈ 1F)
  cong interp {ε-Op , _} {.ε-Op , _} (≡.refl , _)  = ≡.refl

fromPropEq : (A : Type α) (_·_ : A → A → A) (e : A)
           → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
           → (·-idˡ : ∀ a → e · a ≡ a) (·-idʳ : ∀ a → a · e ≡ a)
           → Monoid α α
fromPropEq A _·_ e ·-assoc ·-idˡ ·-idʳ = fromMonoidOps A _·_ e , proof
  where
  proof : (fromMonoidOps A _·_ e) ⊨ Th-Monoid
  proof assoc ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof id-l  ρ = ·-idˡ (ρ 0F)
  proof id-r  ρ = ·-idʳ (ρ 0F)
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Semigroup](Classical.Structures.Semigroup.html)</span>
<span style="float:right;">[Classical.Structures.Group →](Classical.Structures.Group.html)</span>

{% include UALib.Links.md %}
