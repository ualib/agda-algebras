---
layout: default
title : "Base.Structures.Graphs module"
date : "2021-06-22"
author: "agda-algebras development team"
---

### <a id="graph-structures">Graph Structures</a>

This is the [Base.Structures.Graphs][] module of the [Agda Universal Algebra Library][].

N.B. This module differs from 0Graphs.lagda in that this module is universe polymorphic; i.e., we do not restrict universe levels (to, e.g., `ℓ₀`). This complicates some things; e.g., we must use lift and lower in some places (cf. [Base/Structures/Graphs0.lagda][]).

**Definition** (Graph of a structure). Let `𝑨` be an `(𝑅, 𝐹)`-structure (relations from `𝑅` and operations from `𝐹`). The *graph* of `𝑨` is the structure `Gr 𝑨` with the same domain as `𝑨` with relations from `𝑅` together with a (`k+1`)-ary relation symbol `G 𝑓` for each `𝑓 ∈ 𝐹` of arity `k`, which is interpreted in `Gr 𝑨` as all tuples `(t , y) ∈ Aᵏ⁺¹` such that `𝑓 t ≡ y`. (See also Definition 2 of https://arxiv.org/pdf/2010.04958v2.pdf)


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Graphs where

-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive  using () renaming  ( Set to Type ; lzero  to ℓ₀ )
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ )
open import Data.Sum.Base   using ( _⊎_ ) renaming  ( inj₁ to inl ; inj₂ to inr )
open import Data.Unit.Base  using ( ⊤ ; tt )
open import Level           using (  _⊔_ ; Level ; Lift ; lift ; lower )
open import Function.Base   using ( _∘_  )
open import Relation.Binary.PropositionalEquality as ≡
                            using ( _≡_ ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture               using ( ∣_∣ ; ∥_∥ )
open import Base.Relations         using ( Rel )
open import Base.Structures.Basic  using ( signature ; structure )
open import Base.Structures.Homs   using ( hom ; ∘-hom ; is-hom-rel ; is-hom-op)
open import Examples.Structures.Signatures  using ( S∅ )

open signature ; open structure ; open _⊎_

Gr-sig : signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀

Gr-sig 𝐹 𝑅 = record  { symbol = symbol 𝑅 ⊎ symbol 𝐹
                     ; arity  = ar
                     }
 where
 ar : symbol 𝑅 ⊎ symbol 𝐹 → Type _
 ar (inl 𝑟) = (arity 𝑅) 𝑟
 ar (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ ⊤

private variable
 𝐹 𝑅 : signature ℓ₀ ℓ₀
 α ρ : Level

Gr : ∀{α ρ} → structure 𝐹 𝑅 {α} {ρ} → structure S∅ (Gr-sig 𝐹 𝑅) {α} {α ⊔ ρ}
Gr {𝐹}{𝑅}{α}{ρ} 𝑨 = record { carrier = carrier 𝑨 ; op = λ () ; rel = split }
  where
  split : (s : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨) (arity (Gr-sig 𝐹 𝑅) s) {α ⊔ ρ}
  split (inl 𝑟) arg = Lift α (rel 𝑨 𝑟 arg)
  split (inr 𝑓) args = Lift ρ (op 𝑨 𝑓 (args ∘ inl) ≡ args (inr tt))

open ≡-Reasoning

private variable ρᵃ β ρᵇ : Level

module _ {𝑨 : structure 𝐹 𝑅 {α} {ρᵃ}} {𝑩 : structure 𝐹 𝑅 {β} {ρᵇ}} where

 hom→Grhom : hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
 hom→Grhom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
  i (inl 𝑟) a x = lift (∣ hhom ∣ 𝑟 a (lower x))
  i (inr 𝑓) a x = lift goal
   where
   homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
   homop = ∥ hhom ∥ 𝑓 (a ∘ inl)

   goal : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr tt))
   goal =  op 𝑩 𝑓 (h ∘ (a ∘ inl))  ≡⟨ ≡.sym homop ⟩
           h (op 𝑨 𝑓 (a ∘ inl))    ≡⟨ ≡.cong h (lower x) ⟩
           h (a (inr tt))          ∎

  ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
  ii = λ ()

 Grhom→hom : hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
 Grhom→hom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel 𝑨 𝑩 h
  i R a x = lower (∣ hhom ∣ (inl R) a (lift x))
  ii : is-hom-op 𝑨 𝑩 h
  ii f a = goal
   where
   split : arity 𝐹 f ⊎ ⊤ → carrier 𝑨
   split (inl x) = a x
   split (inr y) = op 𝑨 f a
   goal : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
   goal = ≡.sym (lower (∣ hhom ∣ (inr f) split (lift ≡.refl)))
```


--------------------------------

<span style="float:left;">[← Base.Structures.Basic](Base.Structures.Basic.html)</span>
<span style="float:right;">[Base.Structures.Graphs0 →](Base.Structures.Graphs0.html)</span>

{% include UALib.Links.md %}
