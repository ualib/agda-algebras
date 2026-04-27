---
layout: default
title : "Base.Structures.Sigma.Basic module"
date : "2021-05-20"
author: "agda-algebras development team"
---

#### <a id="basic-definitions">Basic Definitions</a>

This is the [Base.Structures.Sigma.Basic][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Sigma.Basic where

-- Imports from the Agda Standard Library ------------------------------------------------
open import Agda.Primitive        using () renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product          using ( _,_ ; _×_ ; Σ-syntax )
                                  renaming ( proj₁ to fst ; proj₂ to snd )
open import Level                 using ( _⊔_ ; suc ; Level )
open import Relation.Binary.Core  using ( _⇒_ ; _=[_]⇒_ )
                                  renaming ( REL to BinREL ; Rel to BinRel )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture        using ( ∣_∣ ; ∥_∥ ; ℓ₁ ; Op )
open import Base.Relations  using ( _|:_ ; _preserves_ ; Rel )

-- Inhabitants of Signature type are pairs, (s , ar), where s is an operation symbol,
Signature : Type ℓ₁                         -- OR a relation symbol (new!),
Signature = Σ[ F ∈ Type ℓ₀ ] (F → Type ℓ₀)  -- and ar the arity of s.

Structure : (𝑅 F : Signature){α ρ : Level} → Type (suc (α ⊔ ρ))
Structure 𝑅 𝐹 {α}{ρ} =
  Σ[ A ∈ Type α ]                        -- the domain of the structure is A
  ( ((r : ∣ 𝑅 ∣) → Rel A (snd 𝑅 r){ρ})   -- the interpretations of the relation symbols
  × ((f : ∣ 𝐹 ∣) → Op A (snd 𝐹 f)) )     -- the interpretations of the operation symbols

RStructure : Signature → {α ρ : Level} → Type (suc (α ⊔ ρ))
RStructure 𝑅 {α} {ρ} = Σ[ A ∈ Type α ] ∀(r : ∣ 𝑅 ∣) → Rel A (snd 𝑅 r) {ρ}

AStructure : Signature → {α : Level} → Type (suc α)
AStructure 𝐹 {α} = Σ[ A ∈ Type α ] ∀ (f : ∣ 𝐹 ∣) → Op A (snd 𝐹 f)

module _ {𝑅 𝐹 : Signature} {α ρ : Level} where

-- Reducts
 Structure→RStructure : Structure 𝑅 𝐹 {α}{ρ} → RStructure 𝑅 {α}{ρ}
 Structure→RStructure (A , (ℛ , _)) = A , ℛ

 Structure→AStructure : Structure 𝑅 𝐹 {α}{ρ} → AStructure 𝐹
 Structure→AStructure (A , (_ , ℱ)) = A , ℱ

  -- Syntax for interpretation of relations and operations.
 _⟦_⟧ᵣ : (𝒜 : Structure 𝑅 𝐹 {α}{ρ})(𝑟 : ∣ 𝑅 ∣) → Rel ∣ 𝒜 ∣ (∥ 𝑅 ∥ 𝑟) {ρ}
 𝒜 ⟦ 𝑟 ⟧ᵣ = λ a → (fst ∥ 𝒜 ∥ 𝑟) a

 _⟦_⟧ₒ : (𝒜 : Structure 𝑅 𝐹 {α}{ρ})(𝑓 : ∣ 𝐹 ∣) → Op ∣ 𝒜 ∣ (∥ 𝐹 ∥ 𝑓)
 𝒜 ⟦ 𝑓 ⟧ₒ = λ a → (snd ∥ 𝒜 ∥ 𝑓) a

 _ʳ_ : (𝑟 : ∣ 𝑅 ∣)(𝒜 : Structure 𝑅 𝐹 {α}) → Rel ∣ 𝒜 ∣ (∥ 𝑅 ∥ 𝑟){ρ}
 𝑟 ʳ 𝒜 = λ a → (𝒜 ⟦ 𝑟 ⟧ᵣ) a

 _ᵒ_ : (𝑓 : ∣ 𝐹 ∣)(𝒜 : Structure 𝑅 𝐹 {α}{ρ}) → Op ∣ 𝒜 ∣(∥ 𝐹 ∥ 𝑓)
 𝑓 ᵒ 𝒜 = λ a → (𝒜 ⟦ 𝑓 ⟧ₒ) a

 Compatible : {ρ' : Level}(𝑨 : Structure 𝑅 𝐹{α}{ρ}) → BinRel ∣ 𝑨 ∣ ρ'  → Type (α ⊔ ρ')
 Compatible 𝑨 r = ∀ 𝑓 → (𝑓 ᵒ 𝑨) |: r

 Compatible' : {ρ' : Level}(𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → BinRel ∣ 𝑨 ∣ ρ'  → Type (α ⊔ ρ')
 Compatible' 𝑨 r = ∀ 𝑓 → (𝑓 ᵒ 𝑨) preserves r

 open Level

 Lift-op : {I : Type ℓ₀}{A : Type α} → Op A I → (ℓ : Level) → Op (Lift ℓ A) I
 Lift-op f ℓ = λ x → lift (f (λ i → lower (x i)))

 Lift-rel : {I : Type ℓ₀}{A : Type α} → Rel A I {ρ} → (ℓ : Level) → Rel (Lift ℓ A) I{ρ}
 Lift-rel r ℓ x = r (λ i → lower (x i))

 Lift-Strucˡ : (ℓ : Level) → Structure 𝑅 𝐹 {α}{ρ} → Structure 𝑅 𝐹 {α = (α ⊔ ℓ)}{ρ}
 Lift-Strucˡ ℓ 𝑨 = Lift ℓ ∣ 𝑨 ∣ , (lrel , lop )
  where
  lrel : (r : ∣ 𝑅 ∣) → Rel (Lift ℓ ∣ 𝑨 ∣)(∥ 𝑅 ∥ r){ρ}
  lrel r = λ x → ((r ʳ 𝑨) (λ i → lower (x i)))
  lop : (f : ∣ 𝐹 ∣) → Op (Lift ℓ ∣ 𝑨 ∣) (∥ 𝐹 ∥ f)
  lop f = λ x → lift ((f ᵒ 𝑨)( λ i → lower (x i)))

 Lift-Strucʳ : (ℓ : Level) → Structure 𝑅 𝐹 {α}{ρ} → Structure 𝑅 𝐹 {α}{ρ = (ρ ⊔ ℓ)}
 Lift-Strucʳ ℓ 𝑨 = ∣ 𝑨 ∣ , lrel , snd ∥ 𝑨 ∥
  where
  lrel : (r : ∣ 𝑅 ∣) → Rel (∣ 𝑨 ∣)(∥ 𝑅 ∥ r){ρ ⊔ ℓ}
  lrel r = λ x → Lift ℓ ((r ʳ 𝑨) x) -- λ x → ((r ʳ 𝑨) (λ i → lower (x i)))

module _ {𝑅 𝐹 : Signature} {α ρ : Level} where

 Lift-Struc : (ℓˡ ℓʳ : Level) → Structure 𝑅 𝐹 {α}{ρ} → Structure 𝑅 𝐹 {α ⊔ ℓˡ}{ρ ⊔ ℓʳ}
 Lift-Struc ℓˡ ℓʳ 𝑨 = Lift-Strucʳ ℓʳ (Lift-Strucˡ ℓˡ 𝑨)
```


--------------------------------

<span style="float:left;">[← Base.Structures.Sigma](Base.Structures.Sigma.html)</span>
<span style="float:right;">[Base.Structures.Sigma.Products →](Base.Structures.Sigma.Products.html)</span>

{% include UALib.Links.md %}
