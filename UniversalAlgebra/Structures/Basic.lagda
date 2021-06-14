---
layout: default
title : Structures.Basic module
date : 2021-05-20
author: [the ualib/agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Basic where

open import Agda.Primitive        using    (  _⊔_ ;  lsuc    )
                                  renaming (  Set   to Type  ;
                                              lzero to ℓ₀    )
open import Data.Product          using    (  _,_ ; Σ ; _×_  ;
                                              Σ-syntax       )
                                  renaming (  proj₁ to fst   ;
                                              proj₂ to snd   )
open import Level                 using    (  Level ; Lift   )
open import Relation.Binary.Core  using    (  _⇒_ ; _=[_]⇒_  )
                                  renaming (  REL  to BinREL ;
                                              Rel  to BinRel )

open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ ; 𝟘 ; 𝟙 ; 𝟚 ; 𝟛 ; ℓ₁)
open import Relations.Discrete     using ( Arity ; Op ; _|:_ ; compatible-op )
open import Relations.Continuous   using ( Rel )

private variable α ρ : Level

-- Inhabitants of Signature type are pairs, (s , ar), where s is an operation symbol,
Signature : Type ℓ₁                                -- OR a relation symbol (new!),
Signature = Σ[ F ∈ Type ℓ₀ ] (F → Arity ℓ₀)        -- and ar the arity of s.


Structure : (𝑅 F : Signature) → Type (lsuc (α ⊔ ρ))
Structure {α}{ρ} 𝑅 𝐹 =
  Σ[ A ∈ Type α ]                        -- the domain of the structure is A
   ( ((r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r}{ρ})  -- the interpretations of the relation symbols
   × ((f : ∣ 𝐹 ∣) → Op A{snd 𝐹 f}) )     -- the interpretations of the operation symbols


RStructure : Signature → Type (lsuc (α ⊔ ρ))
RStructure {α} {ρ} 𝑅 = Σ[ A ∈ Type α ] ∀(r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r} {ρ}

AStructure : Signature → Type (lsuc α)
AStructure  {α} 𝐹 = Σ[ A ∈ Type α ] ∀ (f : ∣ 𝐹 ∣) → Op A {snd 𝐹 f}

-- Reducts
module _ {𝑅 𝐹 : Signature} where
 Structure→RStructure : Structure {α}{ρ} 𝑅 𝐹 → RStructure 𝑅
 Structure→RStructure (A , (ℛ , _)) = A , ℛ

 Structure→AStructure : Structure {α}{ρ} 𝑅 𝐹 → AStructure 𝐹
 Structure→AStructure (A , (_ , ℱ)) = A , ℱ

  -- Syntax for interpretation of relations and operations.
 _⟦_⟧ᵣ : (𝒜 : Structure{α}{ρ} 𝑅 𝐹)(𝑟 : fst 𝑅) → Rel (fst 𝒜) {snd 𝑅 𝑟} {ρ}
 𝒜 ⟦ 𝑟 ⟧ᵣ = λ a → (∣ snd 𝒜 ∣ 𝑟) a

 _⟦_⟧ₒ : (𝒜 : Structure{α}{ρ} 𝑅 𝐹)(𝑓 : fst 𝐹) → Op (fst 𝒜) {snd 𝐹 𝑓}
 𝒜 ⟦ 𝑓 ⟧ₒ = λ a → (snd (snd 𝒜) 𝑓) a

 _ʳ_ : (𝑟 : fst 𝑅)(𝒜 : Structure {α} 𝑅 𝐹) → Rel (fst 𝒜){(snd 𝑅) 𝑟}{ρ}
 𝑟 ʳ 𝒜 = λ a → (𝒜 ⟦ 𝑟 ⟧ᵣ) a

 _ᵒ_ : (𝑓 : fst 𝐹)(𝒜 : Structure {α}{ρ} 𝑅 𝐹) → Op (fst 𝒜){snd 𝐹 𝑓}
 𝑓 ᵒ 𝒜 = λ a → (𝒜 ⟦ 𝑓 ⟧ₒ) a

 Compatible : {ρ' : Level}(𝑨 : Structure{α}{ρ} 𝑅 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
 Compatible 𝑨 r = ∀ 𝑓 → (𝑓 ᵒ 𝑨) |: r

 Compatible' : {ρ' : Level}(𝑨 : Structure{α}{ρ} 𝑅 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
 Compatible' 𝑨 r = ∀ 𝑓 → compatible-op (𝑓 ᵒ 𝑨) r

 open Level

 Lift-op : {I : Arity ℓ₀}{A : Type α} → Op A{I} → (ℓ : Level) → Op (Lift ℓ A){I}
 Lift-op f ℓ = λ x → lift (f (λ i → lower (x i)))

 Lift-rel : {I : Arity ℓ₀}{A : Type α} → Rel A {I}{ρ} → (ℓ : Level) → Rel (Lift ℓ A) {I}{ρ}
 Lift-rel r ℓ x = r (λ i → lower (x i))

 Lift-struc : Structure {α}{ρ}𝑅 𝐹 → (ℓ : Level) → Structure {α = (α ⊔ ℓ)}{ρ} 𝑅 𝐹
 Lift-struc {α}{ρ}𝑨 ℓ = Lift ℓ ∣ 𝑨 ∣ , (lrel , lop )
  where
  lrel : (r : ∣ 𝑅 ∣) → Rel (Lift ℓ ∣ 𝑨 ∣){snd 𝑅 r}{ρ}
  lrel r = λ x → ((r ʳ 𝑨) (λ i → lower (x i)))
  lop : (f : ∣ 𝐹 ∣) → Op (Lift ℓ ∣ 𝑨 ∣) {snd 𝐹 f}
  lop f = λ x → lift ((f ᵒ 𝑨)( λ i → lower (x i)))

\end{code}


#### Alternative definitions using records

\begin{code}

record signature : Type ℓ₁ where
 field
  symbol : Type ℓ₀
  arity : symbol → Arity ℓ₀

open signature public


record structure (𝑅 𝐹 : signature) : Type (lsuc (α ⊔ ρ)) where
 field
  carrier  : Type α
  rsymbol  : ∀ (𝑟 : symbol 𝑅) → Rel carrier{arity 𝑅 𝑟}{ρ}  -- interpretations of relations
  osymbol  : ∀ (𝑓 : symbol 𝐹) → Op carrier{arity 𝐹 𝑓}     -- interpretations of operations

open structure public

compatible : {𝑅 𝐹 : signature}(𝑨 : structure {α}{ρ} 𝑅 𝐹) → BinRel (carrier 𝑨) ρ  → Type (α ⊔ ρ)
compatible {𝐹 = 𝐹} 𝑨 r = ∀ (𝑓 : symbol 𝐹)(u v : (arity 𝐹) 𝑓 → carrier 𝑨) → ((osymbol 𝑨) 𝑓) |: r


\end{code}





#### Examples of finite signatures

\begin{code}

-- The signature with...
-- ... no symbols  (e.g., sets)
Sig∅ : signature
Sig∅ = record { symbol = 𝟘 ; arity = λ () }

-- ... one nulary symbol (e.g., pointed sets)
Sig-0 : signature
Sig-0 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟘 }

Sig-1 : signature -- ...one unary
Sig-1 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟙 }

-- ...one binary symbol (e.g., magmas, semigroups, semilattices)
Sig-2 : signature
Sig-2 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟚 }

-- ...one nulary and one binary (e.g., monoids)
Sig-0-1 : signature
Sig-0-1 = record { symbol = 𝟚 ; arity = λ{ 𝟚.𝟎 → 𝟘 ; 𝟚.𝟏 → 𝟚 } }

-- ...one nulary, one unary, and one binary (e.g., groups)
Sig-0-1-2 : signature
Sig-0-1-2 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟘 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟚 } }

\end{code}



--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team








-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------


















