---
layout: default
title : Structures.AsRecords module
date : 2021-05-20
author: William DeMeo
---

This is a submodule of the Structures module which presents general (relational-algebraic) structures as
inhabitants of record types.  For a similar development using Sigma types see the module called
Structures.Basic. 

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.AsRecords where

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
open import Relations.Discrete     using ( Arity ; Op ; _|:_ ; _preserves_ )
open import Relations.Continuous   using ( Rel )

private variable α ρ : Level


ar : Type ℓ₁
ar = Arity ℓ₀

-- Signatures as records.
record signature : Type ℓ₁ where
 field
  symbol : Type ℓ₀
  arity : symbol → ar

open signature public


record structure {α ρ : Level} (𝑅 : signature) (𝐹 : signature) : Type (lsuc (α ⊔ ρ)) where
 field
  carrier : Type α
  rel : ∀ (𝑟 : symbol 𝑅) → Rel carrier {arity 𝑅 𝑟} {ρ}  -- interpretations of relations
  op : ∀ (𝑓 : symbol 𝐹) → Op carrier{arity 𝐹 𝑓}       -- interpretations of operations

open structure public

compatible : {α ρ β : Level}{𝑅 𝐹 : signature}(𝑨 : structure {α} {ρ} 𝑅 𝐹) → BinRel (carrier 𝑨) β → Type (α ⊔ β)
compatible {𝑅 = 𝑅}{𝐹} 𝑨 r = ∀ (𝑓 : symbol 𝐹) → ((op 𝑨) 𝑓) |: r


module _ {α ρ : Level}{𝑅 𝐹 : signature} where

 open Level

 Lift-op : {I : ar}{A : Type α} → Op A{I} → (ℓ : Level) → Op (Lift ℓ A){I}
 Lift-op f ℓ = λ x → lift (f (λ i → lower (x i)))

 Lift-rel : {I : ar}{A : Type α} → Rel A {I}{ρ} → (ℓ : Level) → Rel (Lift ℓ A) {I}{ρ}
 Lift-rel r ℓ x = r (λ i → lower (x i))

 Lift-structure : structure {α} {ρ} 𝑅 𝐹 → (ℓ : Level) → structure {α ⊔ ℓ} {ρ} 𝑅 𝐹
 Lift-structure 𝑨 ℓ = record { carrier = Lift ℓ (carrier 𝑨) ; rel = lrel ; op = lop }
  where
  lrel : (r : symbol 𝑅 ) → Rel (Lift ℓ (carrier 𝑨)){arity 𝑅 r}{ρ}
  lrel r = λ x → ((rel 𝑨)r) (λ i → lower (x i))
  lop : (f : symbol 𝐹) → Op (Lift ℓ (carrier 𝑨)) {arity 𝐹 f}
  lop f = λ x → lift (((op 𝑨) f)( λ i → lower (x i)))



-- Some examples (of finite signatures)
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








-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------



































-- -- Inhabitants of Signature type are pairs, (s , ar), where s is an operation or
-- -- relation symbol and ar its arity.
-- Signature : Type ℓ₁
-- Signature = Σ[ F ∈ Type ℓ₀ ] (F → Arity)

-- Structure : (α : Level) → Signature → (ρ : Level) → Signature → Type (lsuc (α ⊔ ρ))
-- Structure  α 𝑅 ρ 𝐹 =
--  Σ[ A ∈ Type α ]                        -- the domain of the structure is A
--   ( ((r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r}{ρ})  -- the interpretations of the relation symbols
--   × ((f : ∣ 𝐹 ∣) → Op A{snd 𝐹 f}) )     -- the interpretations of the operation symbols

-- -- Relations of arbitrary arity over a single sort.
-- -- Rel : Type α → {I : Arity} → {ρ : Level} → Type (α ⊔ lsuc ρ)
-- -- Rel A {I} {ρ} = (I → A) → Type ρ

-- RStructure : (α : Level) → Signature → (ρ : Level) → Type (lsuc (α ⊔ ρ))
-- RStructure α 𝑅 ρ = Σ[ A ∈ Type α ] ∀(r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r} {ρ}
-- -- Rel : Arity → Type α → (β : Level) → Type (α ⊔ lsuc β)
-- -- Rel ar A β = (ar → A) → Type β

-- AStructure : (α : Level) → Signature → Type (lsuc α)
-- AStructure α 𝐹 = Σ[ A ∈ Type α ] ∀ (f : ∣ 𝐹 ∣) → Op A {snd 𝐹 f}

-- -- Reducts
-- Structure→AStructure : {α ρ : Level} {𝑅 𝐹 : Signature} → Structure α 𝑅 ρ 𝐹 → AStructure α 𝐹
-- Structure→AStructure (A , (_ , ℱ)) = A , ℱ

-- Structure→RStructure : {α ρ : Level}{𝑅 𝐹 : Signature} → Structure α 𝑅 ρ 𝐹 → RStructure α 𝑅 ρ
-- Structure→RStructure (A , (ℛ , _)) = A , ℛ
-- module _ {α ρ : Level}{𝑅 𝐹 : Signature}  where
-- {- Let 𝑅 and 𝐹 be signatures and let ℬ = (B , (ℛ , ℱ)) be an (𝑅, 𝐹)-structure.
--    - If `r : ∣ 𝑅 ∣` is a relation symbol, then `rel ℬ r` is the interpretation of `r` in `ℬ`.
--    - if `f : ∣ 𝐹 ∣` is an opereation symbol, then `op ℬ f` is the interpretation
--    of `f` in `ℬ`. -}

--   -- Syntax for interpretation of relations and operations.
--   _⟦_⟧ᵣ : (𝒜 : Structure α 𝑅 ρ 𝐹)(𝑟 : fst 𝑅) → Rel (fst 𝒜) {snd 𝑅 𝑟} {ρ}
--   𝒜 ⟦ 𝑟 ⟧ᵣ = λ a → (∣ snd 𝒜 ∣ 𝑟) a

--   _⟦_⟧ₒ : (𝒜 : Structure α 𝑅 ρ 𝐹)(𝑓 : fst 𝐹) → Op (fst 𝒜) {snd 𝐹 𝑓}
--   𝒜 ⟦ 𝑓 ⟧ₒ = λ a → (snd (snd 𝒜) 𝑓) a

--   _ʳ_ : (𝑟 : fst 𝑅)(𝒜 : Structure α 𝑅 ρ _) → Rel (fst 𝒜){(snd 𝑅) 𝑟}{ρ}
--   𝑟 ʳ 𝒜 = λ a → (𝒜 ⟦ 𝑟 ⟧ᵣ) a

--   _ᵒ_ : (𝑓 : fst 𝐹)(𝒜 : Structure α _ ρ 𝐹) → Op (fst 𝒜){snd 𝐹 𝑓} 
--   𝑓 ᵒ 𝒜 = λ a → (𝒜 ⟦ 𝑓 ⟧ₒ) a

-- module _ {α ρ : Level}{𝑅 𝐹 : Signature}  where
--  Compatible : {ρ' : Level}(𝑨 : Structure α 𝑅 ρ 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
--  Compatible 𝑨 r = ∀ 𝑓 → (𝑓 ᵒ 𝑨) |: r

--  Compatible' : {ρ' : Level}(𝑨 : Structure α 𝑅 ρ 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
--  Compatible' 𝑨 r = ∀ 𝑓 → compatible-op (𝑓 ᵒ 𝑨) r
