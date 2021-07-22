---
layout: default
title : Structures.Basic module (Agda Universal Algebra Library)
date : 2021-05-20
author: [agda-algebras development team][]
---

This is a submodule of the Structures module which presents general (relational-algebraic) structures as
inhabitants of record types.  For a similar development using Sigma types see the Structures.Sigma.Basic module.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Basic  where

open import Agda.Primitive       using    ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Function.Base        using    ( flip ; _∘_ )
open import Level                using    ( Level ; Lift ; lift ; lower )
open import Relation.Binary.Core using    () renaming ( Rel to BinRel )

open import Relations.Discrete     using ( Arity ; Op ; _|:_ ; _preserves_ )
open import Relations.Continuous   using ( Rel )


-- Signatures as records.
record signature (𝓞 𝓥 : Level) : Type (lsuc (𝓞 ⊔ 𝓥)) where
 field
  symbol : Type 𝓞
  arity : symbol → Type 𝓥

siglˡ : {𝓞 𝓥 : Level} → signature 𝓞 𝓥 → Level
siglˡ {𝓞}{𝓥} _ = 𝓞

siglʳ : {𝓞 𝓥 : Level} → signature 𝓞 𝓥 → Level
siglʳ {𝓞}{𝓥} _ = 𝓥

sigl : {𝓞 𝓥 : Level} → signature 𝓞 𝓥 → Level
sigl {𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥

open signature public

module _ {𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level} where

 record structure (𝐹 : signature 𝓞₀ 𝓥₀)(𝑅 : signature 𝓞₁ 𝓥₁)
                  {α : Level}{ρ : Level} : Type (𝓞₀ ⊔ 𝓥₀ ⊔ 𝓞₁ ⊔ 𝓥₁ ⊔ (lsuc (α ⊔ ρ))) where
  field
   carrier : Type α
   op  : ∀ (f : symbol 𝐹) → Op  carrier (arity 𝐹 f)      -- interpret. of operations
   rel : ∀ (r : symbol 𝑅) → Rel carrier (arity 𝑅 r) {ρ}  -- interpret. of relations

 open structure public


 module _ {𝐹 : signature 𝓞₀ 𝓥₀}
          {𝑅 : signature 𝓞₁ 𝓥₁}
          where

  -- Syntactic sugar for interpretation of operation
  _ʳ_ : ∀ {α ρ} → (r : symbol 𝑅)(𝒜 : structure 𝐹 𝑅 {α}{ρ}) → Rel (carrier 𝒜) ((arity 𝑅) r) {ρ}
  _ʳ_ = flip rel

  _ᵒ_ : ∀ {α ρ} → (f : symbol 𝐹)(𝒜 : structure 𝐹 𝑅 {α}{ρ}) → Op (carrier 𝒜)((arity 𝐹) f)
  _ᵒ_ = flip op

  compatible : ∀ {α ρ ℓ} → (𝑨 : structure 𝐹 𝑅 {α}{ρ}) → BinRel (carrier 𝑨) ℓ → Type _
  compatible 𝑨 r = ∀ (f : symbol 𝐹) → (f ᵒ 𝑨) |: r

  open Level

  -- lift an operation to act on type of higher universe level
  Lift-op : ∀ {ι α} → {I : Arity ι}{A : Type α} → Op A I → {ℓ : Level} → Op (Lift ℓ A) I
  --  Lift-op f = λ x → lift (f (λ i → lower (x i)))
  Lift-op f = λ z → lift (f (lower ∘ z))

  -- lift a relation to a predicate on type of higher universe level
  -- (note ρ doesn't change; see Lift-Structʳ for that)
  Lift-rel : ∀ {ι α ρ} → {I : Arity ι}{A : Type α} → Rel A I {ρ} → {ℓ : Level} → Rel (Lift ℓ A) I{ρ}
  Lift-rel r x = r (lower ∘ x)

  -- lift the domain of a structure to live in a type at a higher universe level
  Lift-Strucˡ : ∀ {α ρ} → (ℓ : Level) → structure 𝐹 𝑅 {α}{ρ} → structure 𝐹 𝑅  {α ⊔ ℓ}{ρ}
  Lift-Strucˡ ℓ 𝑨 = record { carrier = Lift ℓ (carrier 𝑨)
                           ; op = λ f → Lift-op (f ᵒ 𝑨)
                           ; rel = λ R → Lift-rel (R ʳ 𝑨)
                           }

  -- lift the relations of a structure from level ρ to level ρ ⊔ ℓ
  Lift-Strucʳ : ∀ {α ρ} → (ℓ : Level) → structure 𝐹 𝑅 {α}{ρ} → structure 𝐹 𝑅 {α}{ρ ⊔ ℓ}
  Lift-Strucʳ ℓ 𝑨 = record { carrier = carrier 𝑨 ; op = op 𝑨 ; rel = lrel }
   where
   lrel : (r : symbol 𝑅) → Rel (carrier 𝑨) ((arity 𝑅) r)
   lrel r = Lift ℓ ∘ r ʳ 𝑨


  -- lift both domain of structure and the level of its relations
  Lift-Struc : ∀ {α ρ} → (ℓˡ ℓʳ : Level) → structure 𝐹 𝑅 {α}{ρ} → structure 𝐹 𝑅 {α ⊔ ℓˡ}{ρ ⊔ ℓʳ}
  Lift-Struc ℓˡ ℓʳ 𝑨 = Lift-Strucʳ ℓʳ (Lift-Strucˡ ℓˡ 𝑨)





\end{code}

--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team





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

