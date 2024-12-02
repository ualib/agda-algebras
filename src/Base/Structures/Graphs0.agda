
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Structures.Graphs0 where

open import Agda.Primitive  using () renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax )
open import Data.Sum.Base   using ( _⊎_ ) renaming ( inj₁ to inl ; inj₂ to inr )
open import Data.Fin.Base   using ( Fin )
open import Data.Nat        using ( ℕ )
open import Data.Unit.Base  using ( ⊤ ; tt )
open import Function.Base   using ( _∘_ )
open import Relation.Unary  using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ; module ≡-Reasoning ; cong ; sym ; refl )

open import Overture                        using ( ∣_∣ ; ∥_∥ )
open import Base.Relations                  using ( Rel )
open import Base.Structures.Basic           using ( signature ; structure )
open import Base.Structures.Homs            using ( hom ; is-hom-rel ; is-hom-op )
open import Examples.Structures.Signatures  using ( S∅ )

open signature ; open structure ; open _⊎_

Gr-sig : signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀

Gr-sig 𝐹 𝑅 = record  { symbol = symbol 𝑅 ⊎ symbol 𝐹
                     ; arity  = ar }
 where
 ar : symbol 𝑅 ⊎ symbol 𝐹 → Type ℓ₀
 ar (inl 𝑟) = (arity 𝑅) 𝑟
 ar (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ ⊤

private variable 𝐹 𝑅 : signature ℓ₀ ℓ₀

Gr : structure 𝐹 𝑅 {ℓ₀} {ℓ₀} → structure S∅ (Gr-sig 𝐹 𝑅) {ℓ₀} {ℓ₀}
Gr {𝐹}{𝑅} 𝑨 = record { carrier = carrier 𝑨 ; op = λ () ; rel = split }
  where
  split : (s : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨) (arity (Gr-sig 𝐹 𝑅) s) {ℓ₀}
  split (inl 𝑟) arg = rel 𝑨 𝑟 arg
  split (inr 𝑓) args = op 𝑨 𝑓 (args ∘ inl) ≡ args (inr tt)

open ≡-Reasoning

module _ {𝑨 𝑩 : structure 𝐹 𝑅 {ℓ₀}{ℓ₀}} where

 hom→Grhom : hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
 hom→Grhom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
  i (inl 𝑟) a x = ∣ hhom ∣ 𝑟 a x
  i (inr 𝑓) a x = goal
   where
   homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
   homop = ∥ hhom ∥ 𝑓 (a ∘ inl)

   goal : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr tt))
   goal =  op 𝑩 𝑓 (h ∘ (a ∘ inl))  ≡⟨ sym homop ⟩
           h (op 𝑨 𝑓 (a ∘ inl))    ≡⟨ cong h x ⟩
           h (a (inr tt))          ∎

  ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
  ii = λ ()

 Grhom→hom : hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
 Grhom→hom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel 𝑨 𝑩 h
  i R a x = ∣ hhom ∣ (inl R) a x
  ii : is-hom-op 𝑨 𝑩 h
  ii f a = goal
   where
   split : arity 𝐹 f ⊎ ⊤ → carrier 𝑨
   split (inl x) = a x
   split (inr y) = op 𝑨 f a
   goal : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
   goal = sym (∣ hhom ∣ (inr f) split refl)

record _⇛_⇚_ (𝑩 𝑨 𝑪 : structure 𝐹 𝑅) : Type ℓ₀ where
 field
  to   : hom 𝑩 𝑨 → hom 𝑪 𝑨
  from : hom 𝑪 𝑨 → hom 𝑩 𝑨
  to∼from : ∀ h → (to ∘ from) h ≡ h
  from∼to : ∀ h → (from ∘ to) h ≡ h

