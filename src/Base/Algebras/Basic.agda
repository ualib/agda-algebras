
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Algebras.Basic {𝑆 : Signature 𝓞 𝓥 } where

open import Agda.Primitive   using () renaming ( Set to  Type ; lzero to ℓ₀ )
open import Data.Product     using ( _,_ ; _×_ ; Σ-syntax )
open import Level            using ( Level ; _⊔_ ; suc )
open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary   using ( _∈_ ; Pred )

open  import Overture        using ( ∣_∣ ; ∥_∥ ; Op )
open  import Base.Relations  using ( _|:_ ; _|:pred_ ; Rel ; compatible-Rel )
                             using ( REL ; compatible-REL )

private variable α β ρ : Level

Algebra : (α : Level) → Type (𝓞 ⊔ 𝓥 ⊔ suc α)
Algebra α =  Σ[ A ∈ Type α ]                 -- the domain
             ∀ (f : ∣ 𝑆 ∣) → Op A (∥ 𝑆 ∥ f)  -- the basic operations

record algebra (α : Level) : Type(suc(𝓞 ⊔ 𝓥 ⊔ α)) where
 constructor mkalg
 field
  carrier : Type α
  opsymbol : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → carrier) → carrier

open algebra

algebra→Algebra : algebra α → Algebra α
algebra→Algebra 𝑨 = (carrier 𝑨 , opsymbol 𝑨)

Algebra→algebra : Algebra α → algebra α
Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥

_̂_ : (𝑓 : ∣ 𝑆 ∣)(𝑨 : Algebra α) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣
𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

Level-of-Alg : {α : Level} → Algebra α → Level
Level-of-Alg {α = α} _ = 𝓞 ⊔ 𝓥 ⊔ suc α

Level-of-Carrier : {α  : Level} → Algebra α → Level
Level-of-Carrier {α = α} _ = α

open Level

Lift-alg-op : {I : Type 𝓥} {A : Type α} → Op A I → (β : Level) → Op (Lift β A) I
Lift-alg-op f β = λ x → lift (f (λ i → lower (x i)))

Lift-Alg : Algebra α → (β : Level) → Algebra (α ⊔ β)
Lift-Alg 𝑨 β = Lift β ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-alg-op (𝑓 ̂ 𝑨) β)

open algebra

Lift-algebra : algebra α → (β : Level) → algebra (α ⊔ β)
Lift-algebra  𝑨 β =  mkalg (Lift β (carrier 𝑨)) (λ (f : ∣ 𝑆 ∣)
 →                   Lift-alg-op ((opsymbol 𝑨) f) β)

compatible : (𝑨 : Algebra α) → BinRel ∣ 𝑨 ∣ ρ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

compatible-pred : (𝑨 : Algebra α) → Pred (∣ 𝑨 ∣ × ∣ 𝑨 ∣)ρ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
compatible-pred  𝑨 P = ∀ 𝑓 → (𝑓 ̂ 𝑨) |:pred P

module _ {I : Type 𝓥} where

 compatible-Rel-alg : (𝑨 : Algebra α) → Rel ∣ 𝑨 ∣ I{ρ} → Type(𝓞 ⊔ α ⊔ 𝓥 ⊔ ρ)
 compatible-Rel-alg 𝑨 R = ∀ (𝑓 : ∣ 𝑆 ∣ ) →  compatible-Rel (𝑓 ̂ 𝑨) R

 compatible-REL-alg : (𝒜 : I → Algebra α) → REL I (λ i → ∣ 𝒜  i ∣) {ρ} → Type _
 compatible-REL-alg 𝒜 R = ∀ ( 𝑓 : ∣ 𝑆 ∣ ) →  compatible-REL (λ i → 𝑓 ̂ (𝒜 i)) R

