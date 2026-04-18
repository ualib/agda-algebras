
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Equality.Extensionality where

open import Agda.Primitive   using () renaming ( Set to Type ; Setω to Typeω )
open import Data.Product     using ( _,_ )   renaming ( _×_ to _∧_ )
open import Level            using ( _⊔_ ; Level )
open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Unary   using ( Pred ; _⊆_ )

open  import Axiom.Extensionality.Propositional    using () renaming ( Extensionality to funext )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

open import Overture        using ( transport )
open import Base.Relations  using ( [_] ; []-⊆ ; []-⊇ ; IsBlock ; ⟪_⟫ )
open import Base.Equality.Truncation using ( blk-uip ; to-Σ-≡ )

private variable α β γ ρ 𝓥 : Level

DFunExt : Typeω
DFunExt = (𝓤 𝓥 : Level) → funext 𝓤 𝓥

_≐_ : {α β : Level}{A : Type α}(P Q : Pred A β ) → Type _
P ≐ Q = (P ⊆ Q) ∧ (Q ⊆ P)

pred-ext : (α β : Level) → Type _
pred-ext α β = ∀ {A : Type α}{P Q : Pred A β } → P ⊆ Q → Q ⊆ P → P ≡ Q

module _ {A : Type α}{R : BinRel A ρ} where

 block-ext :  pred-ext α ρ → IsEquivalence{a = α}{ℓ = ρ} R
  →           {u v : A} → R u v → [ u ] R ≡ [ v ] R

 block-ext pe Req {u}{v} Ruv = pe  ([]-⊆ {R = (R , Req)} u v Ruv)
                                   ([]-⊇ {R = (R , Req)} u v Ruv)

 private
   to-subtype|uip :  blk-uip A R
    →                {C D : Pred A ρ}{c : IsBlock C {R}}{d : IsBlock D {R}}
    →                C ≡ D → (C , c) ≡ (D , d)

   to-subtype|uip buip {C}{D}{c}{d} CD =
    to-Σ-≡ (CD , buip D (transport (λ B → IsBlock B) CD c) d)

 block-ext|uip :  pred-ext α ρ → blk-uip A R
  →               IsEquivalence R → ∀{u}{v} → R u v → ⟪ u ⟫ ≡ ⟪ v ⟫

 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)

