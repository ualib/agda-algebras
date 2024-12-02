
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Function         using ( id ; Func )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
                             renaming ( Rel to BinRel )

open import Relation.Binary.PropositionalEquality using ( refl )

open import Overture          using ( ∣_∣  ; ∥_∥  )
open import Base.Relations    using ( 0[_] ; _|:_ ; Equivalence )
open import Setoid.Relations  using ( ⟪_⟫ ; _/_ ; ⟪_∼_⟫-elim )
open import Setoid.Algebras.Basic {𝑆 = 𝑆} using ( ov ; Algebra ; 𝕌[_] ; _̂_ )

private variable α ρ ℓ : Level

_∣≈_ : (𝑨 : Algebra α ρ) → BinRel 𝕌[ 𝑨 ] ℓ → Type _
𝑨 ∣≈ R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

module _ (𝑨 : Algebra α ρ) where
 open Algebra 𝑨  using ()  renaming (Domain to A )
 open Setoid A   using ( _≈_ )

 record IsCongruence (θ : BinRel 𝕌[ 𝑨 ] ℓ) : Type (𝓞 ⊔ 𝓥 ⊔ ρ ⊔ ℓ ⊔ α)  where
  constructor mkcon
  field
   reflexive : ∀ {a₀ a₁} → a₀ ≈ a₁ → θ a₀ a₁
   is-equivalence : IsEquivalence θ
   is-compatible  : 𝑨 ∣≈ θ

  Eqv : Equivalence 𝕌[ 𝑨 ] {ℓ}
  Eqv = θ , is-equivalence

 open IsCongruence public

 Con : {ℓ : Level} → Type (α ⊔ ρ ⊔ ov ℓ)
 Con {ℓ} = Σ[ θ ∈ ( BinRel 𝕌[ 𝑨 ] ℓ ) ] IsCongruence θ

IsCongruence→Con : {𝑨 : Algebra α ρ}(θ : BinRel 𝕌[ 𝑨 ] ℓ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α ρ}((θ , _) : Con 𝑨 {ℓ}) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

open Algebra  using ( Domain ; Interp )
open Setoid   using ( Carrier )
open Func     using ( cong ) renaming ( to to _⟨$⟩_ )

_╱_ : (𝑨 : Algebra α ρ) → Con 𝑨 {ℓ} → Algebra α ℓ
Domain (𝑨 ╱ θ) = 𝕌[ 𝑨 ] / (Eqv ∥ θ ∥)
(Interp (𝑨 ╱ θ)) ⟨$⟩ (f , a) = (f ̂ 𝑨) a
cong (Interp (𝑨 ╱ θ)) {f , u} {.f , v} (refl , a) = is-compatible ∥ θ ∥ f a

module _ (𝑨 : Algebra α ρ) where
 open Algebra 𝑨  using ( )      renaming (Domain to A )
 open Setoid A   using ( _≈_ )  renaming (refl to refl₁)

 _/∙_ : 𝕌[ 𝑨 ] → (θ : Con 𝑨{ℓ}) → Carrier (Domain (𝑨 ╱ θ))
 a /∙ θ = a

 /-≡ :  (θ : Con 𝑨{ℓ}){u v : 𝕌[ 𝑨 ]}
  →     ⟪ u ⟫{Eqv ∥ θ ∥} ≈ ⟪ v ⟫{Eqv ∥ θ ∥} → ∣ θ ∣ u v

 /-≡ θ {u}{v} uv = reflexive ∥ θ ∥ uv

