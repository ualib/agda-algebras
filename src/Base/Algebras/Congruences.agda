
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( Σ-syntax ; _,_ )
open import Function.Base    using ( _∘_ )
open import Level            using ( Level ; _⊔_ ; suc )
open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Overture        using ( ∣_∣ ; ∥_∥ )
open import Base.Relations  using ( _|:_ ; 0[_] ; 0[_]Equivalence ; _/_ ; ⟪_⟫ ; IsBlock )
open import Base.Equality   using ( swelldef )

open import Base.Algebras.Basic     {𝑆 = 𝑆}  using ( Algebra ; compatible ; _̂_ )
open import Base.Algebras.Products  {𝑆 = 𝑆}  using ( ov )

private variable α β ρ : Level

record IsCongruence (𝑨 : Algebra α)(θ : BinRel ∣ 𝑨 ∣ ρ) : Type(ov ρ ⊔ α)  where
 constructor mkcon
 field
  is-equivalence : IsEquivalence θ
  is-compatible  : compatible 𝑨 θ

Con : (𝑨 : Algebra α) → Type(α ⊔ ov ρ)
Con {α}{ρ}𝑨 = Σ[ θ ∈ ( BinRel ∣ 𝑨 ∣ ρ ) ] IsCongruence 𝑨 θ

IsCongruence→Con : {𝑨 : Algebra α}(θ : BinRel ∣ 𝑨 ∣ ρ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α} → ((θ , _) : Con{α}{ρ} 𝑨) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

open Level

0[_]Compatible : {α : Level}(𝑨 : Algebra α){ρ : Level} → swelldef 𝓥 α → (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: (0[ ∣ 𝑨 ∣ ]{ρ})
0[ 𝑨 ]Compatible wd 𝑓 {i}{j} ptws0  = lift γ
  where
  γ : (𝑓 ̂ 𝑨) i ≡ (𝑓 ̂ 𝑨) j
  γ = wd (𝑓 ̂ 𝑨) i j (lower ∘ ptws0)

open IsCongruence
0Con[_] : {α : Level}(𝑨 : Algebra α){ρ : Level} → swelldef 𝓥 α → Con{α}{α ⊔ ρ} 𝑨
0Con[ 𝑨 ]{ρ} wd = let  0eq = 0[ ∣ 𝑨 ∣ ]Equivalence{ρ}  in
                       ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ]Compatible wd)

_╱_ : (𝑨 : Algebra α) → Con{α}{ρ} 𝑨 → Algebra (α ⊔ suc ρ)
𝑨 ╱ θ =  (∣ 𝑨 ∣ / ∣ θ ∣)  ,                              -- domain of quotient algebra
         λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.blk ∥ 𝑎 i ∥) ⟫  -- ops of quotient algebra

𝟘[_╱_] : (𝑨 : Algebra α)(θ : Con{α}{ρ} 𝑨) → BinRel (∣ 𝑨 ∣ / ∣ θ ∣)(α ⊔ suc ρ)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

𝟎[_╱_] :  {α : Level}(𝑨 : Algebra α){ρ : Level}(θ : Con {α}{ρ}𝑨)
 →        swelldef 𝓥 (α ⊔ suc ρ)  → Con (𝑨 ╱ θ)

𝟎[_╱_] {α} 𝑨 {ρ} θ wd = let 0eq = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence  in
 ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ╱ θ ]Compatible {ρ} wd)

open IsCongruence

/-≡ :  {𝑨 : Algebra α}(θ : Con{α}{ρ} 𝑨){u v : ∣ 𝑨 ∣}
 →     ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v

/-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

