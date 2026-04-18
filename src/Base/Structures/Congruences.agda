
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Congruences where

open import Agda.Primitive  using () renaming ( Set  to Type )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax )
                            renaming ( proj₁ to fst )
open import Function.Base   using ( _∘_ )
open import Level           using ( Level ; suc ; _⊔_ ; lower ; lift )

open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Overture        using ( ∣_∣ )
open import Base.Relations  using ( _|:_ ; 0[_] ; Equivalence ; Quotient ; ⟪_⟫ )
                            using ( 0[_]Equivalence ; ⌞_⌟ ; ⟪_∼_⟫-elim ; _/_ )
open import Base.Equality   using ( swelldef )

open import Base.Structures.Basic  using ( signature ; structure ; sigl )
                                   using ( siglʳ ; compatible )
private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 α ρ : Level

open signature ; open structure

con : ∀ {α ρ} → structure 𝐹 𝑅 {α}{ρ} → Type (sigl 𝐹 ⊔ suc α ⊔ suc ρ)
con {α = α}{ρ} 𝑨 = Σ[ θ ∈ Equivalence (carrier 𝑨){α ⊔ ρ} ] (compatible 𝑨 ∣ θ ∣)

0[_]compatible :  (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → swelldef (siglʳ 𝐹) α
 →                (𝑓 : symbol 𝐹) → (op 𝑨) 𝑓 |: (0[ carrier 𝑨 ] {ρ})

0[ 𝑨 ]compatible wd 𝑓 {i}{j} ptws0  = lift γ
 where
 γ : ((op 𝑨) 𝑓) i ≡ ((op 𝑨) 𝑓) j
 γ = wd ((op 𝑨) 𝑓) i j (lower ∘ ptws0)

0con[_] : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → swelldef (siglʳ 𝐹) α → con 𝑨
0con[ 𝑨 ] wd = 0[ carrier 𝑨 ]Equivalence , 0[ 𝑨 ]compatible wd

_╱_  -- alias  (useful on when signature and universe parameters can be inferred)
 quotient : (𝑨 : structure 𝐹 𝑅 {α}{ρ}) → con 𝑨 → structure 𝐹 𝑅
quotient 𝑨 θ =
 record  { carrier = Quotient (carrier 𝑨) ∣ θ ∣     -- domain of quotient structure
         ; op = λ f b → ⟪ ((op 𝑨) f) (λ i → ⌞ b i ⌟) ⟫ {fst ∣ θ ∣} -- interp of operations
         ; rel = λ r x → ((rel 𝑨) r) (λ i → ⌞ x i ⌟)   -- interpretation of relations
         }

_╱_ = quotient  -- (alias)

/≡-elim :  {𝑨 : structure 𝐹 𝑅 {α}{ρ}} ((θ , _ ) : con 𝑨){u v : carrier 𝑨}
 →         ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ {∣ θ ∣} → ∣ θ ∣ u v

/≡-elim θ {u}{v} x =  ⟪ u ∼ v ⟫-elim{R = ∣ θ ∣} x

𝟎[_╱_] :  (𝑨 : structure 𝐹 𝑅 {α}{ρ}) (θ : con 𝑨)
 →        swelldef (siglʳ 𝐹)(suc (α ⊔ ρ)) → con (𝑨 ╱ θ)

𝟎[ 𝑨 ╱ θ ] wd = 0con[ 𝑨 ╱ θ ] wd

