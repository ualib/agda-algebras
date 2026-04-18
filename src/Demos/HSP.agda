{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )
module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where

open import Data.Unit.Polymorphic  using  ( ⊤ ; tt )
open import Function               using  ( id ; _∘_ ; flip )
open import Level                  using  ( Level ;  _⊔_ ; suc )
open import Relation.Binary        using  ( Rel ; Setoid ; IsEquivalence
                                          ; Reflexive ; Symmetric ; Transitive
                                          ; Sym ; Trans )
open import Relation.Unary         using  ( Pred ; _⊆_ ; _∈_ )

open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _×_ ; _,_ ; Σ ; Σ-syntax )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using () renaming ( Func to _⟶_ )

open  _⟶_           using ( cong ) renaming ( to to _⟨$⟩_ )
open IsEquivalence  using ()
                    renaming ( refl to reflᵉ ; sym to symᵉ ; trans to transᵉ )
open Setoid         using ( Carrier ; isEquivalence ) renaming ( _≈_ to _≈ˢ_ )
                    renaming ( refl to reflˢ ; sym to symˢ ; trans to transˢ )

import Function.Definitions                   as FD
import Relation.Binary.PropositionalEquality  as ≡
import Relation.Binary.Reasoning.Setoid       as SetoidReasoning

private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ

module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd

𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { to = id ; cong = id }

_⟨∘⟩_ :  {A : Setoid α ρᵃ} {B : Setoid β ρᵇ} {C : Setoid γ ρᶜ}
 →       B ⟶ C  →  A ⟶ B  →  A ⟶ C

f ⟨∘⟩ g = record  { to = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g)
                  ; cong = (cong f) ∘ (cong g) }

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b

 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈ᴮ_ )
 open FD

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective _≈ᴬ_ _≈ᴮ_ (_⟨$⟩_ f)

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective F = ∀ {y} → Image F ∋ y

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → Carrier 𝑩 → Carrier 𝑨
 SurjInv f fonto b = Inv f (fonto {b})

module _  {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ}
          (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪) where

 ∘-IsInjective : IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-IsInjective finj ginj = finj ∘ ginj

 ∘-IsSurjective : IsSurjective f → IsSurjective g → IsSurjective (g ⟨∘⟩ f)
 ∘-IsSurjective fonto gonto {y} = Goal where
  mp : Image g ∋ y → Image g ⟨∘⟩ f ∋ y
  mp (eq c p) = η fonto where
   open Setoid 𝑪 using ( trans )
   η : Image f ∋ c → Image g ⟨∘⟩ f ∋ y
   η (eq a q) = eq a (trans p (cong g q))

  Goal : Image g ⟨∘⟩ f ∋ y
  Goal = mp gonto

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 Im : (f : 𝑨 ⟶ 𝑩) → Setoid _ _
 Carrier (Im f) = Carrier 𝑨
 _≈ˢ_ (Im f) b1 b2 = f ⟨$⟩ b1 ≈ f ⟨$⟩ b2 where open Setoid 𝑩

 isEquivalence (Im f) = record { refl = refl ; sym = sym; trans = trans }
  where open Setoid 𝑩

 toIm : (f : 𝑨 ⟶ 𝑩) → 𝑨 ⟶ Im f
 toIm f = record { to = id ; cong = cong f }

 fromIm : (f : 𝑨 ⟶ 𝑩) → Im f ⟶ 𝑩
 fromIm f = record { to = λ x → f ⟨$⟩ x ; cong = id }

 fromIm-inj : (f : 𝑨 ⟶ 𝑩) → IsInjective (fromIm f)
 fromIm-inj _ = id

 toIm-surj : (f : 𝑨 ⟶ 𝑩) → IsSurjective (toIm f)
 toIm-surj _ = eq _ (reflˢ 𝑩)

EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)
EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )

⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

Carrier  (⟨ 𝑆 ⟩ ξ)                = Σ[ f ∈ ∣ 𝑆 ∣ ] (∥ 𝑆 ∥ f → ξ .Carrier)
_≈ˢ_     (⟨ 𝑆 ⟩ ξ)(f , u)(g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

reflᵉ   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → reflˢ   ξ
symᵉ    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → symˢ    ξ (g i)
transᵉ  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → transˢ  ξ (g i) (h i)

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ suc (α ⊔ ρ)) where
 field  Domain  : Setoid α ρ
        Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain

open Algebra
𝔻[_] : Algebra α ρᵃ →  Setoid α ρᵃ
𝔻[ 𝑨 ] = Domain 𝑨

𝕌[_] : Algebra α ρᵃ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)

_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρᵃ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)

module _ (𝑨 : Algebra α ρᵃ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans ) ; open Level
 Lift-Algˡ : (ℓ : Level) → Algebra (α ⊔ ℓ) ρᵃ
 Domain (Lift-Algˡ ℓ) =
  record  { Carrier        = Lift ℓ 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → lower x ≈ lower y
          ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }
          }
 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 cong (Interp (Lift-Algˡ ℓ)) (≡.refl , lab) = cong (Interp 𝑨) ((≡.refl , lab))

 Lift-Algʳ : (ℓ : Level) → Algebra α (ρᵃ ⊔ ℓ)
 Domain (Lift-Algʳ ℓ) =
  record  { Carrier        = 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → Lift ℓ (x ≈ y)
          ; isEquivalence  = record  { refl  = lift refl
                                     ; sym   = lift ∘ sym ∘ lower
                                     ; trans = λ x y → lift (trans (lower x)(lower y))
                                     }
          }
 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (Lift-Algʳ ℓ))(≡.refl , lab) =
  lift ( cong (Interp 𝑨) ( ≡.refl , λ i → lower (lab i) ) )

Lift-Alg : Algebra α ρᵃ → (ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁

module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)
 Domain (⨅ 𝒜) =
  record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
          ; _≈_ = λ a b → ∀ i → (_≈ˢ_ 𝔻[ 𝒜 i ]) (a i)(b i)
          ; isEquivalence =
             record  { refl = λ i → reflᵉ (isEquivalence 𝔻[ 𝒜 i ])
                     ; sym = λ x i → symᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)
                     ; trans = λ x y i → transᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i)
                     }
          }

 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong  ( Interp (𝒜 i) )
                                                   ( ≡.refl , flip f=g i )

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type _
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type _
 compatible-map h = ∀ {f} → compatible-map-op h f

 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor  mkhom
  field        compatible : compatible-map h

 hom : Type _
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h
  HomReduct : hom
  HomReduct = h , isHom

 mon : Type _
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h
  HomReduct : hom
  HomReduct = h , isHom

 epi : Type _
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi

open IsHom ; open IsMon ; open IsEpi
module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE

module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ}
          {g : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]}{h : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑪 ]} where
  open Setoid 𝔻[ 𝑪 ] using ( trans )
  ∘-is-hom : IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-hom ghom hhom = mkhom c where
   c : compatible-map 𝑨 𝑪 (h ⟨∘⟩ g)
   c = trans (cong h (compatible ghom)) (compatible hhom)

  ∘-is-epi : IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-epi gE hE =
    record  { isHom = ∘-is-hom (isHom gE) (isHom hE)
            ; isSurjective = ∘-IsSurjective g h (isSurjective gE) (isSurjective hE)
            }

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where
  ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ∘-hom (h , hhom) (g , ghom) = (g ⟨∘⟩ h) , ∘-is-hom hhom ghom

  ∘-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ∘-epi (h , hepi) (g , gepi) = (g ⟨∘⟩ h) , ∘-is-epi hepi gepi

𝒾𝒹 : {𝑨 : Algebra α ρᵃ} → hom 𝑨 𝑨
𝒾𝒹 {𝑨 = 𝑨} =  𝑖𝑑 , mkhom (reflexive ≡.refl)
              where open Setoid ( Domain 𝑨 ) using ( reflexive )

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 open Setoid 𝔻[ 𝑨 ] using ( reflexive ) renaming ( _≈_ to _≈₁_ ; refl to refl₁ )
 open Setoid 𝔻[ Lift-Algˡ 𝑨 ℓ ]  using () renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid 𝔻[ Lift-Algʳ 𝑨 ℓ ]  using () renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)
 open Level

 ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ = record { to = lift ; cong = id } , mkhom (reflexive ≡.refl)

 FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = record { to = lower ; cong = id } , mkhom reflˡ

 ToFromLiftˡ : ∀ b →  ∣ ToLiftˡ ∣ ⟨$⟩ (∣ FromLiftˡ ∣ ⟨$⟩ b) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → ∣ FromLiftˡ ∣ ⟨$⟩ (∣ ToLiftˡ ∣ ⟨$⟩ a) ≈₁ a
 FromToLiftˡ a = refl₁

 ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ = record { to = id ; cong = lift } , mkhom (lift (reflexive ≡.refl))

 FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ = record { to = id ; cong = lower } , mkhom reflˡ

 ToFromLiftʳ : ∀ b → ∣ ToLiftʳ ∣ ⟨$⟩ (∣ FromLiftʳ ∣ ⟨$⟩ b) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → ∣ FromLiftʳ ∣ ⟨$⟩ (∣ ToLiftʳ ∣ ⟨$⟩ a) ≈₁ a
 FromToLiftʳ a = refl₁

module _ {𝑨 : Algebra α ρᵃ}{ℓ r : Level} where
 open  Setoid 𝔻[ 𝑨 ]               using ( refl )
 open  Setoid 𝔻[ Lift-Alg 𝑨 ℓ r ]  using ( _≈_ )
 open  Level
 ToLift : hom 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift = ∘-hom ToLiftˡ ToLiftʳ

 FromLift : hom (Lift-Alg 𝑨 ℓ r) 𝑨
 FromLift = ∘-hom FromLiftʳ FromLiftˡ

 ToFromLift : ∀ b → ∣ ToLift ∣ ⟨$⟩ (∣ FromLift ∣ ⟨$⟩ b) ≈ b
 ToFromLift b = lift refl

 ToLift-epi : epi 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift-epi =
  ∣ ToLift ∣ , record  { isHom = ∥ ToLift ∥
                       ; isSurjective = λ{y} → eq(∣ FromLift ∣ ⟨$⟩ y)(ToFromLift y)
                       }

module _ {ι : Level}{I : Type ι}{𝑨 : Algebra α ρᵃ}(ℬ : I → Algebra β ρᵇ) where
 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom where  h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
                              h ⟨$⟩ a = λ i → ∣ 𝒽 i ∣ ⟨$⟩ a
                              cong h xy i = cong ∣ 𝒽 i ∣ xy
                              hhom : IsHom 𝑨 (⨅ ℬ) h
                              compatible hhom = λ i → compatible ∥ 𝒽 i ∥

module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ]  using ()  renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝔻[ 𝑩 ]  using ()  renaming ( _≈_ to _≈ᴮ_ )

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ ) where
  constructor  mkiso
  field        to    : hom 𝑨 𝑩
               from  : hom 𝑩 𝑨
               to∼from : ∀ b → ∣ to ∣    ⟨$⟩ (∣ from ∣  ⟨$⟩ b)  ≈ᴮ b
               from∼to : ∀ a → ∣ from ∣  ⟨$⟩ (∣ to ∣    ⟨$⟩ a)  ≈ᴬ a

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x}{y} xy = trans (sym (from∼to x)) (trans ξ (from∼to y))
   where  open Setoid 𝔻[ 𝑨 ] using ( sym ; trans )
          ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ᴬ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
          ξ = cong ∣ from ∣ xy

  fromIsSurjective : IsSurjective ∣ from ∣
  fromIsSurjective {x} = eq (∣ to ∣ ⟨$⟩ x) (sym (from∼to x))
   where open Setoid 𝔻[ 𝑨 ] using ( sym )

open _≅_

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} =
 mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl where open Setoid 𝔻[ 𝑨 ] using ( refl )

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ}) (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν where
  f : hom 𝑨 𝑪                ;  g : hom 𝑪 𝑨
  f = ∘-hom (to ab) (to bc)  ;  g = ∘-hom (from bc) (from ab)

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; trans )
  open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈ᶜ_ ; trans to transᶜ )
  τ : ∀ b → ∣ f ∣ ⟨$⟩ (∣ g ∣ ⟨$⟩ b) ≈ᶜ b
  τ b = transᶜ (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)

  ν : ∀ a → ∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a) ≈ a
  ν a = trans (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)

ov : Level → Level         -- shorthand for a common level transformation
ov α = 𝓞 ⊔ 𝓥 ⊔ suc α

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type _
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {α = α}{𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl
 where open Setoid 𝔻[ 𝑨 ] using ( refl )

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 HomIm : (h : hom 𝑨 𝑩) → Algebra _ _
 Domain (HomIm h) = Im ∣ h ∣
 Interp (HomIm h) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (HomIm h)) {x1 , x2} {.x1 , y2} (≡.refl , e) =
  begin
      ∣ h ∣  ⟨$⟩         (Interp 𝑨  ⟨$⟩ (x1 , x2))  ≈⟨ h-compatible                  ⟩
   Interp 𝑩  ⟨$⟩ (x1 , λ x → ∣ h ∣  ⟨$⟩ x2 x)       ≈⟨ cong (Interp 𝑩) (≡.refl , e)  ⟩
   Interp 𝑩  ⟨$⟩ (x1 , λ x → ∣ h ∣  ⟨$⟩ y2 x)       ≈˘⟨ h-compatible                 ⟩
      ∣ h ∣  ⟨$⟩         (Interp 𝑨  ⟨$⟩ (x1 , y2))  ∎
   where  open Setoid 𝔻[ 𝑩 ] ; open SetoidReasoning 𝔻[ 𝑩 ]
          open IsHom ∥ h ∥ renaming (compatible to h-compatible)

 toHomIm : (h : hom 𝑨 𝑩) → hom 𝑨 (HomIm h)
 toHomIm h = toIm ∣ h ∣ , mkhom (reflˢ 𝔻[ 𝑩 ])

 fromHomIm : (h : hom 𝑨 𝑩) → hom (HomIm h) 𝑩
 fromHomIm h = fromIm ∣ h ∣ , mkhom (IsHom.compatible ∥ h ∥)

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})
 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ

_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

≤-reflexive   :  {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive = 𝒾𝒹 , id

mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

data Term (X : Type χ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X

module _ {X : Type χ } where

 data _≃_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≃ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≃ (t i)) → (node f s) ≃ (node f t)

 ≃-isRefl   : Reflexive      _≃_
 ≃-isRefl {ℊ _} = rfl ≡.refl
 ≃-isRefl {node _ _} = gnl λ _ → ≃-isRefl

 ≃-isSym    : Symmetric      _≃_
 ≃-isSym (rfl x) = rfl (≡.sym x)
 ≃-isSym (gnl x) = gnl λ i → ≃-isSym (x i)

 ≃-isTrans  : Transitive     _≃_
 ≃-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≃-isTrans (gnl x) (gnl y) = gnl λ i → ≃-isTrans (x i) (y i)

 ≃-isEquiv  : IsEquivalence  _≃_
 ≃-isEquiv = record { refl = ≃-isRefl ; sym = ≃-isSym ; trans = ≃-isTrans }

TermSetoid : (X : Type χ) → Setoid _ _
TermSetoid X = record { Carrier = Term X ; _≈_ = _≃_ ; isEquivalence = ≃-isEquiv }

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Algebra.Domain (𝑻 X) = TermSetoid X
Algebra.Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Algebra.Interp (𝑻 X)) (≡.refl , ss≃ts) = gnl ss≃ts

module Environment (𝑨 : Algebra α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )

 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ τ → (x : X) → ρ x ≈ τ x
                 ; isEquivalence = record  { refl   = λ _      → refl
                                           ; sym    = λ h x    → sym (h x)
                                           ; trans  = λ g h x  → trans (g x)(h x) }}

 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ    = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ    = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v          = u≈v x
 cong ⟦ node f args ⟧ x≈y  = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

 Equal : {X : Type χ}(s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) → ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

 ≃→Equal : {X : Type χ}(s t : Term X) → s ≃ t → Equal s t
 ≃→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≃→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≃→Equal(s i)(t i)(x i)ρ )

 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 reflᵉ   EqualIsEquiv = λ _        → refl
 symᵉ    EqualIsEquiv = λ x=y ρ    → sym (x=y ρ)
 transᵉ  EqualIsEquiv = λ ij jk ρ  → trans (ij ρ) (jk ρ)

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Environment 𝑨  using ( ⟦_⟧ )
 open Environment 𝑩  using () renaming ( ⟦_⟧ to ⟦_⟧ᴮ )
 open Setoid 𝔻[ 𝑩 ]  using ( _≈_ ; refl  )
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a =  begin
   h(⟦ node f t ⟧ ⟨$⟩ a)            ≈⟨ compatible ∥ hh ∥ ⟩
   (f ̂ 𝑩)(λ i → h(⟦ t i ⟧ ⟨$⟩ a))  ≈⟨ cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term(t i) a) ⟩
   ⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a)   ∎ where open SetoidReasoning 𝔻[ 𝑩 ]

module _ {X : Type χ}{ι : Level} {I : Type ι} (𝒜 : I → Algebra α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ]  using ( _≈_ )
 open Environment      using ( ⟦_⟧ ; ≃→Equal )

 interp-prod : (p : Term X) → ∀ ρ →  (⟦ ⨅ 𝒜 ⟧ p) ⟨$⟩ ρ   ≈   λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
 interp-prod (ℊ x)       = λ ρ i  → ≃→Equal (𝒜 i) (ℊ x) (ℊ x) ≃-isRefl λ _ → (ρ x) i
 interp-prod (node f t)  = λ ρ    → cong (Interp (⨅ 𝒜)) ( ≡.refl , λ j k → interp-prod (t j) ρ k )

module _ {X : Type χ} where
 _⊧_≈_ : Algebra α ρᵃ → Term X → Term X → Type _
 𝑨 ⊧ p ≈ q = Equal p q where open Environment 𝑨

 _⊫_≈_ : Pred (Algebra α ρᵃ) ℓ → Term X → Term X → Type _
 𝒦 ⊫ p ≈ q = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

 _⊨_ : (𝑨 : Algebra α ρᵃ) → Pred(Term X × Term X)(ov χ) → Type _
 𝑨 ⊨ ℰ = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where
 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ = begin
  ⟦ p ⟧     ⟨$⟩             ρ    ≈˘⟨  cong ⟦ p ⟧ (f∼g ∘ ρ)        ⟩
  ⟦ p ⟧     ⟨$⟩ (f ∘  (g ∘  ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
  f(⟦ p ⟧ᴬ  ⟨$⟩       (g ∘  ρ))  ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))   ⟩
  f(⟦ q ⟧ᴬ  ⟨$⟩       (g ∘  ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
  ⟦ q ⟧     ⟨$⟩ (f ∘  (g ∘  ρ))  ≈⟨   cong ⟦ q ⟧ (f∼g ∘ ρ)        ⟩
  ⟦ q ⟧     ⟨$⟩             ρ    ∎
  where  private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
         open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
         open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]

Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

module _ {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ
 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 P _ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where
 ⊧-H-invar : 𝑨 ⊧ p ≈ q → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-H-invar Apq (φh , φE) ρ = begin
       ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
   φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong ∣ φh ∣ (Apq (φ⁻¹ ∘ ρ))         ⟩
   φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
       ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ q ⟧   ⟨$⟩               ρ    ∎ where
   φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
   φ⁻¹ = SurjInv ∣ φh ∣ φE
   private φ = (_⟨$⟩_ ∣ φh ∣)
   open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
   open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]

 ⊧-S-invar : 𝑨 ⊧ p ≈ q → 𝑩 ≤ 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-S-invar Apq B≤A b = ∥ B≤A ∥
  ( begin
    h (  ⟦ p ⟧   ⟨$⟩       b)  ≈⟨   comm-hom-term hh p b  ⟩
         ⟦ p ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈⟨   Apq (h ∘ b)           ⟩
         ⟦ q ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈˘⟨  comm-hom-term hh q b  ⟩
    h (  ⟦ q ⟧   ⟨$⟩       b)  ∎ )
  where
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩  using ( ⟦_⟧ )
  private hh = ∣ B≤A ∣ ; h = _⟨$⟩_ ∣ hh ∣

module _ {X : Type χ}{I : Type ℓ}(𝒜 : I → Algebra α ρᵃ){p q : Term X} where
 ⊧-P-invar : (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar 𝒜pq a = begin
   ⟦ p ⟧₁               ⟨$⟩  a                ≈⟨   interp-prod 𝒜 p a            ⟩
   ( λ i → (⟦ 𝒜 i ⟧ p)  ⟨$⟩  λ x → (a x) i )  ≈⟨ (λ i → 𝒜pq i (λ x → (a x) i))  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ q)  ⟨$⟩  λ x → (a x) i )  ≈˘⟨  interp-prod 𝒜 q a            ⟩
   ⟦ q ⟧₁               ⟨$⟩  a                ∎ where
  open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ
 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) _
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 H-id1 : 𝒦 ⊫ p ≈ q → H{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 H-id1 σ 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ 𝑨 kA) BimgA

 S-id1 : 𝒦 ⊫ p ≈ q → S{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

 S-id2 : S ℓ 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))

 P-id1 : ∀{ι} → 𝒦 ⊫ p ≈ q → P{β = α}{ρᵃ}ℓ ι 𝒦 ⊫ p ≈ q
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A) where
  IH : ⨅ 𝒜 ⊧ p ≈ q
  IH = ⊧-P-invar 𝒜 {p}{q} λ i → σ (𝒜 i) (kA i)

module _ {X : Type χ}{ι : Level}(ℓ : Level){𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι
 V-id1 : 𝒦 ⊫ p ≈ q → V ℓ ι 𝒦 ⊫ p ≈ q
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA)) where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ p ≈ q
   spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x)       = h x
 free-lift (node f t)  = (f ̂ 𝑨) λ i → free-lift (t i)

 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( reflexive to reflexiveᴬ )
  flcong : ∀ {s t} → s ≃ t → free-lift s ≈ free-lift t
  flcong (_≃_.rfl x) = reflexiveᴬ (≡.cong h x)
  flcong (_≃_.gnl x) = cong (Interp 𝑨) (≡.refl , λ i → flcong (x i))

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func ,
   mkhom λ{_}{a} → cong (Interp 𝑨) (≡.refl , λ i → (cong free-lift-func){a i} ≃-isRefl)

module _  {X : Type χ} {𝑨 : Algebra α ρᵃ}   where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x)       = refl
 free-lift-interp η (node f t)  = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)

module FreeAlgebra (𝒦 : Pred (Algebra α ρᵃ) ℓ) where
 private c = α ⊔ ρᵃ ; ι = ov c ⊔ ℓ
 ℑ : {χ : Level} → Type χ → Type (ι ⊔ χ)
 ℑ X = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × (X → 𝕌[ 𝑨 ])

 𝑪 : {χ : Level} → Type χ → Algebra (ι ⊔ χ)(ι ⊔ χ)
 𝑪 X = ⨅ {I = ℑ X} ∣_∣

 homC : (X : Type χ) → hom (𝑻 X) (𝑪 X)
 homC X = ⨅-hom-co _ (λ i → lift-hom (snd ∥ i ∥))

 𝔽[_] : {χ : Level} → Type χ → Algebra (ov χ) (ι ⊔ χ)
 𝔽[ X ] = HomIm (homC X)

module FreeHom {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ; ι = ov c ⊔ ℓ
 open FreeAlgebra 𝒦 using ( 𝔽[_] ; homC )

 epiF[_] : (X : Type c) → epi (𝑻 X) 𝔽[ X ]
 epiF[ X ] = ∣ toHomIm (homC X) ∣ , record  { isHom = ∥ toHomIm (homC X) ∥
                                            ; isSurjective = toIm-surj ∣ homC X ∣ }

 homF[_] : (X : Type c) → hom (𝑻 X) 𝔽[ X ]
 homF[ X ] = IsEpi.HomReduct ∥ epiF[ X ] ∥

module _ {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ)(α ⊔ ρᵃ ⊔ ℓ)}{𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeAlgebra 𝒦 using ( 𝔽[_] ; 𝑪 )
 open Setoid 𝔻[ 𝑨 ] using ( refl ; sym ; trans ) renaming ( Carrier to A ; _≈_ to _≈ᴬ_ )

 F-ModTh-epi : 𝑨 ∈ Mod (Th 𝒦) → epi 𝔽[ A ]  𝑨
 F-ModTh-epi A∈ModThK = φ , isEpi where

  φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
  _⟨$⟩_ φ            = free-lift{𝑨 = 𝑨} id
  cong φ {p} {q} pq  = Goal
   where
   lift-pq : (p , q) ∈ Th 𝒦
   lift-pq 𝑩 x ρ = begin
    ⟦ p ⟧ ⟨$⟩ ρ    ≈⟨ free-lift-interp {𝑨 = 𝑩} ρ p  ⟩
    free-lift ρ p  ≈⟨ pq (𝑩 , x , ρ)                ⟩
    free-lift ρ q  ≈˘⟨ free-lift-interp{𝑨 = 𝑩} ρ q  ⟩
    ⟦ q ⟧ ⟨$⟩ ρ    ∎
     where open SetoidReasoning 𝔻[ 𝑩 ] ; open Environment 𝑩 using ( ⟦_⟧ )

   Goal : free-lift id p ≈ᴬ free-lift id q
   Goal = begin
    free-lift id p  ≈˘⟨ free-lift-interp {𝑨 = 𝑨} id p   ⟩
    ⟦ p ⟧ ⟨$⟩ id    ≈⟨ A∈ModThK {p = p} {q} lift-pq id  ⟩
    ⟦ q ⟧ ⟨$⟩ id    ≈⟨ free-lift-interp {𝑨 = 𝑨} id q    ⟩
    free-lift id q  ∎
     where open SetoidReasoning 𝔻[ 𝑨 ] ; open Environment 𝑨 using ( ⟦_⟧ )

  isEpi : IsEpi 𝔽[ A ] 𝑨 φ
  isEpi = record { isHom = mkhom refl ; isSurjective = eq (ℊ _) refl }

 F-ModThV-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ]  𝑨
 F-ModThV-epi A∈ModThVK = F-ModTh-epi λ {p}{q} → Goal {p}{q}
  where
  Goal : 𝑨 ∈ Mod (Th 𝒦)
  Goal {p}{q} x ρ = A∈ModThVK{p}{q} (V-id1 ℓ {p = p}{q} x) ρ

 F-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 F-ModTh-epi-lift A∈ModThK = ∘-epi (F-ModThV-epi λ {p q} → A∈ModThK{p = p}{q} ) ToLift-epi

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)) where
 V-expa : 𝒦 ⊆ V ℓ (ov (α ⊔ ρᵃ ⊔ ℓ)) 𝒦
 V-expa {x = 𝑨}kA = 𝑨 , (𝑨 , (⊤ , (λ _ → 𝑨), (λ _ → kA), Goal), ≤-reflexive), IdHomImage
  where
  open Setoid 𝔻[ 𝑨 ]            using ( refl )
  open Setoid 𝔻[ ⨅ (λ _ → 𝑨) ]  using () renaming ( refl to refl⨅ )
  to⨅    : 𝔻[ 𝑨 ]            ⟶ 𝔻[ ⨅ (λ _ → 𝑨) ]
  to⨅    = record { to = λ x _ → x   ; cong = λ xy _ → xy }
  from⨅  : 𝔻[ ⨅ (λ _ → 𝑨) ]  ⟶ 𝔻[ 𝑨 ]
  from⨅  = record { to = λ x → x tt  ; cong = λ xy → xy tt }
  Goal   : 𝑨 ≅ ⨅ (λ x → 𝑨)
  Goal   = mkiso (to⨅ , mkhom refl⨅) (from⨅ , mkhom refl) (λ _ _ → refl) (λ _ → refl)

module _ {ℓ : Level}{X : Type ℓ}{ℰ : {Y : Type ℓ} → Pred (Term Y × Term Y) (ov ℓ)} where
 private 𝒦 = Mod{α = ℓ}{ℓ}{X} ℰ     -- an arbitrary equational class

 EqCl⇒Var : V ℓ (ov ℓ) 𝒦 ⊆ 𝒦
 EqCl⇒Var {𝑨} vA {p} {q} pℰq ρ = V-id1 ℓ {𝒦} {p} {q} (λ _ x τ → x pℰq τ) 𝑨 vA ρ

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 ModTh-closure : V{β = β}{ρᵇ}{γ}{ρᶜ}{δ}{ρᵈ} ℓ ι 𝒦 ⊆ Mod{X = X} (Th (V ℓ ι 𝒦))
 ModTh-closure {x = 𝑨} vA {p} {q} x ρ = x 𝑨 vA ρ

 open FreeHom {ℓ = ℓ}{𝒦}
 open FreeAlgebra 𝒦 using (homC ;  𝔽[_] ; 𝑪 )
 homFC : hom 𝔽[ X ] (𝑪 X)
 homFC = fromHomIm (homC X)

 monFC : mon 𝔽[ X ] (𝑪 X)
 monFC = ∣ homFC ∣ , record { isHom = ∥ homFC ∥
                            ; isInjective =  λ {x}{y}→ fromIm-inj ∣ homC X ∣ {x}{y}   }
 F≤C : 𝔽[ X ] ≤ 𝑪 X
 F≤C = mon→≤ monFC

 open FreeAlgebra 𝒦 using ( ℑ )

 SPF : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SPF = 𝑪 X , ((ℑ X) , (∣_∣ , ((λ i → fst ∥ i ∥) , ≅-refl))) ,  F≤C

module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 Var⇒EqCl : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Var⇒EqCl 𝑨 ModThA = 𝔽[ 𝕌[ 𝑨 ] ] , (SPF{ℓ = ℓ} 𝒦 , Aim)
  where
  open FreeAlgebra 𝒦 using ( 𝔽[_] )
  epiFlA : epi 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι)
  epiFlA = F-ModTh-epi-lift{ℓ = ℓ} λ {p q} → ModThA{p = p}{q}

  φ : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  φ = epi→ontohom 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι) epiFlA

  Aim : 𝑨 IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  Aim = ∘-hom ∣ φ ∣(from Lift-≅), ∘-IsSurjective _ _ ∥ φ ∥(fromIsSurjective(Lift-≅{𝑨 = 𝑨}))

