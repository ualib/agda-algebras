
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Varieties.HSP {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
                             renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using () renaming ( Func to _⟶_ )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )

open  import Overture          using ( ∣_∣ ; ∥_∥ )
open  import Setoid.Relations  using ( fkerPred )

open  import Setoid.Algebras {𝑆 = 𝑆}     using ( Algebra ; ov ; Lift-Alg ; ⨅ )
open  import Setoid.Subalgebras {𝑆 = 𝑆}  using ( _≤_ ; mon→≤ )
open  import Setoid.Homomorphisms {𝑆 = 𝑆}
      using  ( hom ; mon ; IsMon ; IsHom ; epi ; epi→ontohom ; ⨅-hom-co
             ; HomFactor ; ≅-refl ; _IsHomImageOf_ )

open  import Setoid.Terms {𝑆 = 𝑆}
      using ( module Environment ; 𝑻 ; lift-hom ; free-lift ; free-lift-interp )

open  import Setoid.Varieties.Closure {𝑆 = 𝑆}
      using ( S ; V ; P ; S-idem ; V-≅-lc )

open  import Setoid.Varieties.Preservation {𝑆 = 𝑆}
      using ( S-id2 ; PS⊆SP )

open  import Setoid.Varieties.FreeAlgebras {𝑆 = 𝑆}
      using ( module FreeHom ; 𝔽-ModTh-epi-lift )

open  import Setoid.Varieties.SoundAndComplete  {𝑆 = 𝑆}
      using ( module FreeAlgebra ; _⊫_ ; _≈̇_ ;  _⊢_▹_≈_ ; Mod ; Th )

open _⟶_          using () renaming ( to to _⟨$⟩_ )
open Setoid       using ( Carrier )
open Algebra      using ( Domain )
open Environment  using ( Env )

module _  {α ρᵃ ℓ : Level}
          (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ))
          {X : Type (α ⊔ ρᵃ ⊔ ℓ)} where

 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

 ℑ⁺ : Type ι
 ℑ⁺ = Σ[ 𝑨 ∈ (Algebra α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → Algebra α ρᵃ
 𝔄⁺ i = ∣ i ∣

 ℭ : Algebra ι ι
 ℭ = ⨅ 𝔄⁺

 skEqual : (i : ℑ⁺) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where
  open Setoid (Domain (𝔄⁺ i)) using ( _≈_ )
  open Environment (𝔄⁺ i) using ( ⟦_⟧ )

 AllEqual⊆ker𝔽 :  ∀ {p q}
  →               (∀ i → skEqual i {p}{q}) → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣

 AllEqual⊆ker𝔽 {p} {q} x = Goal
  where
  open Algebra 𝔽[ X ]  using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F        using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )
  S𝒦⊫pq : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x (𝑨 , sA , ρ)
  Goal : p ≈F≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{ℓ = ℓ}{p = p}{q} S𝒦⊫pq)

 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄⁺ h
  where
  h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
  h i = lift-hom (snd ∥ i ∥)

 open Algebra 𝔽[ X ]  using () renaming ( Domain to F ; Interp to InterpF )
 open Setoid F        using () renaming (refl to reflF ; _≈_ to _≈F≈_ ; Carrier to ∣F∣)

 ker𝔽⊆kerℭ : fkerPred ∣ hom𝔽[ X ] ∣ ⊆ fkerPred ∣ homℭ ∣
 ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid (Domain 𝑨)  using ( _≈_ ; sym ; trans )
  open Environment 𝑨      using ( ⟦_⟧ )
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t
  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = trans (sym (fl p)) (trans subgoal (fl q))

 hom𝔽ℭ : hom 𝔽[ X ] ℭ
 hom𝔽ℭ = ∣ HomFactor ℭ homℭ hom𝔽[ X ] ker𝔽⊆kerℭ hom𝔽[ X ]-is-epic ∣

 open Environment ℭ

 kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ fkerPred ∣ homℭ ∣ → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣
 kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
  where
  pqEqual : ∀ i → skEqual i {p}{q}
  pqEqual i = goal
   where
   open Environment (𝔄⁺ i)      using () renaming ( ⟦_⟧ to ⟦_⟧ᵢ )
   open Setoid (Domain (𝔄⁺ i))  using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ᵢ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ᵢ ⟨$⟩ snd ∥ i ∥
   goal = trans  (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
                 (trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))
  E⊢pq : ℰ ⊢ X ▹ p ≈ q
  E⊢pq = AllEqual⊆ker𝔽 pqEqual

 mon𝔽ℭ : mon 𝔽[ X ] ℭ
 mon𝔽ℭ = ∣ hom𝔽ℭ ∣ , isMon
  where
  open IsMon
  open IsHom
  isMon : IsMon 𝔽[ X ] ℭ ∣ hom𝔽ℭ ∣
  isHom isMon = ∥ hom𝔽ℭ ∥
  isInjective isMon {p} {q} φpq = kerℭ⊆ker𝔽 φpq

 𝔽≤ℭ : 𝔽[ X ] ≤ ℭ
 𝔽≤ℭ = mon→≤ mon𝔽ℭ

 SP𝔽 : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SP𝔽 = S-idem SSP𝔽
  where
  PSℭ : ℭ ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  PSℭ = ℑ⁺ , (𝔄⁺ , ((λ i → fst ∥ i ∥) , ≅-refl))

  SPℭ : ℭ ∈ S ι (P ℓ ι 𝒦)
  SPℭ = PS⊆SP {ℓ = ℓ} PSℭ

  SSP𝔽 : 𝔽[ X ] ∈ S ι (S ι (P ℓ ι 𝒦))
  SSP𝔽 = ℭ , (SPℭ , 𝔽≤ℭ)

module _ {α ρᵃ ℓ : Level}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom (α ⊔ ρᵃ ⊔ ℓ) {α}{ρᵃ}{ℓ}{𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

 Birkhoff : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Birkhoff 𝑨 ModThA = V-≅-lc{α}{ρᵃ}{ℓ} 𝒦 𝑨 VlA
  where
  open Setoid (Domain 𝑨) using () renaming ( Carrier to ∣A∣ )
  sp𝔽A : 𝔽[ ∣A∣ ] ∈ S{ι} ι (P ℓ ι 𝒦)
  sp𝔽A = SP𝔽{ℓ = ℓ} 𝒦

  epi𝔽lA : epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι)
  epi𝔽lA = 𝔽-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})

  lAimg𝔽A : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ ∣A∣ ]
  lAimg𝔽A = epi→ontohom 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 ι ι) epi𝔽lA

  VlA : Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦
  VlA = 𝔽[ ∣A∣ ] , sp𝔽A , lAimg𝔽A

 module _ {𝑨 : Algebra α ρᵃ} where
  open Setoid (Domain 𝑨) using () renaming ( Carrier to ∣A∣ )

  Birkhoff-converse : 𝑨 ∈ V{α}{ρᵃ}{α}{ρᵃ}{α}{ρᵃ} ℓ ι 𝒦 → 𝑨 ∈ Mod{X = ∣A∣} (Th (V ℓ ι 𝒦))
  Birkhoff-converse vA pThq = pThq 𝑨 vA

