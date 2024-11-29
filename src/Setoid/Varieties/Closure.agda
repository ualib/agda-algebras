
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Varieties.Closure {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive         using () renaming ( Set to Type )
open import Data.Product           using ( _,_ ; Σ-syntax )
                                   renaming ( _×_ to _∧_ )
open import Data.Unit.Polymorphic  using ( ⊤ ; tt )
open import Function               using ( id ) renaming ( Func to _⟶_ )
open import Level                  using ( Level ;  _⊔_ ; Lift ; lift ; lower )
open import Relation.Binary        using ( Setoid )
open import Relation.Unary         using ( Pred ; _∈_ ; _⊆_ )

open  import Setoid.Algebras       {𝑆 = 𝑆}  using ( Algebra ; ov ; Lift-Alg ; ⨅ )
open  import Setoid.Homomorphisms  {𝑆 = 𝑆}
      using ( IsHom ; _≅_ ; ≅-trans ; ≅-sym ; Lift-≅ ; ⨅≅⨅ℓρ ; _IsHomImageOf_ )
      using ( IdHomImage ; HomImage-≅ ; HomImage-≅' ; Lift-HomImage-lemma )
open  import Setoid.Subalgebras    {𝑆 = 𝑆}
      using ( _≤_ ; _≤c_ ; ≤-reflexive ; ≤-trans ; ≅-trans-≤ )
      using ( ≤-trans-≅ ; Lift-≤-Lift ; ≤-Lift )

open _⟶_ renaming ( to to _⟨$⟩_ )

module _ {α ρᵃ β ρᵇ : Level} where

 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ

 Level-closure : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 Level-closure ℓ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ]  (𝑨 ∈ 𝒦)  ∧  𝑨 ≅ 𝑩

module _ {α ρᵃ β ρᵇ : Level} where

 Lift-closed :  ∀ ℓ → {𝒦 : Pred(Algebra α ρᵃ) _}{𝑨 : Algebra α ρᵃ} → 𝑨 ∈ 𝒦
  →             Lift-Alg 𝑨 β ρᵇ ∈ (Level-closure ℓ 𝒦)
 Lift-closed _ {𝑨 = 𝑨} kA = 𝑨 , (kA , Lift-≅)

module _  {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ

 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 ∧ 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 ∧ 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ ⊔ ι))
 P ℓ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) ∧ (𝑩 ≅ ⨅ 𝒜))

module _  {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ

 SP : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ ⊔ ι))
 SP ℓ ι 𝒦 = S{α}{ρᵃ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦)

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ ; c = γ ⊔ ρᶜ ; d = δ ⊔ ρᵈ

 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) (d ⊔ ov(a ⊔ b ⊔ c ⊔ ℓ ⊔ ι))
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

module _ {α ρᵃ ℓ ι : Level} where

 is-variety : (𝒱 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)) → Type (ov (α ⊔ ρᵃ ⊔ ℓ ⊔ ι))
 is-variety 𝒱 = V{β = α}{ρᵇ = ρᵃ}{γ = α}{ρᶜ = ρᵃ} ℓ ι 𝒱 ⊆ 𝒱

 variety : Type (ov (α ⊔ ρᵃ ⊔ ov ℓ ⊔ ι))
 variety = Σ[ 𝒱 ∈ (Pred (Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)) ] is-variety 𝒱

module _ {α ρᵃ : Level} where

 private a = α ⊔ ρᵃ

 S-mono :  ∀{ℓ} → {𝒦 𝒦' : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)}
  →        𝒦 ⊆ 𝒦' → S{β = α}{ρᵃ} ℓ 𝒦 ⊆ S ℓ 𝒦'

 S-mono kk {𝑩} (𝑨 , (kA , B≤A)) = 𝑨 , ((kk kA) , B≤A)

 S-idem :  ∀{β ρᵇ γ ρᶜ ℓ} → {𝒦 : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)}
  →        S{β = γ}{ρᶜ} (a ⊔ ℓ) (S{β = β}{ρᵇ} ℓ 𝒦) ⊆ S{β = γ}{ρᶜ} ℓ 𝒦

 S-idem (𝑨 , (𝑩 , sB , A≤B) , x≤A) = 𝑩 , (sB , ≤-trans x≤A A≤B)

 H-expa : ∀{ℓ} → {𝒦 : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)} → 𝒦 ⊆ H ℓ 𝒦
 H-expa {ℓ} {𝒦}{𝑨} kA = 𝑨 , kA , IdHomImage

 S-expa : ∀{ℓ} → {𝒦 : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)} → 𝒦 ⊆ S ℓ 𝒦
 S-expa {ℓ}{𝒦}{𝑨} kA = 𝑨 , (kA , ≤-reflexive)

 P-mono :  ∀{ℓ ι} → {𝒦 𝒦' : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)}
  →        𝒦 ⊆ 𝒦' → P{β = α}{ρᵃ} ℓ ι 𝒦 ⊆ P ℓ ι 𝒦'

 P-mono {ℓ}{ι}{𝒦}{𝒦'} kk {𝑩} (I , 𝒜 , (kA , B≅⨅A)) = I , (𝒜 , ((λ i → kk (kA i)) , B≅⨅A))

 open _≅_
 open IsHom

 P-expa : ∀{ℓ ι} → {𝒦 : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)} → 𝒦 ⊆ P ℓ ι 𝒦
 P-expa {ℓ}{ι}{𝒦}{𝑨} kA = ⊤ , (λ x → 𝑨) , ((λ i → kA) , Goal)
  where
  open Algebra 𝑨 using () renaming (Domain to A)
  open Algebra (⨅ (λ _ → 𝑨)) using () renaming (Domain to ⨅A)
  open Setoid A using ( refl )
  open Setoid ⨅A using () renaming ( refl to refl⨅ )

  to⨅ : A ⟶ ⨅A
  (to⨅ ⟨$⟩ x) = λ _ → x
  cong to⨅ xy = λ _ → xy
  to⨅IsHom : IsHom 𝑨 (⨅ (λ _ → 𝑨)) to⨅
  compatible to⨅IsHom =  refl⨅

  from⨅ : ⨅A ⟶ A
  (from⨅ ⟨$⟩ x) = x tt
  cong from⨅ xy = xy tt
  from⨅IsHom : IsHom (⨅ (λ _ → 𝑨)) 𝑨 from⨅
  compatible from⨅IsHom = refl

  Goal : 𝑨 ≅ ⨅ (λ x → 𝑨)
  to Goal = to⨅ , to⨅IsHom
  from Goal = from⨅ , from⨅IsHom
  to∼from Goal = λ _ _ → refl
  from∼to Goal = λ _ → refl

 V-expa : ∀ ℓ ι → {𝒦 : Pred (Algebra α ρᵃ)(a ⊔ ov ℓ)} → 𝒦 ⊆ V ℓ ι 𝒦
 V-expa ℓ ι {𝒦} {𝑨} x = H-expa {a ⊔ ℓ ⊔ ι} (S-expa {a ⊔ ℓ ⊔ ι} (P-expa {ℓ}{ι} x) )

module _  {α ρᵃ β ρᵇ ℓ ι : Level}{𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}
          {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 S-≅ : 𝑨 ∈ S ℓ 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S{α ⊔ β}{ρᵃ ⊔ ρᵇ}(α ⊔ ρᵃ ⊔ ℓ) (Level-closure ℓ 𝒦)
 S-≅ (𝑨' , kA' , A≤A') A≅B = lA' , (lklA' , B≤lA')
  where
  lA' : Algebra (α ⊔ β) (ρᵃ ⊔ ρᵇ)
  lA' = Lift-Alg 𝑨' β ρᵇ
  lklA' : lA' ∈ Level-closure ℓ 𝒦
  lklA' = Lift-closed ℓ kA'
  subgoal : 𝑨 ≤ lA'
  subgoal = ≤-trans-≅ A≤A' Lift-≅
  B≤lA' : 𝑩 ≤ lA'
  B≤lA' = ≅-trans-≤ (≅-sym A≅B) subgoal

 V-≅ : 𝑨 ∈ V ℓ ι 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V{β = α}{ρᵃ} ℓ ι 𝒦
 V-≅ (𝑨' , spA' , AimgA') A≅B = 𝑨' , spA' , HomImage-≅ AimgA' A≅B

module _  {α ρᵃ ℓ : Level}
          (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ))
          (𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)) where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 V-≅-lc : Lift-Alg 𝑨 ι ι ∈ V{β = ι}{ι} ℓ ι 𝒦 → 𝑨 ∈ V{γ = ι}{ι} ℓ ι 𝒦
 V-≅-lc (𝑨' , spA' , lAimgA') = 𝑨' , (spA' , AimgA')
  where
  AimgA' : 𝑨 IsHomImageOf 𝑨'
  AimgA' = Lift-HomImage-lemma lAimgA'

module _ {α ρᵃ ℓ ι : Level}{𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)} where

 classP : Pred (Algebra α ρᵃ) (ov(α ⊔ ρᵃ ⊔ ℓ ⊔ ι))
 classP = P{β = α}{ρᵃ} ℓ ι 𝒦

 classSP : Pred (Algebra α ρᵃ) (ov(α ⊔ ρᵃ ⊔ ℓ ⊔ ι))
 classSP = S{β = α}{ρᵃ} (α ⊔ ρᵃ ⊔ ℓ ⊔ ι) (P{β = α}{ρᵃ} ℓ ι 𝒦)

 classHSP : Pred (Algebra α ρᵃ) (ov(α ⊔ ρᵃ ⊔ ℓ ⊔ ι))
 classHSP = H{β = α}{ρᵃ}(α ⊔ ρᵃ ⊔ ℓ ⊔ ι) (S{β = α}{ρᵃ}(α ⊔ ρᵃ ⊔ ℓ ⊔ ι) (P{β = α}{ρᵃ}ℓ ι 𝒦))

 classS : ∀{β ρᵇ} → Pred (Algebra β ρᵇ) (β ⊔ ρᵇ ⊔ ov(α ⊔ ρᵃ ⊔ ℓ))
 classS = S ℓ 𝒦
 classK : ∀{β ρᵇ} → Pred (Algebra β ρᵇ) (β ⊔ ρᵇ ⊔ ov(α ⊔ ρᵃ ⊔ ℓ))
 classK = Level-closure{α}{ρᵃ} ℓ 𝒦

module _ {α ρᵃ β ρᵇ γ ρᶜ ℓ : Level}{𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ ; c = γ ⊔ ρᶜ

 LevelClosure-S : Pred (Algebra (α ⊔ γ) (ρᵃ ⊔ ρᶜ)) (c ⊔ ov(a ⊔ b ⊔ ℓ))
 LevelClosure-S = Level-closure{β}{ρᵇ} (a ⊔ ℓ) (S ℓ 𝒦)

 S-LevelClosure : Pred (Algebra (α ⊔ γ) (ρᵃ ⊔ ρᶜ)) (ov(a ⊔ c ⊔ ℓ))
 S-LevelClosure = S{α ⊔ γ}{ρᵃ ⊔ ρᶜ}(a ⊔ ℓ) (Level-closure ℓ 𝒦)

 S-Lift-lemma : LevelClosure-S ⊆ S-LevelClosure
 S-Lift-lemma {𝑪} (𝑩 , (𝑨 , (kA , B≤A)) , B≅C) =
  Lift-Alg 𝑨 γ ρᶜ , (Lift-closed{β = γ}{ρᶜ} ℓ kA) , C≤lA
  where
  B≤lA : 𝑩 ≤ Lift-Alg 𝑨 γ ρᶜ
  B≤lA = ≤-Lift B≤A
  C≤lA : 𝑪 ≤ Lift-Alg 𝑨 γ ρᶜ
  C≤lA = ≅-trans-≤ (≅-sym B≅C) B≤lA

module _ {α ρᵃ : Level} where

 P-Lift-closed :  ∀ ℓ ι → {𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{𝑨 : Algebra α ρᵃ}
  →               𝑨 ∈ P{β = α}{ρᵃ} ℓ ι 𝒦
  →               {γ ρᶜ : Level} → Lift-Alg 𝑨 γ ρᶜ ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (Level-closure ℓ 𝒦)
 P-Lift-closed ℓ ι {𝒦}{𝑨} (I , 𝒜 , kA , A≅⨅𝒜) {γ}{ρᶜ} =
  I , (λ x → Lift-Alg (𝒜 x) γ ρᶜ) , goal1 , goal2
  where
  goal1 : (i : I) → Lift-Alg (𝒜 i) γ ρᶜ ∈ Level-closure ℓ 𝒦
  goal1 i = Lift-closed ℓ (kA i)
  goal2 : Lift-Alg 𝑨 γ ρᶜ ≅ ⨅ (λ x → Lift-Alg (𝒜 x) γ ρᶜ)
  goal2 = ≅-trans (≅-sym Lift-≅) (≅-trans A≅⨅𝒜 (⨅≅⨅ℓρ{ℓ = γ}{ρ = ρᶜ}))

