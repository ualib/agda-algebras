
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Equality.Welldefined where

open import Agda.Primitive  using () renaming ( Set to Type ; Setω to Typeω )
open import Data.Fin        using ( Fin ; toℕ )
open import Data.Product    using ( _,_ ; _×_ )
open import Data.List       using ( List ; [] ; [_] ; _∷_ ; _++_ )
open import Function        using ( _$_ ; _∘_ ; id )
open import Level           using ( _⊔_ ; suc ; Level )

open import Axiom.Extensionality.Propositional     using () renaming ( Extensionality to funext )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; module ≡-Reasoning ; cong )

open import Overture        using ( _≈_ ; _⁻¹ ; Op )
open import Base.Functions  using ( A×A→B-to-Fin2A→B ; UncurryFin2 ; UncurryFin3 )

private variable  ι α β 𝓥 ρ : Level

welldef : {A : Type α}{I : Type 𝓥}(f : Op A I) → ∀ u v → u ≡ v → f u ≡ f v
welldef f u v = cong f

swelldef : ∀ ι α → Type (suc (α ⊔ ι))
swelldef ι α =  ∀ {I : Type ι}{A : Type α}(f : Op A I)(u v : I → A)
 →              u ≈ v → f u ≡ f v

funext→swelldef : {α 𝓥 : Level} → funext 𝓥 α → swelldef 𝓥 α
funext→swelldef fe f u v ptweq = welldef f u v (fe ptweq)

SwellDef : Typeω
SwellDef = (α β : Level) → swelldef α β

swelldef' : ∀ ι α β → Type (suc (ι ⊔ α ⊔ β))
swelldef' ι α β =  ∀ {I : Type ι} {A : Type α} {B : Type β}
 →                 (f : (I → A) → B) {u v : I → A} → u ≈ v → f u ≡ f v

funext' : ∀ α β → Type (suc (α ⊔ β))
funext' α β = ∀ {A : Type α } {B : Type β } {f g : A → B} → f ≈ g → f ≡ g

funext'→swelldef' : funext' ι α → swelldef' ι α β
funext'→swelldef' fe f ptweq = cong f (fe ptweq)

swelldef'→funext' : swelldef' ι α (ι ⊔ α) → funext' ι α
swelldef'→funext' wd ptweq = wd _$_ ptweq

module _ {A : Type α}{B : Type β} where
 open Fin renaming ( zero to z ; suc to s )
 open ≡-Reasoning

 A×A-wd :  (f : A × A → B)(u v : Fin 2 → A)
  →        u ≈ v → (A×A→B-to-Fin2A→B f) u ≡ (A×A→B-to-Fin2A→B f) v

 A×A-wd f u v u≈v = Goal
  where
  zip1 : ∀ {a x y} → x ≡ y → f (a , x) ≡ f (a , y)
  zip1 refl = refl

  zip2 : ∀ {x y b} → x ≡ y → f (x , b) ≡ f (y , b)
  zip2 refl = refl

  Goal : (A×A→B-to-Fin2A→B f) u ≡ (A×A→B-to-Fin2A→B f) v
  Goal =  (A×A→B-to-Fin2A→B f) u  ≡⟨ refl ⟩
          f (u z , u (s z))       ≡⟨ zip1 (u≈v (s z)) ⟩
          f (u z , v (s z))       ≡⟨ zip2 (u≈v z) ⟩
          f (v z , v (s z))       ≡⟨ refl ⟩
          (A×A→B-to-Fin2A→B f) v  ∎

 Fin2-wd :  (f : A → A → B)(u v : Fin 2 → A)
  →         u ≈ v → (UncurryFin2 f) u ≡ (UncurryFin2 f) v

 Fin2-wd f u v u≈v = Goal
  where
  zip1 : ∀ {a x y} → x ≡ y → f a x ≡ f a y
  zip1 refl = refl

  zip2 : ∀ {x y b} → x ≡ y → f x b ≡ f y b
  zip2 refl = refl

  Goal : (UncurryFin2 f) u ≡ (UncurryFin2 f) v
  Goal = (UncurryFin2 f) u  ≡⟨ refl ⟩
         f (u z) (u (s z))  ≡⟨ zip1 (u≈v (s z)) ⟩
         f (u z) (v (s z))  ≡⟨ zip2 (u≈v z) ⟩
         f (v z) (v (s z))  ≡⟨ refl ⟩
         (UncurryFin2 f) v  ∎

 Fin3-wd :  (f : A → A → A → B)(u v : Fin 3 → A)
  →         u ≈ v → (UncurryFin3 f) u ≡ (UncurryFin3 f) v

 Fin3-wd f u v u≈v = Goal
  where
  zip1 : ∀ {a b x y} → x ≡ y → f a b x ≡ f a b y
  zip1 refl = refl

  zip2 : ∀ {a b x y} → x ≡ y → f a x b ≡ f a y b
  zip2 refl = refl

  zip3 : ∀ {a b x y} → x ≡ y → f x a b ≡ f y a b
  zip3 refl = refl

  Goal : (UncurryFin3 f) u ≡ (UncurryFin3 f) v
  Goal = (UncurryFin3 f) u                ≡⟨ refl ⟩
         f (u z) (u (s z)) (u (s (s z)))  ≡⟨ zip1 (u≈v (s (s z))) ⟩
         f (u z) (u (s z)) (v (s (s z)))  ≡⟨ zip2 (u≈v (s z)) ⟩
         f (u z) (v (s z)) (v (s (s z)))  ≡⟨ zip3 (u≈v z) ⟩
         f (v z) (v (s z)) (v (s (s z)))  ≡⟨ refl ⟩
         (UncurryFin3 f) v                ∎

module _ {A : Type α}{B : Type β} where

 ListA→B :  (f : List A → B)(u v : List A) → u ≡ v → f u ≡ f v
 ListA→B f u .u refl = refl

 CurryListA : (List A → B) → (List A → A → B)
 CurryListA f [] a = f [ a ]
 CurryListA f (x ∷ l) a = f ((x ∷ l) ++ [ a ]) 

 CurryListA' : (List A → B) → (A → List A → B)
 CurryListA' f a [] = f [ a ]
 CurryListA' f a (x ∷ l) = f ([ a ] ++ (x ∷ l))

