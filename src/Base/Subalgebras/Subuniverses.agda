
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Subalgebras.Subuniverses {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive       using () renaming ( Set to Type )
open import Function             using ( _∘_ )
open import Level                using ( Level ; _⊔_ )
open import Relation.Unary       using ( Pred ; _∈_ ; _⊆_ ; ⋂ )
open import Axiom.Extensionality.Propositional
                                 using () renaming ( Extensionality to funext )
open import Relation.Binary.PropositionalEquality
                                 using ( module ≡-Reasoning ; _≡_ )

open import Overture                     using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Relations               using ( Im_⊆_ )
open import Base.Equality                using ( swelldef )
open import Base.Algebras       {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; ov )
open import Base.Homomorphisms  {𝑆 = 𝑆}  using ( hom )
open import Base.Terms          {𝑆 = 𝑆}  using ( Term ; ℊ ; node ; _⟦_⟧ )

private variable α β 𝓧 : Level

Subuniverses : (𝑨 : Algebra α) → Pred (Pred ∣ 𝑨 ∣ β) (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

record Subuniverse {𝑨 : Algebra α} : Type(ov β ⊔ α) where
 constructor mksub
 field
  sset  : Pred ∣ 𝑨 ∣ β
  sSub : sset ∈ Subuniverses 𝑨

data Sg (𝑨 : Algebra α)(X : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 where
 var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
 app : ∀ f a → Im a ⊆ Sg 𝑨 X → (f ̂ 𝑨) a ∈ Sg 𝑨 X

sgIsSub : {𝑨 : Algebra α}{X : Pred ∣ 𝑨 ∣ β} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub = app

sgIsSmallest :  {𝓡 : Level}(𝑨 : Algebra α){X : Pred ∣ 𝑨 ∣ β}(Y : Pred ∣ 𝑨 ∣ 𝓡)
 →              Y ∈ Subuniverses 𝑨  →  X ⊆ Y  →  Sg 𝑨 X ⊆ Y

sgIsSmallest _ _ _ XinY (var Xv) = XinY Xv
sgIsSmallest 𝑨 Y YsubA XinY (app f a SgXa) = Yfa
 where
 IH : Im a ⊆ Y
 IH i = sgIsSmallest 𝑨 Y YsubA XinY (SgXa i)

 Yfa : (f ̂ 𝑨) a ∈ Y
 Yfa = YsubA f a IH

⋂s :  {𝓘 : Level}{𝑨 : Algebra α}{I : Type 𝓘}{𝒜 : I → Pred ∣ 𝑨 ∣ β}
 →    (∀ i → 𝒜 i ∈ Subuniverses 𝑨) → ⋂ I 𝒜 ∈ Subuniverses 𝑨

⋂s σ f a ν = λ i → σ i f a (λ x → ν x i)

sub-term-closed :  {𝓧 : Level}{X : Type 𝓧}(𝑨 : Algebra α){B : Pred ∣ 𝑨 ∣ β}
 →                 (B ∈ Subuniverses 𝑨) → (t : Term X)(b : X → ∣ 𝑨 ∣)
 →                 ((x : X) → (b x ∈ B)) → (𝑨 ⟦ t ⟧)b ∈ B

sub-term-closed 𝑨 AB (ℊ x) b Bb = Bb x

sub-term-closed 𝑨{B} σ (node f t)b ν =
 σ f  (λ z → (𝑨 ⟦ t z ⟧) b) λ x → sub-term-closed 𝑨{B} σ (t x) b ν

data TermImage (𝑨 : Algebra α)(Y : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 where
 var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
 app : ∀ 𝑓 𝑡 →  ((x : ∥ 𝑆 ∥ 𝑓) → 𝑡 x ∈ TermImage 𝑨 Y)  → (𝑓 ̂ 𝑨) 𝑡 ∈ TermImage 𝑨 Y

TermImageIsSub : {𝑨 : Algebra α}{Y : Pred ∣ 𝑨 ∣ β} → TermImage 𝑨 Y ∈ Subuniverses 𝑨
TermImageIsSub = app

Y-onlyif-TermImageY : {𝑨 : Algebra α}{Y : Pred ∣ 𝑨 ∣ β} → Y ⊆ TermImage 𝑨 Y
Y-onlyif-TermImageY {a} Ya = var Ya

SgY-onlyif-TermImageY : (𝑨 : Algebra α)(Y : Pred ∣ 𝑨 ∣ β) → Sg 𝑨 Y ⊆ TermImage 𝑨 Y
SgY-onlyif-TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y-onlyif-TermImageY

open ≡-Reasoning

hom-unique :  swelldef 𝓥 β → {𝑨 : Algebra α}{𝑩 : Algebra β}
              (X : Pred ∣ 𝑨 ∣ α)  (g h : hom 𝑨 𝑩)
 →            ((x : ∣ 𝑨 ∣) → (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x))
 →            (a : ∣ 𝑨 ∣) → (a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

hom-unique _ _ _ _ σ a (var x) = σ a x

hom-unique wd {𝑨}{𝑩} X g h σ fa (app 𝑓 a ν) = Goal
 where
 IH : ∀ x → ∣ g ∣ (a x) ≡ ∣ h ∣ (a x)
 IH x = hom-unique wd{𝑨}{𝑩} X g h σ (a x) (ν x)

 Goal : ∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)
 Goal =  ∣ g ∣ ((𝑓 ̂ 𝑨) a)    ≡⟨ ∥ g ∥ 𝑓 a ⟩
         (𝑓 ̂ 𝑩)(∣ g ∣ ∘ a )  ≡⟨ wd (𝑓 ̂ 𝑩) (∣ g ∣ ∘ a) (∣ h ∣ ∘ a) IH ⟩
         (𝑓 ̂ 𝑩)(∣ h ∣ ∘ a)   ≡⟨ ( ∥ h ∥ 𝑓 a )⁻¹ ⟩
         ∣ h ∣ ((𝑓 ̂ 𝑨) a )   ∎

