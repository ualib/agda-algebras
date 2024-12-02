
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Relations.Quotients where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Level           using ( Level ; _⊔_ ; suc )
open import Relation.Binary using ( IsEquivalence ; IsPartialEquivalence) renaming ( Rel to BinRel )
open import Relation.Unary  using ( Pred ; _⊆_ )
open import Relation.Binary.PropositionalEquality as PE
                            using ( _≡_ )

open import Overture                   using ( ∣_∣ )
open import Base.Relations.Discrete    using ( ker ; 0[_] ; kerlift )
open import Base.Relations.Properties  using ( Reflexive ; Symmetric ; Transitive )

private variable a b ℓ : Level

Equivalence : Type a → {ρ : Level} → Type (a ⊔ suc ρ)
Equivalence A {ρ} = Σ[ r ∈ BinRel A ρ ] IsEquivalence r

module _ {X : Type ℓ}{ρ : Level} where

 record IsPartialEquivPred (R : Pred (X × X) ρ) : Type (ℓ ⊔ ρ) where
  field
   sym   : Symmetric R
   trans : Transitive R

 record IsEquivPred (R : Pred (X × X) ρ) : Type (ℓ ⊔ ρ) where
  field
   refl  : Reflexive R
   sym   : Symmetric R
   trans : Transitive R

  reflexive : ∀ x y → x ≡ y → R (x , y)
  reflexive x .x PE.refl = refl

open Level
ker-IsEquivalence : {A : Type a}{B : Type b}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record  { refl = PE.refl
                              ; sym = λ x → PE.sym x
                              ; trans = λ x y → PE.trans x y
                              }

kerlift-IsEquivalence :  {A : Type a}{B : Type b}(f : A → B){ρ : Level}
 →                       IsEquivalence (kerlift f ρ)

kerlift-IsEquivalence f = record  { refl = lift PE.refl
                                  ; sym = λ x → lift (PE.sym (lower x))
                                  ; trans = λ x y → lift (PE.trans (lower x) (lower y))
                                  }

[_] : {A : Type a} → A → {ρ : Level} → BinRel A ρ → Pred A ρ
[ u ]{ρ} R = R u      -- (the R-block containing u : A)

[_/_] : {A : Type a} → A → {ρ : Level} → Equivalence A {ρ} → Pred A ρ
[ u / R ] = ∣ R ∣ u

Block : {A : Type a} → A → {ρ : Level} → Equivalence A{ρ} → Pred A ρ
Block u {ρ} R = ∣ R ∣ u

infix 60 [_]

record IsBlock  {A : Type a}{ρ : Level}
                (P : Pred A ρ){R : BinRel A ρ} : Type(a ⊔ suc ρ) where
 constructor mkblk
 field
  blk : A
  P≡[blk] : P ≡ [ blk ]{ρ} R

Quotient : (A : Type a){ρ : Level} → Equivalence A{ρ} → Type(a ⊔ suc ρ)
Quotient A R = Σ[ P ∈ Pred A _ ] IsBlock P {∣ R ∣}

_/_ : (A : Type a){ρ : Level} → BinRel A ρ → Type(a ⊔ suc ρ)
A / R = Σ[ P ∈ Pred A _ ] IsBlock P {R}

infix -1 _/_

⟪_⟫ : {a : Level}{A : Type a}{ρ : Level} → A → {R : BinRel A ρ} → A / R
⟪ a ⟫{R} = [ a ] R , mkblk a PE.refl

⌞_⌟ : {a : Level}{A : Type a}{ρ : Level}{R : BinRel A ρ} → A / R  → A
⌞ _ , mkblk a _ ⌟ = a

module _  {A : Type a}
          {ρ : Level}    -- note: ρ is an implicit parameter
          {R : Equivalence A {ρ}} where

 open IsEquivalence
 []-⊆ : (x y : A) → ∣ R ∣ x y → [ x ]{ρ} ∣ R ∣ ⊆  [ y ] ∣ R ∣
 []-⊆ x y Rxy {z} Rxz = IsEquivalence.trans (snd R) (IsEquivalence.sym (snd R) Rxy) Rxz

 []-⊇ : (x y : A) → ∣ R ∣ x y → [ y ] ∣ R ∣ ⊆  [ x ] ∣ R ∣
 []-⊇ x y Rxy {z} Ryz = IsEquivalence.trans (snd R) Rxy Ryz

 ⊆-[] : (x y : A) → [ x ] ∣ R ∣ ⊆  [ y ] ∣ R ∣ → ∣ R ∣ x y
 ⊆-[] x y xy = IsEquivalence.sym (snd R) (xy (IsEquivalence.refl (snd R)))

 ⊇-[] : (x y : A) → [ y ] ∣ R ∣ ⊆  [ x ] ∣ R ∣ → ∣ R ∣ x y
 ⊇-[] x y yx = yx (IsEquivalence.refl (snd R))

0[_]IsEquivalence : (A : Type a){ρ : Level} → IsEquivalence (0[ A ] {ρ})
0[ A ]IsEquivalence {ρ} = record  { refl = lift PE.refl
                                  ; sym = λ p → lift (PE.sym (lower p))
                                  ; trans = λ p q → lift (PE.trans (lower p) (lower q))
                                  }

0[_]Equivalence : (A : Type a) {ρ : Level} → Equivalence A {a ⊔ ρ}
0[ A ]Equivalence {ρ} = 0[ A ] {ρ} , 0[ A ]IsEquivalence

⟪_∼_⟫-elim : {A : Type a} → (u v : A) → {ρ : Level}{R : Equivalence A{ρ} }
 →           ⟪ u ⟫{∣ R ∣} ≡ ⟪ v ⟫ → ∣ R ∣ u v

⟪ u ∼ .u ⟫-elim {ρ} {R} PE.refl = IsEquivalence.refl (snd R)

≡→⊆ : {A : Type a}{ρ : Level}(Q R : Pred A ρ) → Q ≡ R → Q ⊆ R
≡→⊆ Q .Q PE.refl {x} Qx = Qx

