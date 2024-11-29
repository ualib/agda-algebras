
{-# OPTIONS --without-K --exact-split --safe #-}
module Base.Functions.Surjective where

open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Empty        using (⊥-elim)
open import Function          using ( StrictlySurjective ; Surjective ; _∘_ ; _$_ )
open import Level             using ( _⊔_ ; Level )
open import Relation.Binary   using ( Decidable )
open import Relation.Nullary  using ( Dec ; yes ; no )
open import Data.Product      using ( _,_ ; Σ ; Σ-syntax )
                              renaming ( proj₁ to fst ; proj₂ to snd )
open import Axiom.UniquenessOfIdentityProofs
                              using ( module Decidable⇒UIP )
open import Relation.Binary.PropositionalEquality
                              using ( _≡_ ; sym ; cong-app ; cong ; refl ; trans)

open import Overture.Basic     using ( _≈_ ; _∙_ ; transport )
open import Base.Functions.Inverses  using ( Image_∋_ ; eq ; Inv ; InvIsInverseʳ )
open import Relation.Binary.Core using (Rel)

private variable a b c ι : Level

module _ {A : Type a}{B : Type b} where

 IsSurjective : (A → B) →  Type _
 IsSurjective f = ∀ y → Image f ∋ y

 onto : Type _
 onto = Σ (A → B) IsSurjective

 IsSurjective→Surjective :  (f : A → B) → IsSurjective f
  →                         Surjective _≡_ _≡_ f

 IsSurjective→Surjective f fE y = Goal   -- `fE y` is a proof of `Image f ∋ y `
  where
  imgfy→A : Image f ∋ y → Σ[ x ∈ A ] f x ≡ y
  imgfy→A (eq x p) = x , sym p
  Goal : Σ[ x ∈ A ] ({z : A} → z ≡ x → f z ≡ y)
  Goal = fst (imgfy→A $ fE y) , λ z≡fst → trans (cong f z≡fst) $ snd (imgfy→A $ fE y)

 Surjective→IsSurjective :  (f : A → B) → Surjective{A = A} _≡_ _≡_ f
  →                         IsSurjective f

 Surjective→IsSurjective f fE y = eq (fst $ fE y) (sym $ snd (fE y) refl)

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE = Inv f ∘ fE

module _ {A : Type a}{B : Type b} where

 SurjInvIsInverseʳ :  (f : A → B)(fE : IsSurjective f)
  →                   ∀ b → f ((SurjInv f fE) b) ≡ b

 SurjInvIsInverseʳ f fE b = InvIsInverseʳ (fE b)

 epic-factor :  {C : Type c}(f : A → B)(g : A → C)(h : C → B)
  →             f ≈ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : y ≡ f (finv y)
   ζ = sym (SurjInvIsInverseʳ f fe y)

   η : y ≡ (h ∘ g) (finv y)
   η = ζ ∙ compId (finv y)

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) η

 epic-factor-intensional :  {C : Type c}(f : A → B)(g : A → C)(h : C → B)
  →                         f ≡ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor-intensional f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : f (finv y) ≡ y
   ζ = SurjInvIsInverseʳ f fe y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (sym compId)(finv y)) ∙ ζ

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) (sym η)

module _  {I : Set ι}(_≟_ : Decidable{A = I} _≡_)
          {B : I → Set b}
          (bs₀ : ∀ i → (B i))
 where
 open Decidable⇒UIP _≟_ using ( ≡-irrelevant )

 proj : (j : I) → (∀ i → (B i)) → (B j)
 proj j xs = xs j

 update : (∀ i → B i) → ((j , _) : Σ I B) → (∀ i → Dec (i ≡ j) → B i)
 update _   (_ , b)  i (yes x) = transport B (sym x) b
 update bs  _        i (no  _) = bs i

 update-id : ∀{j b} → (c : Dec (j ≡ j)) → update bs₀ (j , b) j c ≡ b
 update-id {j}{b}  (yes p) = cong (λ x → transport B x b)(≡-irrelevant (sym p) refl)
 update-id         (no ¬p) = ⊥-elim (¬p refl)

 proj-is-onto : ∀{j} → Surjective{A = ∀ i → (B i)} _≡_ _≡_ (proj j)
 proj-is-onto {j} b = bs , λ x → trans (cong (λ u → proj j u) x) pf
  where
  bs : (i : I) → B i
  bs i = update bs₀ (j , b) i (i ≟ j)

  pf : proj j bs ≡ b
  pf = update-id (j ≟ j)

 projIsOnto : ∀{j} → IsSurjective (proj j)
 projIsOnto {j} = Surjective→IsSurjective (proj j) proj-is-onto

