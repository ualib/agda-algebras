---
layout: default
title : "Base.Overture.Surjective module"
date : "2021-01-12"
author: "the agda-algebras development team"
---

### <a id="surjective-functions">Surjective functions</a>

This is the [Base.Overture.Surjective][] module of the [agda-algebras][] library.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}
module Base.Overture.Surjective where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive   using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Relation.Nullary using ( Dec ; yes ; no )
open import Data.Empty       using (⊥-elim)
open import Function         using ( Surjective ; _∘_ )
open import Relation.Binary  using ( Decidable )
open import Data.Product     using ( _,_ ; Σ ; Σ-syntax )
                             renaming ( proj₁ to fst ; proj₂ to snd )
open import Axiom.UniquenessOfIdentityProofs using ( module Decidable⇒UIP )
open import Relation.Binary.PropositionalEquality
                             using ( _≡_ ; sym ; cong-app ; cong ; refl )


-- Imports from agda-algebras -----------------------------------------------------
open import Base.Overture.Preliminaries using ( _≈_ ; _∙_ ; transport )
open import Base.Overture.Inverses      using ( Image_∋_ ; eq ; Inv ; InvIsInverseʳ )

private variable α β γ c ι : Level

\end{code}

#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

\begin{code}

module _ {A : Type α}{B : Type β} where
 IsSurjective : (A → B) →  Type (α ⊔ β)
 IsSurjective f = ∀ y → Image f ∋ y

 onto : Type (α ⊔ β)
 onto = Σ (A → B) IsSurjective

 IsSurjective→Surjective : (f : A → B) → IsSurjective f → Surjective{A = A} _≡_ _≡_ f
 IsSurjective→Surjective f fE y = imgfy→A (fE y)
  where
  imgfy→A : Image f ∋ y → Σ[ a ∈ A ] f a ≡ y
  imgfy→A (eq a p) = a , sym p

 Surjective→IsSurjective : (f : A → B) → Surjective{A = A} _≡_ _≡_ f → IsSurjective f
 Surjective→IsSurjective f fE y = eq (fst (fE y)) (sym (snd(fE y)))

\end{code}

With the next definition, we can represent a *right-inverse* of a surjective function.

\begin{code}

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

\end{code}
Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Next we prove that this does indeed give the right-inverse.
\begin{code}

module _ {A : Type α}{B : Type β} where

 SurjInvIsInverseʳ : (f : A → B)(fE : IsSurjective f) → ∀ b → f ((SurjInv f fE) b) ≡ b
 SurjInvIsInverseʳ f fE b = InvIsInverseʳ (fE b)

 -- composition law for epics
 epic-factor : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →            f ≈ h ∘ g → IsSurjective f → IsSurjective h

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

 epic-factor-intensional : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →                        f ≡ h ∘ g → IsSurjective f → IsSurjective h

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

\end{code}

Later we will need the fact that the projection of an arbitrary product onto one (or any number) of its factors is surjective.

\begin{code}

module _ {I : Set ι}(_≟_ : Decidable{A = I} _≡_)
         {B : I → Set β}
         (bs₀ : ∀ i → (B i))
 where
 open Decidable⇒UIP _≟_ using ( ≡-irrelevant )

 proj : (j : I) → (∀ i → (B i)) → (B j)
 proj j xs = xs j

 update : (∀ i → B i) → ((j , _) : Σ I B) → (∀ i → Dec (i ≡ j) → B i)
 update _  (_ , b) i (yes x) = transport B (sym x) b
 update bs  _      i (no  _) = bs i

 update-id : ∀{j b} → (c : Dec (j ≡ j)) → update bs₀ (j , b) j c ≡ b
 update-id {j}{b}(yes p) = cong (λ x → transport B x b)(≡-irrelevant (sym p) refl)
 update-id       (no ¬p) = ⊥-elim (¬p refl)

 proj-is-onto : ∀{j} → Surjective{A = ∀ i → (B i)} _≡_ _≡_ (proj j)
 proj-is-onto {j} b = bs , pf
  where
  bs : (i : I) → B i
  bs i = update bs₀ (j , b) i (i ≟ j)

  pf : proj j bs ≡ b
  pf = update-id (j ≟ j)

 projIsOnto : ∀{j} → IsSurjective (proj j)
 projIsOnto {j} = Surjective→IsSurjective (proj j) proj-is-onto

\end{code}


--------------------------------------

<span style="float:left;">[← Base.Overture.Injective](Base.Overture.Injective.html)</span>
<span style="float:right;">[Base.Overture.Transformers →](Base.Overture.Transformers.html)</span>

{% include UALib.Links.md %}


