
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras.Subuniverses {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function         using ( _∘_ ; Func )
open import Level            using ( Level ;  _⊔_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; ⋂ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality using ( refl )

open import Overture        using ( ∣_∣ ; ∥_∥ )
open import Base.Relations  using ( Im_⊆_ )

open import Base.Terms            {𝑆 = 𝑆} using ( Term ; ℊ ; node )
open import Setoid.Algebras       {𝑆 = 𝑆} using ( Algebra ; 𝕌[_] ; _̂_ ; ov )
open import Setoid.Terms          {𝑆 = 𝑆} using ( module Environment )
open import Setoid.Homomorphisms  {𝑆 = 𝑆} using ( hom ; IsHom )

private variable
 α β γ ρᵃ ρᵇ ρᶜ ℓ χ : Level
 X : Type χ

module _ (𝑨 : Algebra α ρᵃ) where
 private A = 𝕌[ 𝑨 ] -- the forgetful functor

 Subuniverses : Pred (Pred A ℓ) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ℓ )
 Subuniverses B = ∀ f a → Im a ⊆ B → (f ̂ 𝑨) a ∈ B

 record Subuniverse : Type(ov (α ⊔ ℓ)) where
  constructor mksub
  field
   sset  : Pred A ℓ
   isSub : sset ∈ Subuniverses

 data Sg (G : Pred A ℓ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ℓ) where
  var : ∀ {v} → v ∈ G → v ∈ Sg G
  app : ∀ f a → Im a ⊆ Sg G → (f ̂ 𝑨) a ∈ Sg G

 sgIsSub : {G : Pred A ℓ} → Sg G ∈ Subuniverses
 sgIsSub = app

 sgIsSmallest :  {G : Pred A ρᵃ}(B : Pred A ρᵇ)
  →              B ∈ Subuniverses  →  G ⊆ B  →  Sg G ⊆ B

 sgIsSmallest _ _ G⊆B (var Gx) = G⊆B Gx
 sgIsSmallest B B≤A G⊆B {.((f ̂ 𝑨) a)} (app f a SgGa) = Goal
  where
  IH : Im a ⊆ B
  IH i = sgIsSmallest B B≤A G⊆B (SgGa i)

  Goal : (f ̂ 𝑨) a ∈ B
  Goal = B≤A f a IH

module _ {𝑨 : Algebra α ρᵃ} where
 private A = 𝕌[ 𝑨 ]

 ⋂s :  {ι : Level}(I : Type ι){ρ : Level}{𝒜 : I → Pred A ρ}
  →    (∀ i → 𝒜 i ∈ Subuniverses 𝑨) → ⋂ I 𝒜 ∈ Subuniverses 𝑨

 ⋂s I σ f a ν = λ i → σ i f a (λ x → ν x i)

module _ {𝑨 : Algebra α ρᵃ} where
 private A = 𝕌[ 𝑨 ]
 open Setoid using ( Carrier )
 open Environment 𝑨
 open Func renaming ( to to _⟨$⟩_ )

 sub-term-closed :  (B : Pred A ℓ)
  →                 (B ∈ Subuniverses 𝑨)
  →                 (t : Term X)
  →                 (b : Carrier (Env X))
  →                 (∀ x → (b x ∈ B)) → (⟦ t ⟧ ⟨$⟩ b) ∈ B

 sub-term-closed _ _ (ℊ x) b Bb = Bb x
 sub-term-closed B B≤A (node f t)b ν =
  B≤A f  (λ z → ⟦ t z ⟧ ⟨$⟩ b) λ x → sub-term-closed B B≤A (t x) b ν

 data TermImage (B : Pred A ρᵃ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ) where
  var : ∀ {b : A} → b ∈ B → b ∈ TermImage B
  app : ∀ f ts →  ((i : ∥ 𝑆 ∥ f) → ts i ∈ TermImage B)  → (f ̂ 𝑨) ts ∈ TermImage B

 TermImageIsSub : {B : Pred A ρᵃ} → TermImage B ∈ Subuniverses 𝑨
 TermImageIsSub = app

 B-onlyif-TermImageB : {B : Pred A ρᵃ} → B ⊆ TermImage B
 B-onlyif-TermImageB Ba = var Ba

 SgB-onlyif-TermImageB : (B : Pred A ρᵃ) → Sg 𝑨 B ⊆ TermImage B
 SgB-onlyif-TermImageB B = sgIsSmallest 𝑨 (TermImage B) TermImageIsSub B-onlyif-TermImageB

 module _ {𝑩 : Algebra β ρᵇ} (gh hh : hom 𝑨 𝑩) where
  open Algebra 𝑩  using ( Interp )  renaming ( Domain to B )
  open Setoid B   using ( _≈_ ; sym )
  open Func       using ( cong )    renaming ( to to _⟨$⟩_ )
  open SetoidReasoning B

  private
   g = _⟨$⟩_ ∣ gh ∣
   h = _⟨$⟩_ ∣ hh ∣

  open IsHom
  open Environment 𝑩

  hom-unique :  (G : Pred A ℓ) → ((x : A) → (x ∈ G → g x ≈ h x))
   →            (a : A) → (a ∈ Sg 𝑨 G → g a ≈ h a)

  hom-unique G σ a (var Ga) = σ a Ga
  hom-unique G σ .((f ̂ 𝑨) a) (app f a SgGa) = Goal
   where
   IH : ∀ i → h (a i) ≈ g (a i)
   IH i = sym (hom-unique G σ (a i) (SgGa i))

   Goal : g ((f ̂ 𝑨) a) ≈ h ((f ̂ 𝑨) a)
   Goal =  begin
           g ((f ̂ 𝑨) a)   ≈⟨ compatible ∥ gh ∥ ⟩
           (f ̂ 𝑩)(g ∘ a ) ≈˘⟨ cong Interp (refl , IH) ⟩
           (f ̂ 𝑩)(h ∘ a)  ≈˘⟨ compatible ∥ hh ∥ ⟩
           h ((f ̂ 𝑨) a )  ∎

