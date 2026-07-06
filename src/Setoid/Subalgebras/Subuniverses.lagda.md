---
layout: default
title : "Setoid.Subalgebras.Subuniverses module (The Agda Universal Algebra Library)"
date : "2021-07-11"
author: "agda-algebras development team"
---

#### Subuniverses of setoid algebras

This is the [Setoid.Subalgebras.Subuniverses][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras.Subuniverses {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function         using ( _∘_ ; Func )
open import Level            using ( Level ;  _⊔_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; ⋂ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------------
open import Overture                       using ( proj₁ ; proj₂ ; ArityOf ; Im_⊆_ )
open import Overture.Terms        {𝑆 = 𝑆}  using ( Term ; ℊ ; node )
open import Setoid.Algebras       {𝑆 = 𝑆}  using ( Algebra ; 𝕌[_] ; _^_ ; ov )
open import Setoid.Terms          {𝑆 = 𝑆}  using ( module Environment )
open import Setoid.Homomorphisms  {𝑆 = 𝑆}  using ( hom ; IsHom )

private variable
  α β γ ρᵃ ρᵇ ρᶜ ℓ χ : Level
  X : Type χ
```


We first show how to represent in [Agda][] the collection of subuniverses of an
algebra `𝑨`.  Since a subuniverse is viewed as a subset of the domain of `𝑨`, we
define it as a predicate on `𝕌[ 𝑨 ]`.  Thus, the collection of subuniverses is a
predicate on predicates on `𝕌[ 𝑨 ]`.


```agda
module _ (𝑨 : Algebra α ρᵃ) where
  private A = 𝕌[ 𝑨 ] -- the forgetful functor

  Subuniverses : Pred (Pred A ℓ) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ℓ )
  Subuniverses B = ∀ f a → Im a ⊆ B → (f ^ 𝑨) a ∈ B

  -- Subuniverses as a record type
  record Subuniverse : Type(ov (α ⊔ ℓ)) where
   constructor mksub
   field
    sset  : Pred A ℓ
    isSub : sset ∈ Subuniverses

  -- Subuniverse Generation
  data Sg (G : Pred A ℓ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ℓ) where
   var : ∀ {v} → v ∈ G → v ∈ Sg G
   app : ∀ f a → Im a ⊆ Sg G → (f ^ 𝑨) a ∈ Sg G
```


(The inferred types in the `app` constructor are `f : OperationSymbolsOf 𝑆` and
`a : ArityOf 𝑆 𝑓 → 𝕌[ 𝑨 ]`.)

Given an arbitrary subset `X` of the domain `𝕌[ 𝑨 ]` of an `𝑆`-algebra `𝑨`, the
type `Sg X` does indeed represent a subuniverse of `𝑨`. Proving this using the
inductive type `Sg` is trivial, as we see here.


```agda
  sgIsSub : {G : Pred A ℓ} → Sg G ∈ Subuniverses
  sgIsSub = app
```


Next we prove by structural induction that `Sg X` is the smallest subuniverse of `𝑨` containing `X`.


```agda
  sgIsSmallest :  {G : Pred A ℓ}(B : Pred A ρᵇ)
   →              B ∈ Subuniverses  →  G ⊆ B  →  Sg G ⊆ B

  sgIsSmallest _ _ G⊆B (var Gx) = G⊆B Gx
  sgIsSmallest B B≤A G⊆B {.((f ^ 𝑨) a)} (app f a SgGa) = Goal
   where
   IH : Im a ⊆ B
   IH i = sgIsSmallest B B≤A G⊆B (SgGa i)

   Goal : (f ^ 𝑨) a ∈ B
   Goal = B≤A f a IH
```


When the element of `Sg G` is constructed as `app f a SgGa`, we may assume (the induction hypothesis) that the arguments in the tuple `a` belong to `B`. Then the result of applying `f` to `a` also belongs to `B` since `B` is a subuniverse.


```agda
module _ {𝑨 : Algebra α ρᵃ} where
  private A = 𝕌[ 𝑨 ]

  ⋂s :  {ι : Level}(I : Type ι){ρ : Level}{𝒜 : I → Pred A ρ}
   →    (∀ i → 𝒜 i ∈ Subuniverses 𝑨) → ⋂ I 𝒜 ∈ Subuniverses 𝑨

  ⋂s I σ f a ν = λ i → σ i f a (λ x → ν x i)
```


In the proof above, we assume the following typing judgments:


    ν  : Im a ⊆ ⋂ I 𝒜
    a  : ArityOf 𝑆 f → Setoid.Subalgebras.A 𝑨
    f  : OperationSymbolsOf 𝑆
    σ  : (i : I) → 𝒜 i ∈ Subuniverses 𝑨

and we must prove `(f ^ 𝑨) a ∈ ⋂ I 𝒜`.  (The command `C-c C-a` works in this case;
Agda fills in the proof term `λ i → σ i f a (λ x → ν x i)` automatically.)


```agda
module _ {𝑨 : Algebra α ρᵃ} where
  private A = 𝕌[ 𝑨 ]
  open Setoid using ( Carrier )
  open Environment 𝑨
  open Func renaming ( to to _⟨$⟩_ )

  -- subuniverses are closed under the action of term operations
  sub-term-closed :  (B : Pred A ℓ)
   →                 (B ∈ Subuniverses 𝑨)
   →                 (t : Term X)
   →                 (b : Carrier (Env X))
   →                 (∀ x → b x ∈ B) → ⟦ t ⟧ ⟨$⟩ b ∈ B

  sub-term-closed _ _ (ℊ x) b Bb = Bb x
  sub-term-closed B B≤A (node f t)b ν =
   B≤A f  (λ z → ⟦ t z ⟧ ⟨$⟩ b) λ x → sub-term-closed B B≤A (t x) b ν
```


In the induction step of the foregoing proof, the typing judgments of the premise are the following:

    ν  : (x : X) → b x ∈ B
    b  : Setoid.Carrier (Env X)
    t  : ArityOf 𝑆 f → Term X
    f  : OperationSymbolsOf 𝑆
    σ  : B ∈ Subuniverses 𝑨
    B  : Pred A ρ
    ρ  : Level
    𝑨  : Algebra α ρᵃ

and the given proof term establishes the goal `⟦ node f t ⟧ ⟨$⟩ b ∈ B`.

Alternatively, we could express the preceeding fact using an inductive type representing images of terms.


```agda
  data TermImage (B : Pred A ρᵃ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ) where
   var : ∀ {b : A} → b ∈ B → b ∈ TermImage B
   app : ∀ f ts →  ((i : ArityOf 𝑆 f) → ts i ∈ TermImage B)  → (f ^ 𝑨) ts ∈ TermImage B

  -- `TermImage B` is a subuniverse of 𝑨 that contains B.
  TermImageIsSub : {B : Pred A ρᵃ} → TermImage B ∈ Subuniverses 𝑨
  TermImageIsSub = app

  B-onlyif-TermImageB : {B : Pred A ρᵃ} → B ⊆ TermImage B
  B-onlyif-TermImageB Ba = var Ba

  -- Since `Sg B` is the smallest subuniverse containing B, we obtain the following inclusion.
  SgB-onlyif-TermImageB : (B : Pred A ρᵃ) → Sg 𝑨 B ⊆ TermImage B
  SgB-onlyif-TermImageB B = sgIsSmallest 𝑨 (TermImage B) TermImageIsSub B-onlyif-TermImageB
```


A basic but important fact about homomorphisms is that they are uniquely determined by
the values they take on a generating set. This is the content of the next theorem, which
we call `hom-unique`.


```agda
  module _ {𝑩 : Algebra β ρᵇ} (gh hh : hom 𝑨 𝑩) where
   open Algebra 𝑩  using ( Interp )  renaming ( Domain to B )
   open Setoid B   using ( _≈_ ; sym )
   open Func       using ( cong )    renaming ( to to _⟨$⟩_ )
   open SetoidReasoning B

   private
    g = _⟨$⟩_ (proj₁ gh)
    h = _⟨$⟩_ (proj₁ hh)

   open IsHom
   open Environment 𝑩

   hom-unique :  (G : Pred A ℓ) → ((x : A) → (x ∈ G → g x ≈ h x))
    →            (a : A) → (a ∈ Sg 𝑨 G → g a ≈ h a)

   hom-unique G σ a (var Ga) = σ a Ga
   hom-unique G σ .((f ^ 𝑨) a) (app f a SgGa) = Goal
    where
    IH : ∀ i → h (a i) ≈ g (a i)
    IH i = sym (hom-unique G σ (a i) (SgGa i))

    Goal : g ((f ^ 𝑨) a) ≈ h ((f ^ 𝑨) a)
    Goal =  begin
            g ((f ^ 𝑨) a)    ≈⟨ compatible (proj₂ gh) ⟩
            (f ^ 𝑩)(g ∘ a )  ≈˘⟨ cong Interp (refl , IH) ⟩
            (f ^ 𝑩)(h ∘ a)   ≈˘⟨ compatible (proj₂ hh) ⟩
            h ((f ^ 𝑨) a )   ∎
```


In the induction step, the following typing judgments are assumed:

    SgGa : Im a ⊆ Sg 𝑨 G
    a    : ArityOf 𝑆 f → Subuniverses 𝑨
    f    : OperationSymbolsOf 𝑆
    σ    : (x : A) → x ∈ G → g x ≈ h x
    G    : Pred A ℓ
    hh   : hom 𝑨 𝑩
    gh   : hom 𝑨 𝑩

and, under these assumptions, we proved `g ((f ^ 𝑨) a) ≈ h ((f ^ 𝑨) a)`.
