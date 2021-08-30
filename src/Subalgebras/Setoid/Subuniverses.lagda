---
layout: default
title : "Subalgebras.Setoid.Subuniverses module (The Agda Universal Algebra Library)"
date : "2021-07-11"
author: "agda-algebras development team"
---

#### <a id="subuniverses-of-setoid-algebras">Subuniverses of setoid algebras</a>

This is the [Subalgebras.Setoid.Subuniverses][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Setoid.Subuniverses {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -----------------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; Σ ; _×_ )
open import Function.Base    using ( _∘_ ; id )
open import Function.Bundles using ( Func ; Injection )
open import Relation.Binary  using ( Setoid ; REL )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; ⋂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Overture.Inverses                  using ( ∘-injective ; IsInjective ; id-is-injective )
open import Relations.Discrete                 using ( Im_⊆_ )
open import Foundations.Welldefined            using ( swelldef )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; _̂_ ; Lift-Alg )
open import Algebras.Products          {𝑆 = 𝑆} using ( ov )
open import Terms.Basic                {𝑆 = 𝑆} using ( Term ; ℊ ; node )
open import Terms.Setoid.Basic         {𝑆 = 𝑆} using ( module Environment )
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; ∘-hom )
open import Homomorphisms.Setoid.Isomorphisms
                                       {𝑆 = 𝑆} using ( _≅_ ;  ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅
                                                     ; ≅toInjective ; ≅fromInjective )

private variable ρ : Level

\end{code}

We first show how to represent in [Agda][] the collection of subuniverses of an algebra `𝑨`.  Since a subuniverse is viewed as a subset of the domain of `𝑨`, we define it as a predicate on `∣ 𝑨 ∣`.  Thus, the collection of subuniverses is a predicate on predicates on `∣ 𝑨 ∣`.

\begin{code}

module _ {α ρᵃ : Level}  (𝑨 : SetoidAlgebra α ρᵃ) where
 private
  A = 𝕌[ 𝑨 ] -- (𝕌 = forgetful functor)

 Subuniverses : Pred (Pred A ρ) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)

 Subuniverses B = ∀ f a → Im a ⊆ B → (f ̂ 𝑨) a ∈ B

 -- Subuniverses as a record type
 record Subuniverse : Type(ov (α ⊔ ρ)) where
  constructor mksub
  field       sset  : Pred A ρ
              isSub : sset ∈ Subuniverses


 -- Subuniverse Generation
 data Sg (G : Pred A ρ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) where
  var : ∀ {v} → v ∈ G → v ∈ Sg G
  app : ∀ f a → Im a ⊆ Sg G → (f ̂ 𝑨) a ∈ Sg G

\end{code}

(The inferred types in the `app` constructor are `f : ∣ 𝑆 ∣` and `a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.)

Given an arbitrary subset `X` of the domain `∣ 𝑨 ∣` of an `𝑆`-algebra `𝑨`, the type `Sg X` does indeed represent a subuniverse of `𝑨`. Proving this using the inductive type `Sg` is trivial, as we see here.

\begin{code}

 sgIsSub : {G : Pred A ρ} → Sg G ∈ Subuniverses
 sgIsSub = app

\end{code}

Next we prove by structural induction that `Sg X` is the smallest subuniverse of `𝑨` containing `X`.

\begin{code}

 sgIsSmallest : {ρᵍ ρᵇ : Level}{G : Pred A ρᵍ}(B : Pred A ρᵇ)
  →             B ∈ Subuniverses  →  G ⊆ B  →  Sg G ⊆ B

 sgIsSmallest _ _ G⊆B (var Gx) = G⊆B Gx
 sgIsSmallest B B≤A G⊆B {.((f ̂ 𝑨) a)} (app f a SgGa) = Goal
  where
  IH : Im a ⊆ B
  IH i = sgIsSmallest B B≤A G⊆B (SgGa i)

  Goal : (f ̂ 𝑨) a ∈ B
  Goal = B≤A f a IH

\end{code}

When the element of `Sg G` is constructed as `app f a SgGa`, we may assume (the induction hypothesis) that the arguments in the tuple `a` belong to `B`. Then the result of applying `f` to `a` also belongs to `B` since `B` is a subuniverse.


\begin{code}

module _ {α ρᵃ : Level}  {𝑨 : SetoidAlgebra α ρᵃ} where
 private
  A = 𝕌[ 𝑨 ]

 ⋂s : {ι : Level}(I : Type ι){ρ : Level}{𝒜 : I → Pred A ρ}
  →   (∀ i → 𝒜 i ∈ Subuniverses 𝑨) → ⋂ I 𝒜 ∈ Subuniverses 𝑨

 ⋂s I σ f a ν = λ i → σ i f a (λ x → ν x i)

\end{code}

In the proof above, we assume the following typing judgments:

```
ν  : Im a ⊆ ⋂ I 𝒜
a  : ∥ 𝑆 ∥ f → Subalgebras.Setoid.A 𝑨
f  : ∣ 𝑆 ∣
σ  : (i : I) → 𝒜 i ∈ Subuniverses 𝑨
```
and we must prove `(f ̂ 𝑨) a ∈ ⋂ I 𝒜`.  When we did this with the old
Algebra type, Agda could fill in the proof term `λ i → σ i f a (λ x → ν x i)`
automatically using `C-c C-a`, but this doesn't work for SetoidAlgebra
as we've implemented it.  We get the error "Agsy does not support copatterns
yet."  We should fix the implementation to resolve this.

\begin{code}

module _ {χ : Level}{X : Type χ}
         {α ρᵃ : Level}{𝑨 : SetoidAlgebra α ρᵃ}
         where

 private A = 𝕌[ 𝑨 ]
 open Setoid
 open Environment 𝑨
 open Func renaming ( f to _<$>_ )

 -- subuniverses are closed under the action of term operations
 sub-term-closed : (B : Pred A ρ)
  →                (B ∈ Subuniverses 𝑨)
  →                (t : Term X)
  →                (b : Carrier (Env X))
  →                (∀ x → (b x ∈ B)) → (⟦ t ⟧ <$> b) ∈ B

 sub-term-closed _ _ (ℊ x) b Bb = Bb x

 sub-term-closed B B≤A (node f t)b ν =
  B≤A f  (λ z → ⟦ t z ⟧ <$> b) λ x → sub-term-closed B B≤A (t x) b ν

\end{code}

In the induction step of the foregoing proof, the typing judgments of the premise are the following:

```
ν  : (x : X) → b x ∈ B
b  : Setoid.Carrier (Env X)
t  : ∥ 𝑆 ∥ f → Term X
f  : ∣ 𝑆 ∣
σ  : B ∈ Subuniverses 𝑨
B  : Pred A ρ
ρ  : Level
𝑨  : SetoidAlgebra α ρᵃ
```
and the given proof term establishes the goal `⟦ node f t ⟧ <$> b ∈ B`.

Alternatively, we could express the preceeding fact using an inductive type representing images of terms.

\begin{code}

 data TermImage (B : Pred A ρ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  where
  var : ∀ {b : A} → b ∈ B → b ∈ TermImage B
  app : ∀ f ts →  ((i : ∥ 𝑆 ∥ f) → ts i ∈ TermImage B)  → (f ̂ 𝑨) ts ∈ TermImage B

 -- `TermImage B` is a subuniverse of 𝑨 that contains B.
 TermImageIsSub : {B : Pred A ρ} → TermImage B ∈ Subuniverses 𝑨
 TermImageIsSub = app

 B-onlyif-TermImageB : {B : Pred A ρ} → B ⊆ TermImage B
 B-onlyif-TermImageB Ba = var Ba

 -- Since `Sg B` is the smallest subuniverse containing B, we obtain the following inclusion.
 SgB-onlyif-TermImageB : (B : Pred A ρ) → Sg 𝑨 B ⊆ TermImage B
 SgB-onlyif-TermImageB B = sgIsSmallest 𝑨 (TermImage B) TermImageIsSub B-onlyif-TermImageB

 module _ {β ρᵇ : Level}{𝑩 : SetoidAlgebra β ρᵇ} where

  private B = 𝕌[ 𝑩 ]
  open Environment 𝑩

  -- Homomorphisms are uniquely determined by their values on a generating set.
  hom-unique : swelldef 𝓥 β → (G : Pred A ρ)  (g h : hom 𝑨 𝑩)
   →           ((x : A) → (x ∈ G → ∣ g ∣ x ≡ ∣ h ∣ x))
               -------------------------------------------------
   →           (a : A) → (a ∈ Sg 𝑨 G → ∣ g ∣ a ≡ ∣ h ∣ a)

  hom-unique _ G g h σ a (var Ga) = σ a Ga
  hom-unique wd G g h σ .((f ̂ 𝑨) a) (app f a SgGa) = Goal
   where
   IH : ∀ x → ∣ g ∣ (a x) ≡ ∣ h ∣ (a x)
   IH x = hom-unique wd G g h σ (a x) (SgGa x)
   open ≡-Reasoning
   Goal : ∣ g ∣ ((f ̂ 𝑨) a) ≡ ∣ h ∣ ((f ̂ 𝑨) a)
   Goal = ∣ g ∣ ((f ̂ 𝑨) a) ≡⟨ ∥ g ∥ f a ⟩
          (f ̂ 𝑩)(∣ g ∣ ∘ a ) ≡⟨ wd (f ̂ 𝑩) (∣ g ∣ ∘ a) (∣ h ∣ ∘ a) IH ⟩
          (f ̂ 𝑩)(∣ h ∣ ∘ a)  ≡⟨ ( ∥ h ∥ f a )⁻¹ ⟩
          ∣ h ∣ ((f ̂ 𝑨) a )  ∎

\end{code}

In the induction step, the following typing judgments are assumed:
```
SgGa : Im a ⊆ Sg 𝑨 G
a    : ∥ 𝑆 ∥ f → Subalgebras.Setoid.A 𝑨
f    : ∣ 𝑆 ∣
σ    : (x : A) → x ∈ G → ∣ g ∣ x ≡ ∣ h ∣ x
h    : hom 𝑨 𝑩
g    : hom 𝑨 𝑩
G    : Pred A ρ
wd   : swelldef 𝓥 β
𝑩    : SetoidAlgebra β ρᵇ
```
and, under these assumptions, we proved `∣ g ∣ ((f ̂ 𝑨) a) ≡ ∣ h ∣ ((f ̂ 𝑨) a)`.

---------------------------------

<span style="float:left;">[↑ Subalgebras.Setoid](Subalgebras.Setoid.html)</span>
<span style="float:right;">[Subalgebras.Setoid.Subalgebras →](Subalgebras.Setoid.Subalgebras.html)</span>

{% include UALib.Links.md %}
