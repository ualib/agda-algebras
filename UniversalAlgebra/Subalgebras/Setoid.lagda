---
layout: default
title : Subalgebras.Setoid module (The Agda Universal Algebra Library)
date : 2021-07-11
author: [agda-algebras development team][]
---

### Subuniverses of Setoid Algebras

This is the [Subalgebras.Setoid][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Setoid {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ ; lsuc ; Level )
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
open import Function.Base           using    ( _∘_ ; id )
open import Function.Bundles        using    ( Func ; Injection )
open import Relation.Binary         using    ( Setoid ; REL )
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ⋂ )
import Relation.Binary.PropositionalEquality as PE

-- -- -- imports from agda-algebras ------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Overture.Inverses            using ( ∘-injective ; IsInjective ; id-is-injective )
open import Relations.Discrete           using ( Im_⊆_ )
open import Relations.Extensionality     using ( swelldef )
open import Algebras.Setoid      {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; _̂_ ; Lift-SetoidAlg )
open import Products.Basic       {𝑆 = 𝑆} using ( ov )
open import Terms.Basic          {𝑆 = 𝑆} using ( Term ; ℊ ; node )
open import Terms.Setoid         {𝑆 = 𝑆} using ( module Environment )
open import Homomorphisms.Setoid {𝑆 = 𝑆} using ( hom ; ∘-hom )
open import Isomorphisms.Setoid  {𝑆 = 𝑆} using ( _≅_ ;  ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅
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


\end{code}

#### Subuniverse Generation

\begin{code}

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
   open PE.≡-Reasoning
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

#### Subalgebras of SetoidAlgebras

\begin{code}
module _ where

 private variable
  α ρᵃ β ρᵇ : Level

 _≥s_  -- (alias for supalgebra (aka overalgebra))
  _IsSupalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
 𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

 _≤s_  -- (alias for subalgebra relation))
  _IsSubalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
 𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

 -- Syntactic sugar for sup/sub-algebra relations.
 𝑨 ≥s 𝑩 = 𝑨 IsSupalgebraOf 𝑩
 𝑨 ≤s 𝑩 = 𝑨 IsSubalgebraOf 𝑩

 open _≅_
 ≅→≤s : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≤s 𝑩
 ≅→≤s φ = (to φ) , ≅toInjective φ

 ≅→≥s : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≥s 𝑩
 ≅→≥s φ = (from φ) , ≅fromInjective φ

 record SubalgebraOf : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ)) where
  field
   algebra : SetoidAlgebra α ρᵃ
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebra : subalgebra ≤s algebra


 Subalgebra : SetoidAlgebra α ρᵃ → {β ρᵇ : Level} → Type _
 Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (SetoidAlgebra β ρᵇ) ] 𝑩 ≤s 𝑨

 -- usage note: for 𝑨 : SetoidAlgebra α ρᵃ, inhabitant of `Subalgebra 𝑨` is a pair
 --             `(𝑩 , p) : Subalgebra 𝑨`  providing
 --                                       - `𝑩 : SetoidAlgebra β ρᵇ` and
 --                                       - `p : 𝑩 ≤s 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴.


 IsSubalgebraREL : {α ρᵃ β ρᵇ : Level} → REL (SetoidAlgebra α ρᵃ)(SetoidAlgebra β ρᵇ) ρ → Type _
 IsSubalgebraREL {α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≤s 𝑩

 record SubalgebraREL(R : REL (SetoidAlgebra β ρᵇ)(SetoidAlgebra α ρᵃ) ρ) : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field isSubalgebraREL : IsSubalgebraREL R


\end{code}

From now on we will use `𝑩 ≤s 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.


#### Subalgebras of a class of algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : SetoidAlgebra β ρᵇ` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

\begin{code}

module _ where

 private variable
  α ρᵃ β ρᵇ : Level

 _≤c_
  _IsSubalgebraOfClass_ : SetoidAlgebra β ρᵇ → Pred (SetoidAlgebra α ρᵃ) ρ → Type _
 𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ SetoidAlgebra _ _ ] ((𝑨 ∈ 𝒦) × (𝑩 ≤s 𝑨))

 𝑩 ≤c 𝒦 = 𝑩 IsSubalgebraOfClass 𝒦

 record SubalgebraOfClass : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field
   class : Pred (SetoidAlgebra α ρᵃ) ρ
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebraofclass : subalgebra ≤c class


 record SubalgebraOfClass' : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field
   class : Pred (SetoidAlgebra α ρᵃ) ρ
   classalgebra : SetoidAlgebra α ρᵃ
   isclassalgebra : classalgebra ∈ class
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebra : subalgebra ≤s classalgebra

 -- The collection of subalgebras of algebras in class 𝒦.
 SubalgebrasOfClass : Pred (SetoidAlgebra α ρᵃ) ρ → {β ρᵇ : Level} → Type _
 SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 ≤c 𝒦

\end{code}


#### Subalgebra lemmas

The subalgebra relation is a *preorder*; i.e., it is a reflexive, transitive binary relation.

\begin{code}


private variable α ρᵃ β ρᵇ γ ρᶜ : Level

≤s-refl : {𝑨 𝑩 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≤s 𝑩
≤s-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤s A≅B

≥s-refl : {𝑨 𝑩 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≥s 𝑩
≥s-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤s (≅-sym A≅B)

≤s-refl' : {𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≤s 𝑨
≤s-refl' {𝑨 = 𝑨} = (id , λ f a → refl) , Injection.injective id-is-injective


≤s-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
  →        𝑨 ≤s 𝑩 → 𝑩 ≤s 𝑪 → 𝑨 ≤s 𝑪

≤s-trans 𝑨 {𝑩} 𝑪 A≤B B≤C = (∘-hom 𝑨 𝑩 𝑪 ∣ A≤B ∣ ∣ B≤C ∣ ) , Goal
 where
 Goal : IsInjective ∣ (∘-hom 𝑨 𝑩 𝑪 ∣ A≤B ∣ ∣ B≤C ∣) ∣
 Goal = ∘-injective ∥ A≤B ∥ ∥ B≤C ∥

≥s-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
  →        𝑨 ≥s 𝑩 → 𝑩 ≥s 𝑪 → 𝑨 ≥s 𝑪
≥s-trans 𝑨 {𝑩} 𝑪 A≥B B≥C = ≤s-trans 𝑪 {𝑩} 𝑨 B≥C A≥B


module _ {α ρᵃ ρ : Level} where

 open import Relation.Binary.Structures {a = ov(α ⊔ ρᵃ)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α)} (_≅_ {α}{ρᵃ}{α}{ρᵃ})

 open IsPreorder
 ≤s-preorder : IsPreorder _≤s_
 isEquivalence ≤s-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≤s-preorder = ≤s-refl
 trans ≤s-preorder {𝑨}{𝑩}{𝑪} A≤B B≤C = ≤s-trans 𝑨 {𝑩} 𝑪 A≤B B≤C



open _≅_

module _ (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ) where

 A≥B→B≅C→A≥C : 𝑨 ≥s 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥s 𝑪
 A≥B→B≅C→A≥C A≥B B≅C  = ≥s-trans 𝑨 {𝑩} 𝑪 A≥B (≅→≥s B≅C)

 A≤B→B≅C→A≤C : 𝑨 ≤s 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤s 𝑪
 A≤B→B≅C→A≤C A≤B B≅C = ≤s-trans 𝑨{𝑩} 𝑪 A≤B (≅→≤s B≅C)

 A≅B→B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥s 𝑪 → 𝑨 ≥s 𝑪

 A≅B→B≥C→A≥C A≅B B≥C = ≥s-trans 𝑨{𝑩}𝑪 (≅→≥s A≅B) B≥C

 A≅B→B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤s 𝑪 → 𝑨 ≤s 𝑪
 A≅B→B≤C→A≤C A≅B B≤C = ≤s-trans 𝑨{𝑩}𝑪 (≅→≤s A≅B) B≤C


≤s-TRANS-≅ : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
 →          𝑨 ≤s 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤s 𝑪
≤s-TRANS-≅ 𝑨 {𝑩} 𝑪 (h , hinj) B≅C = (∘-hom 𝑨 𝑩 𝑪 h (to B≅C)) , ∘-injective hinj (≅toInjective B≅C)

≤s-mono : (𝑩 : SetoidAlgebra β ρᵇ){𝒦 𝒦' : Pred (SetoidAlgebra α ρᵃ) γ}
 →        𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

≤s-mono 𝑩 KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)

\end{code}


#### Lifts of subalgebras

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρᵃ)(ov α)}{𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} where

 Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-SetoidAlg 𝑩 ℓ) IsSubalgebraOfClass 𝒦
 Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B→B≅C→A≥C 𝑨 (Lift-SetoidAlg 𝑩 ℓ) B≤A Lift-≅)

≤s-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≤s 𝑩 → 𝑨 ≤s Lift-SetoidAlg 𝑩 ℓ
≤s-Lift 𝑨 {𝑩}{ℓ} A≤sB = A≤B→B≅C→A≤C 𝑨 (Lift-SetoidAlg 𝑩 ℓ) A≤sB Lift-≅

≥s-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≥s 𝑩 → 𝑨 ≥s Lift-SetoidAlg 𝑩 ℓ
≥s-Lift 𝑨 {𝑩}{ℓ} A≥sB = A≥B→B≅C→A≥C 𝑨 (Lift-SetoidAlg 𝑩 ℓ) A≥sB Lift-≅

Lift-≤s-Lift : {𝑨 : SetoidAlgebra α ρᵃ}(ℓᵃ : Level){𝑩 : SetoidAlgebra β ρᵇ}(ℓᵇ : Level)
 →             𝑨 ≤s 𝑩 → Lift-SetoidAlg 𝑨 ℓᵃ ≤s Lift-SetoidAlg 𝑩 ℓᵇ
Lift-≤s-Lift {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ A≤sB = ≥s-Lift (Lift-SetoidAlg 𝑩 ℓᵇ){𝑨} (≤s-Lift 𝑨{𝑩} A≤sB)

\end{code}


------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


