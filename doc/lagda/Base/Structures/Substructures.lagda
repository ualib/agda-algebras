---
layout: default
title : "Base.Structures.Substructures module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="types-for-substructures-of-general-mathematical-structures">Types for Substructures of General Structures</a>

This is the [Base.Structures.Substructures][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Substructures where

-- Imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₂ to snd )
open import Function         using ( _∘_ )
open import Level            using ( _⊔_ ; suc ; Level )
open import Relation.Binary  using ( REL )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; ⋂ )
open import Relation.Binary.PropositionalEquality
                             using ( _≡_ ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library -------------------------------------
open import Overture         using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Functions   using ( IsInjective )
open import Base.Relations   using ( Im_⊆_ ; PredType )
open import Base.Equality    using ( swelldef )
open import Base.Terms       using ( Term ) -- ; _⟦_⟧ )

open import Base.Structures.Basic  using ( signature ; structure ; _ᵒ_ ; sigl )
                                   using ( siglˡ ; siglʳ )
open import Base.Structures.Homs   using ( hom )
open import Base.Structures.Terms  using ( _⟦_⟧ )

open structure ; open signature

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ ρ α ρᵃ β ρᵇ γ ρᶜ χ ι : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁

module _ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}} {X : Type χ} where

 Subuniverses : Pred (Pred (carrier 𝑨) ρ) (sigl 𝐹 ⊔ α ⊔ ρ)
 Subuniverses B = ∀ f a → Im a ⊆ B → (f ᵒ 𝑨) a ∈ B

 -- Subuniverses as a record type
 record Subuniverse : Type (sigl 𝐹 ⊔ α ⊔ suc ρ) where
  constructor mksub
  field
   sset  : Pred (carrier 𝑨) ρ
   isSub : sset ∈ Subuniverses

 -- Subuniverse Generation
 data Sg (G : Pred (carrier 𝑨) ρ) : Pred (carrier 𝑨) (sigl 𝐹 ⊔ α ⊔ ρ) where
  var : ∀ {v} → v ∈ G → v ∈ Sg G
  app : ∀ f a → Im a ⊆ Sg G → (f ᵒ 𝑨) a ∈ Sg G

\end{code}

(The inferred types in the `app` constructor are `f : ∣ 𝑆 ∣` and `a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.)

Given an arbitrary subset `X` of the domain `∣ 𝑨 ∣` of an `𝑆`-algebra `𝑨`, the type `Sg X` does indeed represent a subuniverse of `𝑨`. Proving this using the inductive type `Sg` is trivial, as we see here.

\begin{code}

 sgIsSub : {G : Pred (carrier 𝑨) ρ} → Sg G ∈ Subuniverses
 sgIsSub = app

\end{code}

Next we prove by structural induction that `Sg X` is the smallest subuniverse of `𝑨` containing `X`.

\begin{code}

 sgIsSmallest :  {G : Pred (carrier 𝑨) ρ}(B : Pred (carrier 𝑨) ρᵇ)
  →              B ∈ Subuniverses  →  G ⊆ B  →  Sg G ⊆ B

 sgIsSmallest _ _ G⊆B (var Gx) = G⊆B Gx
 sgIsSmallest B B≤A G⊆B {.((f ᵒ 𝑨) a)} (app f a SgGa) = Goal
  where
  IH : Im a ⊆ B
  IH i = sgIsSmallest B B≤A G⊆B (SgGa i)

  Goal : (f ᵒ 𝑨) a ∈ B
  Goal = B≤A f a IH

\end{code}

When the element of `Sg G` is constructed as `app f a SgGa`, we may assume (the induction hypothesis) that the arguments in the tuple `a` belong to `B`. Then the result of applying `f` to `a` also belongs to `B` since `B` is a subuniverse.

\begin{code}

 ⋂s :  (I : Type ι){𝒜 : I → Pred (carrier 𝑨) ρ}
  →    (∀ i → 𝒜 i ∈ Subuniverses) → ⋂ I 𝒜 ∈ Subuniverses

 ⋂s I σ f a ν = λ i → σ i f a (λ x → ν x i)

\end{code}

In the proof above, we assume the following typing judgments:

```
ν    : Im a ⊆ ⋂ I 𝒜
a    : arity 𝐹 f → carrier 𝑨
f    : symbol 𝐹
σ    : (i : I) → 𝒜 i ∈ Subuniverses
𝒜    : I → Pred (carrier 𝑨) ρ   (not in scope)
```
and we must prove `(f ᵒ 𝑨) a ∈ ⋂ I 𝒜`.   Agda can fill in the proof term
`λ i → σ i f a (λ x → ν x i)` automatically using `C-c C-a`.

\begin{code}

 open Term
 -- subuniverses are closed under the action of term operations
 sub-term-closed :  (B : Pred (carrier 𝑨) ρ) → (B ∈ Subuniverses)
  →                 (t : Term X)(b : X → (carrier 𝑨))
  →                 (Im b ⊆ B) → (𝑨 ⟦ t ⟧) b ∈ B

 sub-term-closed _ _ (ℊ x) b Bb = Bb x

 sub-term-closed B B≤A (node f t) b ν =
  B≤A f (λ z → (𝑨 ⟦ t z ⟧) b) (λ x → sub-term-closed B B≤A (t x) b ν)

\end{code}

In the induction step of the foregoing proof, the typing judgments of the premise are the following:

```
ν    : Im b ⊆ B
b    : X → carrier 𝑨
t    : arity 𝐹 f → Term X
f    : symbol 𝐹
B≤A  : B ∈ Subuniverses
B    : Pred (carrier 𝑨) ρ
𝑨    : structure 𝐹 𝑅
```
and the given proof term establishes the goal `op 𝑨 f (λ i → (𝑨 ⟦ t i ⟧) b) ∈ B`

Alternatively, we could express the preceeding fact using an inductive type representing images of terms.

\begin{code}

 data TermImage (B : Pred (carrier 𝑨) ρ) : Pred (carrier 𝑨) (sigl 𝐹 ⊔ α ⊔ ρ)
  where
  var : ∀ {b : carrier 𝑨} → b ∈ B → b ∈ TermImage B
  app : ∀ f ts → ((i : (arity 𝐹) f) → ts i ∈ TermImage B)  → (f ᵒ 𝑨) ts ∈ TermImage B

 -- `TermImage B` is a subuniverse of 𝑨 that contains B.
 TermImageIsSub : {B : Pred (carrier 𝑨) ρ} → TermImage B ∈ Subuniverses
 TermImageIsSub = app

 B-onlyif-TermImageB : {B : Pred (carrier 𝑨) ρ} → B ⊆ TermImage B
 B-onlyif-TermImageB Ba = var Ba

 -- Since `Sg B` is the smallest subuniverse containing B, we obtain the following inclusion.
 SgB-onlyif-TermImageB : (B : Pred (carrier 𝑨) ρ) → Sg B ⊆ TermImage B
 SgB-onlyif-TermImageB B = sgIsSmallest  (TermImage B)
                                         TermImageIsSub B-onlyif-TermImageB

 module _ {𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}} where
  private
   A = carrier 𝑨
   B = carrier 𝑩

  -- Homomorphisms are uniquely determined by their values on a generating set.
  hom-unique :  swelldef (siglʳ 𝐹) β → (G : Pred A ρ)  (g h : hom 𝑨 𝑩)
   →            ((x : A) → (x ∈ G → ∣ g ∣ x ≡ ∣ h ∣ x))
                -------------------------------------------------
   →            (a : A) → (a ∈ Sg G → ∣ g ∣ a ≡ ∣ h ∣ a)

  hom-unique _ G g h σ a (var Ga) = σ a Ga
  hom-unique wd G g h σ .((f ᵒ 𝑨) a) (app f a SgGa) = Goal
   where
   IH : ∀ x → ∣ g ∣ (a x) ≡ ∣ h ∣ (a x)
   IH x = hom-unique wd G g h σ (a x) (SgGa x)
   open ≡-Reasoning
   Goal : ∣ g ∣ ((f ᵒ 𝑨) a) ≡ ∣ h ∣ ((f ᵒ 𝑨) a)
   Goal =  ∣ g ∣ ((f ᵒ 𝑨) a)    ≡⟨ snd ∥ g ∥ f a ⟩
           (f ᵒ 𝑩)(∣ g ∣ ∘ a )  ≡⟨ wd (f ᵒ 𝑩) (∣ g ∣ ∘ a) (∣ h ∣ ∘ a) IH ⟩
           (f ᵒ 𝑩)(∣ h ∣ ∘ a)   ≡⟨ (snd ∥ h ∥ f a)⁻¹ ⟩
           ∣ h ∣ ((f ᵒ 𝑨) a )   ∎

\end{code}

In the induction step, the following typing judgments are assumed:

```
SgGa : Im a ⊆ Sg G
a    : arity 𝐹 f → carrier 𝑨
f    : symbol 𝐹
σ    : (x : A) → x ∈ G → ∣ g ∣ x ≡ ∣ h ∣ x
h    : hom 𝑨 𝑩
g    : hom 𝑨 𝑩
G    : Pred A ρ
wd   : swelldef (siglʳ 𝐹) β
𝑩    : structure 𝐹 𝑅
```

and, under these assumptions, we proved `∣ g ∣ ((f ᵒ 𝑨) a) ≡ ∣ h ∣ ((f ᵒ 𝑨) a)`.

#### <a id="substructures">Substructures</a>


\begin{code}

_≥_  -- (alias for supstructure (aka parent structure; aka overstructure))
 _IsSupstructureOf_ :  structure 𝐹 𝑅 {α}{ρᵃ} → structure 𝐹 𝑅 {β}{ρᵇ}
  →                    Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)

𝑨 IsSupstructureOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣


_≤_  -- (alias for subalgebra relation))
 _IsSubstructureOf_ :  structure 𝐹 𝑅 {α}{ρᵃ} → structure 𝐹 𝑅 {β}{ρᵇ}
  →                    Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ )

𝑨 IsSubstructureOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

-- Syntactic sugar for sup/sub-algebra relations.
𝑨 ≥ 𝑩 = 𝑨 IsSupstructureOf 𝑩
𝑨 ≤ 𝑩 = 𝑨 IsSubstructureOf 𝑩


record SubstructureOf : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ suc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)) where
 field
  struc       : structure 𝐹 𝑅 {α}{ρᵃ}
  substruc    : structure 𝐹 𝑅 {β}{ρᵇ}
  issubstruc  : substruc ≤ struc



module _ {𝐹 : signature 𝓞₀ 𝓥₀}{𝑅 : signature 𝓞₁ 𝓥₁} where

 Substructure :  structure 𝐹 𝑅 {α}{ρᵃ} → {β ρᵇ : Level}
  →              Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ suc (β ⊔ ρᵇ))

 Substructure 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (structure 𝐹 𝑅 {β}{ρᵇ}) ] 𝑩 ≤ 𝑨

 {- For 𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}, inhabitant of `Substructure 𝑨` is
    a pair `(𝑩 , p) : Substructure 𝑨`  providing
    + a structure, `𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}`, and
    + a proof, `p : 𝑩 ≤ 𝑨`, that 𝑩 is a substructure of 𝐴. -}


 IsSubstructureREL :  ∀ {α}{ρᵃ}{β}{ρᵇ}
  →                   REL (structure 𝐹 𝑅 {α}{ρᵃ})(structure 𝐹 𝑅 {β}{ρᵇ}) ρ
  →                   Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ suc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ))

 IsSubstructureREL {α = α}{ρᵃ}{β}{ρᵇ} R = ∀  {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}}
                                             {𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}} → 𝑨 ≤ 𝑩

\end{code}

From now on we will use `𝑩 ≤ 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.

#### Substructures of a class of algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubstructureOfClass 𝒦`.

\begin{code}

 _≤c_  -- (alias for substructure-of-class relation)
  _IsSubstructureOfClass_ :  structure 𝐹 𝑅 {β}{ρᵇ} → Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   →                         Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ suc (α ⊔ ρᵃ) ⊔ β ⊔ ρᵇ ⊔ ρ)

 𝑩 IsSubstructureOfClass 𝒦 = Σ[ 𝑨 ∈ PredType 𝒦 ] ((𝑨 ∈ 𝒦) × (𝑩 ≤ 𝑨))

 𝑩 ≤c 𝒦 = 𝑩 IsSubstructureOfClass 𝒦

 record SubstructureOfClass : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ suc (α ⊔ ρ ⊔ β ⊔ ρᵇ ⊔ ρᵃ)) where
  field
   class : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   substruc : structure 𝐹 𝑅 {β}{ρᵇ}
   issubstrucofclass : substruc ≤c class


 record SubstructureOfClass' : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ suc (α ⊔ ρ ⊔ β ⊔ ρᵇ ⊔ ρᵃ)) where
  field
   class : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   classalgebra    : structure 𝐹 𝑅 {α}{ρᵃ}
   isclassalgebra  : classalgebra ∈ class
   subalgebra      : structure 𝐹 𝑅 {β}{ρᵇ}
   issubalgebra    : subalgebra ≤ classalgebra

 -- The collection of subalgebras of algebras in class 𝒦.
 SubstructuresOfClass :  Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ → {β ρᵇ : Level}
  →                      Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ suc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) ⊔ ρ)

 SubstructuresOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ structure 𝐹 𝑅 {β}{ρᵇ} ] 𝑩 ≤c 𝒦
\end{code}

--------------------------------

<span style="float:left;">[← Base.Structures.Terms](Base.Structures.Terms.html)</span>
<span style="float:right;">[Base.Structures.EquationalLogic →](Base.Structures.EquationalLogic.html)</span>

{% include UALib.Links.md %}
