---
layout: default
title : "Base.Subalgebras.Subuniverses module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

### <a id="subuniverses">Subuniverses</a>

This is the [Base.Subalgebras.Subuniverses][] module of the [Agda Universal Algebra Library][].

We start by defining a type that represents the important concept of *subuniverse*. Suppose `𝑨` is an algebra.  A subset `B ⊆ ∣ 𝑨 ∣` is said to be *closed under the operations of* `𝑨` if for each `𝑓 ∈ ∣ 𝑆 ∣` and all tuples `𝒃 : ∥ 𝑆 ∥ 𝑓 → 𝐵` the element `(𝑓 ̂ 𝑨) 𝒃` belongs to `B`. If a subset `B ⊆ 𝐴` is closed under the operations of `𝑨`, then we call B a *subuniverse* of `𝑨`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Base.Subalgebras.Subuniverses {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive                         using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Axiom.Extensionality.Propositional     using () renaming (Extensionality to funext)
open import Function.Base                          using ( _∘_ )
open import Relation.Binary.PropositionalEquality  using ( module ≡-Reasoning ; _≡_ )
open import Relation.Unary                         using ( Pred ; _∈_ ; _⊆_ ; ⋂ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Base.Overture.Preliminaries            using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Relations.Discrete                using ( Im_⊆_ )
open import Base.Equality.Welldefined              using ( swelldef )
open import Base.Algebras.Basic                    using ( Algebra ; _̂_ )
open import Base.Algebras.Products        {𝑆 = 𝑆}  using ( ov )
open import Base.Terms.Basic              {𝑆 = 𝑆}  using ( Term ; ℊ ; node )
open import Base.Terms.Operations         {𝑆 = 𝑆}  using ( _⟦_⟧ )
open import Base.Homomorphisms.Basic      {𝑆 = 𝑆}  using ( hom )

private variable α β 𝓧 : Level

\end{code}

We first show how to represent in [Agda][] the collection of subuniverses of an algebra `𝑨`.  Since a subuniverse is viewed as a subset of the domain of `𝑨`, we define it as a predicate on `∣ 𝑨 ∣`.  Thus, the collection of subuniverses is a predicate on predicates on `∣ 𝑨 ∣`.

\begin{code}

Subuniverses : (𝑨 : Algebra α 𝑆) → Pred (Pred ∣ 𝑨 ∣ β) (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)

Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

\end{code}



#### <a id="subuniverses-as-records">Subuniverses as records</a>

Next we define a type to represent a single subuniverse of an algebra. If `𝑨` is the algebra in question, then a subuniverse of `𝑨` is a subset of (i.e., predicate over) the domain `∣ 𝑨 ∣` that belongs to `Subuniverses 𝑨`.

\begin{code}

record Subuniverse {𝑨 : Algebra α 𝑆} : Type(ov β ⊔ α) where
 constructor mksub
 field       sset  : Pred ∣ 𝑨 ∣ β
             isSub : sset ∈ Subuniverses 𝑨

\end{code}


#### <a id="subuniverse-generation">Subuniverse Generation</a>

If `𝑨` is an algebra and `X ⊆ ∣ 𝑨 ∣` a subset of the domain of `𝑨`, then the *subuniverse of* `𝑨` *generated by* `X` is typically denoted by `Sg`<sup>`𝑨`</sup>`(X)` and defined to be the smallest subuniverse of `𝑨` containing `X`.  Equivalently,

`Sg`<sup>`𝑨`</sup>`(X)`  =  `⋂` { `U` : `U` is a subuniverse of `𝑨` and  `B ⊆ U` }.

We define an inductive type, denoted by `Sg`, that represents the subuniverse generated by a given subset of the domain of a given algebra, as follows.

\begin{code}

data Sg (𝑨 : Algebra α 𝑆)(X : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 where
 var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
 app : ∀ f a → Im a ⊆ Sg 𝑨 X → (f ̂ 𝑨) a ∈ Sg 𝑨 X

\end{code}

(The inferred types in the `app` constructor are `f : ∣ 𝑆 ∣` and `a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.)

Given an arbitrary subset `X` of the domain `∣ 𝑨 ∣` of an `𝑆`-algebra `𝑨`, the type `Sg X` does indeed represent a subuniverse of `𝑨`. Proving this using the inductive type `Sg` is trivial, as we see here.

\begin{code}

sgIsSub : {𝑨 : Algebra α 𝑆}{X : Pred ∣ 𝑨 ∣ β} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub = app

\end{code}

Next we prove by structural induction that `Sg X` is the smallest subuniverse of `𝑨` containing `X`.

\begin{code}

sgIsSmallest : {𝓡 : Level}(𝑨 : Algebra α 𝑆){X : Pred ∣ 𝑨 ∣ β}(Y : Pred ∣ 𝑨 ∣ 𝓡)
 →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y  →  Sg 𝑨 X ⊆ Y

sgIsSmallest _ _ _ XinY (var Xv) = XinY Xv
sgIsSmallest 𝑨 Y YsubA XinY (app f a SgXa) = Yfa
 where
 IH : Im a ⊆ Y
 IH i = sgIsSmallest 𝑨 Y YsubA XinY (SgXa i)

 Yfa : (f ̂ 𝑨) a ∈ Y
 Yfa = YsubA f a IH

\end{code}

When the element of `Sg X` is constructed as `app f a SgXa`, we may assume (the induction hypothesis) that the arguments in the tuple `a` belong to `Y`. Then the result of applying `f` to `a` also belongs to `Y` since `Y` is a subuniverse.



#### <a id="subuniverse-lemmas">Subuniverse Lemmas</a>

Here we formalize a few basic properties of subuniverses. First, the intersection of subuniverses is again a subuniverse.

\begin{code}

⋂s : {𝓘 : Level}{𝑨 : Algebra α 𝑆}{I : Type 𝓘}{𝒜 : I → Pred ∣ 𝑨 ∣ β}
 →   (∀ i → 𝒜 i ∈ Subuniverses 𝑨) → ⋂ I 𝒜 ∈ Subuniverses 𝑨

⋂s σ f a ν = λ i → σ i f a (λ x → ν x i)

\end{code}

In the proof above, we assume the following typing judgments:

```
 σ : ∀ i → 𝒜 i ∈ Subuniverses 𝑨
 f : ∣ 𝑆 ∣
 a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
 ν : Im 𝑎 ⊆ ⋂ I 𝒜
```
and we must prove `(f ̂ 𝑨) a ∈ ⋂ I 𝒜`. In this case, Agda will fill in the proof term `λ i → σ i f a (λ x → ν x i)` automatically with the command `C-c C-a`.

Next, subuniverses are closed under the action of term operations.

\begin{code}

sub-term-closed : {𝓧 : Level}{X : Type 𝓧}(𝑨 : Algebra α 𝑆){B : Pred ∣ 𝑨 ∣ β}
 →                (B ∈ Subuniverses 𝑨) → (t : Term X)(b : X → ∣ 𝑨 ∣)
 →                ((x : X) → (b x ∈ B)) → (𝑨 ⟦ t ⟧)b ∈ B

sub-term-closed 𝑨 AB (ℊ x) b Bb = Bb x

sub-term-closed 𝑨{B} σ (node f t)b ν =
  σ f  (λ z → (𝑨 ⟦ t z ⟧) b) λ x → sub-term-closed 𝑨{B} σ (t x) b ν

\end{code}

In the induction step of the foregoing proof, the typing judgments of the premise are the following:

```
𝑨   : Algebra α 𝑆
B   : Pred ∣ 𝑨 ∣ β
σ   : B ∈ Subuniverses 𝑨
f   : ∣ 𝑆 ∣
t   : ∥ 𝑆 ∥ 𝑓 → Term X
b   : X → ∣ 𝑨 ∣
ν   : ∀ x → b x ∈ B
```
and the given proof term establishes the goal `𝑨 ⟦ node f t ⟧ b ∈ B`.

Alternatively, we could express the preceeding fact using an inductive type representing images of terms.

\begin{code}

data TermImage (𝑨 : Algebra α 𝑆)(Y : Pred ∣ 𝑨 ∣ β) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 where
 var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
 app : ∀ 𝑓 𝑡 →  ((x : ∥ 𝑆 ∥ 𝑓) → 𝑡 x ∈ TermImage 𝑨 Y)  → (𝑓 ̂ 𝑨) 𝑡 ∈ TermImage 𝑨 Y

\end{code}

By what we proved above, it should come as no surprise that `TermImage 𝑨 Y` is a subuniverse of `𝑨` that contains `Y`.

\begin{code}

TermImageIsSub : {𝑨 : Algebra α 𝑆}{Y : Pred ∣ 𝑨 ∣ β} → TermImage 𝑨 Y ∈ Subuniverses 𝑨
TermImageIsSub = app

Y-onlyif-TermImageY : {𝑨 : Algebra α 𝑆}{Y : Pred ∣ 𝑨 ∣ β} → Y ⊆ TermImage 𝑨 Y
Y-onlyif-TermImageY {a} Ya = var Ya

\end{code}

Since `Sg 𝑨 Y` is the smallest subuniverse containing Y, we obtain the following inclusion.

\begin{code}

SgY-onlyif-TermImageY : (𝑨 : Algebra α 𝑆)(Y : Pred ∣ 𝑨 ∣ β) → Sg 𝑨 Y ⊆ TermImage 𝑨 Y
SgY-onlyif-TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y-onlyif-TermImageY

\end{code}



Next we prove the important fact that homomorphisms are uniquely determined by their values on a generating set.

\begin{code}

open ≡-Reasoning

hom-unique : swelldef 𝓥 β → {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
             (X : Pred ∣ 𝑨 ∣ α)  (g h : hom 𝑨 𝑩)
 →           ((x : ∣ 𝑨 ∣) → (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x))
             -------------------------------------------------
 →           (a : ∣ 𝑨 ∣) → (a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

hom-unique _ _ _ _ σ a (var x) = σ a x

hom-unique wd {𝑨}{𝑩} X g h σ fa (app 𝑓 a ν) = Goal
 where
 IH : ∀ x → ∣ g ∣ (a x) ≡ ∣ h ∣ (a x)
 IH x = hom-unique wd{𝑨}{𝑩} X g h σ (a x) (ν x)

 Goal : ∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)
 Goal = ∣ g ∣ ((𝑓 ̂ 𝑨) a)   ≡⟨ ∥ g ∥ 𝑓 a ⟩
        (𝑓 ̂ 𝑩)(∣ g ∣ ∘ a ) ≡⟨ wd (𝑓 ̂ 𝑩) (∣ g ∣ ∘ a) (∣ h ∣ ∘ a) IH ⟩
        (𝑓 ̂ 𝑩)(∣ h ∣ ∘ a)  ≡⟨ ( ∥ h ∥ 𝑓 a )⁻¹ ⟩
        ∣ h ∣ ((𝑓 ̂ 𝑨) a )  ∎

\end{code}

In the induction step, the following typing judgments are assumed:

```
wd  : swelldef 𝓥 β
𝑨   : Algebra α 𝑆
𝑩   : Algebra β 𝑆
X   : Pred ∣ 𝑨 ∣ α
g h  : hom 𝑨 𝑩
σ   : Π x ꞉ ∣ 𝑨 ∣ , (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x)
fa  : ∣ 𝑨 ∣
fa  = (𝑓 ̂ 𝑨) a
𝑓   : ∣ 𝑆 ∣
a   : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
ν   : Im a ⊆ Sg 𝑨 X
```

and, under these assumptions, we proved `∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)`.

---------------------------------

<span style="float:left;">[↑ Subalgebras](Base.Subalgebras.html)</span>
<span style="float:right;">[Base.Subalgebras.Subalgebras →](Base.Subalgebras.Base.Subalgebras.html)</span>

{% include UALib.Links.md %}
