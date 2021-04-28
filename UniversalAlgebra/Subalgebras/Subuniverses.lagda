---
layout: default
title : Subalgebras.Subuniverses module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subuniverses">Subuniverses</a>

This section presents the [Subalgebras.Subuniverses][] module of the [Agda Universal Algebra Library][].

We start by defining a type that represents the important concept of **subuniverse**. Suppose 𝑨 is an algebra.  A subset B ⊆ ∣ 𝑨 ∣ is said to be **closed under the operations of** 𝑨 if for each 𝑓 ∈ ∣ 𝑆 ∣ and all tuples 𝒃 : ∥ 𝑆 ∥ 𝑓 → 𝐵 the element (𝑓 ̂ 𝑨) 𝒃 belongs to B. If a subset B ⊆ 𝐴 is closed under the operations of 𝑨, then we call B a **subuniverse** of 𝑨.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product using (_,_; Σ; _×_)
open import Function.Base  using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Unary using (⋂; _∈_; Pred; _⊆_)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Relations.Discrete using (Im_⊆_)
open import Overture.Preliminaries
 using (Type; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _∙_;_⁻¹; ∣_∣; ∥_∥)



module Subalgebras.Subuniverses  {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Products{𝑆 = 𝑆} using (ov)
open import Homomorphisms.Basic {𝑆 = 𝑆} using (hom)
open import Terms.Basic {𝑆 = 𝑆} using (Term; ℊ; node)
open import Terms.Operations {𝑆 = 𝑆} using (_⟦_⟧)


\end{code}

We first show how to represent in [Agda][] the collection of subuniverses of an algebra `𝑨`.  Since a subuniverse is viewed as a subset of the domain of `𝑨`, we define it as a predicate on `∣ 𝑨 ∣`.  Thus, the collection of subuniverses is a predicate on predicates on `∣ 𝑨 ∣`.

\begin{code}

Subuniverses : (𝑨 : Algebra 𝓤 𝑆) → Pred (Pred ∣ 𝑨 ∣ 𝓦)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

\end{code}



#### <a id="subuniverses-as-records">Subuniverses as records</a>

Next we define a type to represent a single subuniverse of an algebra. If `𝑨` is the algebra in question, then a subuniverse of `𝑨` is a subset of (i.e., predicate over) the domain `∣ 𝑨 ∣` that belongs to `Subuniverses 𝑨`.

\begin{code}

record Subuniverse {𝑨 : Algebra 𝓤 𝑆} : Type(ov (𝓤 ⊔ 𝓦)) where
 constructor mksub
 field       sset : Pred ∣ 𝑨 ∣ 𝓦
             isSub : sset ∈ Subuniverses 𝑨

\end{code}


#### <a id="subuniverse-generation">Subuniverse Generation</a>

If `𝑨` is an algebra and `X ⊆ ∣ 𝑨 ∣` a subset of the domain of `𝑨`, then the **subuniverse of** `𝑨` **generated by** `X` is typically denoted by `Sg`<sup>`𝑨`</sup>`(X)` and defined to be the smallest subuniverse of `𝑨` containing `X`.  Equivalently,

`Sg`<sup>`𝑨`</sup>`(X)`  =  `⋂` { `U` : `U` is a subuniverse of `𝑨` and  `B ⊆ U` }.

We define an inductive type, denoted by `Sg`, that represents the subuniverse generated by a given subset of the domain of a given algebra, as follows.

\begin{code}

data Sg (𝑨 : Algebra 𝓤 𝑆)(X : Pred ∣ 𝑨 ∣ 𝓦) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤) where
 var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
 app : (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ Sg 𝑨 X → (𝑓 ̂ 𝑨) 𝑎 ∈ Sg 𝑨 X

\end{code}

Given an arbitrary subset `X` of the domain `∣ 𝑨 ∣` of an `𝑆`-algebra `𝑨`, the type `Sg X` does indeed represent a subuniverse of `𝑨`. Proving this using the inductive type `Sg` is trivial, as we see here.

\begin{code}

sgIsSub : {𝑨 : Algebra 𝓤 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓦} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub = app

\end{code}

Next we prove by structural induction that `Sg X` is the smallest subuniverse of `𝑨` containing `X`.

\begin{code}

sgIsSmallest : {𝓡 : Level}(𝑨 : Algebra 𝓤 𝑆){X : Pred ∣ 𝑨 ∣ 𝓦}(Y : Pred ∣ 𝑨 ∣ 𝓡)
 →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y  →  Sg 𝑨 X ⊆ Y

sgIsSmallest _ _ _ XinY (var Xv) = XinY Xv
sgIsSmallest 𝑨 Y YsubA XinY (app 𝑓 𝑎 SgXa) = Yfa
 where
 IH : Im 𝑎 ⊆ Y
 IH i = sgIsSmallest 𝑨 Y YsubA XinY (SgXa i)

 Yfa : (𝑓 ̂ 𝑨) 𝑎 ∈ Y
 Yfa = YsubA 𝑓 𝑎 IH

\end{code}

When the element of `Sg X` is constructed as `app 𝑓 𝑎 SgXa`, we may assume (the induction hypothesis) that the arguments in the tuple `𝑎` belong to `Y`. Then the result of applying `𝑓` to `𝑎` also belongs to `Y` since `Y` is a subuniverse.



#### <a id="subuniverse-lemmas">Subuniverse Lemmas</a>

Here we formalize a few basic properties of subuniverses. First, the intersection of subuniverses is again a subuniverse.

\begin{code}

sub-intersection : {𝓘 : Level}{𝑨 : Algebra 𝓤 𝑆}{I : Type 𝓘}{𝒜 : I → Pred ∣ 𝑨 ∣ 𝓦}
 →                 Π[ i ꞉ I ] 𝒜 i ∈ Subuniverses 𝑨
                   ----------------------------------
 →                 ⋂ I 𝒜 ∈ Subuniverses 𝑨

sub-intersection α 𝑓 𝑎 β = λ i → α i 𝑓 𝑎 (λ x → β x i)

\end{code}

In the proof above, we assume the following typing judgments:

```
 α : ∀ i → 𝒜 i ∈ Subuniverses 𝑨
 𝑓 : ∣ 𝑆 ∣
 𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
 β : Im 𝑎 ⊆ ⋂ I 𝒜
```
and we must prove `(𝑓 ̂ 𝑨) 𝑎 ∈ ⋂ I 𝒜`. In this case, Agda will fill in the proof term `λ i → α i 𝑓 𝑎 (λ x → β x i)` automatically with the command `C-c C-a`.

Next, subuniverses are closed under the action of term operations.

\begin{code}

sub-term-closed : {𝓧 : Level}{X : Type 𝓧}(𝑨 : Algebra 𝓤 𝑆){B : Pred ∣ 𝑨 ∣ 𝓦}
 →                (B ∈ Subuniverses 𝑨) → (t : Term X)(b : X → ∣ 𝑨 ∣)
 →                Π[ x ꞉ X ] (b x ∈ B)  →  (𝑨 ⟦ t ⟧)b ∈ B

sub-term-closed 𝑨 AB (ℊ x) b Bb = Bb x
sub-term-closed 𝑨{B}α(node 𝑓 𝑡)b β = α 𝑓(λ z → (𝑨 ⟦ 𝑡 z ⟧)b) λ x → sub-term-closed 𝑨{B}α(𝑡 x)b β

\end{code}

In the induction step of the foregoing proof, the typing judgments of the premise are the following:

```
𝑨   : Algebra 𝓤 𝑆
B   : Pred ∣ 𝑨 ∣ 𝓦
α   : B ∈ Subuniverses 𝑨
𝑓   : ∣ 𝑆 ∣
𝑡   : ∥ 𝑆 ∥ 𝑓 → Term X
b   : X → ∣ 𝑨 ∣
β   : ∀ x → b x ∈ B
```
and the given proof term establishes the goal `𝑨 ⟦ node 𝑓 𝑡 ⟧ b ∈ B`.

Alternatively, we could express the preceeding fact using an inductive type representing images of terms.

\begin{code}

data TermImage (𝑨 : Algebra 𝓤 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓦) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 where
 var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
 app : ∀ 𝑓 𝑡 →  Π[ x ꞉ ∥ 𝑆 ∥ 𝑓 ] 𝑡 x ∈ TermImage 𝑨 Y  → (𝑓 ̂ 𝑨) 𝑡 ∈ TermImage 𝑨 Y

\end{code}

By what we proved above, it should come as no surprise that `TermImage 𝑨 Y` is a subuniverse of 𝑨 that contains Y.

\begin{code}

TermImageIsSub : {𝑨 : Algebra 𝓤 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓦} → TermImage 𝑨 Y ∈ Subuniverses 𝑨
TermImageIsSub = app

Y-onlyif-TermImageY : {𝑨 : Algebra 𝓤 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓦} → Y ⊆ TermImage 𝑨 Y
Y-onlyif-TermImageY {a} Ya = var Ya

\end{code}

Since `Sg 𝑨 Y` is the smallest subuniverse containing Y, we obtain the following inclusion.

\begin{code}

SgY-onlyif-TermImageY : (𝑨 : Algebra 𝓤 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓦) → Sg 𝑨 Y ⊆ TermImage 𝑨 Y
SgY-onlyif-TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y-onlyif-TermImageY

\end{code}



Next we prove the important fact that homomorphisms are uniquely determined by their values on a generating set.

\begin{code}

hom-unique : funext 𝓥 𝓦 → {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
             (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →           Π[ x ꞉ ∣ 𝑨 ∣ ] (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x)
             -------------------------------------------------
 →           Π[ a ꞉ ∣ 𝑨 ∣ ] (a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

hom-unique _ _ _ _ α a (var x) = α a x

hom-unique fe {𝑨}{𝑩} X g h α fa (app 𝑓 𝒂 β) = ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)   ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
                                              (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 ) ≡⟨ cong (𝑓 ̂ 𝑩)(fe IH) ⟩
                                              (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
                                              ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )  ∎
 where IH = λ x → hom-unique fe {𝑨}{𝑩} X g h α (𝒂 x) (β x)

\end{code}

In the induction step, we have the following typing judgments in the premise:

```
fe  : funext 𝓥 𝓦
𝑨   : Algebra 𝓤 𝑆
𝑩   : Algebra 𝓦 𝑆
X   : Pred ∣ 𝑨 ∣ 𝓤
g h  : hom 𝑨 𝑩
α   : Π x ꞉ ∣ 𝑨 ∣ , (x ∈ X → ∣ g ∣ x ≡ ∣ h ∣ x)
fa  : ∣ 𝑨 ∣
fa  = (𝑓 ̂ 𝑨) 𝒂
𝑓   : ∣ 𝑆 ∣
𝒂   : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣
β   : Im 𝒂 ⊆ Sg 𝑨 X
```

and, under these assumptions, we proved `∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)`.

---------------------------------

[↑ Subalgebras](Subalgebras.html)
<span style="float:right;">[Subalgebras.Subalgebras →](Subalgebras.Subalgebras.html)</span>


{% include UALib.Links.md %}

