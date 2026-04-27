---
layout: default
title : "Base.Functions.Inverses module"
date : "2021-01-12"
author: "the agda-algebras development team"
---

### <a id="inverses">Inverses</a>

This is the [Base.Functions.Inverses][] module of the [agda-algebras][] library.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Base.Functions.Inverses where

-- Imports from Agda and the Agda Standard Library ---------------------------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ-syntax )
open import Level             using ( Level ; _⊔_ )
open import Relation.Binary.PropositionalEquality
                              using ( _≡_ ; sym ; refl )
open import Relation.Unary    using ( Pred ; _∈_ )

-- Imports from agda-algebras ----------------------------------------------------------------
open import Overture.Basic using ( ∃-syntax ; ∣_∣ )

private variable a b : Level
```


We begin by defining an data type that represents the semantic concept of *inverse
image* of a function.


```agda


module _ {A : Type a}{B : Type b} where

 data Image_∋_ (f : A → B) : B → Type (a ⊔ b) where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

 open Image_∋_

 Range : (A → B) → Pred B (a ⊔ b)
 Range f b = ∃[ a ∈ A ] (f a) ≡ b

 range : (A → B) → Type (a ⊔ b)
 range f = Σ[ b ∈ B ] ∃[ a ∈ A ](f a) ≡ b

 Image⊆Range : (f : A → B) → ∀ b → Image f ∋ b → b ∈ Range f
 Image⊆Range f b (eq a x) = a , (sym x)

 Range⊆Image : (f : A → B) → ∀ b → b ∈ Range f → Image f ∋ b
 Range⊆Image f b (a , x) = eq a (sym x)

 Imagef∋f : {f : A → B}{a : A} → Image f ∋ (f a)
 Imagef∋f = eq _ refl

 f∈range : {f : A → B}(a : A) → range f
 f∈range {f} a = (f a) , (a , refl)
```


An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and
`p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs
to the image of `f` is always accompanied by a witness `a : A`, we can actually
*compute* a (pseudo)inverse of `f`. For convenience, we define this inverse
function, which we call `Inv`, and which takes an arbitrary `b : B` and a
(*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.


```agda


 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a


 [_]⁻¹ : (f : A → B) → range f →  A
 [ f ]⁻¹ (_ , (a , _)) = a
```


We can prove that `Inv f` is the (range-restricted) *right-inverse* of `f`, as
follows.


```agda


 InvIsInverseʳ : {f : A → B}{b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInverseʳ (eq _ p) = sym p

 ⁻¹IsInverseʳ : {f : A → B}{bap : range f} → f ([ f ]⁻¹ bap) ≡ ∣ bap ∣
 ⁻¹IsInverseʳ {bap = (_ , (_ , p))} = p
```


Of course, the "range-restricted" qualifier is needed because `Inf f` is not defined outside the range of `f`.

In a certain sense, `Inv f` is also a (range-restricted) *left-inverse*.


```agda


 InvIsInverseˡ : ∀ {f a} → Inv f {b = f a} Imagef∋f ≡ a
 InvIsInverseˡ = refl

 ⁻¹IsInverseˡ : ∀ {f a} → [ f ]⁻¹ (f∈range a) ≡ a
 ⁻¹IsInverseˡ = refl
```


--------------------------------------

<span style="float:left;">[← Base.Functions.Preliminaries](Base.Functions.Preliminaries.html)</span>
<span style="float:right;">[Base.Functions.Injective →](Base.Functions.Injective.html)</span>

{% include UALib.Links.md %}


