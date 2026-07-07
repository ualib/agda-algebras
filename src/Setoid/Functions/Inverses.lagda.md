---
layout: default
title : "Setoid.Overture.Inverses module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### Inverses for functions with structure

This is the [Setoid.Functions.Inverses][] module of the [agda-algebras][] library.


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Functions.Inverses where

-- Imports from Agda and the Agda Standard Library --------------------
open import Agda.Primitive    using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Function          using ( _$_ )   renaming ( Func to _⟶_ )
open import Data.Product      using ( _,_ ; Σ-syntax )
                              renaming ( _×_ to _∧_)
open import Relation.Unary    using ( Pred ; _∈_ )
open import Relation.Binary   using ( Setoid ; _Preserves_⟶_ )

-- Imports from agda-algebras -----------------------------------------
open import Overture using ( proj₁ ; proj₂ ; ∃-syntax )

private variable α ρᵃ β ρᵇ : Level
```
-->

```agda
module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

  open Setoid 𝑨 using()  renaming ( Carrier to A ; _≈_ to _≈₁_ )
                         renaming ( refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝑩 using()  renaming ( Carrier to B ; _≈_ to _≈₂_ )
                         renaming ( refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (to to _⟨$⟩_ )
```


We begin by defining two data types that represent the semantic concept of the
*image* of a function.  The first of these is for functions on bare types, while
the second is for functions on setoids.


```agda
  data Img_∋_ (f : A → B) : B → Type (α ⊔ β ⊔ ρᵇ) where
    eq : {b : B} → (a : A) → b ≈₂ (f a) → Img f ∋ b


  data Image_∋_ (F : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
    eq : {b : B} → (a : A) → b ≈₂ (F ⟨$⟩ a) → Image F ∋ b

  open Image_∋_

  IsInRange : (𝑨 ⟶ 𝑩) → Pred B (α ⊔ ρᵇ)
  IsInRange F b = ∃[ a ∈ A ] (F ⟨$⟩ a) ≈₂ b

  Image⊆Range : ∀ {F b} → Image F ∋ b → b ∈ IsInRange F
  Image⊆Range (eq a x) = a , (sym₂ x)

  IsInRange→IsInImage : ∀ {F b} → b ∈ IsInRange F → Image F ∋ b
  IsInRange→IsInImage (a , x) = eq a (sym₂ x)

  Imagef∋f : ∀ {F a} → Image F ∋ (F ⟨$⟩ a)
  Imagef∋f = eq _ refl₂

  -- Alternative representation of the range of a Func as a setoid

  -- the carrier
  range : (𝑨 ⟶ 𝑩) → Type (α ⊔ β ⊔ ρᵇ)
  range F = Σ[ b ∈ B ] ∃[ a ∈ A ](F ⟨$⟩ a) ≈₂ b

  image : (F : 𝑨 ⟶ 𝑩) → range F → B
  image F (b , (_ , _)) = b

  preimage : (F : 𝑨 ⟶ 𝑩) → range F → A
  preimage F (_ , (a , _)) = a

  f∈range : ∀ {F} → A → range F
  f∈range {F} a = (F ⟨$⟩ a) , (a , refl₂)

  ⌜_⌝ : (F : 𝑨 ⟶ 𝑩) → A → range F
  ⌜ F ⌝ a = f∈range{F} a

  Ran : (𝑨 ⟶ 𝑩) → Setoid (α ⊔ β ⊔ ρᵇ) ρᵇ
  Ran F = record  { Carrier = range F
                  ; _≈_ = λ x y → (image F) x ≈₂ (image F) y
                  ; isEquivalence = record  { refl = refl₂
                                            ; sym = sym₂
                                            ; trans = trans₂
                                            }
                  }

  RRan : (𝑨 ⟶ 𝑩) → Setoid (α ⊔ β ⊔ ρᵇ) (ρᵃ ⊔ ρᵇ)
  RRan F = record  { Carrier = range F
                   ; _≈_ = λ x y →  (preimage F) x ≈₁ (preimage F) y
                                    ∧ (image F) x ≈₂ (image F) y

                   ; isEquivalence =
                      record  { refl = refl₁ , refl₂
                              ; sym = λ x → sym₁ (proj₁ x) , sym₂ (proj₂ x)
                              ; trans = λ x y → trans₁ (proj₁ x) (proj₁ y) , trans₂ (proj₂ x) (proj₂ y)
                              }
                   }

  preimage≈image : ∀ F r → F ⟨$⟩ (preimage F) r ≈₂ (image F) r
  preimage≈image F (_ , (_ , p)) = p


  Dom : (𝑨 ⟶ 𝑩) → Setoid α ρᵇ
  Dom F = record  { Carrier = A
                  ; _≈_ = λ x y → F ⟨$⟩ x ≈₂ F ⟨$⟩ y
                  ; isEquivalence = record  { refl = refl₂
                                            ; sym = sym₂
                                            ; trans = trans₂
                                            }
                  }
```


An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.


```agda
  inv : (f : A → B) {b : B} → Img f ∋ b → A
  inv _ (eq a _) = a

  Inv : (F : 𝑨 ⟶ 𝑩) {b : B} → Image F ∋ b → A
  Inv _ (eq a _) = a

  Inv' : (F : 𝑨 ⟶ 𝑩) {b : B} → b ∈ IsInRange F → A
  Inv' _ (a , _) = a

  [_]⁻¹ : (F : 𝑨 ⟶ 𝑩) → range F → A
  [ F ]⁻¹ = preimage F

  ⟦_⟧⁻¹ : (F : 𝑨 ⟶ 𝑩) → Ran F ⟶ Dom F
  ⟦ F ⟧⁻¹ = record
    { to = preimage F
    ; cong = λ {x}{y} ix≈iy → trans₂  (preimage≈image F x)
                                      (trans₂ ix≈iy $ sym₂ $ preimage≈image F y)
    }
```


We can prove that `Inv f` is the range-restricted right-inverse of `f`, as follows.


```agda
  invIsInvʳ : {f : A → B} {b : B} (q : Img f ∋ b) → f (inv f q) ≈₂ b
  invIsInvʳ (eq _ p) = sym₂ p

  InvIsInverseʳ : {F : 𝑨 ⟶ 𝑩} {b : B} (q : Image F ∋ b) → F ⟨$⟩ (Inv F q) ≈₂ b
  InvIsInverseʳ (eq _ p) = sym₂ p

  ⁻¹IsInverseʳ : {F : 𝑨 ⟶ 𝑩} {bap : range F} → F ⟨$⟩ ([ F ]⁻¹ bap ) ≈₂ bap .proj₁
  ⁻¹IsInverseʳ {bap = (_ , (_ , p))} = p
```


Of course, the "range-restricted" qualifier is needed because `Inf f` is not defined outside the range of `f`.

In the following sense, `Inv f` is also a (range-restricted) *left-inverse*.


```agda
  InvIsInverseˡ : ∀ {F a} → Inv F {b = F ⟨$⟩ a} Imagef∋f ≈₁ a
  InvIsInverseˡ = refl₁

  ⁻¹IsInverseˡ : ∀ {F a} → [ F ]⁻¹ (f∈range{F} a) ≈₁ a
  ⁻¹IsInverseˡ = refl₁
```
