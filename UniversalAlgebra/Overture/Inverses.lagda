---
layout: default
title : Overture.Inverses module
date : 2021-01-12
author: [the ualib/agda-algebras development team][]
---

### <a id="inverses">Inverses</a>

This is the [Overture.Inverses][] module of the [agda-algebras][] library.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module Overture.Inverses where

-- Imports from Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality       using ( _≡_ ; refl )
open import Agda.Primitive              using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product                using ( _,_ ; _×_ ; Σ-syntax ; Σ)
open import Data.Fin.Base               using ( Fin )
open import Data.Nat                    using ( ℕ )
open import Function.Base               using ( _∘_ ; id )
open import Function.Definitions        using ( Injective )
open import Function.Bundles            using ( _↣_ ; mk↣ )
open import Function.Construct.Identity using ( id-↣ )
import Relation.Binary.PropositionalEquality as PE

-- Imports from agda-algebras
open import Overture.Preliminaries using ( _⁻¹ ; _≈_ )

\end{code}

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

\begin{code}

private variable α β γ : Level

module _ {A : Type α }{B : Type β } where

 data Image_∋_ (f : A → B) : B → Type (α ⊔ β) where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a

\end{code}

We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

\begin{code}

 InvIsInv : (f : A → B){b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInv f (eq _ p) = p ⁻¹

\end{code}


#### <a id="injective-functions">Injective functions</a>

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

\begin{code}

module _ {A : Type α}{B : Type β} where

 IsInjective : (A → B) → Type (α ⊔ β)
 IsInjective f = Injective _≡_ _≡_ f

\end{code}

Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is injective and that the composition of injectives is injective.

\begin{code}

id-is-injective : {A : Type α} → A ↣ A
id-is-injective {A = A} = id-↣ A

∘-injective : {A : Type α}{B : Type β}{C : Type γ}{f : A → B}{g : B → C}
 →            IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective finj ginj = λ z → finj (ginj z)

\end{code}


#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

\begin{code}

module _ {A : Type α}{B : Type β} where
 IsSurjective : (A → B) →  Type (α ⊔ β)
 IsSurjective f = ∀ y → Image f ∋ y

 Surjective : Type (α ⊔ β)
 Surjective = Σ (A → B) IsSurjective

\end{code}

With the next definition, we can represent a *right-inverse* of a surjective function.

\begin{code}

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

\end{code}

Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Later, we will prove that this does indeed give the right-inverse, but we postpone the proof since it requires function extensionality, a concept we take up in the [Relations.Extensionality][] module.


#### Bijections of function types

In set theory, these would simply be bijections between sets, or "set isomorphisms."

\begin{code}

record Bijection (A : Type α)(B : Type β) : Type (α ⊔ β) where
 field
  to : A → B
  from : B → A
  to-from : to ∘ from ≡ id
  from-to : from ∘ to ≡ id

record BijectionExt (A : Type α)(B : Type β) : Type (α ⊔ β) where
 field
  to : A → B
  from : B → A
  to-from : to ∘ from ≈ id
  from-to : from ∘ to ≈ id


∣_∣=∣_∣ : (A : Type α)(B : Type β) → Type (α ⊔ β)
∣ A ∣=∣ B ∣ = Bijection A B

∣_∣≈∣_∣ : (A : Type α)(B : Type β) → Type (α ⊔ β)
∣ A ∣≈∣ B ∣ = BijectionExt A B


open Fin renaming (zero to zz ; suc to ss)

module _ {A : Type α} where

 uncurry₀ : A → A → A × A
 uncurry₀ x y = x , y

 curry1 : A × A → (Fin 2 → A)
 curry1 (x , y) zz = x
 curry1 (x , y) (ss zz) = y

 uncurry1 : (Fin 2 → A) → A × A
 uncurry1 u = u zz , u (ss zz)

 unc1-cur1 : uncurry1 ∘ curry1 ≡ id
 unc1-cur1 = refl

 cur1-unc1-ext : ∀ u i → (curry1 (uncurry1 u)) i ≡ u i
 cur1-unc1-ext u zz = refl
 cur1-unc1-ext u (ss zz) = refl

module _ {A : Type α}{B : Type β} where

 open PE.≡-Reasoning

 Curry : (A × A → B) → A → A → B
 Curry f x y = f (x , y)

 Uncurry : (A → A → B) → A × A → B
 Uncurry f (x , y) = f x y

 A×A→B≅A→A→B : ∣ (A × A → B) ∣=∣ (A → A → B) ∣
 A×A→B≅A→A→B = record { to = Curry
                      ; from = Uncurry
                      ; to-from = refl
                      ; from-to = refl }

 Curry' : ((Fin 2 → A) → B) → A × A → B
 Curry' f = f ∘ curry1

 Uncurry' : (A × A → B) → ((Fin 2 → A) → B)
 Uncurry' f = f ∘ uncurry1

 -- unc-cur' : ∀ f u → (Uncurry' ∘ Curry') f u ≡ f u
 -- unc-cur' f u = (Uncurry' ∘ Curry') f u ≡⟨ refl ⟩
 --                f (curry1 (uncurry1 u)) ≡⟨ PE.cong f {!!} ⟩ f u ∎

 -- Fin2A≅A×A→B : ∣ ((Fin 2 → A) → B) ∣=∣ (A × A → B) ∣
 -- Fin2A≅A×A→B = record { to = Curry'
 --                      ; from = Uncurry'
 --                      ; to-from = refl
 --                      ; from-to = {!!} }



\end{code}


--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
