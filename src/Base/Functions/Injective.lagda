---
layout: default
title : "Base.Functions.Injective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="injective-functions">Injective functions</a>

This is the [Base.Functions.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` is *injective* (or *monic*) if it
does not map two distinct elements of the domain to the same point in
the codomain. The following type manifests this property.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Functions.Injective where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Function                               using ( _↣_ ;  _∘_ ; Injective )
open import Function.Construct.Identity            using ( ↣-id )
open import Level                                  using ( _⊔_ ; Level )
open import Relation.Binary                        using ( Rel )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

private variable a b c : Level

id-is-injective : {A : Type a} → A ↣ A
id-is-injective {A = A} = ↣-id A

module _ {A : Type a}{B : Type b} where

 IsInjective : (A → B) → Type (a ⊔ b)
 IsInjective f = Injective _≡_ _≡_ f

\end{code}

The composition of injective functions is injective.

\begin{code}

∘-injective :  {A : Type a}{B : Type b}{C : Type c}{f : A → B}{g : B → C}
  →            IsInjective f → IsInjective g → IsInjective (g ∘ f)

∘-injective fi gi = λ x → fi (gi x)
\end{code}

--------------------------------------

<span style="float:left;">[← Base.Functions.FuncInverses](Base.Functions.FuncInverses.html)</span>
<span style="float:right;">[Base.Functions.Surjective →](Base.Functions.Surjective.html)</span>

{% include UALib.Links.md %}


