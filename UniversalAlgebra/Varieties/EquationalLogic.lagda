---
layout: default
title : Varieties.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

## Varieties, Model Theory, and Equational Logic

This is the [Varieties.EquationalLogic.Basic][] module of the [Agda Universal Algebra Library][] where the binary "models" relation ⊧, relating algebras (or classes of algebras) to the identities that they satisfy, is defined.

Agda supports the definition of infix operations and relations, and we use this to define ⊧ so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`.



**Notation**. In the [Agda UniversalAlgebra][] library, because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊫ p ≈ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

**Unicode Hints**. To produce the symbols ≈, ⊧, and ≋ in [agda2-mode][], type `\~~`, `\models`, and `\~~~`, respectively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where


-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive   using    ( _⊔_ ;  lsuc ; Level )
                             renaming ( Set to Type )
open import Data.Product     using    ( _×_ ; _,_ ; Σ-syntax)
                             renaming ( proj₁ to fst ; proj₂ to snd )
open import Relation.Unary   using    ( Pred ; _∈_ )



-- -- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries    using ( _≈_ )
open import Algebras.Basic            using ( Algebra )
open import Algebras.Products {𝑆 = 𝑆} using ( ov )
open import Terms.Basic       {𝑆 = 𝑆} using ( Term ; 𝑻 )
open import Terms.Operations  {𝑆 = 𝑆} using ( _⟦_⟧ )

private variable χ α ρ ι : Level
                 X : Type χ

\end{code}


### The "models" relation
We define the binary "models" relation ⊧ using infix syntax so that we may
write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`, relating algebras (or classes of
algebras) to the identities that they satisfy. We also prove a couple of useful
facts about ⊧.  More will be proved about ⊧ in the next module,
Varieties.EquationalLogic.

\begin{code}

_⊧_≈_ : Algebra α 𝑆 → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

_⊫_≈_ : Pred(Algebra α 𝑆) ρ → Term X → Term X → Type _
𝒦 ⊫ p ≈ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}

The expression `𝑨 ⊧ p ≈ q` represents the assertion that the identity `p ≈ q`
holds when interpreted in the algebra `𝑨`; syntactically, `𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧`.

The expression `𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧` denotes *extensional equality*; that is,
for each "environment" `η :  X → ∣ 𝑨 ∣` (assigning values in the domain of `𝑨`
to the variable symbols in `X`) the (intensional) equality `𝑨 ⟦ p ⟧ η ≡ 𝑨 ⟦ q ⟧ η`
holds.


### Equational theories and models

If 𝒦 denotes a class of structures, then `Th 𝒦` represents the set of identities
modeled by the members of 𝒦.

\begin{code}

Th : Pred (Algebra α 𝑆) (ov α) → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

\end{code}

Perhaps we want to represent Th 𝒦 as an indexed collection.  We do so
essentially by taking `Th 𝒦` itself to be the index set, as follows.

\begin{code}

module _ {X : Type χ}{𝒦 : Pred (Algebra α 𝑆) (ov α)} where

 ℐ : Type (ov(α ⊔ χ))
 ℐ = Σ[ (p , q) ∈ (Term X × Term X) ] 𝒦 ⊫ p ≈ q

 ℰ : ℐ → Term X × Term X
 ℰ ((p , q) , _) = (p , q)


\end{code}

If `ℰ` denotes a set of identities, then `Mod ℰ` is the class of structures
satisfying the identities in `ℰ`.

\begin{code}

Mod : Pred(Term X × Term X) (ov α) → Pred(Algebra α 𝑆) _
Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q
-- (tupled version)
Modᵗ : {I : Type ι} → (I → Term X × Term X) → {α : Level} → Pred(Algebra α 𝑆) _
Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ (fst (ℰ i)) ≈ (snd (ℰ i))

\end{code}

-------------------------------------

[↑ Varieties](Varieties.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}


--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team





<!--

  -- open import Relation.Binary.Core using (_⇔_)

  -- ⊧-H : DFunExt → {p q : Term X} → 𝒦 ⊫ p ≈ q ⇔ (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘(𝑻 X ⟦ q ⟧))
  -- ⊧-H fe {p}{q} = ⊧-H-class-invar fe {p}{q} , ⊧-H-class-coinvar fe {p}{q}


-->
