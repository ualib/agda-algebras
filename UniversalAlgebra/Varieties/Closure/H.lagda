---
layout: default
title : Varieties.Closure.H module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

### <a id="the-inductive-type-h">The Inductive Type H</a>

We define the inductive type `H` to represent classes of algebras that include all homomorphic images of algebras in the class; i.e., classes that are closed under the taking of homomorphic images.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level using ( Level ; Lift )
open import Algebras.Basic

module Varieties.Closure.H {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive                    using ( _⊔_ )
open import Data.Product                      using ( _,_ )
open import Relation.Unary                    using ( Pred ; _∈_ ; _⊆_ )
open import Algebras.Products               {𝑆 = 𝑆} using ( ov ; ⨅ )
open import Homomorphisms.HomomorphicImages {𝑆 = 𝑆} using ( HomImages )


data H {α β : Level} (𝒦 : Pred (Algebra α 𝑆) (ov α)) : Pred (Algebra (α ⊔ β) 𝑆) (ov(α ⊔ β))
 where
 hbase : {𝑨 : Algebra α 𝑆} → 𝑨 ∈ 𝒦 → Lift-Alg 𝑨 β ∈ H 𝒦
 hhimg : {𝑨 𝑩 : Algebra (α ⊔ β) 𝑆} → 𝑨 ∈ H {α} {β} 𝒦 → ((𝑩 , _) : HomImages 𝑨) → 𝑩 ∈ H 𝒦

\end{code}


--------------------------------------

{% include UALib.Links.md %}

--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
