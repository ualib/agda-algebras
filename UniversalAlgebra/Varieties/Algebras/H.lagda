---
layout: default
title : Varieties.Algebras.H module (The Agda Universal Algebra Library)
date : 2021-01-14
author: the agda-algebras development team
---

### <a id="the-inductive-type-h">The Inductive Type H</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from the Agda Standard Library
open import Data.Product using (_,_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Unary using (_∈_; Pred)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic using (Signature; Algebra; Lift-alg)

module Varieties.Algebras.H {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Algebras.Products{𝑆 = 𝑆} using (ov)
open import Homomorphisms.HomomorphicImages{𝑆 = 𝑆} using (HomImages)
open import Homomorphisms.Isomorphisms{𝑆 = 𝑆} using (_≅_)

\end{code}


#### <a id="homomorphic-closure">Homomorphic closure</a>

We define the inductive type `H` to represent classes of algebras that include all homomorphic images of algebras in the class; i.e., classes that are closed under the taking of homomorphic images.

\begin{code}

data H {𝓤 𝓦 : Level} (𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (ov(𝓤 ⊔ 𝓦))
 where
 hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → Lift-alg 𝑨 𝓦 ∈ H 𝒦
 hlift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → Lift-alg 𝑨 𝓦 ∈ H 𝒦
 hhimg : {𝑨 𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H {𝓤} {𝓦} 𝒦 → ((𝑩 , _) : HomImages 𝑨) → 𝑩 ∈ H 𝒦
 hiso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ H {𝓦 = 𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H 𝒦

\end{code}


{% include UALib.Links.md %}
