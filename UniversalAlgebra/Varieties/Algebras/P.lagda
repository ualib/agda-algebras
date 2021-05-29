---
layout: default
title : Varieties.Algebras.P module (The Agda Universal Algebra Library)
date : 2021-01-14
author: the agda-algebras development team
---

### <a id="the-inductive-types-p">The Inductive Type P </a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports the Agda Standard Library
open import Data.Product using (_,_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Unary using (_∈_; Pred; _⊆_)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Preliminaries using (Type)

module Varieties.Algebras.P {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Algebras.Products{𝑆 = 𝑆} using (ov; ⨅)
open import Homomorphisms.Isomorphisms{𝑆 = 𝑆} using (_≅_; ≅-sym; Lift-≅; Lift-alg-iso)
open import Subalgebras.Subalgebras{𝑆 = 𝑆} using (_IsSubalgebraOfClass_; _≤_; Lift-≤-Lift)

\end{code}

#### <a id="product-closure">Product closure</a>

We define the inductive type `P` to represent classes of algebras that is closed under the taking of arbitrary products.

\begin{code}

data P {𝓤 𝓦 : Level}(𝒦 : Pred(Algebra 𝓤 𝑆)(ov 𝓤)) : Pred(Algebra(𝓤 ⊔ 𝓦)𝑆)(ov(𝓤 ⊔ 𝓦))
 where
 pbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → Lift-alg 𝑨 𝓦 ∈ P 𝒦
 pliftu : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → Lift-alg 𝑨 𝓦 ∈ P 𝒦
 pliftw : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → Lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P 𝒦
 produ  : {I : Type 𝓦 }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
 prodw  : {I : Type 𝓦 }{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
 pisou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦
 pisow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦

\end{code}


#### <a id="closure-properties">Closure properties</a>

`P` is a closure operator.  This is proved by checking that `P` is *monotone*, *expansive*, and *idempotent*. The meaning of these terms will be clear from the definitions of the types that follow.

\begin{code}

P-mono : {𝓤 𝓦 : Level}{𝒦 𝒦' : Pred(Algebra 𝓤 𝑆)(ov 𝓤)}
 →       𝒦 ⊆ 𝒦' → P{𝓤}{𝓦} 𝒦 ⊆ P{𝓤}{𝓦} 𝒦'

P-mono kk' (pbase x)    = pbase (kk' x)
P-mono kk' (pliftu x)   = pliftu (P-mono kk' x)
P-mono kk' (pliftw x)   = pliftw (P-mono kk' x)
P-mono kk' (produ x)    = produ (λ i → P-mono kk' (x i))
P-mono kk' (prodw x)    = prodw (λ i → P-mono kk' (x i))
P-mono kk' (pisou x x₁) = pisou (P-mono kk' x) x₁
P-mono kk' (pisow x x₁) = pisow (P-mono kk' x) x₁


P-expa : {𝓤 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → 𝒦 ⊆ P{𝓤}{𝓤} 𝒦
P-expa{𝓤}{𝒦} {𝑨} KA = pisou{𝑨 = (Lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (≅-sym Lift-≅)


module _ {𝓤 𝓦 : Level} where

 P-idemp : {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
  →        P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦

 P-idemp (pbase x)    = pliftw x
 P-idemp (pliftu x)   = pliftw (P-idemp x)
 P-idemp (pliftw x)   = pliftw (P-idemp x)
 P-idemp (produ x)    = prodw (λ i → P-idemp (x i))
 P-idemp (prodw x)    = prodw (λ i → P-idemp (x i))
 P-idemp (pisou x x₁) = pisow (P-idemp x) x₁
 P-idemp (pisow x x₁) = pisow (P-idemp x) x₁

\end{code}

Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.

\begin{code}
module _ {𝓤 𝓦 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 Lift-alg-subP : {𝑩 : Algebra 𝓤 𝑆}
  →              𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
  →              (Lift-alg 𝑩 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

 Lift-alg-subP {𝑩}(𝑨 , (𝑪 , C≤A) , pA , B≅C ) =
  lA , (lC , lC≤lA) , plA , (Lift-alg-iso B≅C)
   where
   lA lC : Algebra (𝓤 ⊔ 𝓦) 𝑆
   lA = Lift-alg 𝑨 𝓦
   lC = Lift-alg 𝑪 𝓦

   lC≤lA : lC ≤ lA
   lC≤lA = Lift-≤-Lift 𝑨 C≤A
   plA : lA ∈ P 𝒦
   plA = pliftu pA

\end{code}



{% include UALib.Links.md %}
