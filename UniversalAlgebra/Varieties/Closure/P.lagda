---
layout: default
title : Varieties.Closure.P module (The Agda Universal Algebra Library)
date : 2021-01-14
author: the agda-algebras development team
---

### <a id="the-inductive-types-p">The Inductive Type P </a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level using ( Level ; Lift )
open import Algebras.Basic

module Varieties.Closure.P {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where


open import Agda.Primitive   using    ( _⊔_ ;  lsuc )
                             renaming ( Set to Type )
open import Data.Product     using    ( _,_ )
open import Relation.Unary   using    ( _∈_ ; Pred; _⊆_)


open import Algebras.Products{𝑆 = 𝑆} using ( ov ; ⨅ )
open import Homomorphisms.Isomorphisms{𝑆 = 𝑆} using ( _≅_ ; ≅-sym ; Lift-≅ ; Lift-alg-iso )
open import Subalgebras.Subalgebras{𝑆 = 𝑆} using (_IsSubalgebraOfClass_ ; _≤_ ; Lift-≤-Lift )

-- private variable α β γ : Level

\end{code}

#### <a id="product-closure">Product closure</a>

We define the inductive type `P` to represent classes of algebras that is closed under the taking of arbitrary products.

\begin{code}

data P {α β : Level}(𝒦 : Pred(Algebra α 𝑆)(ov α)) : Pred(Algebra(α ⊔ β)𝑆)(ov(α ⊔ β))
 where
 pbase  : {𝑨 : Algebra α 𝑆} → 𝑨 ∈ 𝒦 → Lift-alg 𝑨 β ∈ P 𝒦
 pliftu : {𝑨 : Algebra α 𝑆} → 𝑨 ∈ P{α}{α} 𝒦 → Lift-alg 𝑨 β ∈ P 𝒦
 pliftw : {𝑨 : Algebra (α ⊔ β) 𝑆} → 𝑨 ∈ P{α}{β} 𝒦 → Lift-alg 𝑨 (α ⊔ β) ∈ P 𝒦
 produ  : {I : Type β }{𝒜 : I → Algebra α 𝑆} → (∀ i → (𝒜 i) ∈ P{α}{α} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
 prodw  : {I : Type β }{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ P{α}{β} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
 pisow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{α}{β} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦

\end{code}


#### <a id="closure-properties">Closure properties</a>

`P` is a closure operator.  This is proved by checking that `P` is *monotone*, *expansive*, and *idempotent*. The meaning of these terms will be clear from the definitions of the types that follow.

\begin{code}

P-mono : {α β : Level}{𝒦 𝒦' : Pred(Algebra α 𝑆)(ov α)}
 →       𝒦 ⊆ 𝒦' → P{α}{β} 𝒦 ⊆ P{α}{β} 𝒦'

P-mono kk' (pbase x)    = pbase (kk' x)
P-mono kk' (pliftu x)   = pliftu (P-mono kk' x)
P-mono kk' (pliftw x)   = pliftw (P-mono kk' x)
P-mono kk' (produ x)    = produ (λ i → P-mono kk' (x i))
P-mono kk' (prodw x)    = prodw (λ i → P-mono kk' (x i))
P-mono kk' (pisow x x₁) = pisow (P-mono kk' x) x₁


P-expa : {α : Level}{𝒦 : Pred (Algebra α 𝑆)(ov α)} → 𝒦 ⊆ P{α}{α} 𝒦
P-expa{α}{𝒦} {𝑨} KA =  pisow {𝑩 = 𝑨} (pbase KA) (≅-sym Lift-≅)


module _ {α β : Level} where

 P-idemp : {𝒦 : Pred (Algebra α 𝑆)(ov α)}
  →        P{α ⊔ β}{α ⊔ β} (P{α}{α ⊔ β} 𝒦) ⊆ P{α}{α ⊔ β} 𝒦

 P-idemp (pbase x)    = pliftw x
 P-idemp (pliftu x)   = pliftw (P-idemp x)
 P-idemp (pliftw x)   = pliftw (P-idemp x)
 P-idemp (produ x)    = prodw (λ i → P-idemp (x i))
 P-idemp (prodw x)    = prodw (λ i → P-idemp (x i))
 P-idemp (pisow x x₁) = pisow (P-idemp x) x₁

\end{code}

Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.

\begin{code}
module _ {α β : Level}{𝒦 : Pred (Algebra α 𝑆)(ov α)} where

 Lift-alg-subP : {𝑩 : Algebra β 𝑆}
  →              𝑩 IsSubalgebraOfClass (P{α}{β} 𝒦)
  →              (Lift-alg 𝑩 α) IsSubalgebraOfClass (P{α}{β} 𝒦)

 Lift-alg-subP (𝑨 , (𝑪 , C≤A) , pA , B≅C ) = lA , (lC , lC≤lA) , plA , (Lift-alg-iso B≅C)
   where
   lA lC : Algebra (α ⊔ β)  𝑆
   lA = Lift-alg 𝑨 (α ⊔ β)
   lC = Lift-alg 𝑪 α

   lC≤lA : lC ≤ lA
   lC≤lA = Lift-≤-Lift α {𝑨} (α ⊔ β) C≤A
   plA : lA ∈ P{α}{β} 𝒦
   plA = pliftw pA

 Lift-alg-subP' : {𝑨 : Algebra α 𝑆}
  →                𝑨 IsSubalgebraOfClass (P{α}{α} 𝒦)
  →               (Lift-alg 𝑨 β) IsSubalgebraOfClass (P{α}{β} 𝒦)

 Lift-alg-subP' (𝑩 , (𝑪 , C≤B) , pB , A≅C ) = lB , (lC , lC≤lB) , plB , (Lift-alg-iso A≅C)
   where
   lB lC : Algebra (α ⊔ β)  𝑆
   lB = Lift-alg 𝑩 β
   lC = Lift-alg 𝑪 β

   lC≤lB : lC ≤ lB
   lC≤lB = Lift-≤-Lift β {𝑩} β C≤B
   plB : lB ∈ P{α}{β} 𝒦
   plB = pliftu pB

\end{code}



{% include UALib.Links.md %}


--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
