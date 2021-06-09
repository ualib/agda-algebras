---
layout: default
title : Varieties.Closure.S module (The Agda Universal Algebra Library)
date : 2021-01-14
author: the agda-algebras development team
---

### <a id="the-inductive-type-s">The Inductive Type S</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level renaming ( suc to lsuc )
open import Algebras.Basic


module Varieties.Closure.S {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where


open import Data.Product   renaming ( proj₁ to fst
                                    ; proj₂ to snd )
open import Relation.Unary using    ( Pred ; _∈_ ; _⊆_ )


open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ )
open import Algebras.Products          {𝑆 = 𝑆} using ( ov ; ⨅ )
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅ )
open import Subalgebras.Subalgebras    {𝑆 = 𝑆} using (_≤_ ; ≤-iso ; ≤-refl ; ≤-trans ; ≤-TRANS-≅
                                                     ; _IsSubalgebraOfClass_ ; Subalgebra )

\end{code}

#### <a id="subalgebraic-closure">Subalgebraic closure</a>

We define the inductive type `S` to represent classes of algebras that is closed under the taking of subalgebras.

\begin{code}

data S {𝓤 𝓦 : Level}(𝒦 : Pred(Algebra 𝓤 𝑆)(ov 𝓤)) : Pred(Algebra(𝓤 ⊔ 𝓦)𝑆)(ov(𝓤 ⊔ 𝓦))
 where
 sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → Lift-alg 𝑨 𝓦 ∈ S 𝒦
 slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → Lift-alg 𝑨 𝓦 ∈ S 𝒦
 ssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
 siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S 𝒦

\end{code}

S is a closure operator.  The facts that S is idempotent and expansive won't be needed, so we omit these, but we will make use of monotonicity of S.  Here is the proof of the latter.

\begin{code}

S-mono : {𝓤 𝓦 : Level}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →       𝒦 ⊆ 𝒦' → S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'

S-mono kk' (sbase x)            = sbase (kk' x)
S-mono kk' (slift{𝑨} x)         = slift (S-mono kk' x)
S-mono kk' (ssub{𝑨}{𝑩} sA B≤A)  = ssub (S-mono kk' sA) B≤A
S-mono kk' (siso x x₁)          = siso (S-mono kk' x) x₁

\end{code}

We sometimes want to go back and forth between our two representations of subalgebras of algebras in a class. The tools `subalgebra→S` and `S→subalgebra` are made for that purpose.

\begin{code}

module _ {𝓤 𝓦 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 subalgebra→S : {𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 ∈ S{𝓤}{𝓦} 𝒦

 subalgebra→S {𝑩} (𝑨 , ((𝑪 , C≤A) , KA , B≅C)) = ssub sA B≤A
  where
   B≤A : 𝑩 ≤ 𝑨
   B≤A = ≤-iso 𝑨 B≅C C≤A

   slAu : Lift-alg 𝑨 𝓤 ∈ S{𝓤}{𝓤} 𝒦
   slAu = sbase KA

   sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦
   sA = siso slAu (≅-sym Lift-≅)


module _ {𝓤 : Level}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 S→subalgebra : {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S{𝓤}{𝓤} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦

 S→subalgebra (sbase{𝑩} x) =  𝑩 , (𝑩 , ≤-refl) , x , (≅-sym Lift-≅)
 S→subalgebra (slift{𝑩} x) = ∣ BS ∣ , SA , ∣ snd ∥ BS ∥ ∣ , ≅-trans (≅-sym Lift-≅) B≅SA
  where
   BS : 𝑩 IsSubalgebraOfClass 𝒦
   BS = S→subalgebra x
   SA : Subalgebra ∣ BS ∣
   SA = fst ∥ BS ∥
   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BS ∥ ∥

 S→subalgebra {𝑩} (ssub{𝑨} sA B≤A) = ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , ≅-refl
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = ≤-TRANS-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = ≤-trans ∣ AS ∣ B≤SA ∥ SA ∥

 S→subalgebra {𝑩} (siso{𝑨} sA A≅B) = ∣ AS ∣ , SA ,  ∣ snd ∥ AS ∥ ∣ , (≅-trans (≅-sym A≅B) A≅SA)
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd AS ∥

\end{code}

Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.


{% include UALib.Links.md %}
