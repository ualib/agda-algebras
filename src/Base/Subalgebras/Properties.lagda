---
layout: default
title : "Base.Subalgebras.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-18"
author: "agda-algebras development team"
---

### <a id="properties-of-the-subalgebra-inclusion-relation">Properties of the Subalgebra Inclusion Relation</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Base.Subalgebras.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base    using ( _∘_ ; id ; flip )
open import Function.Bundles using ( Injection )
open import Relation.Unary   using ( Pred ; _⊆_ )
open import Relation.Binary.Definitions
                             using ( _Respectsʳ_ ; _Respectsˡ_ )
open import Relation.Binary.PropositionalEquality
                             using ( _≡_ ; refl ; module ≡-Reasoning ; cong )

-- Imports from the Agda Universal Algebra Library --------------------
open import Base.Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Overture.Injective                 using (  id-is-injective ; IsInjective ; ∘-injective )
open import Base.Algebras.Basic                     using ( Algebra ; Lift-Alg )
open import Base.Algebras.Products          {𝑆 = 𝑆} using ( ov )
open import Base.Homomorphisms.Basic        {𝑆 = 𝑆} using ( is-homomorphism )
open import Base.Homomorphisms.Properties   {𝑆 = 𝑆} using ( ∘-hom ; ∘-is-hom )
open import Base.Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅toInjective ; ≅fromInjective ; ≅-refl
                                                     ; ≅-sym ; ≅-trans ; Lift-≅ ; mkiso )
open import Base.Subalgebras.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; _≥_ ; _IsSubalgebraOfClass_ )

private variable α β γ 𝓧 : Level


-- The subalgebra relation is a *preorder*, i.e., a reflexive transitive binary relation.

open _≅_

≤-refl : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≤-refl φ = (to φ) , ≅toInjective φ

≥-refl : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≥-refl φ = (from φ) , ≅fromInjective φ

≤-reflexive : (𝑨 : Algebra α 𝑆) → 𝑨 ≤ 𝑨
≤-reflexive 𝑨 = (id , λ 𝑓 𝑎 → refl) , Injection.injective id-is-injective

≤-trans : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
 →        𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
≤-trans 𝑨 𝑪 A≤B B≤C = (∘-hom 𝑨 𝑪 ∣ A≤B ∣ ∣ B≤C ∣) , ∘-injective ∥ A≤B ∥ ∥ B≤C ∥


≥-trans : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆)
 →        𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
≥-trans 𝑨 𝑪 A≥B B≥C = ≤-trans 𝑪 𝑨 B≥C A≥B

\end{code}

#### <a id="relations-between">Relations between ≤, ≥, and ≅</a>

In case all algebras live in the same universe level, we can use some of the definitions
in the standard library. However, to obtain more general versions, we need to either
extend the standard library's Binary.Structures module to be universe polymorphic, or
just implement what we need here.  For now we do the latter (below).

\begin{code}

module _ {α : Level} where

 open import Relation.Binary.Structures {a = (ov α)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α)} (_≅_ {α}{α})

 open IsPreorder

 ≤-preorder : IsPreorder _≤_
 isEquivalence ≤-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≤-preorder = ≤-refl
 trans ≤-preorder {𝑨}{𝑩}{𝑪} A≤B B≤C = ≤-trans 𝑨 𝑪 A≤B B≤C

 ≥-preorder : IsPreorder _≥_
 isEquivalence ≥-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≥-preorder = ≥-refl
 trans ≥-preorder {𝑨}{𝑩}{𝑪} A≥B B≥C = ≥-trans 𝑨 𝑪 A≥B B≥C

\end{code}

Here are some consequences of the fact that `_≤_` and `_≥_` are preorders relative to `_≅_`.
These are essentially equivalent variations on the following obvious fact: If two algebras are isomorphic and one of them is a subalgebra, then so is the other.

\begin{code}

 -- 1a. If 𝑨 ≤ 𝑩  and  𝑩 ≅ 𝑪, then  𝑨 ≤ 𝑪
 ≤-resp-≅ : _≤_ Respectsʳ _≅_     -- usage: (note the argument order)
 ≤-resp-≅ = ∼-respˡ-≈ ≥-preorder  -- (p : 𝑩 ≅ 𝑪) (q : 𝑨 ≤ 𝑩) → (≤-resp-≅ p q) : 𝑨 ≤ 𝑪

 -- 2a. If 𝑨 ≥ 𝑩  and  𝑩 ≅ 𝑪,   then 𝑨 ≥ 𝑪
 ≥-resp-≅ : _≥_ Respectsʳ _≅_
 ≥-resp-≅ {𝑨} = ∼-respˡ-≈ ≤-preorder {𝑨}

 -- 1b. If 𝑩 ≅ 𝑪   and 𝑩 ≥ 𝑨, then  𝑪 ≥ 𝑨
 ≅-resp-≥ : _≥_ Respectsˡ _≅_
 ≅-resp-≥ = ≤-resp-≅

 -- 2b. If 𝑩 ≅ 𝑪  and 𝑩 ≤ 𝑨, then  𝑪 ≤ 𝑨
 ≅-resp-≤ : _≤_ Respectsˡ _≅_
 ≅-resp-≤ {𝑨} = ≥-resp-≅ {𝑨}

\end{code}

#### <a id="relations-between-polymorphic-versions)">Relations between ≤, ≥, and ≅ (universe-polymorphic versions)</a>

\begin{code}

module _ {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆} where
 ≤-RESP-≅ : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 ≤-RESP-≅ a<b bc = ≤-trans 𝑨 𝑪 a<b (≤-refl bc)

 ≥-RESP-≅ : 𝑨 ≥ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥ 𝑪
 ≥-RESP-≅ a<b ac = ≤-trans 𝑪 𝑨 (≤-refl (≅-sym ac)) a<b

module _ {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}{𝑪 : Algebra γ 𝑆} where

 ≅-RESP-≤ : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≅-RESP-≤ ab b<c = ≥-RESP-≅{𝑨 = 𝑪} b<c (≅-sym ab)

 ≅-RESP-≥ : 𝑨 ≅ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
 ≅-RESP-≥ ab b<c = ≤-RESP-≅ b<c (≅-sym ab)


open ≡-Reasoning
iso→injective : {𝑨 : Algebra α 𝑆}{𝑩 : Algebra β 𝑆}
 →              (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣
iso→injective {𝑨 = 𝑨} (mkiso f g f∼g g∼f) {x} {y} fxfy =
 x                  ≡⟨ (g∼f x)⁻¹ ⟩
 (∣ g ∣ ∘ ∣ f ∣) x  ≡⟨ cong ∣ g ∣ fxfy ⟩
 (∣ g ∣ ∘ ∣ f ∣) y  ≡⟨ g∼f y ⟩
 y                  ∎

≤-mono : (𝑩 : Algebra β 𝑆){𝒦 𝒦' : Pred (Algebra α 𝑆) γ}
 →       𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

≤-mono 𝑩 KK' KB = ∣ KB ∣ , fst ∥ KB ∥ , KK' (∣ snd ∥ KB ∥ ∣) , ∥ (snd ∥ KB ∥) ∥

\end{code}

#### <a id="lifts-of-subalgebras">Lifts of subalgebras</a>

\begin{code}

module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)}{𝑩 : Algebra α 𝑆} where

 Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-Alg 𝑩 α) IsSubalgebraOfClass 𝒦
 Lift-is-sub (𝑨 , (sa , (KA , B≅sa))) = 𝑨 , sa , KA , ≅-trans (≅-sym Lift-≅) B≅sa

≤-Lift : {𝑨 : Algebra α 𝑆}(𝑩 : Algebra β 𝑆){ℓ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Alg 𝑩 ℓ
≤-Lift 𝑩 a<b = ≤-RESP-≅{𝑩 = 𝑩} a<b Lift-≅

≥-Lift : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}{ℓ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Alg 𝑩 ℓ
≥-Lift 𝑨 a>b = ≥-RESP-≅{𝑨 = 𝑨} a>b Lift-≅

Lift-≤-Lift : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level)
 →            𝑨 ≤ 𝑩 → Lift-Alg 𝑨 ℓᵃ ≤ Lift-Alg 𝑩 ℓᵇ

Lift-≤-Lift ℓᵃ {𝑩} ℓᵇ a<b = ≥-Lift (Lift-Alg 𝑩 ℓᵇ) (≤-Lift 𝑩 a<b)

\end{code}

---------------------------------

<span style="float:left;">[← Base.Subalgebras.Subalgebras](Base.Subalgebras.Base.Subalgebras.html)</span>
<span style="float:right;">[Base.Varieties →](Base.Varieties.html)</span>

{% include UALib.Links.md %}
