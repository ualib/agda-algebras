---
layout: default
title : UALib.Subalgebras.Properties module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subuniverse-lemmas">Subuniverse Lemmas</a>

This section presents the [UALib.Subalgebras.Properties][]  module of the [Agda Universal Algebra Library][].

Here we formalize and prove a few basic properties of subuniverses.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Subalgebras.Properties
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Subalgebras.Generation{𝑆 = 𝑆}{gfe}{𝕏} renaming (generator to ℊ) public
open import Relation.Unary using (⋂) public

sub-inter-is-sub : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)
                   (I : 𝓤 ̇)(𝒜 : I → Pred ∣ 𝑨 ∣ 𝓤)
 →                 ((i : I) → 𝒜 i ∈ Subuniverses 𝑨)
                   --------------------------------
 →                 ⋂ I 𝒜 ∈ Subuniverses 𝑨

sub-inter-is-sub 𝑨 I 𝒜 Ai-is-Sub f a ima⊆⋂A = α
 where
  α : (f ̂ 𝑨) a ∈ ⋂ I 𝒜
  α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i

\end{code}

-------------------------------------------------------

#### <a id="conservativity-of-term-operations">Conservativity of term operations</a>

\begin{code}

sub-term-closed : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →                B ∈ Subuniverses 𝑨  → (t : Term)(b : X → ∣ 𝑨 ∣)
 →                (∀ x → b x ∈ B) → ((t ̇ 𝑨) b) ∈ B

sub-term-closed _ _ B≤A (ℊ x) b b∈B = b∈B x

sub-term-closed 𝑨 B B≤A (node f t) b b∈B =
 B≤A f (λ z → (t z ̇ 𝑨) b) (λ x → sub-term-closed 𝑨 B B≤A (t x) b b∈B)

\end{code}


---------------------------------------------------

#### <a id="term-images">Term images</a>

\begin{code}

data TermImage {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓤) :
 Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤) where
  var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
  app : (f : ∣ 𝑆 ∣) (t : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣)
   →    (∀ i  →  t i ∈ TermImage 𝑨 Y)
        -----------------------------
   →    (f ̂ 𝑨) t ∈ TermImage 𝑨 Y

--1. TermImage is a subuniverse
TermImageIsSub : {𝓠 𝓤 : Universe}
                 {𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
                 ----------------------------------
 →               TermImage 𝑨 Y ∈ Subuniverses 𝑨

TermImageIsSub = app -- λ f a x → app f a x

--2. Y ⊆ TermImageY
Y⊆TermImageY : {𝓠 𝓤 : Universe}
               {𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
               ----------------------------------
 →             Y ⊆ TermImage 𝑨 Y

Y⊆TermImageY {a} a∈Y = var a∈Y

-- 3. Sg^A(Y) is the smallest subuniverse containing Y
--    Proof: see `sgIsSmallest`

SgY⊆TermImageY : {𝓠 𝓤 : Universe}
                 (𝑨 : Algebra 𝓠 𝑆)  (Y : Pred ∣ 𝑨 ∣ 𝓤)
                 ------------------------------------
 →               Sg 𝑨 Y ⊆ TermImage 𝑨 Y

SgY⊆TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y⊆TermImageY

\end{code}

---------------------------------

[← UALib.Subalgebras.Generation](UALib.Subalgebras.Generation.html)
<span style="float:right;">[UALib.Subalgebras.Homomorphisms →](UALib.Subalgebras.Homomorphisms.html)</span>

{% include UALib.Links.md %}
