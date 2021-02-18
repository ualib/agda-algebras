---
layout: default
title : UALib.Subalgebras.Subuniverses module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subuniverse-type">Subuniverse Type</a>

This section presents the [UALib.Subalgebras.Subuniverses][] module of the [Agda Universal Algebra Library][].

We show how to represent in Agda subuniverses of a given algebra or a given collection of algebras.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)

open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Subalgebras.Subuniverses
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Terms.Compatibility{𝑆 = 𝑆}{gfe}{𝕏} public


Subuniverses : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆) → Pred (Pred ∣ 𝑨 ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤)
Subuniverses 𝑨 B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → Im a ⊆ B → (f ̂ 𝑨) a ∈ B

\end{code}

-----------------------------------------

[The remaining definitions in this module are not be needed for the proof of Birkhoff's theorem.]


Here is how one could construct an algebra out of a subuniverse.

\begin{code}

SubunivAlg : {𝓠 𝓤 : Universe} (𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →           B ∈ Subuniverses 𝑨
 →           Algebra (𝓠 ⊔ 𝓤) 𝑆
SubunivAlg 𝑨 B B∈SubA = Σ B , λ f x → (f ̂ 𝑨)(∣_∣ ∘ x) , B∈SubA f (∣_∣ ∘ x)(∥_∥ ∘ x)

\end{code}

-----------------------------------------

#### <a id="subuniverses-as-records">Subuniverses as records</a>

We could define the type of subuniverses as a record as follows.

\begin{code}

record Subuniverse {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆} : 𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇ where
 constructor mksub
 field
   sset  : Pred ∣ 𝑨 ∣ 𝓤
   isSub : sset ∈ Subuniverses 𝑨

\end{code}

For example, we could use such a type to prove that the equalizer of two homomorphisms is a subuniverse.

\begin{code}

𝑬𝑯-is-subuniverse : {𝓤 𝓦 : Universe} → funext 𝓥 𝓦 →
                    {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
                    (g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}

𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h = mksub (𝑬𝑯 {𝑩 = 𝑩} g h) λ 𝑓 𝒂 x → 𝑬𝑯-closed {𝑨 = 𝑨}{𝑩 = 𝑩}fe g h 𝑓 𝒂 x

\end{code}

-------------------------------

[↑ UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Subalgebras.Generation →](UALib.Subalgebras.Generation.html)</span>

{% include UALib.Links.md %}
