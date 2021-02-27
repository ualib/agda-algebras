---
layout: default
title : Subalgebras.Subuniverses module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subuniverses">Subuniverses</a>

This section presents the [Subalgebras.Subuniverses][] module of the [Agda Universal Algebra Library][].

We start by defining a type that represents the important concept of **subuniverse**. Suppose 𝑨 is an algebra.  A subset B ⊆ ∣ 𝑨 ∣ is said to be **closed under the operations of** 𝑨 if for each 𝑓 ∈ ∣ 𝑆 ∣ and all tuples 𝒃 : ∥ 𝑆 ∥ 𝑓 → 𝐵 the element (𝑓 ̂ 𝑨) 𝒃 belongs to B. If a subset B ⊆ 𝐴 is closed under the operations of 𝑨, then we call B a **subuniverse** of 𝑨.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Subalgebras.Subuniverses {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Terms.Operations{𝑆 = 𝑆}{gfe} public

\end{code}

We first show how to represent in [Agda][] the collection of subuniverses of an algebra A.  Since a subuniverse is viewed as a subset of the domain of A, we define it as a predicate on ∣ A ∣.  Thus, the collection of subuniverses is a predicate on predicates on ∣ A ∣.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 Subuniverses : (𝑨 : Algebra 𝓤 𝑆) → Pred (Pred ∣ 𝑨 ∣ 𝓦)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 Subuniverses 𝑨 B = (𝑓 : ∣ 𝑆 ∣)(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) → Im 𝑎 ⊆ B → (𝑓 ̂ 𝑨) 𝑎 ∈ B

\end{code}

-----------------------------------------

[The remaining definitions in this module are not be needed for the proof of Birkhoff's theorem.]


Here is how one could construct an algebra out of a subuniverse.

\begin{code}

 SubunivAlg : (𝑨 : Algebra 𝓤 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓦)
  →           B ∈ Subuniverses 𝑨 → Algebra (𝓤 ⊔ 𝓦) 𝑆

 SubunivAlg 𝑨 B B∈SubA = Σ B , λ 𝑓 𝑏 → (𝑓 ̂ 𝑨)(fst ∘ 𝑏) , B∈SubA 𝑓 (fst ∘ 𝑏)(snd ∘ 𝑏)

\end{code}



#### <a id="subuniverses-as-records">Subuniverses as records</a>

We could define the type of subuniverses as a record as follows.

\begin{code}

 record Subuniverse {𝑨 : Algebra 𝓤 𝑆} : ov (𝓤 ⊔ 𝓦) ̇ where
  constructor mksub
  field
    sset  : Pred ∣ 𝑨 ∣ 𝓦
    isSub : sset ∈ Subuniverses 𝑨

\end{code}

For example, we could use such a type to prove that the equalizer of two homomorphisms is a subuniverse.

\begin{code}

 𝑬𝑯-is-subuniverse : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)
                     (g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}

 𝑬𝑯-is-subuniverse 𝑩 g h = mksub (𝑬𝑯 𝑩 g h) λ 𝑓 𝒂 x → 𝑬𝑯-closed 𝑩 g h 𝑓 𝒂 x

\end{code}

-------------------------------

[↑ Subalgebras](Subalgebras.html)
<span style="float:right;">[Subalgebras.Generation →](Subalgebras.Generation.html)</span>

{% include UALib.Links.md %}
