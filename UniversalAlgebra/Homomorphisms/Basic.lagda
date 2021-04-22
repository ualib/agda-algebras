---
layout: default
title : Homomorphisms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="basic-definitions">Basic Definitions</a>

This section describes the [Homomorphisms.Basic] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Homomorphisms.Basic where

open import Algebras.Congruences public
open import MGS-MLTT using (_≡⟨_⟩_; _∎; id) public

module homomorphisms {𝑆 : Signature 𝓞 𝓥} where
 open congruences {𝑆 = 𝑆} public

\end{code}

#### <a id="homomorphisms">Homomorphisms</a>

If `𝑨` and `𝑩` are `𝑆`-algebras, then a *homomorphism* from `𝑨` to `𝑩` is a function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` from the domain of `𝑨` to the domain of `𝑩` that is *compatible* (or *commutes*) with all of the basic operations of the signature; that is, for all operation symbols `𝑓 : ∣ 𝑆 ∣` and tuples `a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of `𝑨`, the following holds:<sup>[1](Homomorphisms.Basic.html#fn1)</sup>

`h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a)`.

To formalize this concept, we first define a type representing the assertion that a function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` commutes with a single basic operation `𝑓`.  With Agda's extremely flexible syntax the defining equation above can be expressed unadulterated.

\begin{code}

 module _ (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) where

  compatible-op-map : ∣ 𝑆 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
  compatible-op-map 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

\end{code}

Agda infers from the shorthand `∀ 𝑎` that `𝑎` has type `∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` since it must be a tuple on `∣ 𝑨 ∣` of "length" `∥ 𝑆 ∥ 𝑓` (the arity of `𝑓`).

We now define the type `hom 𝑨 𝑩` of homomorphisms from `𝑨` to `𝑩` by first defining the type `is-homomorphism` which represents the property of being a homomorphism.

\begin{code}

  is-homomorphism : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
  is-homomorphism g = ∀ 𝑓  →  compatible-op-map 𝑓 g

  hom : Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
  hom = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism g

\end{code}

#### <a id="exmples-of-homomorphisms">Examples of homomorphisms</a>

Let's look at a few examples of homomorphisms. These examples are actually quite special in that the function in question commutes with the basic operations of *all* algebras and so, no matter the algebras involved, is always a homomorphism (trivially). We begin with the identity map, which is proved to be (the underlying map of) a homomorphism as follows.

\begin{code}

 𝒾𝒹 : (𝑨 : Algebra 𝓤 𝑆) → hom 𝑨 𝑨
 𝒾𝒹 _ = id , λ 𝑓 𝑎 → refl

\end{code}

Next, `lift` and `lower`, defined in the [Overture.Lifts][] module, are (the maps of) homomorphisms.  Again, the proofs are trivial.

\begin{code}

 open Lift

 𝓁𝒾𝒻𝓉 : {𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} → hom 𝑨 (Lift-alg 𝑨 𝓦)
 𝓁𝒾𝒻𝓉 = lift , λ 𝑓 𝑎 → refl

 𝓁ℴ𝓌ℯ𝓇 : {𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} → hom (Lift-alg 𝑨 𝓦) 𝑨
 𝓁ℴ𝓌ℯ𝓇 = lower , λ 𝑓 𝑎 → refl

\end{code}




#### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

A *monomorphism* is an injective homomorphism and an *epimorphism* is a surjective homomorphism. These are represented in the [UniversalAlgebra][] library by the following types.

\begin{code}

 is-monomorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × Monic g

 mon : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 mon 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-monomorphism 𝑨 𝑩 g

 is-epimorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × Epic g

 epi : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
 epi 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-epimorphism 𝑨 𝑩 g

\end{code}

It will be convenient to have a function that takes an inhabitant of `mon` (or `epi`) and extracts the homomorphism part, or *hom reduct* (that is, the pair consisting of the map and a proof that the map is a homomorphism).

\begin{code}

 mon-to-hom : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆} → mon 𝑨 𝑩 → hom 𝑨 𝑩
 mon-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

 epi-to-hom : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆) → epi 𝑨 𝑩 → hom 𝑨 𝑩
 epi-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}






#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}

 module _ {𝓤 𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} where

  homker-compatible : dfunext 𝓥 𝓦 → (𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → compatible 𝑨 (ker ∣ h ∣)
  homker-compatible fe 𝑩 h f {u}{v} Kerhab = ∣ h ∣ ((f ̂ 𝑨) u)   ≡⟨ ∥ h ∥ f u ⟩
                                             (f ̂ 𝑩)(∣ h ∣ ∘ u)  ≡⟨ ap (f ̂ 𝑩)(fe λ x → Kerhab x) ⟩
                                             (f ̂ 𝑩)(∣ h ∣ ∘ v)  ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
                                             ∣ h ∣ ((f ̂ 𝑨) v)   ∎

\end{code}

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.

\begin{code}

  kercon : (𝑩 : Algebra 𝓦 𝑆){fe : dfunext 𝓥 𝓦} → hom 𝑨 𝑩 → Con{𝓦} 𝑨
  kercon 𝑩 {fe} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-compatible fe 𝑩 h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.

\begin{code}

  kerquo : dfunext 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
  kerquo fe {𝑩} h = 𝑨 ╱ (kercon 𝑩 {fe} h)


 _[_]/ker_↾_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → hom 𝑨 𝑩 → dfunext 𝓥 𝓦 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
 𝑨 [ 𝑩 ]/ker h ↾ fe = kerquo fe {𝑩} h

 infix 60 _[_]/ker_↾_

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

\begin{code}

 module _ {𝓤 𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} where
  πepi : (θ : Con{𝓦} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
  πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
   cπ-is-epic : Epic (λ a → ⟪ a ⟫)
   cπ-is-epic (C , (a , refl)) =  Image_∋_.im a

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.

\begin{code}

  πhom : (θ : Con{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
  πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)

\begin{code}

  πker : (𝑩 : Algebra 𝓦 𝑆){fe : dfunext 𝓥 𝓦}(h : hom 𝑨 𝑩) → epi 𝑨 (𝑨 [ 𝑩 ]/ker h ↾ fe)
  πker 𝑩 {fe} h = πepi (kercon 𝑩 {fe} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.

\begin{code}

  open IsCongruence

  ker-in-con : {fe : dfunext 𝓥 (𝓤 ⊔ lsuc 𝓦)}(θ : Con{𝓦} 𝑨)
   →           ∀ {x}{y} → ∣ kercon (𝑨 ╱ θ){fe} (πhom θ) ∣ x y →  ∣ θ ∣ x y

  ker-in-con θ hyp = /-≡ θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra 𝓦 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

\begin{code}

 module _ {𝓘 𝓦 : Level}{I : Type 𝓘}(ℬ : I → Algebra 𝓦 𝑆) where

  ⨅-hom-co : dfunext 𝓘 𝓦 → {𝓤 : Level}(𝑨 : Algebra 𝓤 𝑆) → Π i ꞉ I , hom 𝑨 (ℬ i) → hom 𝑨 (⨅ ℬ)
  ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra 𝓤 𝑆 and ℬ : I → Algebra 𝓦 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

\begin{code}

  ⨅-hom : dfunext 𝓘 𝓦 → {𝓤 : Level}(𝒜 : I → Algebra 𝓤 𝑆) → Π i ꞉ I , hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
  ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

\begin{code}

  ⨅-projection-hom : Π i ꞉ I , hom (⨅ ℬ) (ℬ i)
  ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.



--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">
Recall, `h ∘ 𝒂` is the tuple whose i-th component is `h (𝒂 i)`.</span>

<span class="footnote">Instead of "homomorphism," we sometimes use the nickname "hom" to refer to such a map.</span>


<br>

[↑ Homomorphisms](Homomorphisms.html)
<span style="float:right;">[Homomorphisms.Noether →](Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}









