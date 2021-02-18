---
layout: default
title : UALib.Homomorphisms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="basic-definitions">Basic Definitions</a>

This section describes the [UALib.Homomorphisms.Basic] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)

module UALib.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import UALib.Algebras.Congruences{𝑆 = 𝑆} public
open import UALib.Prelude.Preliminaries using (_≡⟨_⟩_; _∎) public

\end{code}

The definition of homomorphism in the \agdaualib is an *extensional* one; that is, the homomorphism condition holds pointwise.  This will become clearer once we have the formal definitions in hand.  Generally speaking, though, we say that two functions 𝑓 𝑔 : X → Y are extensionally equal iff they are pointwise equal, that is, for all x : X we have 𝑓 x ≡ 𝑔 x.

To define **homomorphism**, we first say what it means for an operation 𝑓, interpreted in the algebras 𝑨 and 𝑩, to commute with a function 𝑔 : ∣ 𝑨 ∣ → ∣ 𝑩 ∣, from the domain of 𝑨 to the domain of 𝑩.

\begin{code}

compatible-op-map : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑓 : ∣ 𝑆 ∣)(g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇

compatible-op-map 𝑨 𝑩 𝑓 g = ∀ 𝒂 → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)

\end{code}

Note the appearance of the shorthand `∀ 𝒂` in the definition of `compatible-op-map`.  We can get away with this in place of `(𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)` since Agda is able to infer that the `𝒂` here must be a tuple on ∣ 𝑨 ∣ of "length" `∥ 𝑆 ∥ 𝑓` (the arity of 𝑓).

We now define the type `hom 𝑨 𝑩` of homomorphisms from 𝑨 to 𝑩 by first defining the property `is-homomorphism` as follows.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 is-homomorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-homomorphism 𝑨 𝑩 g = ∀ (𝑓 : ∣ 𝑆 ∣) → compatible-op-map 𝑨 𝑩 𝑓 g

 hom : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

\end{code}

Similarly, we represent **monomorphisms** (injective homomorphisms) and **epimorphisms** (surjective homomorphisms) with the following types.

\begin{code}

 is-monomorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × Monic g

 mon : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 mon 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-monomorphism 𝑨 𝑩 g

 is-epimorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × Epic g

 epi : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 epi 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-epimorphism 𝑨 𝑩 g

\end{code}

Finally, it will be convenient to have functions that return the "hom reduct" of a mon or epi.

\begin{code}

 mon-to-hom : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆} → mon 𝑨 𝑩 → hom 𝑨 𝑩
 mon-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

 epi-to-hom : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆) → epi 𝑨 𝑩 → hom 𝑨 𝑩
 epi-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}



#### <a id="examples">Examples</a>

A simple example is the identity map, which is proved to be a homomorphism as follows.

\begin{code}

𝒾𝒹 : {𝓤 : Universe} (A : Algebra 𝓤 𝑆) → hom A A
𝒾𝒹 _ = (λ x → x) , λ _ _ → 𝓇ℯ𝒻𝓁

id-is-hom : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → is-homomorphism 𝑨 𝑨 (𝑖𝑑 ∣ 𝑨 ∣)
id-is-hom = λ _ _ → 𝓇ℯ𝒻𝓁

\end{code}




#### <a id="equalizers-in-agda">Equalizers in Agda</a>

Recall, the equalizer of two functions (resp., homomorphisms) `g h : A → B` is the subset of `A` on which the values of the functions `g` and `h` agree.  We define the equalizer of functions and homomorphisms in Agda as follows.

\begin{code}

module _ {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} where

 𝑬 : (g h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Pred ∣ 𝑨 ∣ 𝓦
 𝑬 g h x = g x ≡ h x

 𝑬𝑯 : (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓦
 𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x

\end{code}

We will define subuniverses in the [UALib.Subalgebras.Subuniverses] module, but we note here that the equalizer of homomorphisms from 𝑨 to 𝑩 will turn out to be subuniverse of 𝑨.  Indeed, this is easily proved as follows.

\begin{code}

 𝑬𝑯-closed : funext 𝓥 𝓦 →
             (g h : hom 𝑨 𝑩) (𝑓 : ∣ 𝑆 ∣) (𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)
   →         ( ∀ x → (𝒂 x) ∈ 𝑬𝑯 g h )
             ---------------------------------
   →         ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

 𝑬𝑯-closed fe g h 𝑓 𝒂 p = ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)   ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
                          (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (𝑓 ̂ 𝑩)(fe p) ⟩
                          (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
                          ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)   ∎

\end{code}

--------------------------------------

[↑ UALib.Homomorphisms](UALib.Homomorphisms.html)
<span style="float:right;">[UALib.Homomorphisms.Kernels →](UALib.Homomorphisms.Kernels.html)</span>

{% include UALib.Links.md %}
