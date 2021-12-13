---
layout: default
title : "Base.Homomorphisms.Kernels module (The Agda Universal Algebra Library)"
date : "2021-09-08"
author: "agda-algebras development team"
---

### <a id="kernels-of-homomorphisms">Kernels of Homomorphisms</a>

This is the [Base.Homomorphisms.Kernels] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic

module Base.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc )
open import Data.Product   using ( _,_ )
open import Function.Base  using ( _∘_ )
open import Level          using ( Level )
open import Relation.Binary.PropositionalEquality
                           using ( _≡_ ; module ≡-Reasoning ; refl )

-- -- Imports from the Agda Universal Algebras Library --------------------------------
open import Base.Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Overture.Inverses            using ( Image_∋_ )
open import Base.Overture.Surjective          using ( IsSurjective )
open import Base.Equality.Welldefined         using ( swelldef )
open import Base.Relations.Discrete           using ( ker )
open import Base.Relations.Quotients          using ( ker-IsEquivalence ; ⟪_⟫ ; mkblk )
open import Base.Algebras.Congruences {𝑆 = 𝑆} using ( Con ; mkcon ; _╱_ ; IsCongruence ; /-≡ )
open import Base.Homomorphisms.Basic  {𝑆 = 𝑆} using ( hom ; epi ; epi→hom )

private variable α β : Level

\end{code}


#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}

module _ {𝑨 : Algebra α 𝑆} where
 open ≡-Reasoning
 homker-comp : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆}(h : hom 𝑨 𝑩) → compatible 𝑨 (ker ∣ h ∣)
 homker-comp wd {𝑩} h f {u}{v} kuv = ∣ h ∣((f ̂ 𝑨) u)   ≡⟨ ∥ h ∥ f u ⟩
                                     (f ̂ 𝑩)(∣ h ∣ ∘ u) ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
                                     (f ̂ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
                                     ∣ h ∣((f ̂ 𝑨) v)   ∎


\end{code}

(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.

\begin{code}

 kercon : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆} → hom 𝑨 𝑩 → Con{α}{β} 𝑨
 kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.

\begin{code}

 kerquo : swelldef 𝓥 β → {𝑩 : Algebra β 𝑆} → hom 𝑨 𝑩 → Algebra (α ⊔ lsuc β) 𝑆
 kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)


ker[_⇒_]_↾_ : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → hom 𝑨 𝑩 → swelldef 𝓥 β → Algebra (α ⊔ lsuc β) 𝑆
ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [agda-algebras](https://github.com/ualib/agda-algebras) library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

\begin{code}

module _ {α β : Level}{𝑨 : Algebra α 𝑆} where
 πepi : (θ : Con{α}{β} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
  cπ-is-epic (C , mkblk a refl ) =  Image_∋_.eq a refl

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.

\begin{code}

 πhom : (θ : Con{α}{β} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi→hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)

\begin{code}

 πker : (wd : swelldef 𝓥 β){𝑩 : Algebra β 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.

\begin{code}

 open IsCongruence

 ker-in-con : {wd : swelldef 𝓥 (α ⊔ lsuc β)}(θ : Con 𝑨)
  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

\end{code}

---------------------------------

<span style="float:left;">[← Base.Homomorphisms.Properties](Base.Homomorphisms.Properties.html)</span>
<span style="float:right;">[Base.Homomorphisms.Products →](Base.Homomorphisms.Products.html)</span>

{% include UALib.Links.md %}
