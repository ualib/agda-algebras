---
layout: default
title : "Homomorphisms.Basic module (The Agda Universal Algebra Library)"
date : "2021-01-13"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic Definitions</a>

This section describes the [Homomorphisms.Basic] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic

module Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Axiom.Extensionality.Propositional
                           using () renaming (Extensionality to funext)
open import Data.Product   using ( _,_ ; Σ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst )
open import Function.Base  using ( _∘_ ; id )
open import Level          using ( Level )
open import Relation.Binary.PropositionalEquality
                           using ( _≡_ ; module ≡-Reasoning ; cong ; refl )

-- Imports from the Agda Universal Algebras Library --------------------------------
open import Overture.Preliminaries using ( _⁻¹ ; ∣_∣ ; ∥_∥)
open import Overture.Inverses      using ( IsInjective ; IsSurjective ; Image_∋_ )
open import Equality.Welldefined   using ( swelldef )
open import Relations.Discrete     using ( ker )
open import Relations.Quotients    using ( ker-IsEquivalence ; _/_ ; ⟪_⟫ ; R-block )
open import Algebras.Congruences {𝑆 = 𝑆} using ( Con ; IsCongruence ; mkcon ; _╱_ ; /-≡ )
open import Algebras.Products    {𝑆 = 𝑆} using ( ⨅ )

private variable α β γ ρ : Level

\end{code}

#### <a id="homomorphisms">Homomorphisms</a>

If `𝑨` and `𝑩` are `𝑆`-algebras, then a *homomorphism* from `𝑨` to `𝑩` is a function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` from the domain of `𝑨` to the domain of `𝑩` that is *compatible* (or *commutes*) with all of the basic operations of the signature; that is, for all operation symbols `𝑓 : ∣ 𝑆 ∣` and tuples `a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of `𝑨`, the following holds:

`h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a)`.

**Remarks**. Recall, `h ∘ 𝒂` is the tuple whose i-th component is `h (𝒂 i)`. Instead of "homomorphism," we sometimes use the nickname "hom" to refer to such a map.

To formalize this concept, we first define a type representing the assertion that a function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` commutes with a single basic operation `𝑓`.  With Agda's extremely flexible syntax the defining equation above can be expressed unadulterated.

\begin{code}

module _ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) where

 compatible-op-map : ∣ 𝑆 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(α ⊔ 𝓥 ⊔ β)
 compatible-op-map 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

\end{code}

Agda infers from the shorthand `∀ 𝑎` that `𝑎` has type `∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` since it must be a tuple on `∣ 𝑨 ∣` of "length" `∥ 𝑆 ∥ 𝑓` (the arity of `𝑓`).

We now define the type `hom 𝑨 𝑩` of homomorphisms from `𝑨` to `𝑩` by first defining the type `is-homomorphism` which represents the property of being a homomorphism.

\begin{code}

 is-homomorphism : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 is-homomorphism g = ∀ 𝑓  →  compatible-op-map 𝑓 g

 hom : Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 hom = Σ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) is-homomorphism

\end{code}


#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

\begin{code}

open ≡-Reasoning

module _ (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆) where

  ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
  ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal where

   Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)
   Goal 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a)     ≡⟨ cong h ( ghom 𝑓 a ) ⟩
              h ((𝑓 ̂ 𝑩)(g ∘ a))     ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
              (𝑓 ̂ 𝑪)(h ∘ g ∘ a)     ∎


  ∘-is-hom : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
   →         is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g → is-homomorphism 𝑨 𝑪 (g ∘ f)
  ∘-is-hom {f} {g} fhom ghom = ∥ ∘-hom (f , fhom) (g , ghom) ∥

\end{code}



#### <a id="important-exmples-of-homomorphisms">Important examples of homomorphisms</a>

Let's look at a few important examples of homomorphisms. These examples are actually quite special in that every algebra has such a homomorphism.

We begin with the identity map, which is proved to be (the underlying map of) a homomorphism as follows.

\begin{code}

𝒾𝒹 : (𝑨 : Algebra α 𝑆) → hom 𝑨 𝑨
𝒾𝒹 _ = id , λ 𝑓 𝑎 → refl

\end{code}

Next, the lifting of an algebra to a higher universe level is, in fact, a homomorphism. Dually, the lowering of a lifted algebra to its original universe level is a homomorphism.

\begin{code}

open Level

𝓁𝒾𝒻𝓉 : {β : Level}(𝑨 : Algebra α 𝑆) → hom 𝑨 (Lift-Alg 𝑨 β)
𝓁𝒾𝒻𝓉 _ = lift , λ 𝑓 𝑎 → refl

𝓁ℴ𝓌ℯ𝓇 : {β : Level}(𝑨 : Algebra α 𝑆) → hom (Lift-Alg 𝑨 β) 𝑨
𝓁ℴ𝓌ℯ𝓇 _ = lower , λ 𝑓 𝑎 → refl

\end{code}

Finally, a homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

\begin{code}

Lift-hom : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆} (ℓᵇ : Level)
 →         hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)

Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
 where
 lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
 lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → refl) fhom

 Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
 Goal = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ){f ∘ lower}{lift} lABh λ _ _ → refl

\end{code}

We should probably point out that while the lifting and lowering homomorphisms are important for our formal treatment of algebras in type theory, they never arise---in fact, they are not even definable---in classical universal algebra based on set theory.


#### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

A *monomorphism* is an injective homomorphism and an *epimorphism* is a surjective homomorphism. These are represented in the [agda-algebras](https://github.com/ualib/agda-algebras) library by the following types.

\begin{code}

is-monomorphism : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsInjective g

mon : Algebra α 𝑆 → Algebra β 𝑆  → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
mon 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-monomorphism 𝑨 𝑩 g

is-epimorphism : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

epi : Algebra α 𝑆 → Algebra β 𝑆  → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
epi 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epimorphism 𝑨 𝑩 g

\end{code}

It will be convenient to have a function that takes an inhabitant of `mon` (or `epi`) and extracts the homomorphism part, or *hom reduct* (that is, the pair consisting of the map and a proof that the map is a homomorphism).

\begin{code}

mon-to-hom : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆} → mon 𝑨 𝑩 → hom 𝑨 𝑩
mon-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

epi-to-hom : {𝑨 : Algebra α 𝑆}(𝑩 : Algebra β 𝑆) → epi 𝑨 𝑩 → hom 𝑨 𝑩
epi-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}






#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}

module _ {α β : Level}{𝑨 : Algebra α 𝑆} where

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
  cπ-is-epic (C , R-block a refl ) =  Image_∋_.eq a refl

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.

\begin{code}

 πhom : (θ : Con{α}{β} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

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



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

\begin{code}

module _ {𝓘 β : Level}{I : Type 𝓘}(ℬ : I → Algebra β 𝑆) where

 ⨅-hom-co : funext 𝓘 β → {α : Level}(𝑨 : Algebra α 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra α 𝑆 and ℬ : I → Algebra β 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

\begin{code}

 ⨅-hom : funext 𝓘 β → {α : Level}(𝒜 : I → Algebra α 𝑆) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}


#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

\begin{code}

 ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.

---------------------------------

<span style="float:left;">[↑ Homomorphisms](Homomorphisms.html)</span>
<span style="float:right;">[Homomorphisms.Noether →](Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}
