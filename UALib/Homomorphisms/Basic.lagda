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

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Algebras.Congruences{𝑆 = 𝑆} public
open import MGS-MLTT using (_≡⟨_⟩_; _∎) public

\end{code}

#### <a id="homomorphisms">Homomorphisms</a>

If `𝑨` and `𝑩` are algebraic structures in the signature `𝑆`, then a **homomorphism** is a function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` from the domain of `𝑨` to the domain of `𝑩` that is compatible (or commutes) with all of the basic operations of the signature; that is, for all `𝑓 : ∣ 𝑆 ∣` and all tuples `𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` with values in `∣ 𝑨 ∣`, the following equality holds:

`h ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝒂)`.

Recall, `h ∘ 𝒂` is the tuple whose i-th component is `h (𝒂 i)`.

To formalize this concept, we first define a type representing the assertion that a function `h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣`, from the domain of `𝑨` to the domain of `𝑩`, *commutes* (or is *compatible*) with an operation 𝑓, interpreted in the algebras `𝑨` and `𝑩`.  Pleasingly, the defining equation of the previous paragraph can be expressed in Agda without any adulteration.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 compatible-op-map : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)
                     (𝑓 : ∣ 𝑆 ∣)(h : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

 compatible-op-map 𝑨 𝑩 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

\end{code}

Note the appearance of the shorthand `∀ 𝑎` in the definition of `compatible-op-map`.  We can get away with this in place of `(𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)` since Agda is able to infer that the `𝑎` here must be a tuple on `∣ 𝑨 ∣` of "length" `∥ 𝑆 ∥ 𝑓` (the arity of `𝑓`).

We now define the type `hom 𝑨 𝑩` of homomorphisms from `𝑨` to `𝑩` by first defining the property `is-homomorphism`.

\begin{code}

 is-homomorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-homomorphism 𝑨 𝑩 g = ∀ (𝑓 : ∣ 𝑆 ∣) → compatible-op-map 𝑨 𝑩 𝑓 g

 hom : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

\end{code}

#### Examples

Here are a few very special examples of homomorphisms. In each case, the function in question commutes with the basic operations of *all* algebras and so, no matter the algebras involved, is always a homomorphism (trivially).

The most obvious example is the identity map.

\begin{code}

module _ {𝓤 : Universe} where

 id-is-hom : {𝑨 : Algebra 𝓤 𝑆} → is-homomorphism 𝑨 𝑨 (𝑖𝑑 ∣ 𝑨 ∣)
 id-is-hom _ _ = 𝓇ℯ𝒻𝓁

 𝒾𝒹 : (A : Algebra 𝓤 𝑆) → hom A A
 𝒾𝒹 _ = (λ x → x) , id-is-hom

\end{code}

Next, perhaps less obvious, are the two compositions of the lift and lower maps defined in the [Prelude.Lifts][] module.

\begin{code}

 open Lift

 lift-is-hom : {𝑨 : Algebra 𝓤 𝑆}{𝓦 : Universe} → is-homomorphism 𝑨 (lift-alg 𝑨 𝓦) lift
 lift-is-hom _ _ = 𝓇ℯ𝒻𝓁

 𝓁𝒾𝒻𝓉 : {𝑨 : Algebra 𝓤 𝑆}{𝓦 : Universe} → hom 𝑨 (lift-alg 𝑨 𝓦)
 𝓁𝒾𝒻𝓉 = (lift , lift-is-hom)

 lower-is-hom : {𝑨 : Algebra 𝓤 𝑆}{𝓦 : Universe} → is-homomorphism (lift-alg 𝑨 𝓦) 𝑨 lower
 lower-is-hom _ _ = 𝓇ℯ𝒻𝓁

 𝓁ℴ𝓌ℯ𝓇 : (𝑨 : Algebra 𝓤 𝑆){𝓦 : Universe} → hom (lift-alg 𝑨 𝓦) 𝑨
 𝓁ℴ𝓌ℯ𝓇 𝑨 = (lower , lower-is-hom{𝑨})

\end{code}




Similarly, we represent **monomorphisms** (injective homomorphisms) and **epimorphisms** (surjective homomorphisms) with the following types.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 is-monomorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × Monic g

 mon : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 mon 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-monomorphism 𝑨 𝑩 g

 is-epimorphism : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × Epic g

 epi : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 epi 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-epimorphism 𝑨 𝑩 g

\end{code}

Finally, it will be convenient to have functions that return the *hom reduct* of an inhabitant of `mon` or `epi`.

\begin{code}

 mon-to-hom : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆} → mon 𝑨 𝑩 → hom 𝑨 𝑩
 mon-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

 epi-to-hom : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆) → epi 𝑨 𝑩 → hom 𝑨 𝑩
 epi-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}




#### <a id="equalizers-in-agda">Equalizers in Agda</a>

Recall, the equalizer of two functions (resp., homomorphisms) `g h : A → B` is the subset of `A` on which the values of the functions `g` and `h` agree.  We define the equalizer of functions and homomorphisms in Agda as follows.

\begin{code}

module _ {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} where

 𝐸 : {𝑩 : Algebra 𝓦 𝑆}(g h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Pred ∣ 𝑨 ∣ 𝓦
 𝐸 g h x = g x ≡ h x

 𝐸hom : (𝑩 : Algebra 𝓦 𝑆)(g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓦
 𝐸hom _ g h x = ∣ g ∣ x ≡ ∣ h ∣ x

\end{code}

We will define subuniverses in the [Subalgebras.Subuniverses] module, but we note here that the equalizer of homomorphisms from `𝑨` to `𝑩` will turn out to be subuniverse of `𝑨`.  Indeed, this is easily proved as follows.

\begin{code}

 𝐸hom-closed : (𝑩 : Algebra 𝓦 𝑆)(g h : hom 𝑨 𝑩)
  →            ∀ 𝑓 a → (∀ x → a x ∈ 𝐸hom 𝑩 g h)
               -----------------------------------------
  →            ∣ g ∣ ((𝑓 ̂ 𝑨) a) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) a)

 𝐸hom-closed 𝑩 g h 𝑓 a p = ∣ g ∣ ((𝑓 ̂ 𝑨) a)   ≡⟨ ∥ g ∥ 𝑓 a ⟩
                           (𝑓 ̂ 𝑩)(∣ g ∣ ∘ a)  ≡⟨ ap (𝑓 ̂ 𝑩)(gfe p) ⟩
                           (𝑓 ̂ 𝑩)(∣ h ∣ ∘ a)  ≡⟨ (∥ h ∥ 𝑓 a)⁻¹ ⟩
                           ∣ h ∣ ((𝑓 ̂ 𝑨) a)   ∎

\end{code}

The typing judgments for the arguments that we left implicit are `𝑓 : ∣ 𝑆 ∣` and `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`


#### <a id="kernels-of-homomorphisms">Kernels of Homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}


open Congruence

module _ {𝓤 𝓦 : Universe} where

 homker-compatible : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
  →                  compatible 𝑨 (KER-rel ∣ h ∣)

 homker-compatible {𝑨} 𝑩 h f {u}{v} Kerhab = γ
  where
  γ : ∣ h ∣ ((f ̂ 𝑨) u)  ≡ ∣ h ∣ ((f ̂ 𝑨) v)
  γ = ∣ h ∣ ((f ̂ 𝑨) u)  ≡⟨ ∥ h ∥ f u ⟩
      (f ̂ 𝑩)(∣ h ∣ ∘ u) ≡⟨ ap (f ̂ 𝑩)(gfe λ x → Kerhab x) ⟩
      (f ̂ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
      ∣ h ∣ ((f ̂ 𝑨) v)  ∎


 homker-equivalence : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
  →                   IsEquivalence (KER-rel ∣ h ∣)

 homker-equivalence 𝑨 h = map-kernel-IsEquivalence ∣ h ∣

\end{code}

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.

\begin{code}

 kercon : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → Congruence 𝑨
 kercon 𝑩 h = mkcon (KER-rel ∣ h ∣)(homker-compatible 𝑩 h)(homker-equivalence 𝑩 h)

\end{code}

From this congruence we construct the corresponding quotient.

\begin{code}

 kerquo : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
 kerquo {𝑨} 𝑩 h = 𝑨 ╱ (kercon 𝑩 h)

 -- NOTATION.
 _[_]/ker_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
 𝑨 [ 𝑩 ]/ker h = kerquo {𝑨} 𝑩 h

 infix 60 _[_]/ker_

\end{code}

Given an algebra `𝑨` and a congruence `θ`, the canonical epimorphism from `𝑨` onto `𝑨 ╱ θ` is defined as follows.

\begin{code}

 πepi : {𝑨 : Algebra 𝓤 𝑆} (θ : Congruence{𝓤}{𝓦} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi {𝑨} θ = cπ , cπ-is-hom , cπ-is-epic where

  cπ : ∣ 𝑨 ∣ → ∣ 𝑨 ╱ θ ∣
  cπ a = ⟦ a ⟧{⟨ θ ⟩}

  cπ-is-hom : is-homomorphism 𝑨 (𝑨 ╱ θ) cπ
  cπ-is-hom _ _ = 𝓇ℯ𝒻𝓁

  cπ-is-epic : Epic cπ
  cπ-is-epic (.(⟨ θ ⟩ a) , a , refl _) = Image_∋_.im a

\end{code}

To obtain the homomorphism part (or "hom reduct") of the canonical epimorphism, we apply `epi-to-hom`.

\begin{code}

 πhom : {𝑨 : Algebra 𝓤 𝑆}(θ : Congruence{𝓤}{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom {𝑨} θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}

We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)

\begin{code}

 πker : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)  →  epi 𝑨 (𝑨 [ 𝑩 ]/ker h)
 πker {𝑨} 𝑩 h = πepi (kercon 𝑩 h)

\end{code}


The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 ker-in-con : (𝑨 : Algebra 𝓤 𝑆)(θ : Congruence{𝓤}{𝓦} 𝑨)(x y : ∣ 𝑨 ∣)
  →           ⟨ kercon (𝑨 ╱ θ) (πhom θ) ⟩ x y  →  ⟨ θ ⟩ x y

 ker-in-con 𝑨 θ x y hyp = ╱-refl θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, an (index) type `I : 𝓘 ̇`, and a family of algebras `ℬ : I → Algebra 𝓦 𝑆`, and
suppose for each `i : I` we have a homomorphism `hs i : hom 𝑨 (ℬ i)`.  We associate with these data a natural homomorphism from `𝑨` to the product `⨅ ℬ`, as follows.

\begin{code}

module _ {𝓤 𝓘 𝓦 : Universe} where

 ⨅-hom-co : {𝑨 : Algebra 𝓤 𝑆}{I : 𝓘 ̇}(ℬ : I → Algebra 𝓦 𝑆)
  →         (∀ i → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)

 ⨅-hom-co ℬ hs = ϕ , ϕhom
  where
  ϕ : _ → ∣ ⨅ ℬ ∣
  ϕ a = λ i → ∣ hs i ∣ a

  ϕhom : is-homomorphism _ (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒶 = gfe λ i → ∥ hs i ∥ 𝑓 (λ x → 𝒶 x)

\end{code}

This generalizes easily to the case in which the domain is also a product of a family of algebras.  That is, given families `𝒜 : I → Algebra 𝓤 𝑆 and ℬ : I → Algebra 𝓦 𝑆`, and assuming `∀ i` there exists a homomorphism `hom (𝒜 i) (ℬ i)`, we construct the corresponding homomorphism from `⨅ 𝒜` to `⨅ ℬ` as follows.

\begin{code}

 ⨅-hom : {I : 𝓘 ̇}(𝒜 : I → Algebra 𝓤 𝑆)(ℬ : I → Algebra 𝓦 𝑆)
  →      (∀ i → hom (𝒜 i)(ℬ i)) → hom (⨅ 𝒜) (⨅ ℬ)

 ⨅-hom 𝒜 ℬ hs = ϕ , ϕhom
  where
  ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
  ϕ = λ x i → ∣ hs i ∣ (x i)

  ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒶 = gfe λ i → ∥ hs i ∥ 𝑓 (λ x → 𝒶 x i)

\end{code}



#### <a id="projection-homomorphisms">Projection homomorphisms</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

\begin{code}

module _ {𝓘 𝓦 : Universe} where

 ⨅-projection-hom : {I : 𝓘 ̇}(ℬ : I → Algebra 𝓦 𝑆) → (i : I) → hom (⨅ ℬ) (ℬ i)

 ⨅-projection-hom ℬ i = ϕi , ϕihom
  where
  ϕi : ∣ ⨅ ℬ ∣ → ∣ ℬ i ∣
  ϕi = λ x → x i

  ϕihom : is-homomorphism (⨅ ℬ) (ℬ i) ϕi
  ϕihom 𝑓 𝒂 = 𝓇ℯ𝒻𝓁

\end{code}

Of course, we could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.



--------------------------------------

[↑ Homomorphisms](Homomorphisms.html)
<span style="float:right;">[Homomorphisms.Noether →](Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}



<!--
θ is contained in the kernel of the canonical projection onto 𝑨 / θ.
con-in-ker : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆) (θ : Congruence{𝓤}{𝓦} 𝑨)
 → ∀ x y → (⟨ θ ⟩ x y) → (⟨ (kercon 𝑨 {𝑨 ╱ θ} (canonical-hom{𝓤}{𝓦} 𝑨 θ)) ⟩ x y)
con-in-ker 𝑨 θ x y hyp = γ
 where
  h : hom 𝑨 (𝑨 ╱ θ)
  h = canonical-hom 𝑨 θ

  κ : Congruence 𝑨
  κ = kercon 𝑨 {𝑨 ╱ θ} h

  γ : ⟦ x ⟧ {⟨ θ ⟩}≡ ⟦ y ⟧{⟨ θ ⟩}
  γ = {!!}
-->



<!-- The definition of homomorphism in the [Agda UALib][] is an *extensional* one; that is, the homomorphism condition holds pointwise. Generally speaking, we say that two functions 𝑓 𝑔 : X → Y are extensionally equal iff they are pointwise equal, that is, for all x : X we have 𝑓 x ≡ 𝑔 x. -->

