---
layout: default
title : UALib.Terms.Free module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="the-term-algebra">The Term Algebra</a>

This section presents the [UALib.Terms.Free][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Terms.Free
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Terms.Basic{𝑆 = 𝑆}{gfe}{𝕏} hiding (Algebra) public

\end{code}

Terms can be viewed as acting on other terms and we can form an algebraic structure whose domain and basic operations are both the collection of term operations. We call this the **term algebra** and it by `𝑻 X`. In [Agda][] the term algebra is defined as simply as one would hope.

\begin{code}

--The term algebra 𝑻 X.
𝑻 : {𝓧 : Universe}(X : 𝓧 ̇) → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺) 𝑆
𝑻 {𝓧} X = Term{𝓧}{X} , node

\end{code}

-------------------------------------------

#### <a id="the-universal-property">The universal property</a>

The Term algebra is *absolutely free*, or *universal*, for algebras in the signature 𝑆. That is, for every 𝑆-algebra 𝑨,

1.  every map `h : 𝑋 → ∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to 𝑨, and
2.  the induced homomorphism is unique.

\begin{code}

--1.a. Every map (X → 𝑨) lifts.
free-lift : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)
 →          ∣ 𝑻 X ∣ → ∣ 𝑨 ∣

free-lift _ h (generator x) = h x
free-lift 𝑨 h (node f args) = (f ̂ 𝑨) λ i → free-lift 𝑨 h (args i)

--1.b. The lift is (extensionally) a hom
lift-hom : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣)
 →         hom (𝑻 X) 𝑨

lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → ap (_ ̂ 𝑨) 𝓇ℯ𝒻𝓁

--2. The lift to (free → 𝑨) is (extensionally) unique.
free-unique : {𝓧 𝓤 : Universe}{X : 𝓧 ̇} → funext 𝓥 𝓤
 →            (𝑨 : Algebra 𝓤 𝑆)(g h : hom (𝑻 X) 𝑨)
 →            (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
 →            (t : Term{𝓧}{X})
             ---------------------------
 →            ∣ g ∣ t ≡ ∣ h ∣ t

free-unique _ _ _ _ p (generator x) = p x
free-unique fe 𝑨 g h p (node f args) =
   ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
   (f ̂ 𝑨)(λ i → ∣ g ∣ (args i))  ≡⟨ ap (_ ̂ 𝑨) γ ⟩
   (f ̂ 𝑨)(λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
   ∣ h ∣ (node f args)             ∎
   where γ = fe λ i → free-unique fe 𝑨 g h p (args i)

\end{code}

-------------------------------------------------

#### <a id="lifting-and-imaging-tools">Lifting and imaging tools</a>

Next we note the easy fact that the lift induced by `h₀` agrees with `h₀` on `X` and that the lift is surjective if `h₀` is.

\begin{code}

lift-agrees-on-X : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)(x : X)
        ----------------------------------------
 →       h₀ x ≡ ∣ lift-hom 𝑨 h₀ ∣ (generator x)

lift-agrees-on-X _ h₀ x = 𝓇ℯ𝒻𝓁

lift-of-epi-is-epi : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)(h₀ : X → ∣ 𝑨 ∣)
 →                    Epic h₀
                     ----------------------
 →                    Epic ∣ lift-hom 𝑨 h₀ ∣

lift-of-epi-is-epi {𝓧}{𝓤}{X} 𝑨 h₀ hE y = γ
 where
  h₀pre : Image h₀ ∋ y
  h₀pre = hE y

  h₀⁻¹y : X
  h₀⁻¹y = Inv h₀ y (hE y)

  η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (generator h₀⁻¹y)
  η =
   y                                 ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
   h₀ h₀⁻¹y                          ≡⟨ lift-agrees-on-X 𝑨 h₀ h₀⁻¹y ⟩
   ∣ lift-hom 𝑨 h₀ ∣ (generator h₀⁻¹y) ∎

  γ : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
  γ = eq y (generator h₀⁻¹y) η

\end{code}

Since it's absolutely free, 𝑻 X is the domain of a homomorphism to any algebra we like. The following function makes it easy to lay our hands on such homomorphisms when necessary.

\begin{code}

𝑻hom-gen : {𝓧 𝓤 : Universe}{X : 𝓧 ̇} (𝑪 : Algebra 𝓤 𝑆)
 →         Σ h ꞉ (hom (𝑻 X) 𝑪), Epic ∣ h ∣
𝑻hom-gen {𝓧}{𝓤}{X} 𝑪 = h , lift-of-epi-is-epi 𝑪 h₀ hE
 where
  h₀ : X → ∣ 𝑪 ∣
  h₀ = fst (𝕏 𝑪)

  hE : Epic h₀
  hE = snd (𝕏 𝑪)

  h : hom (𝑻 X) 𝑪
  h = lift-hom 𝑪 h₀

\end{code}

--------------------------------------

[← UALib.Terms.Basic](UALib.Terms.Basic.html)
<span style="float:right;">[UALib.Terms.Operations →](UALib.Terms.Operations.html)</span>

{% include UALib.Links.md %}



<!-- term-op : {𝓧 : Universe}{X : 𝓧 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓧}{X} ) → Term
term-op f args = node f args -->

