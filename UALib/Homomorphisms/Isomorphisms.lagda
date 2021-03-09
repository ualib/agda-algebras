---
layout: default
title : Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="isomorphisms">Isomorphisms</a>

This section describes the [Homomorphisms.Isomorphisms][] module of the [Agda Universal Algebra Library][].
Here we formalize the informal notion of isomorphism between algebraic structures.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Homomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Homomorphisms.Noether{𝑆 = 𝑆}{gfe} public
open import MGS-Embeddings using (Nat; NatΠ; NatΠ-is-embedding) public

\end{code}

#### <a id="isomorphism-toolbox">Definition of isomorphism</a>

Recall, `f ~ g` means f and g are *extensionally* (or pointwise) equal; i.e., `∀ x, f x ≡ g x`. We use this notion of equality of functions in the following definition of **isomorphism**.

\begin{code}

_≅_ : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , (∣ f ∣ ∘ ∣ g ∣ ∼ ∣ 𝒾𝒹 ∣)
                                           × (∣ g ∣ ∘ ∣ f ∣ ∼ ∣ 𝒾𝒹 ∣)

\end{code}

That is, two structures are **isomorphic** provided there are homomorphisms going back and forth between them which compose to the identity map.


#### <a id="isomorphism-toolbox">Isomorphism toolbox</a>

Here we collect some tools that will come in handy later on.  The reader is invited to skip over this section and return to it as needed.

\begin{code}

module _ {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆} where

 ≅-hom : (ϕ : 𝑨 ≅ 𝑩) → hom 𝑨 𝑩
 ≅-hom ϕ = ∣ ϕ ∣

 ≅-inv-hom : (ϕ : 𝑨 ≅ 𝑩) → hom 𝑩 𝑨
 ≅-inv-hom ϕ = fst ∥ ϕ ∥

 ≅-map : (ϕ : 𝑨 ≅ 𝑩) → ∣ 𝑨 ∣ → ∣ 𝑩 ∣
 ≅-map ϕ = ∣ ≅-hom ϕ ∣

 ≅-map-is-homomorphism : (ϕ : 𝑨 ≅ 𝑩) → is-homomorphism 𝑨 𝑩 (≅-map ϕ)
 ≅-map-is-homomorphism ϕ = ∥ ≅-hom ϕ ∥

 ≅-inv-map : (ϕ : 𝑨 ≅ 𝑩) → ∣ 𝑩 ∣ → ∣ 𝑨 ∣
 ≅-inv-map ϕ = ∣ ≅-inv-hom ϕ ∣

 ≅-inv-map-is-hom : (ϕ : 𝑨 ≅ 𝑩) → is-homomorphism 𝑩 𝑨 (≅-inv-map ϕ)
 ≅-inv-map-is-hom ϕ = ∥ ≅-inv-hom ϕ ∥

 ≅-map-invertible : (ϕ : 𝑨 ≅ 𝑩) → invertible (≅-map ϕ)
 ≅-map-invertible ϕ = (≅-inv-map ϕ) , (∥ snd ∥ ϕ ∥ ∥ , ∣ snd ∥ ϕ ∥ ∣)

 ≅-map-is-equiv : (ϕ : 𝑨 ≅ 𝑩) → is-equiv (≅-map ϕ)
 ≅-map-is-equiv ϕ = invertibles-are-equivs (≅-map ϕ) (≅-map-invertible ϕ)

 ≅-map-is-embedding : (ϕ : 𝑨 ≅ 𝑩) → is-embedding (≅-map ϕ)
 ≅-map-is-embedding ϕ = equivs-are-embeddings (≅-map ϕ) (≅-map-is-equiv ϕ)

\end{code}



#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}

refl-≅ : {𝓤 : Universe} {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ 𝑨
refl-≅  = 𝒾𝒹 , 𝒾𝒹 , (λ a → 𝓇ℯ𝒻𝓁) , (λ a → 𝓇ℯ𝒻𝓁)

sym-≅ : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
sym-≅ h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

module _ {𝓧 𝓨 𝓩 : Universe} where

 trans-≅ : {𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
  →        𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≅ 𝑪

 trans-≅ {𝑨}{𝑩}{𝑪} ab bc = f , g , α , β
  where
  f1 : hom 𝑨 𝑩
  f1 = ∣ ab ∣
  f2 : hom 𝑩 𝑪
  f2 = ∣ bc ∣
  f : hom 𝑨 𝑪
  f = HCompClosed 𝑨 𝑩 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = fst ∥ bc ∥
  g2 : hom 𝑩 𝑨
  g2 = fst ∥ ab ∥
  g : hom 𝑪 𝑨
  g = HCompClosed 𝑪 𝑩 𝑨 g1 g2

  f1∼g2 : ∣ f1 ∣ ∘ ∣ g2 ∣ ∼ ∣ 𝒾𝒹 ∣
  f1∼g2 = ∣ snd ∥ ab ∥ ∣

  g2∼f1 : ∣ g2 ∣ ∘ ∣ f1 ∣ ∼ ∣ 𝒾𝒹 ∣
  g2∼f1 = ∥ snd ∥ ab ∥ ∥

  f2∼g1 : ∣ f2 ∣ ∘ ∣ g1 ∣ ∼ ∣ 𝒾𝒹 ∣
  f2∼g1 =  ∣ snd ∥ bc ∥ ∣

  g1∼f2 : ∣ g1 ∣ ∘ ∣ f2 ∣ ∼ ∣ 𝒾𝒹 ∣
  g1∼f2 = ∥ snd ∥ bc ∥ ∥

  α : ∣ f ∣ ∘ ∣ g ∣ ∼ ∣ 𝒾𝒹 ∣
  α x = (∣ f ∣ ∘ ∣ g ∣) x                   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        ∣ f2 ∣((∣ f1 ∣ ∘ ∣ g2 ∣)(∣ g1 ∣ x)) ≡⟨ ap ∣ f2 ∣(f1∼g2(∣ g1 ∣ x))⟩
        (∣ f2 ∣ ∘ ∣ g1 ∣) x                  ≡⟨ f2∼g1 x ⟩
        ∣ 𝒾𝒹 ∣ x                         ∎

  β : ∣ g ∣ ∘ ∣ f ∣ ∼ ∣ 𝒾𝒹 ∣
  β x = (ap ∣ g2 ∣ (g1∼f2 (∣ f1 ∣ x))) ∙ g2∼f1 x

\end{code}



#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an "algebraic invariant"), which is why it's a workable solution to the "level hell" problem we mentioned earlier.

\begin{code}

open Lift

module _ {𝓤 𝓦 : Universe} where

 lift-alg-≅ : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ (lift-alg 𝑨 𝓦)
 lift-alg-≅ = (lift , λ _ _ → 𝓇ℯ𝒻𝓁), (lower , λ _ _ → 𝓇ℯ𝒻𝓁), (λ _ → 𝓇ℯ𝒻𝓁), (λ _ → 𝓇ℯ𝒻𝓁)

 lift-alg-hom : (𝓧 : Universe)(𝓨 : Universe)
                {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)
                ----------------------------------------------
  →             hom 𝑨 𝑩  →  hom (lift-alg 𝑨 𝓧) (lift-alg 𝑩 𝓨)

 lift-alg-hom 𝓧 𝓨 {𝑨} 𝑩 (f , fhom) = lift ∘ f ∘ lower , γ
  where
  lh : is-homomorphism (lift-alg 𝑨 𝓧) 𝑨 lower
  lh _ _ = 𝓇ℯ𝒻𝓁

  lABh : is-homomorphism (lift-alg 𝑨 𝓧) 𝑩 (f ∘ lower)
  lABh = ∘-hom (lift-alg 𝑨 𝓧) 𝑨 𝑩 {lower}{f} lh fhom

  Lh : is-homomorphism 𝑩 (lift-alg 𝑩 𝓨) lift
  Lh _ _ = 𝓇ℯ𝒻𝓁

  γ : is-homomorphism(lift-alg 𝑨 𝓧)(lift-alg 𝑩 𝓨) (lift ∘ (f ∘ lower))
  γ = ∘-hom (lift-alg 𝑨 𝓧) 𝑩 (lift-alg 𝑩 𝓨){f ∘ lower}{lift} lABh Lh


lift-alg-iso : {𝓧 : Universe}{𝓨 : Universe}{𝓩 : Universe}{𝓦 : Universe}
               {𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}
               -----------------------------------------
 →             𝑨 ≅ 𝑩 → (lift-alg 𝑨 𝓩) ≅ (lift-alg 𝑩 𝓦)

lift-alg-iso A≅B = trans-≅ (trans-≅ (sym-≅ lift-alg-≅) A≅B) lift-alg-≅

\end{code}



#### <a id="lift-associativity">Lift associativity</a>

The lift is also associative, up to isomorphism at least.

\begin{code}

module _ {𝓘 𝓤 𝓦 : Universe} where

 lift-alg-assoc : {𝑨 : Algebra 𝓤 𝑆} → lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
 lift-alg-assoc = trans-≅ (trans-≅ (sym-≅ lift-alg-≅) lift-alg-≅) lift-alg-≅

 lift-alg-associative : (𝑨 : Algebra 𝓤 𝑆) → lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
 lift-alg-associative 𝑨 = lift-alg-assoc {𝑨}

\end{code}

#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

\begin{code}

module _ {𝓘 𝓤 𝓦 : Universe} where

 ⨅≅ : global-dfunext → {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓤 𝑆}{ℬ : I → Algebra 𝓦 𝑆}
  →                     (∀ i → 𝒜 i ≅ ℬ i)  →  ⨅ 𝒜 ≅ ⨅ ℬ

 ⨅≅ gfe {I}{𝒜}{ℬ} AB = γ
  where
   F : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣
   F i = ∣ fst (AB i) ∣
   Fhom : ∀ i → is-homomorphism (𝒜 i) (ℬ i) (F i)
   Fhom i = ∥ fst (AB i) ∥

   G : ∀ i → ∣ ℬ i ∣ → ∣ 𝒜 i ∣
   G i = fst ∣ snd (AB i) ∣
   Ghom : ∀ i → is-homomorphism (ℬ i) (𝒜 i) (G i)
   Ghom i = snd ∣ snd (AB i) ∣

   F∼G : ∀ i → (F i) ∘ (G i) ∼ (∣ 𝒾𝒹 ∣)
   F∼G i = fst ∥ snd (AB i) ∥

   G∼F : ∀ i → (G i) ∘ (F i) ∼ (∣ 𝒾𝒹 ∣)
   G∼F i = snd ∥ snd (AB i) ∥

   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = F i (a i)

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 𝒂 = gfe (λ i → (Fhom i) 𝑓 (λ x → 𝒂 x i))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = gfe (λ i → (Ghom i) 𝑓 (λ x → 𝒃 x i))

   ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 ∣
   ϕ~ψ 𝒃 = gfe λ i → F∼G i (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹 ∣
   ψ~ϕ 𝒂 = gfe λ i → G∼F i (𝒂 i)

   γ : ⨅ 𝒜 ≅ ⨅ ℬ
   γ = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

\end{code}

A nearly identical proof goes through for isomorphisms of lifted products.


\begin{code}

module _ {𝓘 𝓤 𝓦 𝓩 : Universe} where

 lift-alg-⨅≅ : global-dfunext → {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓤 𝑆}
                                  {ℬ : (Lift{𝓩} I) → Algebra 𝓦 𝑆}
   →                              (∀ i → 𝒜 i ≅ ℬ (lift i))
                                  -------------------------------
   →                              lift-alg (⨅ 𝒜) 𝓩 ≅ ⨅ ℬ

 lift-alg-⨅≅ gfe {I}{𝒜}{ℬ} AB = γ
  where
   F : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ (lift i) ∣
   F i = ∣ fst (AB i) ∣
   Fhom : ∀ i → is-homomorphism (𝒜 i) (ℬ (lift i)) (F i)
   Fhom i = ∥ fst (AB i) ∥

   G : ∀ i → ∣ ℬ (lift i) ∣ → ∣ 𝒜 i ∣
   G i = fst ∣ snd (AB i) ∣
   Ghom : ∀ i → is-homomorphism (ℬ (lift i)) (𝒜 i) (G i)
   Ghom i = snd ∣ snd (AB i) ∣

   F∼G : ∀ i → (F i) ∘ (G i) ∼ ∣ 𝒾𝒹 ∣
   F∼G i = fst ∥ snd (AB i) ∥

   G∼F : ∀ i → (G i) ∘ (F i) ∼ ∣ 𝒾𝒹 ∣
   G∼F i = snd ∥ snd (AB i) ∥

   ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
   ϕ a i = F (lower i) (a (lower i))

   ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
   ϕhom 𝑓 𝒂 = gfe λ i → (Fhom (lower i)) 𝑓 (λ x → 𝒂 x (lower i))

   ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
   ψ b i = ∣ fst ∥ AB i ∥ ∣ (b (lift i))

   ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
   ψhom 𝑓 𝒃 = gfe λ i → (Ghom i) 𝑓 (λ x → 𝒃 x (lift i))

   ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 ∣
   ϕ~ψ 𝒃 = gfe λ i → F∼G (lower i) (𝒃 i)

   ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹  ∣
   ψ~ϕ 𝒂 = gfe λ i → G∼F i (𝒂 i)

   A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
   A≅B = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

   γ : lift-alg (⨅ 𝒜) 𝓩 ≅ ⨅ ℬ
   γ = trans-≅ (sym-≅ lift-alg-≅) A≅B

\end{code}

#### <a id="embedding-tools">Embedding tools</a>

\begin{code}

module _ {𝓘 𝓤 𝓦 : Universe} where

 embedding-lift-nat : hfunext 𝓘 𝓤 → hfunext 𝓘 𝓦
  →                   {I : 𝓘 ̇}{A : I → 𝓤 ̇}{B : I → 𝓦 ̇}
                      (h : Nat A B) → (∀ i → is-embedding (h i))
                      ------------------------------------------
  →                   is-embedding (NatΠ h)

 embedding-lift-nat hfiu hfiw h hem = NatΠ-is-embedding hfiu hfiw h hem


 embedding-lift-nat' : hfunext 𝓘 𝓤 → hfunext 𝓘 𝓦
  →                    {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓤 𝑆}{ℬ : I → Algebra 𝓦 𝑆}
                       (h : Nat(fst ∘ 𝒜)(fst ∘ ℬ)) → (∀ i → is-embedding (h i))
                       --------------------------------------------------------
  →                    is-embedding(NatΠ h)

 embedding-lift-nat' hfiu hfiw h hem = NatΠ-is-embedding hfiu hfiw h hem


 embedding-lift : hfunext 𝓘 𝓤 → hfunext 𝓘 𝓦
  →               {I : 𝓘 ̇} → {𝒜 : I → Algebra 𝓤 𝑆}{ℬ : I → Algebra 𝓦 𝑆}
  →               (h : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣) → (∀ i → is-embedding (h i))
                  ----------------------------------------------------------
  →               is-embedding(λ (x : ∣ ⨅ 𝒜 ∣) (i : I) → (h i)(x i))

 embedding-lift hfiu hfiw {I}{𝒜}{ℬ} h hem = embedding-lift-nat' hfiu hfiw {I}{𝒜}{ℬ} h hem


iso→embedding : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
 →              (ϕ : 𝑨 ≅ 𝑩) → is-embedding (fst ∣ ϕ ∣)

iso→embedding ϕ = equivs-are-embeddings (fst ∣ ϕ ∣)
                   (invertibles-are-equivs (fst ∣ ϕ ∣) finv)
 where
 finv : invertible (fst ∣ ϕ ∣)
 finv = ∣ fst ∥ ϕ ∥ ∣ , (snd ∥ snd ϕ ∥ , fst ∥ snd ϕ ∥)

\end{code}

--------------------------------------

[← Homomorphisms.Noether](Homomorphisms.Noether.html)
<span style="float:right;">[Homomorphisms.HomomorphicImages →](Homomorphisms.HomomorphicImages.html)</span>

{% include UALib.Links.md %}

