---
layout: default
title : UALib.Homomorphisms.Isomoprhisms module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="isomorphisms-type">Isomorphism Type</a>

This section describes the [UALib.Homomorphisms.Isomorphisms][] module of the [Agda Universal Algebra Library][].

We implement (the extensional version of) the notion of isomorphism between algebraic structures.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)


module UALib.Homomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Homomorphisms.Products{𝑆 = 𝑆}{gfe} public
open import UALib.Prelude.Preliminaries using (is-equiv; hfunext; Nat; NatΠ; NatΠ-is-embedding) public

_≅_ : {𝓤 𝓦 : Universe} (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , ((∣ f ∣ ∘ ∣ g ∣) ∼ ∣ 𝒾𝒹 𝑩 ∣) × ((∣ g ∣ ∘ ∣ f ∣) ∼ ∣ 𝒾𝒹 𝑨 ∣)
\end{code}

Recall, f ~ g means f and g are extensionally equal; i.e., ∀ x, f x ≡ g x.

#### <a id="isomorphism-toolbox">Isomorphism toolbox</a>

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

 ≅-inv-map-is-homomorphism : (ϕ : 𝑨 ≅ 𝑩) → is-homomorphism 𝑩 𝑨 (≅-inv-map ϕ)
 ≅-inv-map-is-homomorphism ϕ = ∥ ≅-inv-hom ϕ ∥

 ≅-map-invertible : (ϕ : 𝑨 ≅ 𝑩) → invertible (≅-map ϕ)
 ≅-map-invertible ϕ = (≅-inv-map ϕ) , (∥ snd ∥ ϕ ∥ ∥ , ∣ snd ∥ ϕ ∥ ∣)

 ≅-map-is-equiv : (ϕ : 𝑨 ≅ 𝑩) → is-equiv (≅-map ϕ)
 ≅-map-is-equiv ϕ = invertibles-are-equivs (≅-map ϕ) (≅-map-invertible ϕ)

 ≅-map-is-embedding : (ϕ : 𝑨 ≅ 𝑩) → is-embedding (≅-map ϕ)
 ≅-map-is-embedding ϕ = equivs-are-embeddings (≅-map ϕ) (≅-map-is-equiv ϕ)
\end{code}



#### <a id="isomorphism-is-an-equivalence-relation">Isomorphism is an equivalence relation</a>

\begin{code}
REFL-≅ ID≅ : {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ≅ 𝑨
ID≅ 𝑨 = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , (λ a → 𝓇ℯ𝒻𝓁) , (λ a → 𝓇ℯ𝒻𝓁)
REFL-≅ = ID≅

refl-≅ id≅ : {𝓤 : Universe} {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ 𝑨
id≅ {𝓤}{𝑨} = ID≅ {𝓤} 𝑨
refl-≅ = id≅

sym-≅ : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
sym-≅ h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

trans-≅ : {𝓠 𝓤 𝓦 : Universe}
          (𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑪 : Algebra 𝓦 𝑆)
 →         𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪
          ----------------
 →            𝑨 ≅ 𝑪

trans-≅ 𝑨 𝑩 𝑪 ab bc = f , g , α , β
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

  f1∼g2 : ∣ f1 ∣ ∘ ∣ g2 ∣ ∼ ∣ 𝒾𝒹 𝑩 ∣
  f1∼g2 = ∣ snd ∥ ab ∥ ∣

  g2∼f1 : ∣ g2 ∣ ∘ ∣ f1 ∣ ∼ ∣ 𝒾𝒹 𝑨 ∣
  g2∼f1 = ∥ snd ∥ ab ∥ ∥

  f2∼g1 : ∣ f2 ∣ ∘ ∣ g1 ∣ ∼ ∣ 𝒾𝒹 𝑪 ∣
  f2∼g1 =  ∣ snd ∥ bc ∥ ∣

  g1∼f2 : ∣ g1 ∣ ∘ ∣ f2 ∣ ∼ ∣ 𝒾𝒹 𝑩 ∣
  g1∼f2 = ∥ snd ∥ bc ∥ ∥

  α : ∣ f ∣ ∘ ∣ g ∣ ∼ ∣ 𝒾𝒹 𝑪 ∣
  α x = (∣ f ∣ ∘ ∣ g ∣) x                   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        ∣ f2 ∣ ( (∣ f1 ∣ ∘ ∣ g2 ∣) (∣ g1 ∣ x)) ≡⟨ ap ∣ f2 ∣ (f1∼g2 (∣ g1 ∣ x)) ⟩
        ∣ f2 ∣ ( ∣ 𝒾𝒹 𝑩 ∣ (∣ g1 ∣ x))        ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        (∣ f2 ∣ ∘ ∣ g1 ∣) x                  ≡⟨ f2∼g1 x ⟩
        ∣ 𝒾𝒹 𝑪 ∣ x                         ∎
  β : ∣ g ∣ ∘ ∣ f ∣ ∼ ∣ 𝒾𝒹 𝑨 ∣
  β x = (ap ∣ g2 ∣ (g1∼f2 (∣ f1 ∣ x))) ∙ g2∼f1 x

TRANS-≅ : {𝓠 𝓤 𝓦 : Universe}
          {𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}{𝑪 : Algebra 𝓦 𝑆}
 →         𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪
          ----------------
 →            𝑨 ≅ 𝑪
TRANS-≅ {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪} = trans-≅ 𝑨 𝑩 𝑪

Trans-≅ : {𝓠 𝓤 𝓦 : Universe}
          (𝑨 : Algebra 𝓠 𝑆){𝑩 : Algebra 𝓤 𝑆}(𝑪 : Algebra 𝓦 𝑆)
 →         𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪
          ----------------
 →            𝑨 ≅ 𝑪
Trans-≅ 𝑨 {𝑩} 𝑪 = trans-≅ 𝑨 𝑩 𝑪
\end{code}



#### <a id="lift-is-an-algebraic-invariant">Lift is an algebraic invariant</a>

Fortunately, the lift operation preserves isomorphism (i.e., it's an "algebraic invariant"), which is why it's a workable solution to the "level hell" problem we mentioned earlier.

\begin{code}
open Lift

--An algebra is isomorphic to its lift to a higher universe level
lift-alg-≅ : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ (lift-alg 𝑨 𝓦)
lift-alg-≅ = (lift , λ _ _ → 𝓇ℯ𝒻𝓁) ,
                         (lower , λ _ _ → 𝓇ℯ𝒻𝓁) ,
                         (λ _ → 𝓇ℯ𝒻𝓁) , (λ _ → 𝓇ℯ𝒻𝓁)

lift-alg-hom : (𝓧 : Universe){𝓨 : Universe}
               (𝓩 : Universe){𝓦 : Universe}
               (𝑨 : Algebra 𝓧 𝑆)
               (𝑩 : Algebra 𝓨 𝑆)
 →             hom 𝑨 𝑩
              ------------------------------------
 →             hom (lift-alg 𝑨 𝓩) (lift-alg 𝑩 𝓦)
lift-alg-hom 𝓧 𝓩 {𝓦} 𝑨 𝑩 (f , fhom) = lift ∘ f ∘ lower , γ
 where
  lh : is-homomorphism (lift-alg 𝑨 𝓩) 𝑨 lower
  lh = λ _ _ → 𝓇ℯ𝒻𝓁
  lABh : is-homomorphism (lift-alg 𝑨 𝓩) 𝑩 (f ∘ lower)
  lABh = ∘-hom (lift-alg 𝑨 𝓩) 𝑨 𝑩 {lower}{f} lh fhom
  Lh : is-homomorphism 𝑩 (lift-alg 𝑩 𝓦) lift
  Lh = λ _ _ → 𝓇ℯ𝒻𝓁
  γ : is-homomorphism (lift-alg 𝑨 𝓩) (lift-alg 𝑩 𝓦) (lift ∘ (f ∘ lower))
  γ = ∘-hom (lift-alg 𝑨 𝓩) 𝑩 (lift-alg 𝑩 𝓦) {f ∘ lower}{lift} lABh Lh

lift-alg-iso : (𝓧 : Universe){𝓨 : Universe}(𝓩 : Universe){𝓦 : Universe}(𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)
 →               𝑨 ≅ 𝑩 → (lift-alg 𝑨 𝓩) ≅ (lift-alg 𝑩 𝓦)
lift-alg-iso 𝓧 {𝓨} 𝓩 {𝓦} 𝑨 𝑩 A≅B = TRANS-≅ (TRANS-≅ lA≅A A≅B) lift-alg-≅
 where
  lA≅A : (lift-alg 𝑨 𝓩) ≅ 𝑨
  lA≅A = sym-≅ lift-alg-≅
\end{code}



#### <a id="lift-associativity">Lift associativity</a>

The lift is also associative, up to isomorphism at least.

\begin{code}
lift-alg-assoc : {𝓤 𝓦 𝓘 : Universe}{𝑨 : Algebra 𝓤 𝑆}
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
lift-alg-assoc {𝓤} {𝓦} {𝓘} {𝑨} = TRANS-≅ (TRANS-≅ ζ lift-alg-≅) lift-alg-≅
 where
  ζ : lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ 𝑨
  ζ = sym-≅ lift-alg-≅

lift-alg-associative : {𝓤 𝓦 𝓘 : Universe}(𝑨 : Algebra 𝓤 𝑆)
 →           lift-alg 𝑨 (𝓦 ⊔ 𝓘) ≅ (lift-alg (lift-alg 𝑨 𝓦) 𝓘)
lift-alg-associative{𝓤}{𝓦}{𝓘} 𝑨 = lift-alg-assoc{𝓤}{𝓦}{𝓘}{𝑨}
\end{code}

#### <a id="products-preserve-isomorphisms">Products preserve isomorphisms</a>

\begin{code}
⨅≅ : global-dfunext → {𝓠 𝓤 𝓘 : Universe}
     {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
 →   ((i : I) → (𝒜 i) ≅ (ℬ i))
     ---------------------------
 →       ⨅ 𝒜 ≅ ⨅ ℬ

⨅≅ gfe {𝓠}{𝓤}{𝓘}{I}{𝒜}{ℬ} AB = γ
 where
  F : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣
  F i = ∣ fst (AB i) ∣
  Fhom : ∀ i → is-homomorphism (𝒜 i) (ℬ i) (F i)
  Fhom i = ∥ fst (AB i) ∥

  G : ∀ i → ∣ ℬ i ∣ → ∣ 𝒜 i ∣
  G i = fst ∣ snd (AB i) ∣
  Ghom : ∀ i → is-homomorphism (ℬ i) (𝒜 i) (G i)
  Ghom i = snd ∣ snd (AB i) ∣

  F∼G : ∀ i → (F i) ∘ (G i) ∼ (∣ 𝒾𝒹 (ℬ i) ∣)
  F∼G i = fst ∥ snd (AB i) ∥

  G∼F : ∀ i → (G i) ∘ (F i) ∼ (∣ 𝒾𝒹 (𝒜 i) ∣)
  G∼F i = snd ∥ snd (AB i) ∥

  ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
  ϕ a i = F i (a i)

  ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒂 = gfe (λ i → (Fhom i) 𝑓 (λ x → 𝒂 x i))

  ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
  ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

  ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
  ψhom 𝑓 𝒃 = gfe (λ i → (Ghom i) 𝑓 (λ x → 𝒃 x i))

  ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 (⨅ ℬ) ∣
  ϕ~ψ 𝒃 = gfe λ i → F∼G i (𝒃 i)

  ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
  ψ~ϕ 𝒂 = gfe λ i → G∼F i (𝒂 i)

  γ : ⨅ 𝒜 ≅ ⨅ ℬ
  γ = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)
\end{code}

A nearly identical proof goes through for isomorphisms of lifted products.

\begin{code}
lift-alg-⨅≅ : global-dfunext → {𝓠 𝓤 𝓘 𝓩 : Universe}
     {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : (Lift{𝓘}{𝓩} I) → Algebra 𝓤 𝑆}
 →   ((i : I) → (𝒜 i) ≅ (ℬ (lift i)))
     ---------------------------
 →       lift-alg (⨅ 𝒜) 𝓩 ≅ ⨅ ℬ

lift-alg-⨅≅ gfe {𝓠}{𝓤}{𝓘}{𝓩}{I}{𝒜}{ℬ} AB = γ
 where
  F : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ (lift i) ∣
  F i = ∣ fst (AB i) ∣
  Fhom : ∀ i → is-homomorphism (𝒜 i) (ℬ (lift i)) (F i)
  Fhom i = ∥ fst (AB i) ∥

  G : ∀ i → ∣ ℬ (lift i) ∣ → ∣ 𝒜 i ∣
  G i = fst ∣ snd (AB i) ∣
  Ghom : ∀ i → is-homomorphism (ℬ (lift i)) (𝒜 i) (G i)
  Ghom i = snd ∣ snd (AB i) ∣

  F∼G : ∀ i → (F i) ∘ (G i) ∼ (∣ 𝒾𝒹 (ℬ (lift i)) ∣)
  F∼G i = fst ∥ snd (AB i) ∥

  G∼F : ∀ i → (G i) ∘ (F i) ∼ (∣ 𝒾𝒹 (𝒜 i) ∣)
  G∼F i = snd ∥ snd (AB i) ∥

  ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
  ϕ a i = F (lower i) (a (lower i))

  ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒂 = gfe (λ i → (Fhom (lower i)) 𝑓 (λ x → 𝒂 x (lower i)))

  ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
  ψ b i = ∣ fst ∥ AB i ∥ ∣ (b (lift i))

  ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
  ψhom 𝑓 𝒃 = gfe (λ i → (Ghom i) 𝑓 (λ x → 𝒃 x (lift i)))

  ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 (⨅ ℬ) ∣
  ϕ~ψ 𝒃 = gfe λ i → F∼G (lower i) (𝒃 i)

  ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
  ψ~ϕ 𝒂 = gfe λ i → G∼F i (𝒂 i)

  A≅B : ⨅ 𝒜 ≅ ⨅ ℬ
  A≅B = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)

  γ : lift-alg (⨅ 𝒜) 𝓩 ≅ ⨅ ℬ
  γ = Trans-≅ (lift-alg (⨅ 𝒜) 𝓩) (⨅ ℬ) (sym-≅ lift-alg-≅) A≅B

\end{code}

#### <a id="embedding-tools">Embedding tools</a>

\begin{code}

embedding-lift-nat : {𝓠 𝓤 𝓘 : Universe} → hfunext 𝓘 𝓠 → hfunext 𝓘 𝓤
 →                   {I : 𝓘 ̇}{A : I → 𝓠 ̇}{B : I → 𝓤 ̇}
                     (h : Nat A B)
 →                   ((i : I) → is-embedding (h i))
                     -------------------------------
 →                   is-embedding(NatΠ h)

embedding-lift-nat hfiq hfiu h hem = NatΠ-is-embedding hfiq hfiu h hem

embedding-lift-nat' : {𝓠 𝓤 𝓘 : Universe} → hfunext 𝓘 𝓠 → hfunext 𝓘 𝓤
 →                    {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
                      (h : Nat (fst ∘ 𝒜) (fst ∘ ℬ))
 →                   ((i : I) → is-embedding (h i))
                     -------------------------------
 →                   is-embedding(NatΠ h)

embedding-lift-nat' hfiq hfiu h hem = NatΠ-is-embedding hfiq hfiu h hem

embedding-lift : {𝓠 𝓤 𝓘 : Universe} → hfunext 𝓘 𝓠 → hfunext 𝓘 𝓤
 →               {I : 𝓘 ̇} -- global-dfunext → {𝓠 𝓤 𝓘 : Universe}{I : 𝓘 ̇}
                 {𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
 →               (h : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣)
 →               ((i : I) → is-embedding (h i))
                 ----------------------------------------------------
 →               is-embedding(λ (x : ∣ ⨅ 𝒜 ∣) (i : I) → (h i) (x i))
embedding-lift {𝓠} {𝓤} {𝓘} hfiq hfiu {I} {𝒜} {ℬ} h hem =
 embedding-lift-nat' {𝓠} {𝓤} {𝓘} hfiq hfiu {I} {𝒜} {ℬ} h hem

iso→embedding : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
 →              (ϕ : 𝑨 ≅ 𝑩) → is-embedding (fst ∣ ϕ ∣)
iso→embedding {𝓤}{𝓦}{𝑨}{𝑩} ϕ = γ
 where
  f : hom 𝑨 𝑩
  f = ∣ ϕ ∣
  g : hom 𝑩 𝑨
  g = ∣ snd ϕ ∣

  finv : invertible ∣ f ∣
  finv = ∣ g ∣ , (snd ∥ snd ϕ ∥ , fst ∥ snd ϕ ∥)

  γ : is-embedding ∣ f ∣
  γ = equivs-are-embeddings ∣ f ∣ (invertibles-are-equivs ∣ f ∣ finv)

\end{code}

--------------------------------------

[← UALib.Homomorphisms.Products](UALib.Homomorphisms.Products.html)
<span style="float:right;">[UALib.Algebras.HomomorphicImages →](UALib.Algebras.HomomorphicImages.html)</span>

{% include UALib.Links.md %}
