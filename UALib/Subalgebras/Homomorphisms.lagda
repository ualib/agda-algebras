---
layout: default
title : UALib.Subalgebras.Homomorphisms module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="homomorphisms-and-subuniverses">Homomorphisms and subuniverses</a>

This section presents the [UALib.Subalgebras.Homomorphisms][]  module of the [Agda Universal Algebra Library][].

The interaction of homomorphisms and subuniverses is a basic cog in the universal algebra machine.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Subalgebras.Homomorphisms
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Subalgebras.Properties{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

#### Homomorphic images are subuniverses

The image of a homomorphism is a subuniverse of its codomain.

\begin{code}

hom-image-is-sub : {𝓤 𝓦 : Universe} → global-dfunext
 →                 {𝑨 : Algebra 𝓤 𝑆} {𝑩 : Algebra 𝓦 𝑆} (ϕ : hom 𝑨 𝑩)
                  -------------------------------------------------
 →                 (HomImage 𝑩 ϕ) ∈ Subuniverses 𝑩

hom-image-is-sub gfe {𝑨}{𝑩} ϕ f b b∈Imf = eq ((f ̂ 𝑩) b) ((f ̂ 𝑨) ar) γ
 where
  ar : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
  ar = λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)

  ζ : ∣ ϕ ∣ ∘ ar ≡ b
  ζ = gfe (λ x → InvIsInv ∣ ϕ ∣(b x)(b∈Imf x))

  γ : (f ̂ 𝑩) b ≡ ∣ ϕ ∣((f ̂ 𝑨)(λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)))

  γ = (f ̂ 𝑩) b          ≡⟨ ap (f ̂ 𝑩)(ζ ⁻¹) ⟩
      (f ̂ 𝑩)(∣ ϕ ∣ ∘ ar)  ≡⟨(∥ ϕ ∥ f ar)⁻¹ ⟩
      ∣ ϕ ∣((f ̂ 𝑨) ar)   ∎
\end{code}

#### Uniqueness property for homomorphisms

A homomorphism is uniquely determined by its action on generators.

\begin{code}

HomUnique : {𝓤 𝓦 : Universe} → funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
            (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →          (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
            ---------------------------------------------
 →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x

HomUnique {𝓤}{𝓦} fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )    ∎
 where induction-hypothesis = λ x → HomUnique{𝓤}{𝓦} fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

\end{code}

---------------------------------

[← UALib.Subalgebras.Properties](UALib.Subalgebras.Properties.html)
<span style="float:right;">[UALib.Subalgebras.Subalgebras →](UALib.Subalgebras.Subalgebras.html)</span>

{% include UALib.Links.md %}
