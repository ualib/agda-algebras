---
layout: default
title : Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This chapter presents the [Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Homomorphisms.Basic{𝑆 = 𝑆}{gfe} public

\end{code}


#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem</a>

Here is a version of the so-called *First Homomorphism theorem* (sometimes called Noether's First Homomorphism theorem, after Emmy Noether who was among the first proponents of the abstract approach to algebra that we now refer to as "modern algebra").<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

open Congruence

module _ {𝓤 𝓦 : Universe}
         -- extensionality assumptions --
            (fe : dfunext 𝓥 𝓦)
            (pe : prop-ext 𝓤 𝓦)

         (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)

         -- truncation assumptions --
            (Bset : is-set ∣ 𝑩 ∣)
            (ssR : ∀ a x → is-subsingleton (⟨ kercon 𝑩 h ⟩ a x))
            (ssA : ∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑩 h ⟩} C))

 where


 FirstHomomorphismTheorem :

  Σ ϕ ꞉ hom (𝑨 [ 𝑩 ]/ker h) 𝑩 ,
       (∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ πker 𝑩 h ∣) × Monic ∣ ϕ ∣ × is-embedding ∣ ϕ ∣

 FirstHomomorphismTheorem = (ϕ , ϕhom) , ϕcom , ϕmon , ϕemb
  where
  θ : Congruence 𝑨
  θ = kercon 𝑩 h

  ϕ : ∣ 𝑨 [ 𝑩 ]/ker h ∣ → ∣ 𝑩 ∣
  ϕ a = ∣ h ∣ ⌜ a ⌝

  𝑹 : Pred₂ ∣ 𝑨 ∣ 𝓦
  𝑹 = ⟨ kercon 𝑩 h ⟩ , ssR

  ϕhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h) 𝑩 ϕ
  ϕhom 𝑓 𝒂 =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ 𝒂 x ⌝) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
             (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌜ 𝒂 x ⌝)) ≡⟨ ap (𝑓 ̂ 𝑩) (fe λ x → refl) ⟩
             (𝑓 ̂ 𝑩) (λ x → ϕ (𝒂 x))             ∎

  ϕmon : Monic ϕ
  ϕmon (.(⟨ θ ⟩ u) , u , refl) (.(⟨ θ ⟩ v) , v , refl) ϕuv =
   class-extensionality' {𝑹 = 𝑹} pe ssA (IsEquiv θ) ϕuv

  ϕcom : ∣ h ∣ ≡ ϕ ∘ ∣ πker 𝑩 h ∣
  ϕcom = refl

  ϕemb : is-embedding ϕ
  ϕemb = monic-is-embedding|sets ϕ Bset ϕmon

\end{code}

Next we prove that the homomorphism `ϕ`, whose existence we just proved, is unique.

\begin{code}

 NoetherHomUnique : (f g : hom (𝑨 [ 𝑩 ]/ker h) 𝑩)
  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣
  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 h ∣
                    ---------------------------------
  →                 ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherHomUnique f g hfk hgk (.(⟨ kercon 𝑩 h ⟩ a) , a , refl) =

  let θ = (⟨ kercon 𝑩 h ⟩ a , a , refl) in

   ∣ f ∣ θ   ≡⟨ cong-app(hfk ⁻¹)a ⟩  ∣ h ∣ a   ≡⟨ cong-app(hgk)a ⟩   ∣ g ∣ θ   ∎

\end{code}

If we postulate function extensionality, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

 fe-NoetherHomUnique : funext (𝓤 ⊔ 𝓦 ⁺) 𝓦 → (f g : hom (𝑨 [ 𝑩 ]/ker h) 𝑩)
  →                    ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣
  →                    ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 h ∣
                       ----------------------------
  →                    ∣ f ∣ ≡ ∣ g ∣

 fe-NoetherHomUnique fe f g hfk hgk = fe (NoetherHomUnique f g hfk hgk)

\end{code}

If we assume the hypotheses of the First Homomorphism theorem and add the assumption that `h` is epic, then we get the so-called First Isomorphism theorem.

\begin{code}

 FirstIsomorphismTheorem :

  dfunext 𝓦 𝓦 → Epic ∣ h ∣  →  Σ f ꞉ (epi (𝑨 [ 𝑩 ]/ker h) 𝑩) ,
                        (∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣) × is-embedding ∣ f ∣

 FirstIsomorphismTheorem fev hE = (fmap , fhom , fepic) , refl , femb
  where
  θ : Congruence 𝑨
  θ = kercon 𝑩 h

  fmap : ∣ 𝑨 [ 𝑩 ]/ker h ∣ → ∣ 𝑩 ∣
  fmap ⟦a⟧ = ∣ h ∣ ⌜ ⟦a⟧ ⌝

  fhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h) 𝑩 fmap
  fhom 𝑓 𝒂 =  ∣ h ∣((𝑓 ̂ 𝑨) λ x → ⌜ 𝒂 x ⌝)   ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
              (𝑓 ̂ 𝑩)(∣ h ∣ ∘ λ x → ⌜ 𝒂 x ⌝) ≡⟨ ap(𝑓 ̂ 𝑩)(fe λ _ → refl)⟩
              (𝑓 ̂ 𝑩) (fmap ∘ 𝒂)              ∎

  fepic : Epic fmap
  fepic b = γ where
   a : ∣ 𝑨 ∣
   a = EpicInv ∣ h ∣ hE b

   bfa : b ≡ fmap ⟦ a ⟧
   bfa = (cong-app (EpicInvIsRightInv {fe = fev} ∣ h ∣ hE) b)⁻¹

   γ : Image fmap ∋ b
   γ = Image_∋_.eq b ⟦ a ⟧ bfa

  fmon : Monic fmap
  fmon (.(⟨ θ ⟩ u) , u , refl) (.(⟨ θ ⟩ v) , v , refl) fuv =
   class-extensionality' {𝑹 = ⟨ kercon 𝑩 h ⟩ , ssR} pe ssA (IsEquiv θ) fuv

  femb : is-embedding fmap
  femb = monic-is-embedding|sets fmap Bset fmon

\end{code}

The argument used above to prove `NoetherHomUnique` can also be used to prove uniqueness of the epimorphism `f` found in the isomorphism theorem.

\begin{code}

 NoetherIsoUnique : (f g : epi (𝑨 [ 𝑩 ]/ker h) 𝑩) → ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣
  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 h ∣ → ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherIsoUnique f g hfk hgk (.(⟨ kercon 𝑩 h ⟩ a) , a , refl) =

  let θ = (⟨ kercon 𝑩 h ⟩ a , a , refl) in

   ∣ f ∣ θ  ≡⟨ cong-app (hfk ⁻¹) a ⟩  ∣ h ∣ a  ≡⟨ cong-app (hgk) a ⟩  ∣ g ∣ θ  ∎

\end{code}





#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 ∘-hom : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
  →       hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪

 ∘-hom 𝑨 {𝑩} 𝑪 (g , ghom) (h , hhom) = h ∘ g , γ where

  γ : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)

  γ 𝑓 a = (h ∘ g) ((𝑓 ̂ 𝑨) a) ≡⟨ ap h ( ghom 𝑓 a ) ⟩
          h ((𝑓 ̂ 𝑩) (g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
          (𝑓 ̂ 𝑪) (h ∘ g ∘ a) ∎


 ∘-is-hom : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
            {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →         is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g
  →         is-homomorphism 𝑨 𝑪 (g ∘ f)

 ∘-is-hom 𝑨 𝑪 {f} {g} fhom ghom = ∥ ∘-hom 𝑨 𝑪 (f , fhom) (g , ghom) ∥

\end{code}



#### <a id="homomorphism-decomposition">Homomorphism decomposition</a>

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `ϕ : hom 𝑪 𝑩` such that `g = ϕ ∘ h`, that is, such that the following diagram commutes;

```
𝑨---- h -->>𝑪
 \         .
  \       .
   g     ∃ϕ
    \   .
     \ .
      V
      𝑩
```

This, or some variation of it, is sometimes referred to as the Second Isomorphism Theorem.  We formalize its statement and proof as follows. (Notice that the proof is constructive.)

\begin{code}

homFactor : {𝓤 : Universe} → funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
            -------------------------------------------
 →          Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe{𝑨}{𝑩}{𝑪}(g , ghom)(h , hhom) Kh⊆Kg hEpi = (ϕ , ϕIsHomCB) , g≡ϕ∘h
 where
 hInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
 hInv = λ c → (EpicInv h hEpi) c

 ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
 ϕ = λ c → g ( hInv c )

 ξ : ∀ x → ker-pred h (x , hInv (h x))
 ξ x = (cong-app (EpicInvIsRightInv {fe = fe} h hEpi) (h x))⁻¹

 g≡ϕ∘h : g ≡ ϕ ∘ h
 g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

 ζ : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)(x : ∥ 𝑆 ∥ 𝑓) →  𝒄 x ≡ (h ∘ hInv)(𝒄 x)
 ζ  𝑓 𝒄 x = (cong-app (EpicInvIsRightInv {fe = fe} h hEpi) (𝒄 x))⁻¹

 ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) →  𝒄 ≡ h ∘ (hInv ∘ 𝒄)
 ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EpicInvIsRightInv {fe = fe} h hEpi)⁻¹

 useker : ∀ 𝑓 𝒄 → g(hInv (h((𝑓 ̂ 𝑨)(hInv ∘ 𝒄)))) ≡ g((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))
 useker 𝑓 c = Kh⊆Kg (cong-app (EpicInvIsRightInv{fe = fe} h hEpi)
                              (h ((𝑓 ̂ 𝑨)(hInv ∘ c))) )

 ϕIsHomCB : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → ϕ((𝑓 ̂ 𝑪) 𝒄) ≡ (𝑓 ̂ 𝑩)(ϕ ∘ 𝒄)

 ϕIsHomCB 𝑓 𝒄 =  g (hInv ((𝑓 ̂ 𝑪) 𝒄))              ≡⟨ i   ⟩
                g (hInv ((𝑓 ̂ 𝑪)(h ∘ (hInv ∘ 𝒄)))) ≡⟨ ii  ⟩
                g (hInv (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))))   ≡⟨ iii ⟩
                g ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))              ≡⟨ iv  ⟩
                (𝑓 ̂ 𝑩)(λ x → g (hInv (𝒄 x)))      ∎
  where
  i   = ap (g ∘ hInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
  ii  = ap (g ∘ hInv) (hhom 𝑓 (hInv ∘ 𝒄))⁻¹
  iii = useker 𝑓 𝒄
  iv  = ghom 𝑓 (hInv ∘ 𝒄)

\end{code}

Here's a more general version.

```
𝑨 --- γ ->> 𝑪
 \         .
  \       .
   β     ∃ϕ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 HomFactor : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
             (β : hom 𝑨 𝑩) (γ : hom 𝑨 𝑪)
  →          Epic ∣ γ ∣ → (KER-pred ∣ γ ∣) ⊆ (KER-pred ∣ β ∣)
             --------------------------------------------
  →          Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ β ∣ ≡ ∣ ϕ ∣ ∘ ∣ γ ∣

 HomFactor 𝑨 {𝑩}{𝑪} β γ γE Kγβ = (ϕ , ϕIsHomCB) , βϕγ
  where
  γInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  γInv = λ y → (EpicInv ∣ γ ∣ γE) y

  ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  ϕ = λ y → ∣ β ∣ ( γInv y )

  ξ : (x : ∣ 𝑨 ∣) → KER-pred ∣ γ ∣ (x , γInv (∣ γ ∣ x))
  ξ x =  ( cong-app (EpicInvIsRightInv{fe = gfe} ∣ γ ∣ γE) ( ∣ γ ∣ x ) )⁻¹

  βϕγ : ∣ β ∣ ≡ ϕ ∘ ∣ γ ∣
  βϕγ = gfe λ x → Kγβ (ξ x)

  ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → 𝒄 ≡  ∣ γ ∣ ∘ (γInv ∘ 𝒄)
  ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄) (EpicInvIsRightInv{fe = gfe} ∣ γ ∣ γE)⁻¹

  useker : ∀ 𝑓 𝒄 → ∣ β ∣ (γInv (∣ γ ∣ ((𝑓 ̂ 𝑨) (γInv ∘ 𝒄)))) ≡ ∣ β ∣((𝑓 ̂ 𝑨) (γInv ∘ 𝒄))
  useker 𝑓 𝒄 = Kγβ (cong-app (EpicInvIsRightInv {fe = gfe} ∣ γ ∣ γE)
                             (∣ γ ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))))

  ϕIsHomCB : ∀ 𝑓 𝒄 → ϕ ((𝑓 ̂ 𝑪) 𝒄) ≡ ((𝑓 ̂ 𝑩)(ϕ ∘ 𝒄))

  ϕIsHomCB 𝑓 𝒄 = ∣ β ∣ (γInv ((𝑓 ̂ 𝑪) 𝒄))                   ≡⟨ i   ⟩
                ∣ β ∣ (γInv ((𝑓 ̂ 𝑪)(∣ γ ∣ ∘ (γInv ∘ 𝒄)))) ≡⟨ ii  ⟩
                ∣ β ∣ (γInv (∣ γ ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))))   ≡⟨ iii ⟩
                ∣ β ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))                  ≡⟨ iv  ⟩
                ((𝑓 ̂ 𝑩)(λ x → ∣ β ∣ (γInv (𝒄 x))))        ∎
   where
   i   = ap (∣ β ∣ ∘ γInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
   ii  = ap (∣ β ∣ ∘ γInv) (∥ γ ∥ 𝑓 (γInv ∘ 𝒄))⁻¹
   iii = useker 𝑓 𝒄
   iv  = ∥ β ∥ 𝑓 (γInv ∘ 𝒄)

\end{code}

If, in addition, both β and γ are epic, then so is ϕ.

\begin{code}

 HomFactorEpi : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
                (β : hom 𝑨 𝑩) (βe : Epic ∣ β ∣)
                (ξ : hom 𝑨 𝑪) (ξe : Epic ∣ ξ ∣)
  →             (KER-pred ∣ ξ ∣) ⊆ (KER-pred ∣ β ∣)
                ----------------------------------
  →             Σ ϕ ꞉ (epi 𝑪 𝑩) , ∣ β ∣ ≡ ∣ ϕ ∣ ∘ ∣ ξ ∣

 HomFactorEpi 𝑨 {𝑩}{𝑪} β βe ξ ξe kerincl = (fst ∣ ϕF ∣ , (snd ∣ ϕF ∣ , ϕE)) , ∥ ϕF ∥
  where
  ϕF : Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ β ∣ ≡ ∣ ϕ ∣ ∘ ∣ ξ ∣
  ϕF = HomFactor  𝑨 {𝑩}{𝑪} β ξ ξe kerincl

  ξinv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  ξinv = λ c → (EpicInv ∣ ξ ∣ ξe) c

  βinv : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  βinv = λ b → (EpicInv ∣ β ∣ βe) b

  ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  ϕ = λ c → ∣ β ∣ ( ξinv c )

  ϕE : Epic ϕ
  ϕE = epic-factor gfe ∣ β ∣ ∣ ξ ∣ ϕ ∥ ϕF ∥ βe

\end{code}


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">Note that we already assumed *global* function extensionality in this module, so we could just appeal to that in this case.  However, we make a local function extensionality assumption explicit here merely to highlight where and how the principle is applied.</span>

<p></p>

[← Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms →](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
