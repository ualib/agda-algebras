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

open import Homomorphisms.Basic{𝑆 = 𝑆}{gfe = gfe} public

\end{code}




#### <a id="the-first-isomorphism-theorem">The First Isomorphism Theorem</a>

Here is a version of the first isomorphism theorem.

\begin{code}

open Congruence

open import MGS-Powerset using (propext)
open import MGS-Embeddings using (is-set)
open import MGS-Subsingleton-Theorems using (is-subsingleton)

FirstIsomorphismTheorem : {𝓤 𝓦 : Universe}
                          (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)
                          (ϕ : hom 𝑨 𝑩) (ϕE : Epic ∣ ϕ ∣ )
                           --extensionality assumptions:
 →                            propext 𝓦 → is-set ∣ 𝑩 ∣
 →                            (∀ a x → is-subsingleton (⟨ kercon 𝑩 ϕ ⟩ a x))
 →                            (∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑩 ϕ ⟩} C))
           ------------------------------------------------------------------------------------
 →         Σ f ꞉ (epi (𝑨 [ 𝑩 ]/ker ϕ) 𝑩) , ( ∣ ϕ ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 ϕ ∣ ) × is-embedding ∣ f ∣

FirstIsomorphismTheorem 𝑨 𝑩 ϕ ϕE pe Bset ssR ssA = (fmap , fhom , fepic) , 𝓇ℯ𝒻𝓁 , femb
 where
  θ : Congruence 𝑨
  θ = kercon 𝑩 ϕ

  fmap : ∣ 𝑨 [ 𝑩 ]/ker ϕ ∣ → ∣ 𝑩 ∣
  fmap ⟦a⟧ = ∣ ϕ ∣ ⌜ ⟦a⟧ ⌝

  fhom : is-homomorphism (𝑨 [ 𝑩 ]/ker ϕ) 𝑩 fmap
  fhom 𝑓 𝒂 =  ∣ ϕ ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ 𝒂 x ⌝) ) ≡⟨ ∥ ϕ ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
              (𝑓 ̂ 𝑩)(∣ ϕ ∣ ∘ (λ x → ⌜ 𝒂 x ⌝))  ≡⟨ ap (𝑓 ̂ 𝑩) (gfe λ _ → 𝓇ℯ𝒻𝓁) ⟩
              (𝑓 ̂ 𝑩)(fmap ∘ 𝒂)                 ∎

  fepic : Epic fmap
  fepic b = γ
   where
    a : ∣ 𝑨 ∣
    a = EpicInv ∣ ϕ ∣ ϕE b

    bfa : b ≡ fmap ⟦ a ⟧
    bfa = (cong-app (EpicInvIsRightInv gfe ∣ ϕ ∣ ϕE) b)⁻¹

    γ : Image fmap ∋ b
    γ = Image_∋_.eq b ⟦ a ⟧ bfa

  fmon : Monic fmap
  fmon (.(⟨ θ ⟩ a) , a , 𝓇ℯ𝒻𝓁) (.(⟨ θ ⟩ a') , a' , 𝓇ℯ𝒻𝓁) faa' =
   class-extensionality' pe gfe ssR ssA (IsEquiv θ) faa'

  femb : is-embedding fmap
  femb = monic-into-set-is-embedding Bset fmap fmon

\end{code}

**TODO**: Proof of uniqueness of `f` is missing.

If we don't assume the mapping ϕ is onto, and then we get the following version of the first homomorphism theorem.

\begin{code}

FirstHomomorphismTheorem : {𝓤 𝓦 : Universe}
                           (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)
                           (h : hom 𝑨 𝑩)
                           --extensionality assumptions:
 →                            propext 𝓦 → is-set ∣ 𝑩 ∣
 →                            (∀ a x → is-subsingleton (⟨ kercon 𝑩 h ⟩ a x))
 →                            (∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑩 h ⟩} C))
    ---------------------------------------------------------------------------------------------
 →  Σ ϕ ꞉ hom (𝑨 [ 𝑩 ]/ker h) 𝑩 , (∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ πker 𝑩 h ∣ ) × Monic ∣ ϕ ∣ × is-embedding ∣ ϕ ∣


FirstHomomorphismTheorem 𝑨 𝑩 h pe Bset ssR ssA = (ϕ , ϕhom) , ϕcom , ϕmon , ϕemb
 where
  θ : Congruence 𝑨
  θ = kercon 𝑩 h

  ϕ : ∣ 𝑨 [ 𝑩 ]/ker h ∣ → ∣ 𝑩 ∣
  ϕ a = ∣ h ∣ ⌜ a ⌝

  ϕhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h) 𝑩 ϕ
  ϕhom 𝑓 𝒂 =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ 𝒂 x ⌝) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
             (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌜ 𝒂 x ⌝)) ≡⟨ ap (𝑓 ̂ 𝑩) (gfe λ x → 𝓇ℯ𝒻𝓁) ⟩
             (𝑓 ̂ 𝑩) (λ x → ϕ (𝒂 x))             ∎

  ϕmon : Monic ϕ
  ϕmon (.(⟨ θ ⟩ a) , a , refl _) (.(⟨ θ ⟩ a') , a' , refl _) ϕaa' =
   class-extensionality' pe gfe ssR ssA (IsEquiv θ) ϕaa'

  ϕcom : ∣ h ∣ ≡ ϕ ∘ ∣ πker 𝑩 h ∣
  ϕcom = 𝓇ℯ𝒻𝓁

  ϕemb : is-embedding ϕ
  ϕemb = monic-into-set-is-embedding Bset ϕ ϕmon

\end{code}



#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 HCompClosed : (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
  →            hom 𝑨 𝑩  →  hom 𝑩 𝑪
               --------------------
  →            hom 𝑨 𝑪

 HCompClosed 𝑨 𝑩 𝑪 (g , ghom) (h , hhom) = h ∘ g , γ
   where
    γ : (𝑓 : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)

    γ 𝑓 a = (h ∘ g) ((𝑓 ̂ 𝑨) a) ≡⟨ ap h ( ghom 𝑓 a ) ⟩
            h ((𝑓 ̂ 𝑩) (g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
            (𝑓 ̂ 𝑪) (h ∘ g ∘ a) ∎


 HomComp : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
  →        hom 𝑨 𝑩  →  hom 𝑩 𝑪
           --------------------
  →        hom 𝑨 𝑪

 HomComp 𝑨 {𝑩} 𝑪 f g = HCompClosed 𝑨 𝑩 𝑪 f g


 ∘-hom : (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
         {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →      is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g
         ----------------------------------------------
  →      is-homomorphism 𝑨 𝑪 (g ∘ f)

 ∘-hom 𝑨 𝑩 𝑪 {f} {g} fhom ghom = ∥ HCompClosed 𝑨 𝑩 𝑪 (f , fhom) (g , ghom) ∥


 ∘-Hom : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
         {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →      is-homomorphism 𝑨 𝑩 f  →  is-homomorphism 𝑩 𝑪 g
         ------------------------------------------------
  →      is-homomorphism 𝑨 𝑪 (g ∘ f)

 ∘-Hom 𝑨 {𝑩} 𝑪 {f} {g} = ∘-hom 𝑨 𝑩 𝑪 {f} {g}


 trans-hom : (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
             (f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣ )(g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣ )
  →          is-homomorphism 𝑨 𝑩 f  →  is-homomorphism 𝑩 𝑪 g
             ------------------------------------------------
  →          is-homomorphism 𝑨 𝑪 (g ∘ f)

 trans-hom 𝑨 𝑩 𝑪 f g = ∘-hom 𝑨 𝑩 𝑪 {f}{g}

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


open import MGS-Subsingleton-Theorems using (funext)

homFactor : {𝓤 : Universe} → funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
            -------------------------------------------
 →          Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe {𝑨}{𝑩}{𝑪} (g , ghom) (h , hhom) Kh⊆Kg hEpi = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   hInv = λ c → (EpicInv h hEpi) c

   ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   ϕ = λ c → g ( hInv c )

   ξ : ∀ x → ker-pred h (x , hInv (h x))
   ξ x = (cong-app (EpicInvIsRightInv fe h hEpi) (h x))⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

   ζ : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)(x : ∥ 𝑆 ∥ 𝑓) →  𝒄 x ≡ (h ∘ hInv)(𝒄 x)
   ζ  𝑓 𝒄 x = (cong-app (EpicInvIsRightInv fe h hEpi) (𝒄 x))⁻¹

   ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) →  𝒄 ≡ h ∘ (hInv ∘ 𝒄)
   ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EpicInvIsRightInv fe h hEpi)⁻¹

   useker : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → g(hInv (h((𝑓 ̂ 𝑨)(hInv ∘ 𝒄)))) ≡ g((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))
   useker 𝑓 c = Kh⊆Kg (cong-app (EpicInvIsRightInv fe h hEpi) (h ((𝑓 ̂ 𝑨)(hInv ∘ c))))

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

HomFactor : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
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
  ξ x =  ( cong-app (EpicInvIsRightInv gfe ∣ γ ∣ γE) ( ∣ γ ∣ x ) )⁻¹

  βϕγ : ∣ β ∣ ≡ ϕ ∘ ∣ γ ∣
  βϕγ = gfe λ x → Kγβ (ξ x)

  ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → 𝒄 ≡  ∣ γ ∣ ∘ (γInv ∘ 𝒄)
  ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EpicInvIsRightInv gfe ∣ γ ∣ γE)⁻¹

  useker : ∀ 𝑓 𝒄 → ∣ β ∣ (γInv (∣ γ ∣ ((𝑓 ̂ 𝑨) (γInv ∘ 𝒄)))) ≡ ∣ β ∣((𝑓 ̂ 𝑨) (γInv ∘ 𝒄))
  useker 𝑓 𝒄 = Kγβ (cong-app (EpicInvIsRightInv gfe ∣ γ ∣ γE)(∣ γ ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))))

  ϕIsHomCB : ∀ 𝑓 𝒄 → ϕ ((𝑓 ̂ 𝑪) 𝒄) ≡ ((𝑓 ̂ 𝑩)(ϕ ∘ 𝒄))

  ϕIsHomCB 𝑓 𝒄 = ∣ β ∣ (γInv ((𝑓 ̂ 𝑪) 𝒄))                  ≡⟨ i   ⟩
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

```
𝑨 --- ξ ->> 𝑪
 \         .
  \       .
   β     ∃ϕ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

HomFactorEpi : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
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

[← Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms →](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
