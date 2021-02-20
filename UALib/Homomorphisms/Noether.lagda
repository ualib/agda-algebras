---
layout: default
title : UALib.Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This chapter presents the [UALib.Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)

module UALib.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Homomorphisms.Basic{𝑆 = 𝑆}{gfe} hiding (global-dfunext) public
open import UALib.Prelude.Preliminaries using (is-embedding) public

\end{code}




#### <a id="the-first-isomorphism-theorem">The First Isomorphism Theorem</a>

Here is a version of the first isomorphism theorem.

\begin{code}

open Congruence

FirstIsomorphismTheorem : {𝓤 𝓦 : Universe}
                          (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)
                          (ϕ : hom 𝑨 𝑩) (ϕE : Epic ∣ ϕ ∣ )
                           --extensionality assumptions:
 →                            propext 𝓦 → is-set ∣ 𝑩 ∣
 →                            (∀ a x → is-subsingleton (⟨ kercon 𝑨{𝑩} ϕ ⟩ a x))
 →                            (∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑨{𝑩} ϕ ⟩} C))
           ------------------------------------------------------------------------------------
 →         Σ f ꞉ (epi (𝑨 [ 𝑩 ]/ker ϕ) 𝑩) , ( ∣ ϕ ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑨 {𝑩} ϕ ∣ ) × is-embedding ∣ f ∣

FirstIsomorphismTheorem 𝑨 𝑩 ϕ ϕE pe Bset ssR ssA = (fmap , fhom , fepic) , 𝓇ℯ𝒻𝓁 , femb
 where
  θ : Congruence 𝑨
  θ = kercon 𝑨{𝑩} ϕ

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
 →                            (∀ a x → is-subsingleton (⟨ kercon 𝑨{𝑩} h ⟩ a x))
 →                            (∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑨{𝑩} h ⟩} C))
    ---------------------------------------------------------------------------------------------
 →  Σ ϕ ꞉ hom (𝑨 [ 𝑩 ]/ker h) 𝑩 , (∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ πker 𝑨 {𝑩} h ∣ ) × Monic ∣ ϕ ∣ × is-embedding ∣ ϕ ∣


FirstHomomorphismTheorem 𝑨 𝑩 h pe Bset ssR ssA = (ϕ , ϕhom) , ϕcom , ϕmon , ϕemb
 where
  θ : Congruence 𝑨
  θ = kercon 𝑨 {𝑩} h

  ϕ : ∣ 𝑨 [ 𝑩 ]/ker h ∣ → ∣ 𝑩 ∣
  ϕ a = ∣ h ∣ ⌜ a ⌝

  ϕhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h) 𝑩 ϕ
  ϕhom 𝑓 𝒂 =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ 𝒂 x ⌝) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
             (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌜ 𝒂 x ⌝)) ≡⟨ ap (𝑓 ̂ 𝑩) (gfe λ x → 𝓇ℯ𝒻𝓁) ⟩
             (𝑓 ̂ 𝑩) (λ x → ϕ (𝒂 x))             ∎

  ϕmon : Monic ϕ
  ϕmon (.(⟨ θ ⟩ a) , a , refl _) (.(⟨ θ ⟩ a') , a' , refl _) ϕaa' =
   class-extensionality' pe gfe ssR ssA (IsEquiv θ) ϕaa'

  ϕcom : ∣ h ∣ ≡ ϕ ∘ ∣ πker 𝑨 {𝑩} h ∣
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

 HCompClosed (A , FA) (B , FB) (C , FC) (g , ghom) (h , hhom) = h ∘ g , γ
   where
    γ : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f  →  A) → (h ∘ g)(FA f a) ≡ FC f (h ∘ g ∘ a)

    γ f a = (h ∘ g) (FA f a)  ≡⟨ ap h ( ghom f a ) ⟩
             h (FB f (g ∘ a)) ≡⟨ hhom f ( g ∘ a ) ⟩
             FC f (h ∘ g ∘ a) ∎


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

homFactor : {𝓤 : Universe} → funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
           ---------------------------------------------
 →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
 (g , ghom) (h , hhom) Kh⊆Kg hEpi = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpi) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → ker-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EpicInvIsRightInv fe h hEpi) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EpicInvIsRightInv fe h hEpi) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EpicInvIsRightInv fe h hEpi)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EpicInvIsRightInv fe h hEpi)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C)
    →         ϕ (FC f a)  ≡  FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))                ≡⟨ i   ⟩
    g (hInv (FC f (h ∘ (hInv ∘ c)))) ≡⟨ ii  ⟩
    g (hInv (h (FA f (hInv ∘ c))))   ≡⟨ iii ⟩
    g (FA f (hInv ∘ c))              ≡⟨ iv  ⟩
    FB f (λ x → g (hInv (c x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC f) (ι f c))
     ii  = ap (λ - → g (hInv -)) (hhom f (hInv ∘ c))⁻¹
     iii = useker f c
     iv  = ghom f (hInv ∘ c)

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

HomFactor : global-dfunext
 →          {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
            (β : hom 𝑨 𝑩) (γ : hom 𝑨 𝑪)
 →          Epic ∣ γ ∣ → (KER-pred ∣ γ ∣) ⊆ (KER-pred ∣ β ∣)
            --------------------------------------------
 →          Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ β ∣ ≡ ∣ ϕ ∣ ∘ ∣ γ ∣

HomFactor gfe 𝑨 {𝑩}{𝑪} β γ γE Kγβ = (ϕ , ϕIsHomCB) , βϕγ
 where
  γInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  γInv = λ y → (EpicInv ∣ γ ∣ γE) y

  ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  ϕ = λ y → ∣ β ∣ ( γInv y )

  ξ : (x : ∣ 𝑨 ∣) → KER-pred ∣ γ ∣ (x , γInv (∣ γ ∣ x))
  ξ x =  ( cong-app (EpicInvIsRightInv gfe ∣ γ ∣ γE) ( ∣ γ ∣ x ) )⁻¹

  βϕγ : ∣ β ∣ ≡ ϕ ∘ ∣ γ ∣
  βϕγ = gfe λ x → Kγβ (ξ x)

  ι : (f : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ f → ∣ 𝑪 ∣) → (λ x → 𝒄 x) ≡ (λ x → ∣ γ ∣ (γInv (𝒄 x)))
  ι f 𝒄 = ap (λ - → - ∘ 𝒄)(EpicInvIsRightInv gfe ∣ γ ∣ γE)⁻¹

  useker : ∀ f 𝒄 → ∣ β ∣ (γInv (∣ γ ∣ ((f ̂ 𝑨) (γInv ∘ 𝒄)))) ≡ ∣ β ∣((f ̂ 𝑨) (γInv ∘ 𝒄))
  useker f 𝒄 = Kγβ (cong-app (EpicInvIsRightInv gfe ∣ γ ∣ γE)(∣ γ ∣ ((f ̂ 𝑨)(γInv ∘ 𝒄))))

  ϕIsHomCB : ∀ f 𝒄 → ϕ ((f ̂ 𝑪) 𝒄) ≡ ((f ̂ 𝑩)(ϕ ∘ 𝒄))
  ϕIsHomCB f 𝒄 =
   ∣ β ∣ (γInv ((f ̂ 𝑪) 𝒄))                   ≡⟨ i   ⟩
   ∣ β ∣ (γInv ((f ̂ 𝑪)(∣ γ ∣ ∘ (γInv ∘ 𝒄)))) ≡⟨ ii  ⟩
   ∣ β ∣ (γInv (∣ γ ∣ ((f ̂ 𝑨)(γInv ∘ 𝒄))))   ≡⟨ iii ⟩
   ∣ β ∣ ((f ̂ 𝑨)(γInv ∘ 𝒄))                  ≡⟨ iv  ⟩
   ((f ̂ 𝑩)(λ x → ∣ β ∣ (γInv (𝒄 x))))        ∎
   where
    i   = ap (∣ β ∣ ∘ γInv) (ap (f ̂ 𝑪) (ι f 𝒄))
    ii  = ap (λ - → ∣ β ∣ (γInv -)) (∥ γ ∥ f (γInv ∘ 𝒄))⁻¹
    iii = useker f 𝒄
    iv  = ∥ β ∥ f (γInv ∘ 𝒄)

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

HomFactorEpi : global-dfunext
 →             {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
               (β : hom 𝑨 𝑩) (βe : Epic ∣ β ∣)
               (ξ : hom 𝑨 𝑪) (ξe : Epic ∣ ξ ∣)
 →             (KER-pred ∣ ξ ∣) ⊆ (KER-pred ∣ β ∣)
               ----------------------------------
 →             Σ ϕ ꞉ (epi 𝑪 𝑩) , ∣ β ∣ ≡ ∣ ϕ ∣ ∘ ∣ ξ ∣

HomFactorEpi gfe 𝑨 {𝑩}{𝑪} β βe ξ ξe kerincl = (fst ∣ ϕF ∣ , (snd ∣ ϕF ∣ , ϕE)) , ∥ ϕF ∥
 where
  ϕF : Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ β ∣ ≡ ∣ ϕ ∣ ∘ ∣ ξ ∣
  ϕF = HomFactor gfe 𝑨 {𝑩}{𝑪} β ξ ξe kerincl

  ξinv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  ξinv = λ c → (EpicInv ∣ ξ ∣ ξe) c

  βinv : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  βinv = λ b → (EpicInv ∣ β ∣ βe) b

  ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  ϕ = λ c → ∣ β ∣ ( ξinv c )

  ϕE : Epic ϕ
  ϕE = epic-factor {fe = gfe} ∣ β ∣ ∣ ξ ∣ ϕ ∥ ϕF ∥ βe

\end{code}




--------------------------------------

[← UALib.Homomorphisms.Basic](UALib.Homomorphisms.Basic.html)
<span style="float:right;">[UALib.Homomorphisms.Isomorphisms →](UALib.Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
