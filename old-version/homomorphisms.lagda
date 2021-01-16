---
layout: default
title : homomorphisms module (of the Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: homomorphisms.agda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATE: 12 Jan 2021
-->

## Homomorphisms

### Options, imports

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext)

module homomorphisms {𝑆 : Signature 𝓞 𝓥} {gfe : global-dfunext} where

open import congruences {𝑆 = 𝑆}{gfe}

open import prelude using (_≃_; _∼_; Image_∋_; cong-app; EpicInv; EpicInvIsRightInv;
 Nat; NatΠ; NatΠ-is-embedding; is-embedding; invertible; hfunext; _=̇_; Monic;
 invertibles-are-embeddings; monic-into-set-is-embedding; equivs-are-embeddings; invertibles-are-equivs;
 intensionality; is-equiv; Inv; eq; InvIsInv) public

OV : Universe → Universe
OV 𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
\end{code}

### Basic definitions

\begin{code}
compatible-op-map : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)
                    (𝑓 : ∣ 𝑆 ∣)(g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇

compatible-op-map 𝑨 𝑩 𝑓 g = ∀ 𝒂 → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)
--(infered type  𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)

op_interpreted-in_and_commutes-with : {𝓠 𝓤 : Universe}
   (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓠 𝑆) (𝑩 : Algebra 𝓤 𝑆)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g = compatible-op-map 𝑨 𝑩 𝑓 g

is-homomorphism : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
is-homomorphism 𝑨 𝑩 g = ∀ (𝑓 : ∣ 𝑆 ∣) → compatible-op-map 𝑨 𝑩 𝑓 g

hom : {𝓠 𝓤 : Universe} → Algebra 𝓠 𝑆 → Algebra 𝓤 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g
\end{code}

### Kernel congruences

The kernel of a homomorphism is a congruence and conversely for every congruence θ, there exists a homomorphism with kernel θ.

\begin{code}
open congruence-predicates
open relation-predicate-classes
open Congruence

module _ {𝓤 𝓦 : Universe} where

 hom-kernel-is-compatible : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
  →                         compatible 𝑨 (KER-rel ∣ h ∣)

 hom-kernel-is-compatible 𝑨 {𝑩} h f {𝒂}{𝒂'} Kerhab = γ
  where
   γ : ∣ h ∣ ((f ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((f ̂ 𝑨) 𝒂')
   γ = ∣ h ∣ ((f ̂ 𝑨) 𝒂) ≡⟨ ∥ h ∥ f 𝒂 ⟩
       (f ̂ 𝑩) (∣ h ∣ ∘ 𝒂) ≡⟨ ap (λ - → (f ̂ 𝑩) -) (gfe λ x → Kerhab x) ⟩
       (f ̂ 𝑩) (∣ h ∣ ∘ 𝒂') ≡⟨ (∥ h ∥ f 𝒂')⁻¹ ⟩
       ∣ h ∣ ((f ̂ 𝑨) 𝒂') ∎

 hom-kernel-is-equivalence : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
  →                          IsEquivalence (KER-rel ∣ h ∣)

 hom-kernel-is-equivalence 𝑨 h = map-kernel-IsEquivalence ∣ h ∣

 kercon -- (alias)
  hom-kernel-congruence : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩)
  →                      Congruence 𝑨

 hom-kernel-congruence 𝑨 {𝑩} h = mkcon (KER-rel ∣ h ∣)
                                        (hom-kernel-is-compatible 𝑨 {𝑩} h)
                                         (hom-kernel-is-equivalence 𝑨 {𝑩} h)
 kercon = hom-kernel-congruence -- (alias)

 quotient-by-hom-kernel : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}
                          (h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆

 quotient-by-hom-kernel 𝑨{𝑩} h = 𝑨 ╱ (hom-kernel-congruence 𝑨{𝑩} h)

 -- NOTATION.
 _[_]/ker_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
 𝑨 [ 𝑩 ]/ker h = quotient-by-hom-kernel 𝑨 {𝑩} h


epi : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
epi 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g × Epic g

epi-to-hom : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}
 →           epi 𝑨 𝑩 → hom 𝑨 𝑩
epi-to-hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

canonical-projection : {𝓤 𝓦 : Universe}
                       (𝑨 : Algebra 𝓤 𝑆)(θ : Congruence{𝓤}{𝓦} 𝑨)
                     -----------------------------------------------
  →                     epi 𝑨 (𝑨 ╱ θ)

canonical-projection 𝑨 θ = cπ , cπ-is-hom , cπ-is-epic
  where
   cπ : ∣ 𝑨 ∣ → ∣ 𝑨 ╱ θ ∣
   cπ a = ⟦ a ⟧  -- ([ a ] (KER-rel ∣ h ∣)) , ?

   cπ-is-hom : is-homomorphism 𝑨 (𝑨 ╱ θ) cπ
   cπ-is-hom 𝑓 𝒂 = γ
    where
     γ : cπ ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ (𝑨 ╱ θ)) (λ x → cπ (𝒂 x))
     γ = cπ ((𝑓 ̂ 𝑨) 𝒂) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         ⟦ (𝑓 ̂ 𝑨) 𝒂 ⟧ ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         (𝑓 ̂ (𝑨 ╱ θ)) (λ x → ⟦ 𝒂 x ⟧) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         (𝑓 ̂ (𝑨 ╱ θ)) (λ x → cπ (𝒂 x)) ∎

   cπ-is-epic : Epic cπ
   cπ-is-epic (.(⟨ θ ⟩ a) , a , refl _) = Image_∋_.im a

module _ {𝓤 𝓦 : Universe}{pe : propext 𝓦} where
 πᵏ -- alias
  kernel-quotient-projection : (𝑨 : Algebra 𝓤 𝑆){𝑩 : Algebra 𝓦 𝑆}
                               (h : hom 𝑨 𝑩)
                              -----------------------------------
   →                             epi 𝑨 (𝑨 [ 𝑩 ]/ker h)

 kernel-quotient-projection 𝑨 {𝑩} h = canonical-projection 𝑨 (kercon 𝑨{𝑩} h)

 πᵏ = kernel-quotient-projection
\end{code}

### The First Isomorphism Theorem

\begin{code}
 NoetherIsomorphism1 : (𝑨 : Algebra 𝓤 𝑆)                 -- domain is 𝑨
                       (𝑩 : Algebra 𝓦 𝑆)                -- codomain is 𝑩
                       (ϕ : hom 𝑨 𝑩)                     -- ϕ is an epimorphism from 𝑨 onto 𝑩
                       (ϕE : Epic ∣ ϕ ∣ )
                -- extensionality assumptions:
  →                                       (Bset : is-set ∣ 𝑩 ∣)
  →                                       (∀ a x → is-subsingleton (⟨ kercon 𝑨{𝑩} ϕ ⟩ a x))
  →                                       (∀ C → is-subsingleton (𝒜{A = ∣ 𝑨 ∣}{⟨ kercon 𝑨{𝑩} ϕ ⟩} C))
               ----------------------------------------------------------------------------------------
  →              Σ f ꞉ (epi (𝑨 [ 𝑩 ]/ker ϕ) 𝑩) , ( ∣ ϕ ∣ ≡ ∣ f ∣ ∘ ∣ πᵏ 𝑨 {𝑩} ϕ ∣ ) × is-embedding ∣ f ∣

 NoetherIsomorphism1 𝑨 𝑩 ϕ ϕE Bset ssR ssA = (fmap , fhom , fepic) , commuting , femb
  where
   θ : Congruence{𝓤}{𝓦} 𝑨
   θ = kercon 𝑨{𝑩} ϕ

   𝑨/θ : Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
   𝑨/θ = 𝑨 [ 𝑩 ]/ker ϕ

   fmap : ∣ 𝑨/θ ∣ → ∣ 𝑩 ∣
   fmap a = ∣ ϕ ∣ ⌜ a ⌝ --   fmap (.(⟨ θ ⟩ a) , a , refl _) = ∣ ϕ ∣ a

   fhom : is-homomorphism 𝑨/θ 𝑩 fmap
   fhom 𝑓 𝒂 =  ∣ ϕ ∣ ( fst ∥ (𝑓 ̂ 𝑨/θ) 𝒂 ∥ ) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             ∣ ϕ ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ (𝒂 x) ⌝) ) ≡⟨ ∥ ϕ ∥ 𝑓 (λ x → ⌜ (𝒂 x) ⌝)  ⟩
              (𝑓 ̂ 𝑩) (∣ ϕ ∣ ∘ (λ x → ⌜ (𝒂 x) ⌝)) ≡⟨ ap (λ - → (𝑓 ̂ 𝑩) -) (gfe λ x → 𝓇ℯ𝒻𝓁) ⟩
              (𝑓 ̂ 𝑩) (λ x → fmap (𝒂 x)) ∎

   fepic : Epic fmap
   fepic b = γ
    where
     a : ∣ 𝑨 ∣
     a = EpicInv ∣ ϕ ∣ ϕE b

     a/θ : ∣ 𝑨/θ ∣
     a/θ = ⟦ a ⟧

     bfa : b ≡ fmap a/θ
     bfa = (cong-app (EpicInvIsRightInv gfe ∣ ϕ ∣ ϕE) b)⁻¹

     γ : Image fmap ∋ b
     γ = Image_∋_.eq b a/θ bfa


   commuting : ∣ ϕ ∣ ≡ fmap ∘ ∣ πᵏ 𝑨 {𝑩} ϕ ∣
   commuting = 𝓇ℯ𝒻𝓁

   fmon : Monic fmap
   fmon (.(⟨ θ ⟩ a) , a , refl _) (.(⟨ θ ⟩ a') , a' , refl _) faa' = γ
    where
     aθa' : ⟨ θ ⟩ a a'
     aθa' = faa'

     γ : (⟨ θ ⟩ a , a , 𝓇ℯ𝒻𝓁) ≡ (⟨ θ ⟩ a' , a' , 𝓇ℯ𝒻𝓁)
     γ = class-extensionality' pe gfe ssR ssA (IsEquiv θ) aθa'

   femb : is-embedding fmap
   femb = monic-into-set-is-embedding Bset fmap fmon

\end{code}

#### miscellany

\begin{code}
𝒾𝒹 : {𝓤 : Universe} (A : Algebra 𝓤 𝑆) → hom A A
𝒾𝒹 _ = (λ x → x) , λ _ _ → 𝓇ℯ𝒻𝓁

id-is-hom : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → is-homomorphism 𝑨 𝑨 (𝑖𝑑 ∣ 𝑨 ∣)
id-is-hom = λ _ _ → refl _
\end{code}

### Homomorphism composition

\begin{code}
-- composition of homomorphisms 1
HCompClosed : {𝓠 𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑪 : Algebra 𝓦 𝑆)
 →            hom 𝑨 𝑩  →  hom 𝑩 𝑪
              --------------------
 →                 hom 𝑨 𝑪

HCompClosed (A , FA) (B , FB) (C , FC) (g , ghom) (h , hhom) = h ∘ g , γ
  where
   γ : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f  →  A) → (h ∘ g)(FA f a) ≡ FC f (h ∘ g ∘ a)

   γ f a = (h ∘ g) (FA f a) ≡⟨ ap h ( ghom f a ) ⟩
          h (FB f (g ∘ a)) ≡⟨ hhom f ( g ∘ a ) ⟩
          FC f (h ∘ g ∘ a) ∎

-- composition of homomorphisms 2
HomComp : {𝓠 𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓠 𝑆){𝑩 : Algebra 𝓤 𝑆}(𝑪 : Algebra 𝓦 𝑆)
 →            hom 𝑨 𝑩  →  hom 𝑩 𝑪
              --------------------
 →                 hom 𝑨 𝑪
HomComp {𝓠}{𝓤}{𝓦} 𝑨 {𝑩} 𝑪 f g = HCompClosed {𝓠}{𝓤}{𝓦} 𝑨 𝑩 𝑪 f g

-- composition of homomorphisms 3
∘-hom : {𝓧 𝓨 𝓩 : Universe}
        (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
        {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
 →      is-homomorphism{𝓧}{𝓨} 𝑨 𝑩 f  →  is-homomorphism{𝓨}{𝓩} 𝑩 𝑪 g
       --------------------------------------------------------------------
 →          is-homomorphism{𝓧}{𝓩} 𝑨 𝑪 (g ∘ f)

∘-hom 𝑨 𝑩 𝑪 {f} {g} fhom ghom = ∥ HCompClosed 𝑨 𝑩 𝑪 (f , fhom) (g , ghom) ∥

-- composition of homomorphisms 4
∘-Hom : {𝓧 𝓨 𝓩 : Universe}
        (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
        {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
 →      is-homomorphism{𝓧}{𝓨} 𝑨 𝑩 f  →  is-homomorphism{𝓨}{𝓩} 𝑩 𝑪 g
       --------------------------------------------------------------------
 →          is-homomorphism{𝓧}{𝓩} 𝑨 𝑪 (g ∘ f)

∘-Hom 𝑨 {𝑩} 𝑪 {f} {g} = ∘-hom 𝑨 𝑩 𝑪 {f} {g}


trans-hom : {𝓧 𝓨 𝓩 : Universe}
        (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
        (f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣ )(g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣ )
 →      is-homomorphism{𝓧}{𝓨} 𝑨 𝑩 f  →  is-homomorphism{𝓨}{𝓩} 𝑩 𝑪 g
       --------------------------------------------------------------------
 →          is-homomorphism{𝓧}{𝓩} 𝑨 𝑪 (g ∘ f)
trans-hom {𝓧}{𝓨}{𝓩} 𝑨 𝑩 𝑪 f g = ∘-hom {𝓧}{𝓨}{𝓩} 𝑨 𝑩 𝑪 {f}{g}
\end{code}

### Homomorphism decomposition

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

### The Second Isomorphism Theorem

\begin{code}
module _ {𝓠 𝓤 𝓦 : Universe}{gfe : global-dfunext} where
 HomFactor : {𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}{𝑪 : Algebra 𝓦 𝑆}
             (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
  →          (KER-pred ∣ h ∣) ⊆ (KER-pred ∣ g ∣)  →  Epic ∣ h ∣
            ------------------------------------------------
  →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

 HomFactor {A , FA}{B , FB}{C , FC}(g , ghom)(h , hhom) Kh⊆Kg hEpi = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpi) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → KER-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EpicInvIsRightInv gfe h hEpi) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = gfe  λ x → Kh⊆Kg (ξ x)

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EpicInvIsRightInv gfe h hEpi) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EpicInvIsRightInv gfe h hEpi)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EpicInvIsRightInv gfe h hEpi)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C) → ϕ (FC f a) ≡ FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))               ≡⟨ i   ⟩
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

### Homomorphisms of products

\begin{code}
⨅-hom : global-dfunext → {𝓠 𝓤 𝓘 : Universe}
       {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
 →     ((i : I) → hom (𝒜 i)(ℬ i))
     ---------------------------
 →       hom (⨅ 𝒜) (⨅ ℬ)

⨅-hom gfe {𝓠}{𝓤}{𝓘}{I}{𝒜}{ℬ} homs = ϕ , ϕhom
 where
  ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
  ϕ = λ x i → ∣ homs i ∣ (x i)

  ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒂 = gfe (λ i → ∥ homs i ∥ 𝑓 (λ x → 𝒂 x i))
\end{code}

### Projection homomorphisms

\begin{code}
⨅-projection-hom : {𝓤 𝓘 : Universe}
                   {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓤 𝑆}
                   --------------------------------
 →                  (i : I) → hom (⨅ 𝒜) (𝒜 i)

⨅-projection-hom {𝓤}{𝓘}{I}{𝒜} i = ϕi , ϕihom
 where
  ϕi : ∣ ⨅ 𝒜 ∣ → ∣ 𝒜 i ∣
  ϕi = λ x → x i

  ϕihom : is-homomorphism (⨅ 𝒜) (𝒜 i) ϕi
  ϕihom 𝑓 𝒂 = ϕi ((𝑓 ̂ ⨅ 𝒜) 𝒂) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             ((𝑓 ̂ ⨅ 𝒜) 𝒂) i ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             (𝑓 ̂ 𝒜 i) (λ x → 𝒂 x i) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             (𝑓 ̂ 𝒜 i) (λ x → ϕi (𝒂 x)) ∎
\end{code}

### Examples

\begin{code}
--Equalizers of functions
𝑬 : {𝓠 𝓤 : Universe}{A : 𝓠 ̇ }{B : 𝓤 ̇} → (g h : A → B) → Pred A 𝓤
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 𝑆} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x

𝑬𝑯-is-closed : funext 𝓥 𝓤
 →     {𝑓 : ∣ 𝑆 ∣ } {𝑨 𝑩 : Algebra 𝓤 𝑆}
       (g h : hom 𝑨 𝑩)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →     ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
       --------------------------------------------------
 →      ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 p =
   (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂))    ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
   (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
   (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
   ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)    ∎
\end{code}

### Isomorphism

We implement an extensional version of the notion of isomorphism between algebraic structures as follows.

\begin{code}
_≅_ : {𝓤 𝓦 : Universe} (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , ((∣ f ∣ ∘ ∣ g ∣) ∼ ∣ 𝒾𝒹 𝑩 ∣) × ((∣ g ∣ ∘ ∣ f ∣) ∼ ∣ 𝒾𝒹 𝑨 ∣)
\end{code}

Recall, f ~ g means f and g are extensionally equal; i.e., ∀ x, f x ≡ g x.

#### Isomorphism toolbox

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

### Properties of isomorphism

#### Isomorphism is obviously an equivalence relation.

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

#### Invariance under lift

\begin{code}
open Lift

--An algebra is isomorphic to its lift to a higher universe level
lift-alg-≅ : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≅ (lift-alg 𝑨 𝓦)
lift-alg-≅ {𝓤}{𝓦}{𝑨} = (lift , λ _ _ → 𝓇ℯ𝒻𝓁) ,
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

#### Invariance under product

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

### Embedding tools

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
\end{code}

### Isomorphism, intensionally

This is not used so much, and this section may be absent from future releases of the library.

\begin{code}
--Isomorphism
_≅'_ : {𝓤 𝓦 : Universe} (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑨 ≅' 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , ((∣ f ∣ ∘ ∣ g ∣) ≡ ∣ 𝒾𝒹 𝑩 ∣) × ((∣ g ∣ ∘ ∣ f ∣) ≡ ∣ 𝒾𝒹 𝑨 ∣)
-- An algebra is (intensionally) isomorphic to itself
id≅' : {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ≅' 𝑨
id≅' 𝑨 = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , 𝓇ℯ𝒻𝓁 , 𝓇ℯ𝒻𝓁

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

### Homomorphic images

We descibe here what seems to us the most useful definition of the class of homomomrphic images of an algebra.

\begin{code}
HomImage : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}(𝑩 : Algebra 𝓤 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓠 ⊔ 𝓤 ̇
HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b

HomImagesOf : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ (𝓦 ⁺) ̇
HomImagesOf {𝓤}{𝓦} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

_is-hom-image-of_ : {𝓤 𝓦 : Universe} (𝑩 : Algebra 𝓦 𝑆)
  →                (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇

_is-hom-image-of_ {𝓤}{𝓦} 𝑩 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf{𝓤}{𝓦} 𝑨) , ∣ 𝑪ϕ ∣ ≅ 𝑩
\end{code}

#### Homomorphic images of a class

\begin{code}
_is-hom-image-of-class_ : {𝓤 : Universe}
  →                       Algebra 𝓤 𝑆
  →                       Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)
  →                       𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

_is-hom-image-of-class_ {𝓤} 𝑩 𝓚 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
                             (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ 𝑆) ,
                     (𝑩 is-hom-image-of-class 𝓚)

all-ops-in_and_commute-with : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
all-ops-in 𝑨 and 𝑩 commute-with g = is-homomorphism 𝑨 𝑩 g
\end{code}

### Lifting tools

\begin{code}
open Lift

lift-function : (𝓧 : Universe){𝓨 : Universe}
                (𝓩 : Universe){𝓦 : Universe}
                (A : 𝓧 ̇)(B : 𝓨 ̇) → (f : A → B)
 →               Lift{𝓧}{𝓩} A → Lift{𝓨}{𝓦} B
lift-function  𝓧 {𝓨} 𝓩 {𝓦} A B f = λ la → lift (f (lower la))

lift-of-alg-epic-is-epic : (𝓧 : Universe){𝓨 : Universe}
                       (𝓩 : Universe){𝓦 : Universe}
                       (𝑨 : Algebra 𝓧 𝑆)
                       (𝑩 : Algebra 𝓨 𝑆)
                       (f : hom 𝑨 𝑩)  →  Epic ∣ f ∣
                      ---------------------------------------
 →                     Epic ∣ lift-alg-hom 𝓧 𝓩{𝓦} 𝑨 𝑩 f ∣

lift-of-alg-epic-is-epic 𝓧 {𝓨} 𝓩 {𝓦} 𝑨 𝑩 f fepi = lE
 where
  lA : Algebra (𝓧 ⊔ 𝓩) 𝑆
  lA = lift-alg 𝑨 𝓩
  lB : Algebra (𝓨 ⊔ 𝓦) 𝑆
  lB = lift-alg 𝑩 𝓦

  lf : hom (lift-alg 𝑨 𝓩) (lift-alg 𝑩 𝓦)
  lf = lift-alg-hom 𝓧 𝓩 𝑨 𝑩 f

  lE : (y : ∣ lB ∣ ) → Image ∣ lf ∣ ∋ y
  lE y = ξ
   where
    b : ∣ 𝑩 ∣
    b = lower y

    ζ : Image ∣ f ∣ ∋ b
    ζ = fepi b

    a : ∣ 𝑨 ∣
    a = Inv ∣ f ∣ b ζ

    η : y ≡ ∣ lf ∣ (lift a)
    η = y                                       ≡⟨ (intensionality lift∼lower) y ⟩
        lift b                                  ≡⟨ ap lift (InvIsInv ∣ f ∣ (lower y) ζ)⁻¹ ⟩
        lift (∣ f ∣ a)                           ≡⟨ (ap (λ - → lift (∣ f ∣ ( - a)))) (lower∼lift{𝓦 = 𝓦}) ⟩
        lift (∣ f ∣ ((lower{𝓦 = 𝓦} ∘ lift) a)) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        (lift ∘ ∣ f ∣ ∘ lower{𝓦 = 𝓦}) (lift a) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        ∣ lf ∣ (lift a)                          ∎
    ξ : Image ∣ lf ∣ ∋ y
    ξ = eq y (lift a) η


lift-alg-hom-image : {𝓧 : Universe}{𝓨 : Universe}{𝓩 : Universe}{𝓦 : Universe}{𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}
 →             𝑩 is-hom-image-of 𝑨 → (lift-alg 𝑩 𝓦) is-hom-image-of (lift-alg 𝑨 𝓩)
lift-alg-hom-image {𝓧}{𝓨}{𝓩}{𝓦}{𝑨}{𝑩} ((𝑪 , ϕ , ϕhom , ϕepic) , C≅B) = γ
 where
  lA : Algebra (𝓧 ⊔ 𝓩) 𝑆
  lA = lift-alg 𝑨 𝓩
  lB lC : Algebra (𝓨 ⊔ 𝓦) 𝑆
  lB = lift-alg 𝑩 𝓦
  lC = lift-alg 𝑪 𝓦

  lϕ : hom lA lC
  lϕ = (lift-alg-hom 𝓧 𝓩 𝑨 𝑪) (ϕ , ϕhom)

  lϕepic : Epic ∣ lϕ ∣
  lϕepic = lift-of-alg-epic-is-epic 𝓧 𝓩 𝑨 𝑪 (ϕ , ϕhom) ϕepic

  lCϕ : HomImagesOf {𝓧 ⊔ 𝓩}{𝓨 ⊔ 𝓦} lA
  lCϕ = lC , ∣ lϕ ∣ , ∥ lϕ ∥ , lϕepic

  lC≅lB : lC ≅ lB
  lC≅lB = lift-alg-iso 𝓨 𝓦 𝑪 𝑩 C≅B

  γ : lB is-hom-image-of lA
  γ = lCϕ , lC≅lB
\end{code}
