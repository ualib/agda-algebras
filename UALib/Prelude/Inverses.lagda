---
layout: default
title : UALib.Prelude.Inverses module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="inverses">Inverses</a>

This section presents the [UALib.Prelude.Inverses][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module UALib.Prelude.Inverses where


open import UALib.Prelude.Equality public

open import UALib.Prelude.Preliminaries using (_⁻¹; funext; _∘_; _∙_; 𝑖𝑑; fst; snd; is-set; is-embedding;
 transport; to-Σ-≡; invertible; equivs-are-embeddings; invertibles-are-equivs; fiber; 𝓇ℯ𝒻𝓁) public


module _ {𝓤 𝓦 : Universe} where

 data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

 ImageIsImage : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
               (f : A → B) (b : B) (a : A)
  →              b ≡ f a
               ----------------------------
  →              Image f ∋ b
 ImageIsImage {A}{B} f b a b≡fa = eq b a b≡fa

 Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
 Inv f .(f a) (im a) = a
 Inv f b (eq b a b≡fa) = a

 InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
            (b : B) (b∈Imgf : Image f ∋ b)
           ---------------------------------
  →         f (Inv f b b∈Imgf) ≡ b
 InvIsInv f .(f a) (im a) = refl _
 InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

 Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
 Epic g = ∀ y → Image g ∋ y


 EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
 EpicInv f fEpi b = Inv f b (fEpi b)

 -- The (psudo-)inverse of an epic is the right inverse.
 EpicInvIsRightInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
              (f : A → B)  (fEpi : Epic f)
             ---------------------------------
  →           f ∘ (EpicInv f fEpi) ≡ 𝑖𝑑 B
 EpicInvIsRightInv fe f fEpi = fe (λ x → InvIsInv f x (fEpi x))

 Monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) → 𝓤 ⊔ 𝓦 ̇
 Monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂

 --The (pseudo-)inverse of a monic function
 MonicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Monic f
  →           (b : B) → Image f ∋ b → A
 MonicInv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

 --The (psudo-)inverse of a monic is the left inverse.
 MonicInvIsLeftInv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                     (f : A → B) (fmonic : Monic f)(x : A)
                    ----------------------------------------
   →                 (MonicInv f fmonic) (f x) (im x) ≡ x
 MonicInvIsLeftInv f fmonic x = refl _

 Bijective : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) → 𝓤 ⊔ 𝓦 ̇
 Bijective f = Epic f × Monic f

 Inverse : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
  →         Bijective f  →   B → A
 Inverse f fbi b = Inv f b (fst( fbi ) b)

--The next three are from UF-Base.lagda and UF-Equiv.lagda (resp.) which, at one time,
--were part of Matin Escsardo's UF Agda repository.
refl-left-neutral : {𝓤 : Universe} {X : 𝓤 ̇ } {x y : X} (p : x ≡ y) → (refl _) ∙ p ≡ p
refl-left-neutral (refl _) = refl _

refl-right-neutral : {𝓤 : Universe}{X : 𝓤 ̇ } {x y : X} (p : x ≡ y) → p ≡ p ∙ (refl _)
refl-right-neutral p = refl _

identifications-in-fibers : {𝓤 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
 →                          (Σ γ ꞉ x ≡ x' , ap f γ ∙ p' ≡ p) → (x , p) ≡ (x' , p')
identifications-in-fibers f .(f x) x .x 𝓇ℯ𝒻𝓁 p' (𝓇ℯ𝒻𝓁 , r) = g
 where
  g : x , 𝓇ℯ𝒻𝓁 ≡ x , p'
  g = ap (λ - → (x , -)) (r ⁻¹ ∙ refl-left-neutral _)


module _ {𝓤 𝓦 : Universe} where

 monic-into-set-is-embedding : {A : 𝓤 ̇}{B : 𝓦 ̇} → is-set B
  →                            (f : A → B)  →  Monic f
                             ---------------------------
  →                             is-embedding f

 monic-into-set-is-embedding {A} Bset f fmon b (a , fa≡b) (a' , fa'≡b) = γ
  where
   faa' : f a ≡ f a'
   faa' = ≡-Trans (f a) (f a') fa≡b (fa'≡b ⁻¹)

   aa' : a ≡ a'
   aa' = fmon a a' faa'

   𝒜 : A → 𝓦 ̇
   𝒜 a = f a ≡ b

   arg1 : Σ p ꞉ (a ≡ a') , (transport 𝒜 p fa≡b) ≡ fa'≡b
   arg1 = aa' , Bset (f a') b (transport 𝒜 aa' fa≡b) fa'≡b

   γ : a , fa≡b ≡ a' , fa'≡b
   γ = to-Σ-≡ arg1

 invertibles-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓦 ̇ }(f : X → Y)
  →               invertible f → is-embedding f
 invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)

 -- Embedding elimination (makes it easier to apply is-embedding)
 embedding-elim : {X : 𝓤 ̇ } {Y : 𝓦 ̇ }{f : X → Y}
  →               is-embedding f
  →               (x x' : X)
  →               f x ≡ f x' → x ≡ x'
 embedding-elim {f = f} femb x x' fxfx' = γ
  where
   fibx : fiber f (f x)
   fibx = x , 𝓇ℯ𝒻𝓁
   fibx' : fiber f (f x)
   fibx' = x' , ((fxfx') ⁻¹)
   iss-fibffx : is-subsingleton (fiber f (f x))
   iss-fibffx = femb (f x)
   fibxfibx' : fibx ≡ fibx'
   fibxfibx' = iss-fibffx fibx fibx'
   γ : x ≡ x'
   γ = ap pr₁ fibxfibx'

\end{code}

-------------------------------------

[← UALib.Prelude.Equality](UALib.Prelude.Equality.html)
<span style="float:right;">[UALib.Prelude.Extensionality →](UALib.Prelude.Extensionality.html)</span>

{% include UALib.Links.md %}
