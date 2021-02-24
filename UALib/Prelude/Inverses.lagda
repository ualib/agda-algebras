---
layout: default
title : UALib.Prelude.Inverses module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="inverses">Inverses</a>

This section presents the [UALib.Prelude.Inverses][] module of the [Agda Universal Algebra Library][].
Here we define (the syntax of) a type for the (semantic concept of) **inverse image** of a function.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Inverses where

open import Prelude.Equality public 
open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁) public
-- pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

module _ {𝓤 𝓦 : Universe} where

 open import MGS-Subsingleton-Theorems using (funext)

 data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

 ImageIsImage : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                (f : A → B) (b : B) (a : A)
  →              b ≡ f a
                ---------------------------
  →              Image f ∋ b

 ImageIsImage {A}{B} f b a b≡fa = eq b a b≡fa

\end{code}

Note that an inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Thus, a proof that `b` belongs to the image of `f` (i.e., an inhabitant of `Image f ∋ b`), always has a witness `a : A`, and a proof that `b = f a`, so a (pseudo)inverse can actually be *computed*.

For convenience, we define a pseudo-inverse function, which we call `Inv`, that takes `b : B` and `(a , p) : Image f ∋ b` and returns `a`.

\begin{code}

 Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
 Inv f .(f a) (im a) = a
 Inv f _ (eq _ a _) = a

\end{code}

Of course, we can prove that `Inv f` is really the (right-) inverse of `f`.

\begin{code}

 open import MGS-MLTT using (_⁻¹) public

 InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
            (b : B) (b∈Imgf : Image f ∋ b)
           ---------------------------------
  →         f (Inv f b b∈Imgf) ≡ b
 InvIsInv f .(f a) (im a) = refl _
 InvIsInv f _ (eq _ _ p) = p ⁻¹

\end{code}





#### <a id="surjective-functions">Surjective functions</a>

An epic (or surjective) function from type `A : 𝓤 ̇` to type `B : 𝓦 ̇` is as an inhabitant of the `Epic` type, which we define as follows.

\begin{code}

 Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
 Epic g = ∀ y → Image g ∋ y

\end{code}

We obtain the right-inverse (or pseudoinverse) of an epic function `f` by applying the function `EpicInv` (which we now define) to the function `f` along with a proof, `fE : Epic f`, that `f` is surjective.

\begin{code}

 EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
           (f : A → B) → Epic f
           -------------------------
  →           B → A

 EpicInv f fE b = Inv f b (fE b)

\end{code}

The function defined by `EpicInv f fE` is indeed the right-inverse of `f`.

\begin{code}

 open import MGS-MLTT using (_∘_; 𝑖𝑑) public
 open import MGS-Subsingleton-Theorems using (funext)

 EpicInvIsRightInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                     (f : A → B)  (fE : Epic f)
                     ----------------------------
  →                   f ∘ (EpicInv f fE) ≡ 𝑖𝑑 B

 EpicInvIsRightInv fe f fE = fe (λ x → InvIsInv f x (fE x))

\end{code}





#### <a id="injective-functions">Injective functions</a>

We say that a function `g : A → B` is monic (or injective) if we have a proof of `Monic g`, where

\begin{code}

 Monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ }(g : A → B) → 𝓤 ⊔ 𝓦 ̇
 Monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂

\end{code}

Again, we obtain a pseudoinverse. Here it is obtained by applying the function `MonicInv` to `g` and a proof that `g` is monic.

\begin{code}

 --The (pseudo-)inverse of a monic function
 MonicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
            (f : A → B)  →  Monic f
           -----------------------------
  →         (b : B) →  Image f ∋ b  →  A

 MonicInv f _ = λ b Imf∋b → Inv f b Imf∋b

\end{code}

The function defined by `MonicInv f fM` is the left-inverse of `f`.

\begin{code}

 --The (psudo-)inverse of a monic is the left inverse.
 MonicInvIsLeftInv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                     (f : A → B) (fmonic : Monic f)(x : A)
                    ----------------------------------------
   →                 (MonicInv f fmonic) (f x) (im x) ≡ x

 MonicInvIsLeftInv f fmonic x = refl _

\end{code}





#### <a id="composition-laws">Composition laws</a>

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 open import MGS-Subsingleton-Theorems using (funext)
 open import MGS-Subsingleton-Truncation using (_∙_) public

 epic-factor : funext 𝓨 𝓨 → {A : 𝓧 ̇}{B : 𝓨 ̇}{C : 𝓩 ̇}
               (β : A → B)(ξ : A → C)(ϕ : C → B)
  →            β ≡ ϕ ∘ ξ →  Epic β → Epic ϕ

 epic-factor fe {A}{B}{C} β ξ ϕ compId βe y = γ
  where
   βinv : B → A
   βinv = EpicInv β βe

   ζ : β (βinv y) ≡ y
   ζ = ap (λ - → - y) (EpicInvIsRightInv fe β βe)
   η : (ϕ ∘ ξ) (βinv y) ≡ y
   η = (ap (λ - → - (βinv y)) (compId ⁻¹)) ∙ ζ
   γ : Image ϕ ∋ y
   γ = eq y (ξ (βinv y)) (η ⁻¹)

\end{code}





#### <a id="neutral-elements">Neutral elements</a>

The next three lemmas appeared in the `UF-Base` and `UF-Equiv` modules which were (at one time) part of Matin Escsardo's UF Agda repository.

\begin{code}

refl-left-neutral : {𝓧 : Universe} {X : 𝓧 ̇ } {x y : X} (p : x ≡ y) → (refl _) ∙ p ≡ p
refl-left-neutral (refl _) = refl _

refl-right-neutral : {𝓧 : Universe}{X : 𝓧 ̇ } {x y : X} (p : x ≡ y) → p ≡ p ∙ (refl _)
refl-right-neutral p = refl _

identifications-in-fibers : {𝓧 𝓨 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ } (f : X → Y)
                            (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
 →                          (Σ γ ꞉ x ≡ x' , ap f γ ∙ p' ≡ p) → (x , p) ≡ (x' , p')
identifications-in-fibers f .(f x) x .x 𝓇ℯ𝒻𝓁 p' (𝓇ℯ𝒻𝓁 , r) = g
 where
  g : x , 𝓇ℯ𝒻𝓁 ≡ x , p'
  g = ap (λ - → (x , -)) (r ⁻¹ ∙ refl-left-neutral _)

\end{code}

#### Injective functions are set embeddings

This is the first point at which [truncation](UALib.Preface.html#truncation) comes into play.  An [embedding](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#embeddings) is defined in the [Type Topology][] library as follows.<sup>1</sup>

\begin{code}

open import MGS-MLTT using (domain; codomain) public

module hidden where

 is-subsingleton : {𝓧 : Universe} → 𝓧 ̇ → 𝓧 ̇
 is-subsingleton X = (x y : X) → x ≡ y

 fiber : {𝓧 𝓨 : Universe}{X : 𝓧 ̇ }{Y : 𝓨 ̇ }(f : X → Y) → Y → 𝓧 ⊔ 𝓨 ̇
 fiber f y = Σ x ꞉ domain f , f x ≡ y

 is-embedding : {𝓧 𝓨 : Universe}{X : 𝓧 ̇ } {Y : 𝓨 ̇ } → (X → Y) → 𝓧 ⊔ 𝓨 ̇
 is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)

\end{code}

This is a very nice, natural way to represent what we usually mean in mathematics by embedding.  Observe that an embedding does not simply correspond to an injective map.  However, if we assume that the codomain `B` has unique identity proofs (i.e., is a set), then we can prove that a monic function into `B` is an embedding as follows:

\begin{code}

open import MGS-MLTT using (transport)
open import MGS-Subsingleton-Truncation using (fiber) public
open import MGS-Embeddings using (is-embedding; to-Σ-≡; invertible; equivs-are-embeddings; invertibles-are-equivs) public
open import MGS-Embeddings using (is-set)

monic-into-set-is-embedding : {𝓧 𝓨 : Universe}{A : 𝓧 ̇}{B : 𝓨 ̇} → is-set B
 →                            (f : A → B)  →  Monic f
                              -----------------------
 →                            is-embedding f

monic-into-set-is-embedding Bset f fmon b (a , fa≡b) (a' , fa'≡b) = γ
 where
  faa' : f a ≡ f a'
  faa' = ≡-Trans (f a) (f a') fa≡b (fa'≡b ⁻¹)

  aa' : a ≡ a'
  aa' = fmon a a' faa'

  𝒜 : domain f → _ ̇
  𝒜 a = f a ≡ b

  arg1 : Σ p ꞉ (a ≡ a') , (transport 𝒜 p fa≡b) ≡ fa'≡b
  arg1 = aa' , Bset (f a') b (transport 𝒜 aa' fa≡b) fa'≡b

  γ : a , fa≡b ≡ a' , fa'≡b
  γ = to-Σ-≡ arg1

\end{code}

Of course, invertible maps are embeddings.

\begin{code}

invertibles-are-embeddings : {𝓧 𝓨 : Universe}
                             {X : 𝓧 ̇} {Y : 𝓨 ̇} (f : X → Y)
 →                           invertible f → is-embedding f

invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)

\end{code}

Finally, if we have a proof `p : is-embedding f` that the map `f` is an embedding, here's a tool that can make it easier to apply `p`.

\begin{code}

embedding-elim : {𝓧 𝓨 : Universe}{X : 𝓧 ̇} {Y : 𝓨 ̇}
                 (f : X → Y) → is-embedding f
 →               ∀ x x' → f x ≡ f x' → x ≡ x'

embedding-elim f femb x x' fxfx' = ap pr₁ ((femb (f x)) fa fb)
 where
  fa : fiber f (f x)
  fa = x , 𝓇ℯ𝒻𝓁

  fb : fiber f (f x)
  fb = x' , (fxfx' ⁻¹)

\end{code}


-------------------------------------

<sup>1</sup> Whenever we wish to hide some code from the rest of the development, we will enclose it in a module called `hidden.` In this case, we don't want the code inside the `hidden` module to conflict with the original definitions of these functions from Escardo's Type Topology library, which we will import later.  As long as we don't invoke `open hidden`, the code inside the `hidden` model remains essentially hidden (for the purposes of resolving conflicts, though Agda *will* type-check the code).


[← Prelude.Equality](Prelude.Equality.html)
<span style="float:right;">[Prelude.Extensionality →](Prelude.Extensionality.html)</span>

{% include UALib.Links.md %}
