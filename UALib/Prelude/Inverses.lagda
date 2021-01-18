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

\end{code}

Note that the assertion `Image f ∋ y` must come with a proof, which is of the form `∃a f a = y`.  Thus, we always have a witness and the inverse can be *computed* by applying the function `Inv` (which we now define) to the function `f`.

\begin{code}

 Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
 Inv f .(f a) (im a) = a
 Inv f b (eq b a b≡fa) = a

\end{code}

Of course, we can prove that `Inv f` is really the (right-) inverse of `f`.

\begin{code}

 InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
            (b : B) (b∈Imgf : Image f ∋ b)
           ---------------------------------
  →         f (Inv f b b∈Imgf) ≡ b
 InvIsInv f .(f a) (im a) = refl _
 InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹

\end{code}

#### Surjective functions

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

 EpicInvIsRightInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                     (f : A → B)  (fE : Epic f)
                     ----------------------------
  →                   f ∘ (EpicInv f fE) ≡ 𝑖𝑑 B

 EpicInvIsRightInv fe f fE = fe (λ x → InvIsInv f x (fE x))

\end{code}

#### Injective functions

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

#### Bijective functions

Finally, bijective functions are defined.

\begin{code}

 Bijective : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) → 𝓤 ⊔ 𝓦 ̇
 Bijective f = Epic f × Monic f

 Inverse : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
            (f : A → B) → Bijective f
            -------------------------
  →          B → A

 Inverse f fbi b = Inv f b (fst( fbi ) b)

\end{code}

#### Neutral elements

The next three lemmas appeared in the `UF-Base` and `UF-Equiv` modules which were (at one time) part of Matin Escsardo's UF Agda repository.

\begin{code}

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

\end{code}

#### Injective functions are set embeddings

This is the first point at which [truncation](UALib.Preface.html#truncation) comes into play.  An [embedding](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#embeddings) is defined in the [Type Topology][] library as follows:

```agda
is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)
```

where

```agda
is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y
```

and

```agda
fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ domain f , f x ≡ y
```

This is a very nice, natural way to represent what we usually mean in mathematics by embedding.  However, with this definition, an embedding does not correspond simply to an injective map.  However, if we assume that the codomain `B` has unique identity proofs (i.e., is a set), then we can prove that a monic function into `B` is an embedding as follows:

\begin{code}

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

\end{code}

Of course, invertible maps are embeddings.

\begin{code}

 invertibles-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓦 ̇ }(f : X → Y)
  →               invertible f → is-embedding f
 invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)

\end{code}

Finally, if we have a proof `p : is-embedding f` that the map `f` is an embedding, here's a tool that makes it easier to apply `p`.

\begin{code}

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
