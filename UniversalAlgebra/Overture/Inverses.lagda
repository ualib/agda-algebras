---
layout: default
title : Overture.Inverses module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="inverses">Inverses</a>

This is the [Overture.Inverses][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Inverses where

open import Overture.FunExtensionality public

open import MGS-Embeddings
 using (equivs-are-embeddings; invertible; invertibles-are-equivs) public

\end{code}

We begin by defining an inductive type that represents the semantic concept of *inverse image* of a function.

\begin{code}

module _ {A : Type 𝓤 }{B : Type 𝓦 } where

 data Image_∋_ (f : A → B) : B → Type (𝓤 ⊔ 𝓦)
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

\end{code}

Next we verify that the type behaves as we expect.

\begin{code}

 ImageIsImage : (f : A → B)(b : B)(a : A) → b ≡ f a → Image f ∋ b
 ImageIsImage f b a b≡fa = eq b a b≡fa

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f {.(f a)} (im a) = a
 Inv f (eq _ a _) = a

\end{code}

We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

\begin{code}

 InvIsInv : (f : A → B){b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInv f {.(f a)} (im a) = refl
 InvIsInv f (eq _ _ p) = p ⁻¹

\end{code}





#### <a id="epics">Epics (surjective functions)</a>

An epic (or surjective) function from `A` to `B` is as an inhabitant of the `Epic` type, which we now define.

\begin{code}

 Epic : (A → B) →  Type (𝓤 ⊔ 𝓦)
 Epic f = ∀ y → Image f ∋ y

\end{code}

With the next definition, we can represent the *right-inverse* of an epic function.

\begin{code}

 EpicInv : (f : A → B) → Epic f → B → A
 EpicInv f fE b = Inv f (fE b)

\end{code}
The right-inverse of `f` is obtained by applying `EpicInv` to `f` and a proof of `Epic f`. To see that this does indeed give the right-inverse we prove the `EpicInvIsRightInv` lemma below. This requires function composition, denoted `∘` and defined in the [Type Topology][] library.

\begin{code}

module hide-∘ {A : Type 𝓤}{B : Type 𝓦}{C : B → Type 𝓦 } where

 _∘_ : Π C → (f : A → B) → (x : A) → C (f x)
 g ∘ f = λ x → g (f x)

open import MGS-MLTT using (_∘_) public

\end{code}

Note that the next proof requires function extensionality, which we postulate in the module declaration.

\begin{code}

module _ {fe : funext 𝓦 𝓦}{A : Type 𝓤}{B : Type 𝓦} where

 EpicInvIsRightInv : (f : A → B)(fE : Epic f) → f ∘ (EpicInv f fE) ≡ 𝑖𝑑 B
 EpicInvIsRightInv f fE = fe (λ x → InvIsInv f (fE x))

\end{code}

We can also prove the following composition law for epics.

\begin{code}

 epic-factor : {C : Type 𝓩}(f : A → B)(g : A → C)(h : C → B)
  →            f ≡ h ∘ g → Epic f → Epic h

 epic-factor f g h compId fe y = γ
  where
   finv : B → A
   finv = EpicInv f fe

   ζ : f (finv y) ≡ y
   ζ = cong-app (EpicInvIsRightInv f fe) y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (compId ⁻¹)(finv y)) ∙ ζ

   γ : Image h ∋ y
   γ = eq y (g (finv y)) (η ⁻¹)

\end{code}






#### <a id="monics">Monics (injective functions)</a>

We say that a function `f : A → B` is *monic* (or *injective*) if it does not map distinct elements to a common point. This following type manifests this property.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where

 Monic : (f : A → B) → Type (𝓤 ⊔ 𝓦)
 Monic f = ∀ x y → f x ≡ f y → x ≡ y

\end{code}

Again, we obtain a pseudoinverse. Here it is obtained by applying the function `MonicInv` to `g` and a proof that `g` is monic.

\begin{code}

 MonicInv : (f : A → B) → Monic f → (b : B) → Image f ∋ b → A
 MonicInv f _ = λ b imfb → Inv f imfb

\end{code}

The function defined by `MonicInv f fM` is the left-inverse of `f`.

\begin{code}

 MonicInvIsLeftInv : {f : A → B}{fM : Monic f}{x : A} → (MonicInv f fM)(f x)(im x) ≡ x
 MonicInvIsLeftInv = refl

\end{code}





#### <a id="embeddings">Embeddings</a>

The `is-embedding` type is defined in the [Type Topology][] library in the following way.

\begin{code}
module hide-is-embedding{A : Type 𝓤}{B : Type 𝓦} where

 is-embedding : (A → B) → Type (𝓤 ⊔ 𝓦)
 is-embedding f = ∀ b → is-subsingleton (fiber f b)

open import MGS-Embeddings using (is-embedding) public

\end{code}

Thus, `is-embedding f` asserts that `f` is a function all of whose fibers are subsingletons. Observe that an embedding is not simply an injective map. However, if we assume that the codomain `B` has *unique identity proofs* (UIP), then we can prove that a monic function into `B` is an embedding.  We will do exactly that in the [Relations.Truncation][] module when we take up the topic of *sets* and the UIP.

Finding a proof that a function is an embedding isn't always easy, but one path that is often straightforward is to first prove that the function is invertible and then invoke the following theorem.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where

 invertibles-are-embeddings : (f : A → B) → invertible f → is-embedding f
 invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)

\end{code}

-------------------------------------

<p></p>

[← Overture.FunExtensionality](Overture.FunExtensionality.html)
<span style="float:right;">[Overture.Lifts →](Overture.Lifts.html)</span>


{% include UALib.Links.md %}
