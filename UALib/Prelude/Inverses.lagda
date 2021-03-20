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

module Prelude.Inverses where

open import Prelude.Extensionality public

open import MGS-Embeddings
 using (equivs-are-embeddings; invertible; invertibles-are-equivs) public

\end{code}

We begin by defining an inductive type that represents the semantic concept of **inverse image** of a function.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
  where
  im : (x : A) → Image f ∋ f x
  eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b


module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 ImageIsImage : (f : A → B)(b : B)(a : A) → b ≡ f a → Image f ∋ b
 ImageIsImage f b a b≡fa = eq b a b≡fa

\end{code}

The following restatement of the last lemma simply rearranges the arguments in case that makes it clearer.

\begin{code}

 ImageIsImage' : (f : A → B)(a : A)(b : B) → f a ≡ b → Image f ∋ b
 ImageIsImage' f a b fab = eq b a (fab ⁻¹)

\end{code}

Note that an inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a "witness" `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

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





#### <a id="epics"">Epics (surjective functions)</a>

An epic (or surjective) function from type `A : 𝓤 ̇` to type `B : 𝓦 ̇` is as an inhabitant of the `Epic` type, which we define as follows.

\begin{code}

 Epic : (g : A → B) →  𝓤 ⊔ 𝓦 ̇
 Epic g = ∀ y → Image g ∋ y

\end{code}

We obtain the right-inverse (or pseudoinverse) of an epic function `f` by applying the function `EpicInv` (which we now define) to the function `f` along with a proof, `fE : Epic f`, that `f` is surjective.

\begin{code}

 EpicInv : (f : A → B) → Epic f → B → A
 EpicInv f fE b = Inv f (fE b)

\end{code}

The function defined by `EpicInv f fE` is indeed the right-inverse of `f`. To state this, we'll use the function composition operation, `∘`, which is already defined in the [Type Topology][] library as follows.

\begin{code}

module hide-∘ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 _∘_ : {C : B → 𝓦 ̇ } → Π C → (f : A → B) → (x : A) → C (f x)
 g ∘ f = λ x → g (f x)

open import MGS-MLTT using (_∘_) public


module _ {𝓤 𝓦 : Universe}{fe : funext 𝓦 𝓦}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 EpicInvIsRightInv : (f : A → B)(fE : Epic f) → f ∘ (EpicInv f fE) ≡ 𝑖𝑑 B
 EpicInvIsRightInv f fE = fe (λ x → InvIsInv f (fE x))

\end{code}





#### <a id="monics">Monics (injective functions)</a>

We say that a function `g : A → B` is *monic* (or *injective* or *one-to-one*) if it doesn't map distinct elements to a common point. This property is formalized quite naturally using the `Monic` type, which we now define.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 Monic : (g : A → B) → 𝓤 ⊔ 𝓦 ̇
 Monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂

\end{code}

Again, we obtain a pseudoinverse. Here it is obtained by applying the function `MonicInv` to `g` and a proof that `g` is monic.

\begin{code}

 MonicInv : (f : A → B) → Monic f → (b : B) → Image f ∋ b → A
 MonicInv f _ = λ b Imf∋b → Inv f Imf∋b

\end{code}

The function defined by `MonicInv f fM` is the left-inverse of `f`.

\begin{code}

 MonicInvIsLeftInv : {f : A → B}{fM : Monic f}{x : A}
   →                 (MonicInv f fM)(f x)(im x) ≡ x
 MonicInvIsLeftInv = refl

\end{code}



#### <a id="composition-laws">Composition laws</a>

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 epic-factor : funext 𝓨 𝓨 → {A : 𝓧 ̇}{B : 𝓨 ̇}{C : 𝓩 ̇}
               (β : A → B)(ξ : A → C)(ϕ : C → B)
  →            β ≡ ϕ ∘ ξ →  Epic β → Epic ϕ

 epic-factor fe {A}{B}{C} β ξ ϕ compId βe y = γ
  where
   βinv : B → A
   βinv = EpicInv β βe

   ζ : β (βinv y) ≡ y
   ζ = cong-app (EpicInvIsRightInv {fe = fe} β βe) y

   η : (ϕ ∘ ξ) (βinv y) ≡ y
   η = (cong-app (compId ⁻¹)(βinv y)) ∙ ζ

   γ : Image ϕ ∋ y
   γ = eq y (ξ (βinv y)) (η ⁻¹)

\end{code}





#### <a id="embeddings">Embeddings</a>

The `is-embedding` type is defined in the [Type Topology][] library in the following way.

\begin{code}
module hide-is-embedding {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓦 ̇ } where

 is-embedding : (A → B) → 𝓤 ⊔ 𝓦 ̇
 is-embedding f = ∀ b → is-subsingleton (fiber f b)

open import MGS-Embeddings using (is-embedding) public

\end{code}

Thus, `is-embedding f` asserts that `f` is a function all of whose fibers are subsingletons. This is a natural way to represent what we usually mean in mathematics by embedding.  Observe that an embedding does not simply correspond to an injective map.  However, if we assume that the codomain `B` has unique identity proofs (i.e., is a set), then we can prove that a monic function into `B` is an embedding. We will do so in the [Relations.Truncation][] module when we take up the topic of sets in some detail.

Finding a proof that a function is an embedding isn't always easy, but one path that is often straightforward is to first prove that the function is invertible and then invoke the following theorem.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 invertibles-are-embeddings : (f : A → B) → invertible f → is-embedding f
 invertibles-are-embeddings f fi = equivs-are-embeddings f (invertibles-are-equivs f fi)

\end{code}

Finally, embeddings are monic; from a proof `p : is-embedding f` that `f` is an embedding we can construct a proof of `Monic f`.  We confirm this as follows.

\begin{code}

 embedding-is-monic : (f : A → B) → is-embedding f → Monic f
 embedding-is-monic f femb x y fxfy = ap pr₁ ((femb (f x)) fx fy)
  where
  fx : fiber f (f x)
  fx = x , refl

  fy : fiber f (f x)
  fy = y , (fxfy ⁻¹)

\end{code}


-------------------------------------

<p></p>

[← Prelude.Extensionality](Prelude.Extensionality.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>


{% include UALib.Links.md %}


<!-- 
This is the first point at which [truncation](UALib.Preface.html#truncation) comes into play.  An [embedding](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#embeddings) is defined in the [Type Topology][] library, using the `is-subsingleton` type [described earlier](Prelude.Extensionality.html#alternative-extensionality-type), as follows.
-->
