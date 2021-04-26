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
open import Data.Product renaming (_,_ to infixr 50 _,_) using (_×_) public

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

 IsSurjective : (A → B) →  Type (𝓤 ⊔ 𝓦)
 IsSurjective f = ∀ y → Image f ∋ y

 Surjective : Type (𝓤 ⊔ 𝓦)
 Surjective = Σ f ꞉ (A → B) , IsSurjective f

\end{code}

With the next definition, we can represent the *right-inverse* of an epic function.

\begin{code}

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

\end{code}
The right-inverse of `f` is obtained by applying `EpicInv` to `f` and a proof of `Epic f`. To see that this does indeed give the right-inverse we prove the `EpicInvIsRightInv` lemma below. This requires function composition, denoted `∘` and defined in the [Type Topology][] library.

\begin{code}

module hide-∘ {A : Type 𝓤}{B : Type 𝓦}{C : B → Type 𝓦 } where

 _∘_ : Π C → (f : A → B) → (x : A) → C (f x)
 g ∘ f = λ x → g (f x)

open import Function.Base renaming (_∘_ to infixl 70 _∘_) using (id) public

\end{code}

The following are some useful lemmas lifted from the `MGS-Retracts` module of Escardó's [Type Topology][] library.

\begin{code}

𝑖𝑑 : (A : Type 𝓤 ) → A → A
𝑖𝑑 A = λ x → x


has-section : {X : Type 𝓤 } {Y : Type 𝓦 } → (X → Y) → Type (𝓤 ⊔ 𝓦)
has-section {𝓤}{𝓦}{X}{Y} r = Σ s ꞉ (Y → X), r ∘ s ∼ id

_◁_ : Type 𝓤 → Type 𝓦 → Type (𝓤 ⊔ 𝓦)
X ◁ Y = Σ r ꞉ (Y → X), has-section r

subst-is-retraction : {X : Type 𝓤} (A : X → Type 𝓥) {x y : X} (p : x ≡ y)
                        → subst A p ∘ subst A (p ⁻¹) ∼ 𝑖𝑑 (A y)
subst-is-retraction A refl = λ x → refl

subst-is-section : {X : Type 𝓤} (A : X → Type 𝓥) {x y : X} (p : x ≡ y)
 →                 subst A (p ⁻¹) ∘ subst A p ∼ 𝑖𝑑 (A x)
subst-is-section A refl = λ x → refl


\end{code}





Note that the next proof requires function extensionality, which we postulate in the module declaration.

\begin{code}

module _ {fe : funext 𝓦 𝓦}{A : Type 𝓤}{B : Type 𝓦} where

 EpicInvIsRightInv : (f : A → B)(fE : IsSurjective f) → f ∘ (SurjInv f fE) ≡ 𝑖𝑑 B
 EpicInvIsRightInv f fE = fe (λ x → InvIsInv f (fE x))

\end{code}

We can also prove the following composition law for epics.

\begin{code}

 epic-factor : {C : Type 𝓩}(f : A → B)(g : A → C)(h : C → B)
  →            f ≡ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = γ
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : f (finv y) ≡ y
   ζ = cong-app (EpicInvIsRightInv f fe) y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (compId ⁻¹)(finv y)) ∙ ζ

   γ : Image h ∋ y
   γ = eq y (g (finv y)) (η ⁻¹)

\end{code}






#### <a id="injective-functions">Injective functions</a>

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map distinct elements to a common point. This following type manifests this property.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where

 IsInjective : (A → B) → Type (𝓤 ⊔ 𝓦)
 IsInjective f = ∀ {x y} → f x ≡ f y → x ≡ y

 Injective : Type (𝓤 ⊔ 𝓦)
 Injective = Σ f ꞉ (A → B) , IsInjective f

\end{code}

A left inverse is obtained as follows.

\begin{code}

 InjInv : (f : A → B) → IsInjective f → (b : B) → Image f ∋ b → A
 InjInv f _ = λ b imfb → Inv f imfb

\end{code}

We prove that the function defined by `MonicInv f fM` is the left-inverse of `f` by
applying the function `InjInv` to `g` and a proof that `g` is injective.

\begin{code}

 InjInvIsLeftInv : {f : A → B}{fM : IsInjective f}{x : A} → (InjInv f fM)(f x)(im x) ≡ x
 InjInvIsLeftInv = refl

id-is-injective : {A : Type 𝓤} → IsInjective{A = A}{B = A} (λ x → x)
id-is-injective = λ z → z

∘-injective : {A : Type 𝓤}{B : Type 𝓦}{C : Type 𝓩}{f : A → B}{g : B → C}
 →            IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective finj ginj = λ z → finj (ginj z)

\end{code}





#### <a id="embeddings">Embeddings</a>

The `is-embedding` type is defined in the `MGS-Embeddings` module of the [Type Topology][] library in the following way.

\begin{code}

is-embedding : {A : Type 𝓤}{B : Type 𝓦} → (A → B) → Type (𝓤 ⊔ 𝓦)
is-embedding f = ∀ b → is-prop (fiber f b)

singleton-type : {A : Type 𝓤} → A → Type 𝓤
singleton-type {𝓤}{A} x = Σ y ꞉ A , (y ≡ x)


\end{code}

Thus, `is-embedding f` asserts that `f` is a function all of whose fibers are subsingletons. Observe that an embedding is not simply an injective map. However, if we assume that the codomain `B` has *unique identity proofs* (UIP), then we can prove that a monic function into `B` is an embedding.  We will do exactly that in the [Relations.Truncation][] module when we take up the topic of *sets* and the UIP.

Finding a proof that a function is an embedding isn't always easy, but one approach that is often fairly straightforward is to first prove that the function is invertible and then invoke the `invertible-is-embedding` theorem from the [Type Topology][] library.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where
 invertible : (A → B) → Type (𝓤 ⊔ 𝓦)
 invertible f = Σ g ꞉ (B → A) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

 equiv-is-embedding : (f : A → B) → is-equiv f → is-embedding f
 equiv-is-embedding f i y = singleton-is-prop (fiber f y) (i y)

-- open import MGS-Retracts using (_◁⟨_⟩_; _◀; Σ-retract; retract-of-singleton; singleton-type-center; singleton-type-centered)

 -- invertible-is-equiv : (f : A → B) → invertible f → is-equiv f
 -- invertible-is-equiv f (g , η , ε) b₀ = γ
 --  where
 --  s : (b : B) → f (g b) ≡ b₀ → b ≡ b₀
 --  s b = subst (_≡ b₀) (ε b)
 --  r : (b : B) → b ≡ b₀ → f (g b) ≡ b₀
 --  r b = subst (_≡ b₀) ((ε b)⁻¹)

 --  β : (b : B) → (f (g b) ≡ b₀) ◁ (b ≡ b₀)
 --  β b = (r b) , (s b) , subst-is-section (_≡ b₀) (ε b)

  -- α : fiber f b₀ ◁ singleton-type b₀
  -- α = (λ _ → g b₀ , ε b₀) , ((λ _ → b₀ , refl) , (λ x → {!!}))
  -- (Σ a ꞉ A , (f a ≡ b₀))     ◁⟨ Σ-reindexing-retract g (f , η) ⟩
  --      (Σ b ꞉ B , f (g b) ≡ b₀) ◁⟨ Σ-retract  β                   ⟩
  --      (Σ b ꞉ B , b ≡ b₀)       ◀

  -- γ : is-singleton (fiber f b₀)
  -- γ = (g b₀ , ε b₀) , {!!}

  -- γ : is-singleton (fiber f b₀)
  -- γ = (g b₀ , ε b₀) , {!!}

 -- invertible-is-embedding : (f : A → B) → invertible f → is-embedding f
 -- invertible-is-embedding f fi = equiv-is-embedding f (invertible-is-equiv f fi)

\end{code}

-------------------------------------

<p></p>

[← Overture.FunExtensionality](Overture.FunExtensionality.html)
<span style="float:right;">[Overture.Lifts →](Overture.Lifts.html)</span>


{% include UALib.Links.md %}









<!--


to-Σ-≡ : {A : Type 𝓤} {B : A → Type 𝓦} {σ τ : Σ A B}
       → (Σ p ꞉ fst σ ≡ fst τ , subst B p (snd σ) ≡ snd τ)
       → σ ≡ τ

to-Σ-≡ (refl , refl) = refl


Σ-reindexing-retract : {A : Type 𝓤} {C : Type 𝓥} {B : A → Type 𝓦} (r : C → A)
                     → has-section r
                     → (Σ x ꞉ A , B x) ◁ (Σ y ꞉ C , B (r y))

Σ-reindexing-retract {𝓤} {𝓥} {𝓦} {X} {Y} {A} = ?
-- r (s , η) = γ , φ , γφ
--  where
--   γ : Σ (A ∘ r) → Σ A
--   γ (y , a) = (r y , a)

--   φ : Σ A → Σ (A ∘ r)
--   φ (x , a) = (s x , subst A ((η x)⁻¹) a)

--   γφ : (σ : Σ A) → γ (φ σ) ≡ σ
--   γφ (x , a) = p
--    where
--     p : (r (s x) , subst A ((η x)⁻¹) a) ≡ (x , a)
--     p = to-Σ-≡ (η x , subst-is-retraction A (η x) a)
-->
