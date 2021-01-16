---
layout: default
title : UALib.Prelude.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

[Prelude ↑](Prelude.html)

### <a id="equality">Equality</a>

This section describes the [UALib.Prelude.Equality module][] of the [Agda Universal Algebra Library][] (UALib).

#### refl

Perhaps the most important types in type theory are the equality types.

The definitional equality we use is the standard one, which is often referred to as "reflexivity" or "refl". In our case, it is defined in the `Identity-Type` module of the [Type Topology][] library, but apart from syntax it is equivalent to the identity type used in most other Agda libraries.  Here is the full listing of the `Identity-Type` module.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Identity-Type where

open import Universes

data _≡_ {𝓤} {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where
  refl : {x : X} → x ≡ x
```

We being the [Prelude.Equality module][] by proving that this `≡` relation is an equivalence relation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Prelude.Equality where

open import UALib.Prelude.Preliminaries using (𝓞; 𝓥; Universe; _̇; _⊔_; _⁺; _≡_; refl; Σ; -Σ; _×_; _,_;
 is-subsingleton; is-prop; ∣_∣; ∥_∥; 𝟙; pr₁; pr₂; ap) public

module _  {𝓤 : Universe}{X : 𝓤 ̇ }  where
 ≡-rfl : (x : X) → x ≡ x
 ≡-rfl x = refl _

 ≡-sym : (x y : X) → x ≡ y → y ≡ x
 ≡-sym x y (refl _) = refl _

 ≡-trans : (x y z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-trans x y z (refl _) (refl _) = refl _

 ≡-Trans : (x : X){y : X}(z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-Trans x {y} z (refl _) (refl _) = refl _
\end{code}

#### Functions preserve refl

\begin{code}

ap-cong : {𝓤 𝓦 : Universe}
          {A : 𝓤 ̇ } {B : 𝓦 ̇ }
          {f g : A → B} {a b : A}
 →         f ≡ g   →   a ≡ b
         -----------------------
 →            f a ≡ g b

ap-cong (refl _) (refl _) = refl _
\end{code}

We will have many occasions to apply this fact, and we sometimes need a version that works for *dependent* function types, such as the following.

\begin{code}
cong-app : {𝓤 𝓦 : Universe}
           {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
           {f g : (a : A) → B a}
 →          f ≡ g   →   (a : A)
          -----------------------
 →              f a ≡ g a

cong-app (refl _) a = refl _
\end{code}

#### ≡-intro and ≡-elim for nondependent pairs

We conclude the Equality module with some occasionally useful introduction and elimination rules for the equality relation on (nondependent) pair types.

\begin{code}
≡-elim-left : {𝓤 𝓦 : Universe}
              {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →            (A₁ , B₁) ≡ (A₂ , B₂)
              ----------------------
 →                   A₁ ≡ A₂

≡-elim-left e = ap pr₁ e


≡-elim-right : {𝓤 𝓦 : Universe}
               {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇}
 →             (A₁ , B₁) ≡ (A₂ , B₂)
               -----------------------
 →                    B₁ ≡ B₂

≡-elim-right e = ap pr₂ e


≡-×-intro : {𝓤 𝓦 : Universe}
            {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →           A₁ ≡ A₂  →  B₁ ≡ B₂
           ------------------------
 →          (A₁ , B₁) ≡ (A₂ , B₂)

≡-×-intro (refl _ ) (refl _ ) = (refl _ )


≡-×-int : {𝓤 𝓦 : Universe}
          {A : 𝓤 ̇} {B : 𝓦 ̇}
          (a a' : A)(b b' : B)
 →         a ≡ a'  →  b ≡ b'
          ------------------------
 →         (a , b) ≡ (a' , b')

≡-×-int a a' b b' (refl _ ) (refl _ ) = (refl _ )
\end{code}

---------------------

{% include UALib.Links.md %}
