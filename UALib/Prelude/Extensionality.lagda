---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: Extensionality.lagda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 12 Jan 2021
REF: Parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->


### <a id="extensionality">Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module UALib.Prelude.Extensionality where


open import UALib.Prelude.Inverses public
open import UALib.Prelude.Preliminaries using (_∼_; 𝓤ω; Π; Ω; 𝓟; ⊆-refl-consequence; _∈₀_; _⊆₀_; _holds) public

\end{code}


#### Function extensionality

\begin{code}
extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ∼ g   →   f ≡ g
\end{code}

#### Function intensionality

This is the opposite of function extensionality)

\begin{code}
intensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

intensionality  (refl _ ) _  = refl _
\end{code}

#### Dependent intensionality


\begin{code}
dintensionality : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } {f g : (x : A) → B x}
 →                f ≡ g  →  (x : A)
                  ------------------
 →                    f x ≡ g x

dintensionality  (refl _ ) _  = refl _

dep-intensionality : ∀ {𝓤 𝓦}{A : 𝓤 ̇ }{B : A → 𝓦 ̇ }
                     {f g : ∀(x : A) → B x}
 →                   f ≡ g  →  (x : A)
                    ------------------
 →                    f x ≡ g x

dep-intensionality (refl _ ) _ = refl _
\end{code}


#### Dependent function extensionality

\begin{code}
dep-extensionality : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
dep-extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
  {f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

∀-extensionality : 𝓤ω
∀-extensionality = ∀  {𝓤 𝓥} → extensionality 𝓤 𝓥

∀-dep-extensionality : 𝓤ω
∀-dep-extensionality = ∀ {𝓤 𝓥} → dep-extensionality 𝓤 𝓥

extensionality-lemma : ∀ {𝓘 𝓤 𝓥 𝓣} →
                       {I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )
                       (args : X → (Π A))
 →                     p ≡ q
   -------------------------------------------------------------
 → (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q =
 ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

\end{code}

#### Some tools for powersets

\begin{code}

record Σω {X : 𝓤ω} (Y : X → 𝓤ω ) : 𝓤ω  where
  constructor
   _⸲_  -- notation: type \,3 for ⸲
  field
   π₁ : X
   π₂ : Y π₁

infixr 50 _⸲_

-Σω : (X : 𝓤ω) (Y : X → 𝓤ω ) → 𝓤ω
-Σω X Y = Σω Y

syntax -Σω X (λ x → y) = Σω x ꞉ X ⸲ y

_⨉_ : 𝓤ω → 𝓤ω → 𝓤ω
X ⨉ Y = Σω x ꞉ X ⸲ Y

KER-𝓟 : {𝓤 𝓦 : Universe}{A : 𝓤 ̇} {B : 𝓦 ̇} → is-set B → (f : A → B) → A → A → Ω 𝓦
KER-𝓟 Bset f x y = (f x ≡ f y) , Bset (f x) (f y)

\end{code}

This says `(f x) ≡ (f y)` and `is-singleton (f x) ≡ (f y)`.


\begin{code}

ker-𝓟 : {𝓤 : Universe}{A B : 𝓤 ̇} → is-set B → (f : A → B) → A → 𝓟 A
ker-𝓟 {𝓤} = KER-𝓟 {𝓤}{𝓤}

module _ {𝓤 : Universe} where

 cong-app-𝓟 : ∀ { A : 𝓤 ̇ } { B C : 𝓟 A} (x : A)
  →             x ∈₀ B   →   B ≡ C
               -------------------------
  →                    x ∈₀ C

 cong-app-𝓟 {A}{B}{C} x Bx B≡C = B⊆C x Bx
  where
   B⊆C : B ⊆₀ C
   B⊆C = fst (⊆-refl-consequence B C B≡C)

 cong-𝓟 : {A : 𝓤 ̇ } {B : 𝓟 A} (x y : A)
  →            x ∈₀ B   →   x ≡ y
             -------------------------
  →                   y ∈₀ B
 cong-𝓟 {A}{B} x y Bx xy  = transport (λ - → B - holds) xy Bx

\end{code}

-------------------------------------

[← UALib.Prelude.Inverses](UALib.Prelude.Inverses.html)
<span style="float:right;">[UALib.Algebras →](UALib.Algebras.html)</span>

{% include UALib.Links.md %}
