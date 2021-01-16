---
layout: default
title : UALib.Relations.Unary module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="unary-relation-types">Unary Relation Types</a>

This section presents the [UALib.Relations.Unary][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Relations.Unary where

open import UALib.Algebras.Lifts public

open import UALib.Prelude.Preliminaries using (¬; propext; global-dfunext ) public

\end{code}

Unary relations are sometimes called predicates.  We use them to represent subsets as a function type.

#### Sets, elements, subsets, set union, set intersection

\begin{code}

module _ {𝓤 : Universe} where

 Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
 Pred A 𝓥 = A → 𝓥 ̇

 Pred₀ : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
 Pred₀ A 𝓥 = Σ P ꞉ (A → 𝓥 ̇) , ∀ x → is-subsingleton (P x)

module _ {𝓤 𝓦 : Universe} where

 _∈_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
 x ∈ P = P x

 _∉_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
 x ∉ P = ¬ (x ∈ P)

 infix 4 _∈_ _∉_


_⊆_ : {𝓤 𝓦 𝓣 : Universe}{A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : {𝓤 𝓦 𝓣 : Universe}{A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P ⊇ Q = Q ⊆ P

infix 4 _⊆_ _⊇_


_=̇_ : {𝓤 𝓦 𝓣 : Universe}{A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
P =̇ Q = (P ⊆ Q) × (Q ⊆ P)

_∈∈_ : {𝓤 𝓦 𝓣 : Universe}{A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A  →  B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
_∈∈_ f S = (x : _) → f x ∈ S

Pred-refl : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → (a : A) → a ∈ P → a ∈ Q
Pred-refl (refl _) _ = λ z → z

Pred-≡ : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → P =̇ Q
Pred-≡ (refl _) = (λ z → z) , λ z → z

Pred-≡→⊆ : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → (P ⊆ Q)
Pred-≡→⊆ (refl _) = (λ z → z)

Pred-≡→⊇ : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          P ≡ Q → (P ⊇ Q)
Pred-≡→⊇ (refl _) = (λ z → z)

Pred-=̇-≡ : {𝓤 𝓦 : Universe}
 →          propext 𝓦 → global-dfunext
 →          {A : 𝓤 ̇}{P Q : Pred A 𝓦}
 →          ((x : A) → is-subsingleton (P x))
 →          ((x : A) → is-subsingleton (Q x))
 →          P =̇ Q → P ≡ Q
Pred-=̇-≡ pe gfe {A}{P}{Q} ssP ssQ (pq , qp) = gfe γ
 where
  γ : (x : A) → P x ≡ Q x
  γ x = pe (ssP x) (ssQ x) pq qp

-- Disjoint Union.
data _⊎_ {𝓤 𝓦 : Universe}(A : 𝓤 ̇) (B : 𝓦 ̇) : 𝓤 ⊔ 𝓦 ̇ where
 inj₁ : (x : A) → A ⊎ B
 inj₂ : (y : B) → A ⊎ B
infixr 1 _⊎_

-- Union.
_∪_ : {𝓤 𝓦 𝓣 : Universe}{A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓣 → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q
infixr 1 _∪_


-- The empty set.
∅ : {𝓤 : Universe}{A : 𝓤 ̇} → Pred A 𝓤₀
∅ = λ _ → 𝟘

-- Singletons.
｛_｝ : {𝓤 : Universe}{A : 𝓤 ̇} → A → Pred A _
｛ x ｝ = x ≡_

Im_⊆_ : {𝓤 𝓦 𝓣 : Universe} {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
Im_⊆_ {A = A} f S = (x : A) → f x ∈ S


img : {𝓤 : Universe}{X : 𝓤 ̇ } {Y : 𝓤 ̇ }
      (f : X → Y) (P : Pred Y 𝓤)
 →    Im f ⊆ P →  X → Σ P
img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁

\end{code}

#### Products of predicates and their meanings

The product `Π P` of a predicate `P : Pred X 𝓤` is inhabited iff  P x holds for all x : X.

\begin{code}

ΠP-meaning : {𝓧 𝓤 : Universe}{X : 𝓧 ̇}{P : Pred X 𝓤}
 →            Π P  →  (x : X) → P x
ΠP-meaning f x = f x

\end{code}

#### Predicate transport

Finally, here are some "transport" lemmas that will come in handy later.

\begin{code}
module _ {𝓤 𝓦 : Universe} where

 cong-app-pred : {A : 𝓤 ̇ }{B₁ B₂ : Pred A 𝓦}
                 (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                ------------------------------
  →                         x ∈ B₂
 cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

 cong-pred : {A : 𝓤 ̇ }{B : Pred A 𝓦}
             (x y : A) →  x ∈ B  →  x ≡ y
             ----------------------------
  →                       y ∈ B
 cong-pred x .x x∈B (refl _ ) = x∈B
\end{code}


--------------------------------------

[↑ UALib.Relations](UALib.Relations.html)
<span style="float:right;">[UALib.Relations.Binary →](UALib.Relations.Binary.html)</span>

{% include UALib.Links.md %}
