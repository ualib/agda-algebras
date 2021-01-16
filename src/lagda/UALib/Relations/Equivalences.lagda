---
layout: default
title : UALib.Relations.Equivalences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

[UALib.Relations ↑](UALib.Relations.html)

### <a id="equivalence-relation-types">Equivalence Relation Types</a>

This section presents the [UALib.Relations.Equivalences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Relations.Equivalences where

open import UALib.Relations.Binary public

module _ {𝓤 𝓡 : Universe} where

 record IsEquivalence {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
  field
   rfl   : reflexive _≈_
   sym   : symmetric _≈_
   trans : transitive _≈_

 is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-equivalence-relation _≈_ = is-subsingleton-valued _≈_
                               × reflexive _≈_ × symmetric _≈_ × transitive _≈_

module _ {𝓤 : Universe} where

 𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence{𝓤 = 𝓤}{A = A} 𝟎-rel
 𝟎-IsEquivalence = record { rfl = λ x → refl _
                          ; sym = λ x y x≡y → x≡y ⁻¹
                          ; trans = λ x y z x≡y y≡z → x≡y ∙ y≡z }

 ≡-IsEquivalence : {X : 𝓤 ̇} → IsEquivalence{𝓤}{𝓤}{X} _≡_
 ≡-IsEquivalence = record { rfl = ≡-rfl ; sym = ≡-sym ; trans = ≡-trans }


 map-kernel-IsEquivalence : {𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}
                            (f : A → B) → IsEquivalence (KER-rel f)

 map-kernel-IsEquivalence {𝓦} f =
  record { rfl = λ x → 𝓇ℯ𝒻𝓁
         ; sym = λ x y x₁ → ≡-sym{𝓦} (f x) (f y) x₁
         ; trans = λ x y z x₁ x₂ → ≡-trans (f x) (f y) (f z) x₁ x₂ }
\end{code}


--------------------------------------

{% include UALib.Links.md %}
