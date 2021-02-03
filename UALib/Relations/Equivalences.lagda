---
layout: default
title : UALib.Relations.Equivalences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relation-types">Equivalence Relation Types</a>

This section presents the [UALib.Relations.Equivalences][] module of the [Agda Universal Algebra Library][].

This is all pretty standard.  The notions of reflexivity, symmetry, and transitivity are defined as one would expect, so we need not dwell on them.

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

\end{code}

We should also have at our disposal a proof of the fact that the kernel of a function is an equivalence relation.

\begin{code}

map-kernel-IsEquivalence : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}
                            (f : A → B) → IsEquivalence (KER-rel{𝓤}{𝓦} f)

map-kernel-IsEquivalence {𝓤}{𝓦} f =
 record { rfl = λ x → 𝓇ℯ𝒻𝓁
        ; sym = λ x y x₁ → ≡-sym{𝓦} (f x) (f y) x₁
        ; trans = λ x y z x₁ x₂ → ≡-trans (f x) (f y) (f z) x₁ x₂ }

\end{code}


--------------------------------------

[← UALib.Relations.Binary](UALib.Relations.Binary.html)
<span style="float:right;">[UALib.Relations.Quotients →](UALib.Relations.Quotients.html)</span>

{% include UALib.Links.md %}
