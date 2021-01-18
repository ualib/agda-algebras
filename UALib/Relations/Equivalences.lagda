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

#### Examples

The zero relation 𝟎 is equivalent to the identity relation `≡` and, of course, these are both equivalence relations. (In fact, we already proved reflexivity, symmetry, and transitivity of `≡` in the [UALib.Prelude.Equality][] module, so we simply apply the corresponding proofs where appropriate.)
\begin{code}

module _ {𝓤 : Universe} where

 𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence{𝓤}{A = A} 𝟎-rel
 𝟎-IsEquivalence = record { rfl = ≡-rfl; sym = ≡-sym; trans = ≡-trans }

 ≡-IsEquivalence : {A : 𝓤 ̇} → IsEquivalence{𝓤}{A = A} _≡_
 ≡-IsEquivalence = record { rfl = ≡-rfl ; sym = ≡-sym ; trans = ≡-trans }

\end{code}

Finally, we should have at our disposal a proof of the fact that the kernel of a function is an equivalence relation.

\begin{code}

 map-kernel-IsEquivalence : {𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}
                            (f : A → B) → IsEquivalence (KER-rel f)

 map-kernel-IsEquivalence {𝓦} f =
  record { rfl = λ x → 𝓇ℯ𝒻𝓁
         ; sym = λ x y x₁ → ≡-sym{𝓦} (f x) (f y) x₁
         ; trans = λ x y z x₁ x₂ → ≡-trans (f x) (f y) (f z) x₁ x₂ }

\end{code}


--------------------------------------

[← UALib.Relations.Binary](UALib.Relations.Binary.html)
<span style="float:right;">[UALib.Relations.Equivalences →](UALib.Relations.Equivalences.html)</span>

{% include UALib.Links.md %}
