---
layout: default
title : Relations.Extensionality module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="relation-extensionality">Relation Extensionality</a>

This section presents the [Relations.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Extensionality where

open import Relations.Truncation public
open import MGS-MLTT using (𝟙) public

\end{code}

The principle of *proposition extensionality* asserts that logically equivalent propositions are equivalent.  That is, if `P` and `Q` are propositions and if `P ⊆ Q` and `Q ⊆ P`, then `P ≡ Q`. For our purposes, it will suffice to formalize this notion for general predicates, rather than for propositions (i.e., truncated predicates).

\begin{code}

pred-ext : (𝓤 𝓦 : Universe) → (𝓤 ⊔ 𝓦) ⁺ ̇
pred-ext 𝓤 𝓦 = ∀ {A : 𝓤 ̇}{P Q : Pred A 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

\end{code}

Note that `pred-ext` merely defines an extensionality principle. It does not postulate that the principle holds.  If we wish to postulate `pred-ext`, then we do so by assuming that type is inhabited (see `block-ext` below, for example).



#### <a id="quotient-extensionality">Quotient extensionality</a>

We need an identity type for congruence classes (blocks) over sets so that two different presentations of the same block (e.g., using different representatives) may be identified.  This requires two postulates: (1) *predicate extensionality*, manifested by the `pred-ext` type; (2) *equivalence class truncation* or "uniqueness of block identity proofs", manifested by the `blk-uip` type defined in the [Relations.Truncation][] module. We now use `pred-ext` and `blk-uip` to define a type called `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in [Homomorphisms.Noether][].

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{R : Rel A 𝓦} where

 block-ext : pred-ext 𝓤 𝓦 → IsEquivalence R → {u v : A} → R u v → [ u ]{R} ≡ [ v ]{R}
 block-ext pe Req {u}{v} Ruv = pe (/-subset Req Ruv) (/-supset Req Ruv)


 to-subtype|uip : blk-uip A R → {C D : Pred A 𝓦}{c : IsBlock C {R}}{d : IsBlock D {R}}
  →               C ≡ D → (C , c) ≡ (D , d)

 to-subtype|uip buip {C}{D}{c}{d}CD = to-Σ-≡(CD , buip D(transport(λ B → IsBlock B)CD c)d)


 block-ext|uip : pred-ext 𝓤 𝓦 → blk-uip A R → IsEquivalence R
  →              ∀ {u v : A}  →  R u v  →  ⟪ u ⟫ ≡ ⟪ v ⟫

 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)

\end{code}

-------

#### <a id="question-prop-vs-pred-extensionality">Question: prop vs pred extensionality</a>

Is predicate extensionality stronger than proposition extensionality?  That is, does `pred-ext 𝓤 𝓦` imply the following?

```
  ∀(A : 𝓤 ̇)(P : Pred A 𝓦)(x : A)(p q : P x) → p ≡ q
```

We could also define *relation extensionality* principles which generalize the predicate extensionality principle (`pred-ext`) defined above

\begin{code}

cont-rel-ext : (𝓤 𝓥 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇
cont-rel-ext 𝓤 𝓥 𝓦 = ∀ {I : 𝓥 ̇}{A : 𝓤 ̇}{P Q : ContRel I A 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

dep-rel-ext : (𝓤 𝓥 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇
dep-rel-ext 𝓤 𝓥 𝓦 = ∀ {I : 𝓥 ̇}{𝒜 : I → 𝓤 ̇}{P Q : DepRel I 𝒜 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

\end{code}

These types are not used in other modules of the [UALib][] and we pose the same question about them as the one above.  That is, we ask whether these general relation extensionality principles are stonger than proposition extensionality.

---------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}



<!-- NOT USED

pred→prop : {𝓤 𝓦 : Universe}{A : 𝓤 ̇} → Pred A 𝓦 → Pred A 𝓦
pred→prop P = λ x → P x → 𝟙

pred-ext→uip : {𝓤 𝓦 : Universe}{A : 𝓤 ̇} → pred-ext 𝓤 𝓦  → (P : Pred A 𝓦) → ∀ x → is-subsingleton (P x)
pred-ext→uip {𝓤}{𝓦}{A} pe P x p q = {!γ!}
 where
  P' : Pred A 𝓦
  P' = pred→prop P

  PP' : P ≡ P'
  PP' = pe (λ _ _ → MGS-MLTT.⋆) λ x₁ → {!!}

  γ : p ≡ q
  γ = {!!}
-->
