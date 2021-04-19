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

\end{code}

#### <a id="propositions">Predicate extensionality</a>

The principle of *proposition extensionality* asserts that logically equivalent propositions are equivalent.  That is, if `P` and `Q` are propositions and if `P ⊆ Q` and `Q ⊆ P`, then `P ≡ Q`. For our purposes, it will suffice to formalize this notion for general predicates, rather than for propositions (i.e., truncated predicates).   As such, we call the next type `pred-ext` (instead of, say, `prop-ext`).

\begin{code}

pred-ext : (𝓤 𝓦 : Universe) → (𝓤 ⊔ 𝓦) ⁺ ̇
pred-ext 𝓤 𝓦 = ∀ {A : 𝓤 ̇}{P Q : Pred A 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q
\end{code}



#### <a id="quotient-extensionality">Quotient extensionality</a>

We need an identity type for congruence classes (blocks) over sets so that two different presentations of the same block (e.g., using different representatives) may be identified.  This requires two postulates: (1) *predicate extensionality* (captured above by the `pred-ext` type) and (2) *block truncation* (or "quotient class truncation") which we now define.

Recall, `IsBlock` was defined in the [Relations.Quotients][] module as follows:

```
 IsBlock : {A : 𝓤 ̇}(C : Pred A 𝓦){R : Rel A 𝓦} → 𝓤 ⊔ 𝓦 ⁺ ̇
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}
```

We will need to assume that for each predicate `C : Pred A 𝓦` there is at most one proof of `IsBlock C`. We call this proof-irrelevance principle "uniqueness of block identity proofs", and define it as follows.

\begin{code}

blk-uip : {𝓦 𝓤 : Universe}(A : 𝓤 ̇)(R : Rel A 𝓦 ) → 𝓤 ⊔ 𝓦 ⁺ ̇
blk-uip {𝓦} A R = ∀ (C : Pred A 𝓦) → is-subsingleton (IsBlock C {R})

\end{code}

We now use `pred-ext` and `blk-uip` to define a type called `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in [Homomorphisms.Noether][].

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{R : Rel A 𝓦} where

 block-ext : pred-ext 𝓤 𝓦 → IsEquivalence R → {u v : A} → R u v → [ u ]{R} ≡ [ v ]{R}
 block-ext pe Req {u}{v} Ruv = pe (/-subset Req Ruv) (/-supset Req Ruv)

 to-subtype|uip :
  blk-uip A R → {C D : Pred A 𝓦}{c : IsBlock C {R}}{d : IsBlock D {R}} → C ≡ D → (C , c) ≡ (D , d)
 to-subtype|uip buip {C}{D}{c}{d}CD = to-Σ-≡(CD , buip D(transport(λ B → IsBlock B)CD c)d)


 block-ext|uip :
  pred-ext 𝓤 𝓦 → blk-uip A R → IsEquivalence R → {u v : A} → R u v  →  ⟪ u ⟫ ≡ ⟪ v ⟫
 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)

\end{code}


----------------------------

#### <a id="general-propositions">General propositions*</a>

This section presents the `general-propositions` submodule of the [Relations.Truncation][] module.<sup>[*](Relations.Truncation.html#fn0)</sup>


Recall, we defined a type called `ContRel` in the [Relations.Continuous][] module to represent relations of arbitrary arity. Naturally, we define the corresponding truncated types, the inhabitants of which we will call *continuous propositions*.

\begin{code}

module general-propositions {𝓤 : Universe}{I : 𝓥 ̇} where

 open import Relations.Continuous using (ContRel; DepRel)

 IsContProp : {A : 𝓤 ̇}{𝓦 : Universe} → ContRel I A 𝓦  → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 IsContProp {A = A} P = Π 𝑎 ꞉ (I → A) , is-subsingleton (P 𝑎)

 ContProp : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 ContProp A 𝓦 = Σ P ꞉ (ContRel I A 𝓦) , IsContProp P

 cont-prop-ext : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 cont-prop-ext A 𝓦 = {P Q : ContProp A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}


While we're at it, we might as well take the abstraction one step further and define the type of *truncated dependent relations*, which we call *dependent propositions*.

\begin{code}

 IsDepProp : {I : 𝓥 ̇}{𝒜 : I → 𝓤 ̇}{𝓦 : Universe} → DepRel I 𝒜 𝓦  → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 IsDepProp {I = I} {𝒜} P = Π 𝑎 ꞉ Π 𝒜 , is-subsingleton (P 𝑎)

 DepProp : (I → 𝓤 ̇) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 DepProp 𝒜 𝓦 = Σ P ꞉ (DepRel I 𝒜 𝓦) , IsDepProp P

 dep-prop-ext : (I → 𝓤 ̇) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 dep-prop-ext 𝒜 𝓦 = {P Q : DepProp 𝒜 𝓦} → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}


-----------------------------------

<sup>*</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general than some of the types defined in other sections. As yet these general types are not used elsewhere in the [UALib][], so sections marked * may be safely skimmed or skipped.</span>

<br>
<br>

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}
