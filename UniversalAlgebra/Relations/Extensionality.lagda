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

pred-ext : (𝓤 𝓦 : Level) → Type (lsuc (𝓤 ⊔ 𝓦))
pred-ext 𝓤 𝓦 = ∀ {A : Type 𝓤}{P Q : Pred A 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

\end{code}

Note that `pred-ext` merely defines an extensionality principle. It does not postulate that the principle holds.  If we wish to postulate `pred-ext`, then we do so by assuming that type is inhabited (see `block-ext` below, for example).



#### <a id="quotient-extensionality">Quotient extensionality</a>

We need an identity type for congruence classes (blocks) over sets so that two different presentations of the same block (e.g., using different representatives) may be identified.  This requires two postulates: (1) *predicate extensionality*, manifested by the `pred-ext` type; (2) *equivalence class truncation* or "uniqueness of block identity proofs", manifested by the `blk-uip` type defined in the [Relations.Truncation][] module. We now use `pred-ext` and `blk-uip` to define a type called `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in [Homomorphisms.Noether][].

\begin{code}

module _ {A : Type 𝓤}{R : Rel A 𝓦} where

 block-ext : pred-ext 𝓤 𝓦 → IsEquivalence R → {u v : A} → R u v → [ u ]{R} ≡ [ v ]{R}
 block-ext pe Req {u}{v} Ruv = pe (/-subset Req Ruv) (/-supset Req Ruv)


 to-subtype|uip : blk-uip A R → {C D : Pred A 𝓦}{c : IsBlock C {R}}{d : IsBlock D {R}}
  →               C ≡ D → (C , c) ≡ (D , d)

 to-subtype|uip buip {C}{D}{c}{d}CD = to-Σ-≡(CD , buip D(transport(λ B → IsBlock B)CD c)d)


 block-ext|uip : pred-ext 𝓤 𝓦 → blk-uip A R → IsEquivalence R → ∀{u}{v} → R u v → ⟪ u ⟫ ≡ ⟪ v ⟫
 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)

\end{code}



#### <a id="strongly-well-defined-operations">Strongly well-defined operations</a>

We now describe an extensionality principle that seems weaker than function extensionality, but still (probably) not provable in [MLTT][]. (We address this and other questions  below.)  We call this the principle *strong well-definedness of operations*. We will encounter situations in which this weaker extensionality principle suffices as a substitute for function extensionality.

Suppose we have a function whose domain is a function type, say, `I → A`.  For example, inhabitants of the type `Op` defined above are such functions.  (Recall, the domain of inhabitants of type `Op I A := (I → A) → A` is `I → A`.)

Of course, operations of type `Op I A` are well-defined in the sense that equal inputs result in equal outputs.

\begin{code}

welldef : {A : Type 𝓤}{I : Type 𝓥}(f : Op I A) → ∀ u v → u ≡ v → f u ≡ f v
welldef f u v refl = refl

\end{code}

A stronger form of well-definedness of operations is to suppose that point-wise equal inputs lead to the same output.  In other terms, we could suppose that  for all `f : Op I A`, we have `f u ≡ f v` whenever `∀ i → u i ≡ v i` holds.  We call this formalize this notation in the following type.

\begin{code}

swelldef : (𝓥 𝓤 : Level) → Type (lsuc (𝓤 ⊔ 𝓥))
swelldef 𝓥 𝓤 = ∀ {A : Type 𝓤}{I : Type 𝓥}(f : Op I A)(u v : I → A) → (∀ i → u i ≡ v i) → f u ≡ f v

funext→swelldef : {𝓤 𝓥 : Level} → dfunext 𝓥 𝓤 → swelldef 𝓥 𝓤
funext→swelldef fe f u v ptweq = γ
 where
 uv : u ≡ v
 uv = fe ptweq
 γ : f u ≡ f v
 γ = welldef f u v uv

\end{code}


-----------------------------

#### <a id="general-relation-extensionality">General relation extensionality*</a>

We define the following *relation extensionality* principles which generalize the predicate extensionality principle (`pred-ext`) defined above.

\begin{code}

cont-relext : (𝓤 𝓥 𝓦 : Level) → Type (lsuc (𝓤 ⊔ 𝓥 ⊔ 𝓦))
cont-relext 𝓤 𝓥 𝓦 = ∀ {I : Type 𝓥}{A : Type 𝓤}{P Q : ContRel I A 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

dep-relext : (𝓤 𝓥 𝓦 : Level) → Type (lsuc (𝓤 ⊔ 𝓥 ⊔ 𝓦))
dep-relext 𝓤 𝓥 𝓦 = ∀ {I : Type 𝓥}{𝒜 : I → Type 𝓤}{P Q : DepRel I 𝒜 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

\end{code}

These types are not used in other modules of the [UniversalAlgebra][] library.


-------

#### <a id="open-questions-about-extensionality">Open questions about strength and provability of extensionality principles</a>

Here are some questions about extensionaity for future consideration.

**Questions about strong vs weak well-definedness**.

1. Is strong well-definedness of operations (`swelldef`) provable in [MLTT][]?

2. Is strong well-definedness of operations strictly weaker than function extensionality?


**Questions about prop vs pred extensionality**.

1. Is predicate extensionality (`pred-ext`) at least as strong as proposition extensionality?  That is, does `pred-ext 𝓤 𝓦` imply

   `∀(A : Type 𝓤)(P : Pred A 𝓦)(x : A)(p q : P x) → p ≡ q` ?

2. Are the relation extensionality principles `cont-relext` and `dep-relext` at least as strong as proposition extensionality?

---------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}


