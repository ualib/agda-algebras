---
layout: default
title : Terms.Operations module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="term-operations">Term Operations</a>

This section presents the [Terms.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a particular algebra, and we prove some compatibility properties of term operations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product using (_,_; Σ; _×_)
open import Function.Base  using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Unary using (Pred)

-- Imports from the Agda Universal Algebra Library
open import Overture.Inverses using (IsSurjective; Image_∋_; Inv; InvIsInv; eq)
open import Overture.Preliminaries
 using (Type; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _∙_;_⁻¹; ∣_∣; ∥_∥)

open import Algebras.Basic
open import Relations.Discrete using (_|:_)
open import Relations.Quotients using (Equivalence; _/_; ⟪_⟫)
open import Relations.Extensionality using (DFunExt; swelldef)



module Terms.Operations {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Congruences{𝑆 = 𝑆} using (Con; IsCongruence)
open import Algebras.Products{𝑆 = 𝑆} using (ov; ⨅)
open import Homomorphisms.Basic {𝑆 = 𝑆} using (hom)
open import Terms.Basic {𝑆 = 𝑆}

\end{code}

**Notation**. In the line above, we renamed for notational convenience the `generator` constructor of the `Term` type, so from now on we use `ℊ` in place of `generator`.

When we interpret a term in an algebra we call the resulting function a *term operation*.  Given a term `p` and an algebra `𝑨`, we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in `𝑨`.  This is defined inductively as follows.

1. If `p` is a variable symbol `x : X` and if `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = 𝑓 𝑡`, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol, if `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of terms, and if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define `𝑨 ⟦ p ⟧ a = 𝑨 ⟦ 𝑓 𝑡 ⟧ a := (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ a)`.

Thus the interpretation of a term is defined by induction on the structure of the term, and the definition is formally implemented in [UniversalAlgebra][] as follows.

\begin{code}

_⟦_⟧ : (𝑨 : Algebra 𝓤 𝑆){X : Type 𝓧 } → Term X → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
𝑨 ⟦ ℊ x ⟧ = λ η → η x
𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → (𝑓 ̂ 𝑨) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

_⌜_⌝_ : {X : Type 𝓧 }(𝑨 : Algebra 𝓤 𝑆) → Term X → ((ρ , _) : Equivalence X) → (X / ρ → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
𝑨 ⌜ ℊ x ⌝ ρ = λ η → η ⟪ x ⟫
𝑨 ⌜ node 𝑓 𝑡 ⌝ ρ = λ η → (𝑓 ̂ 𝑨) (λ i → (𝑨 ⌜ 𝑡 i ⌝ ρ) η)


\end{code}

It turns out that the intepretation of a term is the same as the `free-lift` (modulo argument order and assuming function extensionality).

\begin{code}

free-lift-interp : swelldef 𝓥 𝓤 → (𝑨 : Algebra 𝓤 𝑆){X : Type 𝓧 }(η : X → ∣ 𝑨 ∣)(p : Term X)
 →                 (𝑨 ⟦ p ⟧) η ≡ (free-lift 𝑨 η) p

free-lift-interp _ 𝑨 η (ℊ x) = refl
free-lift-interp wd 𝑨 η (node 𝑓 𝑡) = wd (𝑓 ̂ 𝑨) (λ z → (𝑨 ⟦ 𝑡 z ⟧) η)
                                       ((free-lift 𝑨 η) ∘ 𝑡)((free-lift-interp wd 𝑨 η) ∘ 𝑡)


\end{code}

If the algebra 𝑨 happens to be `𝑻 X`, then we expect that `∀ 𝑠` we have `(𝑻 X)⟦ p ⟧ 𝑠 ≡ p 𝑠`. But what is `(𝑻 X)⟦ p ⟧ 𝑠` exactly? By definition, it depends on the form of `p` as follows:

* if `p = ℊ x`, then `(𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ ℊ x ⟧ 𝑠 ≡ 𝑠 x`

* if `p = node 𝑓 𝑡`, then `(𝑻 X)⟦ p ⟧ 𝑠 := (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠`

Now, assume `ϕ : hom 𝑻 𝑨`. Then by `comm-hom-term`, we have `∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = 𝑨 ⟦ p ⟧ ∣ ϕ ∣ ∘ 𝑠`.

* if `p = ℊ x` (and `𝑡 : X → ∣ 𝑻 X ∣`), then

  `∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x) ≡ ∣ ϕ ∣ (λ 𝑡 → h 𝑡) ≡ λ 𝑡 → (∣ ϕ ∣ ∘ 𝑡) x`

* if `p = node 𝑓 𝑡`, then

   ∣ ϕ ∣ p ≡ ∣ ϕ ∣ (𝑻 X)⟦ p ⟧ 𝑠 = (𝑻 X)⟦ node 𝑓 𝑡 ⟧ 𝑠 = (𝑓 ̂ 𝑻 X) λ i → (𝑻 X)⟦ 𝑡 i ⟧ 𝑠

We claim that for all `p : Term X` there exists `q : Term X` and `𝔱 : X → ∣ 𝑻 X ∣` such that `p ≡ (𝑻 X)⟦ q ⟧ 𝔱`. We prove this fact as follows.

\begin{code}

term-interp : swelldef 𝓥 (ov 𝓧) → {X : Type 𝓧} (𝑓 : ∣ 𝑆 ∣){𝑠 𝑡 : ∥ 𝑆 ∥ 𝑓 → Term X} → (∀ i → 𝑠 i ≡ 𝑡 i) → node 𝑓 𝑠 ≡ (𝑓 ̂ 𝑻 X) 𝑡
term-interp wd 𝑓 {𝑠}{𝑡} st = wd (node 𝑓) 𝑠 𝑡 st -- cong (node 𝑓) st

term-gen : swelldef 𝓥 (ov 𝓧) → {X : Type 𝓧}(p : ∣ 𝑻 X ∣) → Σ[ q ꞉ ∣ 𝑻 X ∣ ] p ≡ (𝑻 X ⟦ q ⟧) ℊ
term-gen _ (ℊ x) = (ℊ x) , refl
term-gen wd (node 𝑓 t) = (node 𝑓 (λ i → ∣ term-gen wd (t i) ∣)) , term-interp wd 𝑓 λ i → ∥ term-gen wd (t i) ∥

term-gen-agreement : (wd : swelldef 𝓥 (ov 𝓧)){X : Type 𝓧}(p : ∣ 𝑻 X ∣) → (𝑻 X ⟦ p ⟧) ℊ ≡ (𝑻 X ⟦ ∣ term-gen wd p ∣ ⟧) ℊ
term-gen-agreement _ (ℊ x) = refl
term-gen-agreement wd {X} (node f t) = wd (f ̂ 𝑻 X) (λ x → (𝑻 X ⟦ t x ⟧) ℊ)
                                          (λ x → (𝑻 X ⟦ ∣ term-gen wd (t x) ∣ ⟧) ℊ) λ i → term-gen-agreement wd (t i)

term-agreement : swelldef 𝓥 (ov 𝓧) → {X : Type 𝓧}(p : ∣ 𝑻 X ∣) → p ≡  (𝑻 X ⟦ p ⟧) ℊ
term-agreement wd {X} p = ∥ term-gen wd p ∥ ∙ (term-gen-agreement wd p)⁻¹

\end{code}



#### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>

(Previously we proved the next theorem (`interp-prod`, about the interpretation of terms in a product) using function extensionality, but we were able to modify the proof to use the weaker postulate of *strong well-definedness of functions*.)

\begin{code}

module _ (wd : swelldef 𝓥 (𝓦 ⊔ 𝓤)){X : Type 𝓧 }{I : Type 𝓦} where

 interp-prod : (p : Term X)(𝒜 : I → Algebra 𝓤 𝑆)(a : X → Π[ i ꞉ I ] ∣ 𝒜 i ∣)
  →            (⨅ 𝒜 ⟦ p ⟧) a ≡ λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x) i)

 interp-prod (ℊ _) 𝒜 a = refl
 interp-prod (node 𝑓 𝑡) 𝒜 a = wd ((𝑓 ̂ ⨅ 𝒜)) u v IH
  where
  u : ∀ x → ∣ ⨅ 𝒜 ∣
  u = λ x → (⨅ 𝒜 ⟦ 𝑡 x ⟧) a
  v : ∀ x i → ∣ 𝒜 i ∣
  v = λ x i → (𝒜 i ⟦ 𝑡 x ⟧)(λ j → a j i)
  IH : ∀ i → u i ≡ v i
  IH = λ x → interp-prod (𝑡 x) 𝒜 a

 interp-prod2 : funext (𝓤 ⊔ 𝓦 ⊔ 𝓧) (𝓤 ⊔ 𝓦) → (p : Term X)(𝒜 : I → Algebra 𝓤 𝑆)
  →             ⨅ 𝒜 ⟦ p ⟧ ≡ (λ a i → (𝒜 i ⟦ p ⟧) λ x → a x i)
 interp-prod2 _ (ℊ x₁) 𝒜 = refl
 interp-prod2 fe (node f t) 𝒜 = fe λ a → wd (f ̂ ⨅ 𝒜)(u a) (v a) (IH a)
  where
  u : ∀ a x → ∣ ⨅ 𝒜 ∣
  u a = λ x → (⨅ 𝒜 ⟦ t x ⟧) a
  v : ∀ (a : X → ∣ ⨅ 𝒜 ∣) → ∀ x i → ∣ 𝒜 i ∣
  v a = λ x i → (𝒜 i ⟦ t x ⟧)(λ z → (a z) i)
  IH : ∀ a x → (⨅ 𝒜 ⟦ t x ⟧) a ≡ λ i → (𝒜 i ⟦ t x ⟧)(λ z → (a z) i)
  IH a = λ x → interp-prod (t x) 𝒜 a

\end{code}




#### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

comm-hom-term : swelldef 𝓥 𝓦 → {𝑨 : Algebra 𝓤 𝑆} (𝑩 : Algebra 𝓦 𝑆)
                (h : hom 𝑨 𝑩){X : Type 𝓧}(t : Term X) (a : X → ∣ 𝑨 ∣)
                ----------------------------------------------
  →             ∣ h ∣ ((𝑨 ⟦ t ⟧) a) ≡ (𝑩 ⟦ t ⟧) (∣ h ∣ ∘ a)

comm-hom-term _ 𝑩 h (ℊ x) a = refl
comm-hom-term wd {𝑨} 𝑩 h (node 𝑓 𝑡) a = ∣ h ∣((𝑓 ̂ 𝑨) λ i →  (𝑨 ⟦ 𝑡 i ⟧) a)    ≡⟨ i  ⟩
                                         (𝑓 ̂ 𝑩)(λ i →  ∣ h ∣ ((𝑨 ⟦ 𝑡 i ⟧) a))  ≡⟨ ii ⟩
                                         (𝑓 ̂ 𝑩)(λ r → (𝑩 ⟦ 𝑡 r ⟧) (∣ h ∣ ∘ a)) ∎
 where i  = ∥ h ∥ 𝑓 λ i → (𝑨 ⟦ 𝑡 i ⟧) a
       u = (λ j → ∣ h ∣ ((𝑨 ⟦ 𝑡 j ⟧) a))
       v = (λ j → (𝑩 ⟦ 𝑡 j ⟧) (∣ h ∣ ∘ a))
       ii = wd (𝑓 ̂ 𝑩) u v (λ i → comm-hom-term wd{𝑨} 𝑩 h (𝑡 i) a)

\end{code}

To conclude this module, we prove that every term is compatible with every congruence relation. That is, if `t : Term X` and `θ : Con 𝑨`, then `a θ b → t(a) θ t(b)`. (Recall, the compatibility relation `|:` was defined in [Relations.Discrete][].)

\begin{code}


module _ {𝓤 𝓦 : Level}{X : Type 𝓤} where

 open IsCongruence

 _∣:_ : {𝑨 : Algebra 𝓤 𝑆}(t : Term X)(θ : Con{𝓤}{𝓦} 𝑨) → (𝑨 ⟦ t ⟧) |: ∣ θ ∣
 ((ℊ x) ∣: θ) p = p x
 ((node 𝑓 𝑡) ∣: θ) p = (is-compatible ∥ θ ∥) 𝑓 λ x → ((𝑡 x) ∣: θ) p

\end{code}

**WARNING!** The compatibility relation for terms `∣:` is typed as \|:, whereas the compatibility type for functions `|:` (defined in the [Relations.Discrete][] module) is typed as `|:`.


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1">We plan to resolve this before the next major release of the [Agda UALib][].</span>

<br>
<br>

[← Terms.Basic](Terms.Basic.html)
<span style="float:right;">[Subalgebras →](Subalgebras.html)</span>

{% include UALib.Links.md %}














<!-- For the sake of comparison, here is the analogous theorem using `compatible-fun`.

--   compatible-term : {𝑨 : Algebra 𝓤 𝑆}(t : Term X)(θ : Con{𝓦} 𝑨) → compatible-op (𝑨 ⟦ t ⟧) ∣ θ ∣
--   compatible-term (ℊ x) θ p = λ y z → z x
--   compatible-term (node 𝑓 𝑡) θ u v p = (is-compatible ∥ θ ∥) 𝑓 λ x → ((compatible-op (𝑡 x) θ) u v) p
-->
