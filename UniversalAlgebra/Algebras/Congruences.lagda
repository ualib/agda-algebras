---
layout: default
title : Algebras.Congruences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="congruence-relations">Congruence Relations</a>
This section presents the [Algebras.Congruences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Product using (_,_; Σ; _×_; Σ-syntax)
open import Data.Product.Properties
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; subst)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; ∣_∣; ∥_∥; fst)
open import Relations.Discrete using (𝟎; _|:_)
open import Relations.Quotients using (_/_; ⟪_⟫; IsBlock)


module Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Products{𝑆 = 𝑆} using (ov)

\end{code}

A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of being a congruence, and we define a Sigma type (`Con`) to represent the type of congruences of a given algebra.

\begin{code}

record IsCongruence (𝑨 : Algebra 𝓤 𝑆)(θ : Rel ∣ 𝑨 ∣ 𝓦) : Type(ov 𝓦 ⊔ 𝓤)  where
 constructor mkcon
 field       is-equivalence : IsEquivalence θ
             is-compatible  : compatible 𝑨 θ

Con : (𝑨 : Algebra 𝓤 𝑆) → Type(𝓤 ⊔ ov 𝓦)
Con {𝓤}{𝓦}𝑨 = Σ[ θ ∈ ( Rel ∣ 𝑨 ∣ 𝓦 ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

IsCongruence→Con : {𝑨 : Algebra 𝓤 𝑆}(θ : Rel ∣ 𝑨 ∣ 𝓦) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra 𝓤 𝑆} → ((θ , _) : Con{𝓤}{𝓦} 𝑨) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

\end{code}

#### <a id="example">Example</a>
We defined the *zero relation* `𝟎` in the [Relations.Discrete][] module.  We now build the *trivial congruence*, which has `𝟎` as its underlying relation. Observe that `𝟎` is equivalent to the identity relation `≡` and these are obviously both equivalence relations. In fact, we already proved this of `≡` in the [Overture.Equality][] module, so we simply apply the corresponding proofs.

\begin{code}

𝟎-IsEquivalence : {A : Type 𝓤} →  IsEquivalence {A = A} 𝟎
𝟎-IsEquivalence = record { refl = refl ; sym = sym; trans = trans }

\end{code}

Next we formally record another obvious fact---that `𝟎-rel` is compatible with all operations of all algebras.

\begin{code}

𝟎-compatible-op : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: 𝟎
𝟎-compatible-op fe {𝑨} 𝑓 {i}{j} ptws0  = cong (𝑓 ̂ 𝑨) (fe ptws0)

𝟎-compatible : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} → compatible 𝑨 𝟎
𝟎-compatible fe {𝑨} = λ 𝑓 x → 𝟎-compatible-op fe {𝑨} 𝑓 x

\end{code}

Finally, we have the ingredients need to construct the zero congruence of any algebra we like.

\begin{code}

Δ : (𝑨 : Algebra 𝓤 𝑆){fe : funext 𝓥 𝓤} → IsCongruence 𝑨 𝟎
Δ 𝑨 {fe} = mkcon 𝟎-IsEquivalence (𝟎-compatible fe)

𝟘 : (𝑨 : Algebra 𝓤 𝑆){fe : funext 𝓥 𝓤} → Con{𝓤} 𝑨
𝟘 𝑨 {fe} = IsCongruence→Con 𝟎 (Δ 𝑨 {fe})

\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

#### <a id="quotient-algebras">Quotient algebras</a>
In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.<sup>[1](Algebras.Congruences.html#fn1)</sup>

\begin{code}

_╱_ : (𝑨 : Algebra 𝓤 𝑆) → Con{𝓤}{𝓦} 𝑨 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆

𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)  ,                                  -- the domain of the quotient algebra
        λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.block-u ∥ 𝑎 i ∥) ⟫  -- the basic operations of the quotient algebra

\end{code}

**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}


𝟘[_╱_] : (𝑨 : Algebra 𝓤 𝑆)(θ : Con{𝓤}{𝓦} 𝑨) → Rel (∣ 𝑨 ∣ / ∣ θ ∣)(𝓤 ⊔ lsuc 𝓦)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.

\begin{code}

𝟎[_╱_] : (𝑨 : Algebra 𝓤 𝑆)(θ : Con{𝓤}{𝓦} 𝑨){fe : funext 𝓥 (𝓤 ⊔ lsuc 𝓦)} → Con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] {fe} = 𝟘[ 𝑨 ╱ θ ] , Δ (𝑨 ╱ θ) {fe}

\end{code}


Finally, the following elimination rule is sometimes useful (but it 'cheats' a lot by baking in
a large amount of extensionality that is miraculously true).

\begin{code}

open IsCongruence

/-≡ : {𝑨 : Algebra 𝓤 𝑆}(θ : Con{𝓤}{𝓦} 𝑨){u v : ∣ 𝑨 ∣} → ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
/-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. Produce the `╱` symbol in [agda2-mode][] by typing `\---` and then `C-f` a number of times.</span>


<br>
<br>

[← Algebras.Products](Algebras.Products.html)
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}
