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

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)

module Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Products {𝑆 = 𝑆} public

\end{code}

A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of different ways, not only in type theory, but also in the informal presentation.  Informally, a relation is a congruence if and only if it is both an equivalence relation on the domain of `𝑨` and a subalgebra of the square of `𝑨`.  Formally, a compatible equivalence relation can be represented as an inhabitant of a certain Sigma type (which we denote by `Con`) or a record type (which we denote by `Congruence`).

\begin{code}

Con : {𝓤 : Universe}(𝑨 : Algebra 𝓤 𝑆) → ov 𝓤 ̇
Con {𝓤} 𝑨 = Σ θ ꞉ ( Rel ∣ 𝑨 ∣ 𝓤 ) , IsEquivalence θ × compatible 𝑨 θ

record Congruence {𝓤 𝓦 : Universe} (𝑨 : Algebra 𝓤 𝑆) : ov 𝓦 ⊔ 𝓤 ̇  where
 constructor mkcon
 field
  ⟨_⟩ : Rel ∣ 𝑨 ∣ 𝓦
  Compatible : compatible 𝑨 ⟨_⟩
  IsEquiv : IsEquivalence ⟨_⟩

open Congruence

\end{code}

Each of these options captures the informal notion of congruence, and each one is useful in certain contexts.



#### <a id="example">Example</a>
We defined the zero relation `𝟎-rel` in the [Relations.Discrete][] module, and we now demonstrate how to build the trivial congruence out of this relation.

The relation `𝟎-rel` is equivalent to the identity relation `≡` and these are obviously both equivalences. In fact, we already proved this of `≡` in the [Overture.Equality][] module, so we simply apply the corresponding proofs.

\begin{code}

𝟎-IsEquivalence : {A : 𝓤 ̇} →  IsEquivalence {A = A} 𝟎
𝟎-IsEquivalence = record {rfl = λ x → refl{x = x}; sym = ≡-symmetric; trans = ≡-transitive}

\end{code}

Next we formally record another obvious fact---that `𝟎-rel` is compatible with all operations of all algebras.

\begin{code}

𝟎-compatible-op : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: 𝟎
𝟎-compatible-op fe {𝑨} 𝑓 {i}{j} ptws0  = ap (𝑓 ̂ 𝑨) (fe ptws0)

𝟎-compatible : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} → compatible 𝑨 𝟎
𝟎-compatible fe {𝑨} = λ 𝑓 args → 𝟎-compatible-op fe {𝑨} 𝑓 args

\end{code}

Finally, we have the ingredients need to construct the zero congruence of any algebra we like. (For example, see the proof of `⟦𝟎⟧ 𝑨 ╱ θ` below.)

\begin{code}

Δ : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} → Congruence 𝑨
Δ fe = mkcon 𝟎 (𝟎-compatible fe) 𝟎-IsEquivalence

\end{code}


#### <a id="quotient-algebras">Quotient algebras</a>
In many areas of abstract mathematics (including universal algebra) the quotient of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays a central role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.<sup>[1](Algebras.Congruences.html#fn1)</sup>

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 _╱_ : (𝑨 : Algebra 𝓤 𝑆) → Congruence{𝓤}{𝓦} 𝑨 → Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆

 𝑨 ╱ θ = ( ∣ 𝑨 ∣ / ⟨ θ ⟩ ) ,                     -- the domain of the quotient algebra

         λ 𝑓 𝒂 → ⟦ (𝑓 ̂ 𝑨) (λ i → ∣ ∥ 𝒂 i ∥ ∣) ⟧  -- the basic operations of the quotient algebra

\end{code}

**Example**. If we adopt the notation `[𝟎] 𝑨 ╱ θ` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}


 [𝟎]_╱_ : (𝑨 : Algebra 𝓤 𝑆)(θ : Congruence{𝓤}{𝓦} 𝑨) → Rel (∣ 𝑨 ∣ / ⟨ θ ⟩)(𝓤 ⊔ 𝓦 ⁺)
 [𝟎] 𝑨 ╱ θ = λ x x₁ → x ≡ x₁

\end{code}

We easily obtain from this the zero congruence relation of `𝑨 ╱ θ` (which we denote by `⟦𝟎⟧ 𝑨 ╱ θ`) using the `Δ` function defined above.

\begin{code}

 ⟦𝟎⟧_╱_ : (𝑨 : Algebra 𝓤 𝑆)(θ : Congruence{𝓤}{𝓦} 𝑨){fe : funext 𝓥 (𝓤 ⊔ (𝓦 ⁺))} → Congruence (𝑨 ╱ θ)
 (⟦𝟎⟧ 𝑨 ╱ θ) {fe} = Δ fe

\end{code}


Finally, the following elimination rule is sometimes useful.

\begin{code}

module _ {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} where

 ╱-≡ : (θ : Congruence{𝓤}{𝓦} 𝑨){u v : ∣ 𝑨 ∣} → ⟦ u ⟧{⟨ θ ⟩} ≡ ⟦ v ⟧ → ⟨ θ ⟩ u v
 ╱-≡ θ refl = IsEquivalence.rfl (IsEquiv θ) _

\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. Produce the `╱` symbol in [agda2-mode][] by typing `\---` and then `C-f` a number of times.</span>



<br>
<br>

[← Algebras.Products](Algebras.Products.html)
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}
