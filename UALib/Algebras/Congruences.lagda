---
layout: default
title : UALib.Algebras.Congruences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="congruence-relations">Congruence Relations</a>

This section presents the [UALib.Algebras.Congruences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)

module UALib.Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import UALib.Algebras.Products {𝑆 = 𝑆} public

\end{code}

A **congruence relation** of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of 𝑨.  This concept can be represented in a number of different ways in type theory.  For example, we define both a Sigma type `Con` and a record type `Congruence`, each of which captures the informal notion of congruence, and each one is useful in certain contexts. (We will see examples later.)

\begin{code}

Con : {𝓤 : Universe}(A : Algebra 𝓤 𝑆) → ov 𝓤 ̇
Con {𝓤} A = Σ θ ꞉ ( Rel ∣ A ∣ 𝓤 ) , IsEquivalence θ × compatible A θ

record Congruence {𝓤 𝓦 : Universe} (A : Algebra 𝓤 𝑆) : ov 𝓦 ⊔ 𝓤 ̇  where
 constructor mkcon
 field
  ⟨_⟩ : Rel ∣ A ∣ 𝓦
  Compatible : compatible A ⟨_⟩
  IsEquiv : IsEquivalence ⟨_⟩

open Congruence

\end{code}



#### <a id="example">Example</a>

We defined the zero relation <a href="https://ualib.gitlab.io/UALib.Relations.Binary.html#1995">𝟎-rel</a> in the <a href="https://ualib.gitlab.io/UALib.Relations.Binary.html#1995">Examples</a> section of the [UALib.Relations.Binary][] module.  We now demonstrate how one constructs the trivial congruence out of this relation.

The relation <a href="https://ualib.gitlab.io/UALib.Relations.Binary.html#1995">𝟎-rel</a> is equivalent to the identity relation `≡` and these are obviously both equivalences. In fact, we already proved this of ≡ in the [UALib.Prelude.Equality][] module, so we simply apply the corresponding proofs.

\begin{code}

module _ {𝓤 : Universe} where

 𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence{𝓤}{A = A} 𝟎-rel
 𝟎-IsEquivalence = record { rfl = ≡-rfl; sym = ≡-sym; trans = ≡-trans }

 ≡-IsEquivalence : {A : 𝓤 ̇} → IsEquivalence{𝓤}{A = A} _≡_
 ≡-IsEquivalence = record { rfl = ≡-rfl ; sym = ≡-sym ; trans = ≡-trans }

\end{code}

Next we formally record another obvious fact---that `𝟎-rel` is compatible with all operations of all algebras.

\begin{code}

module _ {𝓤 : Universe} where

 𝟎-compatible-op : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} (f : ∣ 𝑆 ∣) → compatible-op {𝑨 = 𝑨}  f 𝟎-rel
 𝟎-compatible-op fe {𝑨} f ptws0  = ap (f ̂ 𝑨) (fe (λ x → ptws0 x))

 𝟎-compatible : funext 𝓥 𝓤 → {A : Algebra 𝓤 𝑆} → compatible A 𝟎-rel
 𝟎-compatible fe {A} = λ f args → 𝟎-compatible-op fe {A} f args

\end{code}

Finally, we have the ingredients need to construct the zero congruence.

\begin{code}

Δ : {𝓤 : Universe} → funext 𝓥 𝓤 → (A : Algebra 𝓤 𝑆) → Congruence A
Δ fe A = mkcon 𝟎-rel ( 𝟎-compatible fe ) ( 𝟎-IsEquivalence )

\end{code}




#### <a id="quotient-algebras">Quotient algebras</a>

An important construction in universal algebra is the quotient of an algebra 𝑨 with respect to a congruence relation θ of 𝑨.  This quotient is typically denote by 𝑨 / θ and Agda allows us to define and express quotients using the standard notation.

\begin{code}

_╱_ : {𝓤 𝓡 : Universe}(A : Algebra 𝓤 𝑆) → Congruence{𝓤}{𝓡} A → Algebra (𝓤 ⊔ 𝓡 ⁺) 𝑆

A ╱ θ = ( ∣ A ∣ / ⟨ θ ⟩ ) ,  -- the domain

        λ f 𝒂 → ⟦ (f ̂ A) (λ i → ∣ ∥ 𝒂 i ∥ ∣) ⟧  -- the basic operations

\end{code}

**Unicode Hints**. Produce the ╱ symbol in [agda2-mode][] by typing `\---` and then `C-f` a number of times.

#### <a id="examples">Examples</a>

The zero element of a quotient can be expressed as follows.

\begin{code}

module _ {𝓤 𝓡 : Universe} where

 Zero╱ : {A : Algebra 𝓤 𝑆}(θ : Congruence{𝓤}{𝓡} A) → Rel (∣ A ∣ / ⟨ θ ⟩)(𝓤 ⊔ 𝓡 ⁺)

 Zero╱ θ = λ x x₁ → x ≡ x₁

\end{code}

Finally, the following elimination rule is sometimes useful.

\begin{code}

 ╱-refl : (A : Algebra 𝓤 𝑆){θ : Congruence{𝓤}{𝓡} A}{a a' : ∣ A ∣}
  →       ⟦ a ⟧{⟨ θ ⟩} ≡ ⟦ a' ⟧ → ⟨ θ ⟩ a a'

 ╱-refl A {θ} 𝓇ℯ𝒻𝓁 = IsEquivalence.rfl (IsEquiv θ) _

\end{code}

--------------------------------------

[← UALib.Algebras.Products](UALib.Algebras.Products.html)
<span style="float:right;">[UALib.Homomorphisms →](UALib.Homomorphisms.html)</span>

{% include UALib.Links.md %}
