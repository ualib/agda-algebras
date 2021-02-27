---
layout: default
title : UALib.Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebras">Algebras</a>

This section presents the [UALib.Algebras.Algebras][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras.Algebras where

open import Algebras.Signatures public

\end{code}


#### <a id="algebra-types">Algebra types</a>

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe 𝓤, we define the type of **algebras in the signature** 𝑆 (or 𝑆-**algebras**) and with **domain** (or **carrier** or **universe**) `𝐴 : 𝓤 ̇` as follows

\begin{code}

Algebra : (𝓤 : Universe)(𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

Algebra 𝓤  𝑆 = Σ A ꞉ 𝓤 ̇ , ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)

\end{code}

We could refer to an inhabitant of this type as a "∞-algebra" because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Prelude.Preliminaries.html#truncation](UALib.Prelude.Preliminaries.html#truncation).)

We might take this opportunity to define the type of "0-algebras" (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of our algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

\begin{code}

module _ {𝓞 𝓥 : Universe} where
 record algebra (𝓤 : Universe) (𝑆 : Signature 𝓞 𝓥) : (𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺ ̇ where
  constructor mkalg
  field
   univ : 𝓤 ̇
   op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ


\end{code}

(Recall, the type `Signature 𝓞 𝓥` is simply defined as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.)

Of course, we can go back and forth between the two representations of algebras, like so.

\begin{code}

module _ {𝓤 𝓞 𝓥 : Universe} {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra 𝓤 𝑆 → Algebra 𝓤 𝑆
 algebra→Algebra 𝑨 = (univ 𝑨 , op 𝑨)

 Algebra→algebra : Algebra 𝓤 𝑆 → algebra 𝓤 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥

\end{code}




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We conclude this module by defining a convenient shorthand for the interpretation of an operation symbol that we will use often.  It looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with.

\begin{code}

 _̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ f  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 f ̂ 𝑨 = λ x → (∥ 𝑨 ∥ f) x

 infix 40 _̂_
\end{code}




#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection X of variable symbols such that, for every algebra 𝑨, no matter the type of its domain, we have a surjective map h₀ : X → ∣ 𝑨 ∣ from variables onto the domain of 𝑨.  We may use the following definition to express this assumption when we need it.

\begin{code}

_↠_ : {𝑆 : Signature 𝓞 𝓥}{𝓤 𝓧 : Universe} → 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h

\end{code}

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

module _ {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨} where

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Lifts of algebras</a>

Finaly, we provide domain-specific lifting tools for algebraic operation types and algebra types.
\begin{code}


module _ {𝓞 𝓥 : Universe}{𝑆 : Signature 𝓞 𝓥} where -- Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)} where

 lift-op : {𝓤 : Universe}{I : 𝓥 ̇}{A : 𝓤 ̇} → ((I → A) → A) → (𝓦 : Universe)
  →        ((I → Lift{𝓤}{𝓦}A) → Lift{𝓤}{𝓦}A)

 lift-op f 𝓦 = λ x → lift (f (λ i → Lift.lower (x i)))

 open algebra

 lift-alg : {𝓤 : Universe} → Algebra 𝓤 𝑆 → (𝓦 : Universe) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-alg 𝑨 𝓦 = Lift ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → lift-op (𝑓 ̂ 𝑨) 𝓦)

 lift-alg-record-type : {𝓤 : Universe} → algebra 𝓤 𝑆 → (𝓦 : Universe) → algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-alg-record-type 𝑨 𝓦 = mkalg (Lift (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → lift-op ((op 𝑨) f) 𝓦)

\end{code}

We use the function `lift-alg` to resolve errors that arise when working in Agda's noncummulative hierarchy of type universes. (See the discussion in [Prelude.Lifts][].)




#### <a id="compatibility-of-operations-and-relations">Compatibility of operations and relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Here is the definition.

\begin{code}

module _ {𝓤 𝓦 : Universe} {𝑆 : Signature 𝓞 𝓥} where

 compatible : (𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 compatible  𝑨 R = ∀ 𝑓 → compatible-fun (𝑓 ̂ 𝑨) R

\end{code}

Previously we defined `compatible` using the helper function `compatible-op` before we realized that `compatible-fun` makes this helper function redundant. Nonetheless, here is the (now deprecated) definition.

`compatible-op : {𝑨 : Algebra 𝓤 𝑆} → ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇`

`compatible-op {𝑨} f R = ∀{𝒂}{𝒃} → (lift-rel R) 𝒂 𝒃  → R ((f ̂ 𝑨) 𝒂) ((f ̂ 𝑨) 𝒃)`

--------------------------------------

[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
