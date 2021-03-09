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

We could refer to an inhabitant of this type as a "∞-algebra" because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Prelude.Preliminaries.html#truncation](Prelude.Preliminaries.html#truncation).)

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

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signature][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.

If for some reason we want to use both representations of algebras and move back and forth between them, this is easily accomplished with the following functions.

\begin{code}

module _ {𝓤 𝓞 𝓥 : Universe} {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra 𝓤 𝑆 → Algebra 𝓤 𝑆
 algebra→Algebra 𝑨 = (univ 𝑨 , op 𝑨)

 Algebra→algebra : Algebra 𝓤 𝑆 → algebra 𝓤 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥

\end{code}




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UALib][].

\begin{code}

 _̂_ : (𝑓 : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

\end{code}

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection `X` of variable symbols such that, for every algebra `𝑨`, no matter the type of its domain, we have a surjective map `h₀ : X → ∣ 𝑨 ∣` from variables onto the domain of `𝑨`.  We may use the following definition to express this assumption when we need it.

\begin{code}

_↠_ : {𝑆 : Signature 𝓞 𝓥}{𝓤 𝓧 : Universe} → 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h

\end{code}

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

module _ {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨} where

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Lifts of algebras</a>

Here we define some domain-specific lifting tools for our operation and algebra types.

\begin{code}

module _ {𝓞 𝓥 : Universe}{𝑆 : Signature 𝓞 𝓥} where -- Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)} where

 lift-op : {𝓤 : Universe}{I : 𝓥 ̇}{A : 𝓤 ̇} → ((I → A) → A) → (𝓦 : Universe)
  →        ((I → Lift{𝓦} A) → Lift {𝓦} A)

 lift-op f 𝓦 = λ x → lift (f (λ i → Lift.lower (x i)))

 open algebra

 lift-alg : {𝓤 : Universe} → Algebra 𝓤 𝑆 → (𝓦 : Universe) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-alg 𝑨 𝓦 = Lift ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → lift-op (𝑓 ̂ 𝑨) 𝓦)

 lift-alg-record-type : {𝓤 : Universe} → algebra 𝓤 𝑆 → (𝓦 : Universe) → algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-alg-record-type 𝑨 𝓦 = mkalg (Lift (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → lift-op ((op 𝑨) f) 𝓦)

\end{code}

We use the function `lift-alg` to resolve errors that arise when working in Agda's noncummulative hierarchy of type universes. (See the discussion in [Prelude.Lifts][].)




#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Recall, informally this means for every operation symbol `𝑓 : ∣ 𝑆 ∣` and all pairs `𝑎 𝑎' : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of tuples from the domain of 𝑨, the following implication holds:

if `R (𝑎 i) (𝑎' i)` for all `i`, then  `R ((𝑓 ̂ 𝑨) 𝑎) ((𝑓 ̂ 𝑨) 𝑎')`.

The formal definition representing this notion of compatibility is easy to write down since we already have a type that does all the work.

\begin{code}

module _ {𝓤 𝓦 : Universe} {𝑆 : Signature 𝓞 𝓥} where

 compatible : (𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 compatible  𝑨 R = ∀ 𝑓 → compatible-fun (𝑓 ̂ 𝑨) R

\end{code}

Recall the `compatible-fun` type was defined in [Relations.Discrete][] module.



#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations</a>

Next we define a type that represents *compatibility of a continuous relation* with all operations of an algebra. We start by defining compatibility of a continuous relations with a single operation.

\begin{code}

module _ {𝓤 𝓦 : Universe} {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝓤 𝑆} {I : 𝓥 ̇} where

 con-compatible-op : ∣ 𝑆 ∣ → ConRel I ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 con-compatible-op 𝑓 R = con-compatible-fun (λ _ → (𝑓 ̂ 𝑨)) R

\end{code}

In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

\begin{code}

 con-compatible-op' : ∣ 𝑆 ∣ → ConRel I ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 con-compatible-op' 𝑓 R = ∀ 𝕒 → (lift-con-rel R) 𝕒 → R (λ i → (𝑓 ̂ 𝑨) (𝕒 i))

\end{code}

where we have let Agda infer the type of `𝕒`, which is `(i : I) → ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`.

With `con-compatible-op` in hand, it is a trivial matter to define a type that represents *compatibility of a continuous relation with an algebra*.

\begin{code}

 con-compatible : ConRel I ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 con-compatible R = ∀ (𝑓 : ∣ 𝑆 ∣ ) → con-compatible-op 𝑓 R

\end{code}



--------------------------------------


[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
