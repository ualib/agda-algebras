---
layout: default
title : UALib.Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebra-types">Algebra Types</a>

This section presents the [UALib.Algebras.Algebras] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Algebras.Algebras where

open import UALib.Algebras.Signatures public

open import UALib.Prelude.Preliminaries using (𝓤₀; 𝟘; 𝟚) public

\end{code}

-------------------------------

#### <a id="algebra-types">Algebra types</a>

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe 𝓤, we define the type of **algebras in the signature** 𝑆 (or 𝑆-**algebras**) and with **domain** (or **carrier** or **universe**) `𝐴 : 𝓤 ̇` as follows

\begin{code}

Algebra   -- alias
 ∞-algebra : (𝓤 : Universe)(𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

∞-algebra 𝓤  𝑆 = Σ A ꞉ 𝓤 ̇ , ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)
Algebra = ∞-algebra

\end{code}

We may refer to an inhabitant of this type as a "∞-algebra" because its domain can be an arbitrary type, say, `A : 𝓤 ̇` &nbsp;&nbsp; and need not be truncated at some level; in particular, `A` need to be a set. (See the [discussion of truncation and sets](UALib.Prelude.Preliminaries.html#truncation).)

We might take this opportunity to define the type of "0-algebras" (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, we will only need to know that the domains of our algebras are sets in a few places in the UALib, so it seems preferable to work with general ∞-algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.

The type `Algebra 𝓤 𝑆` itself has a type; it is `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`. This type appears so often in the UALib that we will define the following shorthand for its universe level.

```agda
OV : Universe → Universe
OV = λ 𝓤 → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
```

<!-- We can now write simply `Algebra 𝓤 𝑆 : OV 𝓤` in place of the laborious ``Algebra 𝓤 𝑆 : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`. -->

---------------------------------------

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

----------------------------------------

#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We conclude this module by defining a convenient shorthand for the interpretation of an operation symbol that we will use often.  It looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with.

\begin{code}

 _̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ f  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 f ̂ 𝑨 = λ x → (∥ 𝑨 ∥ f) x

\end{code}

#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

Finally, we will want to assume that we always have at our disposal an arbitrary collection \ab X of variable symbols such that, for every algebra \ab 𝑨, no matter the type of its domain, we have a surjective map \ab{h₀} \as : \ab X \as → \aiab{∣}{𝑨} from variables onto the domain of \ab 𝑨.

\begin{code}

_↠_ : {𝑆 : Signature 𝓞 𝓥}{𝓤 𝓧 : Universe} → 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h

\end{code}

-------------------------------------

[← UALib.Algebras.Signatures](UALib.Algebras.Signatures.html)
<span style="float:right;">[UALib.Algebras.Products →](UALib.Algebras.Products.html)</span>


{% include UALib.Links.md %}
