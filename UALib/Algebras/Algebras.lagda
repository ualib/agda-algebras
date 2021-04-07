---
layout: default
title : Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebras">Algebras</a>

This section presents the [Algebras.Algebras][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras.Algebras where

open import Algebras.Signatures public

\end{code}


#### <a id="algebra-types">Algebra types</a>

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signatures][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`. For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe `𝓤`, we define the type of *algebras in the signature* 𝑆 (or 𝑆-*algebras*) and with *domain* (or *carrier*) `𝐴 : 𝓤 ̇` &nbsp as follows.<sup>[1](Algebras.Algebras.html#fn1)</sup>

\begin{code}

Algebra : (𝓤 : Universe)(𝑆 : Signature 𝓞 𝓥) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

Algebra 𝓤 𝑆 = Σ A ꞉ 𝓤 ̇ ,                     -- the domain
              Π f ꞉ ∣ 𝑆 ∣ , Op (∥ 𝑆 ∥ f) A    -- the basic operations

\end{code}

We might refer to inhabitants of this type as ∞-*algebras* because their domains can be of arbitrary type and need not be truncated at some level and, in particular, need to be a set. (See the [Relations.Truncation][] module.)

We might take this opportunity to define the type of 0-*algebras*, that is, algebras whose domains are sets, which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of certain algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then explicitly postulate [uniquness of identity proofs](Relations.Truncation.html#uniqueness-of-identity-proofs) when and only when necessary.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Some people prefer to represent algebraic structures in type theory using records, and for those folks we offer the following (equivalent) definition.

\begin{code}

record algebra (𝓤 : Universe) (𝑆 : Signature 𝓞 𝓥) : (𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺ ̇ where
 constructor mkalg
 field
  univ : 𝓤 ̇
  op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ


\end{code}

This representation of algebras as inhabitants of a record type is equivalent to the representation using Sigma types in the sense that a bi-implication between the two representations is obvious.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} where

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




#### <a id="lifts-of-algebras">Level lifting algebra types</a>

Recall, in the [section on level lifting and lowering](Overture.Lifts.html#level-lifting-and-lowering), we described the difficulties one may encounter when working with a noncumulative universe hierarchy. We made a promise to provide some domain-specific level lifting and level lowering methods. Here we fulfill this promise by supplying a couple of bespoke tools designed specifically for our operation and algebra types.

\begin{code}


module _ {𝓘 : Universe} {I : 𝓘 ̇}{A : 𝓤 ̇} where

 open Lift

 Lift-op : Op I A → (𝓦 : Universe) → Op I (Lift{𝓦} A)
 Lift-op f 𝓦 = λ x → lift (f (λ i → lower (x i)))

module _ {𝑆 : Signature 𝓞 𝓥}  where

 Lift-alg : Algebra 𝓤 𝑆 → (𝓦 : Universe) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 Lift-alg 𝑨 𝓦 = Lift ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-op (𝑓 ̂ 𝑨) 𝓦)

 open algebra

 Lift-alg-record-type : algebra 𝓤 𝑆 → (𝓦 : Universe) → algebra (𝓤 ⊔ 𝓦) 𝑆
 Lift-alg-record-type 𝑨 𝓦 = mkalg (Lift (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → Lift-op ((op 𝑨) f) 𝓦)

\end{code}

What makes the types just defined useful for resolving type level errors is the nice properties they possess.  Indeed, the [UALib][] contains formal proofs of the following facts.

+ [`Lift` is a homomorphism](Homomorphisms.Basic.html#exmples-of-homomorphisms) (see [Homomorphisms.Basic][])
+ [`Lift` is an algebraic invariant](Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant") (see [Homomorphisms.Isomorphisms][])
+ [`Lift` of a subalgebra is a subalgebra](Subalgebras.Subalgebras.html#lifts-of-subalgebras) (see [Subalgebras.Subalgebras][])
+ [`Lift` preserves identities](Varieties.EquationalLogic.html#lift-invariance)) (see [Varieties.EquationalLogic][])


#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Recall (from [Relations.Discrete][]) that informally this means for every operation symbol `𝑓 : ∣ 𝑆 ∣` and all pairs `u v : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of tuples from the domain of 𝑨, the following implication holds:

&nbsp;&nbsp; `(Π i ꞉ I , R (u i) (u i))` &nbsp;&nbsp;  `→`  &nbsp;&nbsp; `R ((𝑓 ̂ 𝑨) u) ((𝑓 ̂ 𝑨) v)`.

In other terms, `∀ 𝑓 → (𝑓 ̂ 𝑨) |: R`. The formal definition of this notion of compatibility is immediate since all the work is done by the relation `|:` (which we already defined in [Relations.Discrete][]).

\begin{code}

 compatible : (𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R

\end{code}

Recall, the `|:` type was defined in [Relations.Discrete][] module.




#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations<sup>[★](Algebras.Algebras.html#fn0)</sup></a>

In the [Relations.Continuous][] module, we defined a function called `cont-compatible-op` to represent the assertion that a given continuous relation is compatible with a given operation. With that, it is easy to define a function, which we call `cont-compatible`, representing compatibility of a continuous relation with all operations of an algebra.  Similarly, we define the analogous `dep-compatible` function for the (even more general) type of *dependent relations*.

\begin{code}

module continuous-compatibility {𝓤 𝓦 : Universe}{𝑆 : Signature 𝓞 𝓥} where
 open import Relations.Continuous using (ContRel; DepRel; cont-compatible-op; dep-compatible-op)

 cont-compatible : {I : 𝓥 ̇}(𝑨 : Algebra 𝓤 𝑆) → ContRel I ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 cont-compatible 𝑨 R = Π 𝑓 ꞉ ∣ 𝑆 ∣ , cont-compatible-op (𝑓 ̂ 𝑨) R

 dep-compatible : {I : 𝓥 ̇}(𝒜 : I → Algebra 𝓤 𝑆) → DepRel I (λ i → ∣ 𝒜  i ∣) 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 dep-compatible 𝒜 R = Π 𝑓 ꞉ ∣ 𝑆 ∣ , dep-compatible-op (λ i → 𝑓 ̂ (𝒜 i)) R

\end{code}



--------------------------------------

<sup>★</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<sup>[1]</sup><span class="footnote" id="fn1"> In classical universal algebra, the domain of an algebra `𝑨` is usualled called the "universe" of `𝑨`.  We avoid this terminology and reserve universe for use in defining the type hierarchy. (See the [Agda Universes](Overture.Preliminaries.html#agda-universes)</a> section of the [Overture.Preliminaries][] module.</span>

<br>
<br>

[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}


<!-- In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

 cont-compatible-op' : ∣ 𝑆 ∣ → ContRel I ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 cont-compatible-op' 𝑓 R = Π 𝒂 ꞉ (I → ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣) , (eval-cont-rel R 𝒂 → R λ i → (𝑓 ̂ 𝑨)(𝒂 i))

-->
