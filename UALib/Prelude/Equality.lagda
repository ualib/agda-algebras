---
layout: default
title : UALib.Prelude.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="equality">Equality</a>

This section describes the [UALib.Prelude.Equality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Equality where

open import Prelude.Preliminaries public

\end{code}

#### <a id="refl">refl</a>

The type referred to as "reflexivity" or "refl" is a very basic but important one. It represents [definitional equality](https://ncatlab.org/nlab/show/equality#definitional_equality).

The `refl` type we use is a standard one. It is defined in the `Identity-Type` module of the [Type Topology][] library, but apart from syntax it is equivalent to the identity type used in most other Agda libraries.

We make `refl` available by importing it from the `Identity-Type` module.  However, we first repeat the definition here (inside a hidden submodule) for clarity.<sup>[1](Prelude.Equality.html#fn1)</sup>

\begin{code}

module hide-refl {𝓤 : Universe} where

 data _≡_ {𝓤} {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where refl : {x : X} → x ≡ x

open import Identity-Type renaming (_≡_ to infix 0 _≡_) public

\end{code}

Thus, whenever we need to complete a proof by simply asserting that `x` is definitionally equal to itself, we can invoke `refl`.  If we need to make `x` explicit, we use `refl {x = x}`.

Let us now formalize the obvious fact that `≡` is an equivalence relation.  We don't have to prove reflexivity, because that is the defining property of `≡`.

\begin{code}

module _  {𝓤 : Universe}{X : 𝓤 ̇ }  where

 ≡-symmetric : (x y : X) → x ≡ y → y ≡ x
 ≡-symmetric _ _ refl = refl

 ≡-sym : {x y : X} → x ≡ y → y ≡ x
 ≡-sym refl = refl

 ≡-transitive : (x y z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-transitive _ _ _ refl refl = refl

 ≡-trans : {x y z : X} → x ≡ y → y ≡ z → x ≡ z
 ≡-trans refl refl = refl

\end{code}

The only difference between `≡-symmetric` and `≡-sym` (respectively, `≡-transitive` and `≡-trans`) is that the latter has fewer explicit arguments, which is sometimes convenient.

Many proofs make abundant use of the symmetry of `_≡_`, and the following syntactic sugar can often improve the readability of such proofs.<sup>[2](Prelude.Equality.html#fn2)</sup>

\begin{code}

module hide-sym {𝓤 : Universe} where

 _⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
 p ⁻¹ = ≡-sym p

open import MGS-MLTT using (_⁻¹) public

\end{code}

So, if we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `≡-sym p` we can use the more intuitive `p ⁻¹` .

Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.<sup>[2](Prelude.Equality.html#fn2)</sup>

\begin{code}

module hide-trans-dot {𝓤 : Universe} where

 _∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
 p ∙ q = ≡-trans p q

open import MGS-MLTT using (_∙_) public

\end{code}

#### <a id="transport">Transport</a>

Alonzo Church characterized equality by declaring two things equal iff no property (predicate) can distinguish them.<sup>[3](Prelude.Equality.html#fn3)</sup>  In other terms, `x` and `y` are equal iff for all `P` we have `P x → P y`.  One direction of this implication is sometimes called *substitution* or *transport* or *transport along an identity*.  It asserts that *if* two objects are equal and one of them satisfies a predicate, then so does the other. A type representing this notion is defined in the `MGS-MLTT` module of the [Type Topology][] library as follows.

\begin{code}

module hide-transport {𝓤 𝓦 : Universe} where

 𝑖𝑑 : {𝓧 : Universe} (X : 𝓧 ̇ ) → X → X
 𝑖𝑑 X = λ x → x

 transport : {X : 𝓤 ̇ } (A : X → 𝓦 ̇ ) {x y : X} → x ≡ y → A x → A y
 transport A (refl {x = x}) = 𝑖𝑑 (A x)

open import MGS-MLTT using (𝑖𝑑; transport) public

\end{code}

As usual, we display `transport` in a hidden module and then imported the existing definition from [Type Topology][].<sup>[1](Preliminaries.Equality.html#fn1)</sup> See [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#70309) of Escardó's [HoTT/UF in Agda notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) for a discussion of transport; cf. [HoTT-Agda's definition](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda).

A function is well defined if and only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  If we have a function `f : X → Y`, two elements `x x' : X` of the domain, and an identity proof `p : x ≡ x'`, then we obtain a proof of `f x ≡ f x'` by simply applying the `ap` function like so, `ap f p : f x ≡ f x'`. Escardó defines `ap` in the [Type Topology][] library as follows.

\begin{code}

module hide-ap  {𝓤 : Universe} where

 ap : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y){x x' : X} → x ≡ x' → f x ≡ f x'
 ap f {x}{x'} p = transport (λ - → f x ≡ f -) p (refl {x = f x})

open import MGS-MLTT using (ap) public

\end{code}

We now define some variations of `ap` that are sometimes useful.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 ap-cong : {A : 𝓤 ̇}{B : 𝓦 ̇}{f g : A → B}{a b : A} → f ≡ g → a ≡ b → f a ≡ g b
 ap-cong refl refl = refl

\end{code}

We sometimes need a version of this that works for [dependent types][], such as the following (which we borrow from the `Relation/Binary/Core.agda` module of the [Agda Standard Library][], transcribed into MHE/UALib notation of course):

\begin{code}

 cong-app : {A : 𝓤 ̇}{B : A → 𝓦 ̇}{f g : Π B} → f ≡ g → ∀ a → f a ≡ g a
 cong-app refl _ = refl

\end{code}




#### <a id="≡-intro-and-≡-elim-for-nondependent-pairs">≡-intro and ≡-elim for nondependent pairs</a>

We conclude the Equality module with some occasionally useful introduction and elimination rules for the equality relation on (nondependent) pair types.


\begin{code}

 ≡-elim-left : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇} → (A₁ , B₁) ≡ (A₂ , B₂) → A₁ ≡ A₂
 ≡-elim-left e = ap fst e


 ≡-elim-right : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇} → (A₁ , B₁) ≡ (A₂ , B₂) → B₁ ≡ B₂
 ≡-elim-right e = ap snd e


 ≡-×-intro : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇} → A₁ ≡ A₂ → B₁ ≡ B₂ → (A₁ , B₁) ≡ (A₂ , B₂)
 ≡-×-intro refl refl = refl


 ≡-×-int : {A : 𝓤 ̇}{B : 𝓦 ̇}{a x : A}{b y : B} → a ≡ x → b ≡ y → (a , b) ≡ (x , y)
 ≡-×-int refl refl = refl
\end{code}

-------------------------------------

<sup>1</sup><span class="footnote" id="fn1">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library, even though we import the latter right after repeating their definitions.  As long as we don't invoke `open hide-refl`, the code inside the `hide-refl` module remains essentially hidden (though Agda *will* type-check this code). It may seem odd to both define things in the hidden module only to immediately import the definition that we actually use, but we do this in order to describe all or most of the types on which the [UALib][] depends, in a clear and self-contained way, while at the same time making sure that this is not misinterpreted as a claim to originality.</span>


<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. In [agda2-mode][] type `⁻¹` as `\^-\^1`, type `𝑖𝑑` as `\Mii\Mid`, and type `∙` as `\.`. In general, to get information about a given unicode character (e.g., how to type it) place the cursor over that character and type `M-x describe-char` (or `M-x h d c`).</span>

<sup>3</sup><span class="footnote" id="fn3"> Alonzo Church, "A Formulation of the Simple Theory of Types," *Journal of Symbolic Logic*, (2)5:56--68, 1940 [JSOR link](http://www.jstor.org/stable/2266170).

<p></p>
<p></p>


[← Prelude.Preliminaries ](Prelude.Preliminaries.html)
<span style="float:right;">[Prelude.Extensionality →](Prelude.Extensionality.html)</span>

{% include UALib.Links.md %}
