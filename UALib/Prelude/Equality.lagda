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

open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁) public

\end{code}

Since `refl _` is used so often, the following convenient shorthand is also provided in the [Type Topology][] library.

\begin{code}

pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}
\end{code}

Thus, whenever we need to complete a proof by simply asserting that `x`, or the (possibly implicit) thing in question, is definitionally equal to itself, we can invoke `refl x`, or (in the implicit case) `refl _` or even `𝓇ℯ𝒻𝓁`. (The `pattern` directive above is what makes last option available.)


Let us now formalize the obvious fact that `≡` is an equivalence relation.

First we import the original definitions of `_≡_` and `refl` from the [Type Topology][] library. (The definition given above, inside the `hide-refl` module, was merely for illustration.)

\begin{code}


module _  {𝓤 : Universe}{X : 𝓤 ̇ }  where
 ≡-rfl : (x : X) → x ≡ x
 ≡-rfl _ = 𝓇ℯ𝒻𝓁

 ≡-sym : (x y : X) → x ≡ y → y ≡ x
 ≡-sym _ _ 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

 ≡-SYM : {x y : X} → x ≡ y → y ≡ x
 ≡-SYM 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

 ≡-trans : (x y z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-trans _ _ _ 𝓇ℯ𝒻𝓁 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

 ≡-Trans : (x : X){y : X}(z : X) → x ≡ y → y ≡ z → x ≡ z
 ≡-Trans _ _ 𝓇ℯ𝒻𝓁 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁

 ≡-TRANS : {x y z : X} → x ≡ y → y ≡ z → x ≡ z
 ≡-TRANS 𝓇ℯ𝒻𝓁 𝓇ℯ𝒻𝓁 = 𝓇ℯ𝒻𝓁
\end{code}

The only difference between `≡-trans` and `≡-Trans` is that the second argument to `≡-Trans` is implicit so we can omit it when applying `≡-Trans`.  This is sometimes convenient; after all, `≡-Trans` is used to prove that the first and last arguments are the same, and often we don't care about the middle argument. Similarly, we sometimes don't need any of the arguments explicitly; in such cases `≡-TRANS` is easier to apply.

We use the symmetry of `_≡_` very often and we can sometimes improve the readability of a proof by employing some syntactic sugar.<sup>[2](Prelude.Equality.html#fn2)</sup>

\begin{code}

module hide-sym {𝓤 : Universe} where

 _⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
 p ⁻¹ = ≡-SYM p

open import MGS-MLTT using (_⁻¹) public

\end{code}

So, if we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `≡-SYM p` we can use the more elegant and intuitive `p ⁻¹` .

Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.<sup>[2](Prelude.Equality.html#fn2)</sup>

\begin{code}

module hide-trans {𝓤 : Universe} where

 _∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
 p ∙ q = ≡-TRANS p q

open import MGS-MLTT using (_∙_) public

\end{code}

#### <a id="functions-preserve-refl">Functions preserve refl</a>

A simple but useful operation that we will make heavy use of is sometimes called **transport** (or "transport along an identity"). It is defined in the `MGS-MLTT` module of the [Type Topology][] library as follows.<sup>[2](Prelude.Equality.html#fn2)</sup>

\begin{code}

module hide-transport {𝓤 𝓦 : Universe} where

 𝑖𝑑 : {𝓧 : Universe} (X : 𝓧 ̇ ) → X → X
 𝑖𝑑 X = λ x → x

 transport : {X : 𝓤 ̇ } (A : X → 𝓦 ̇ ) {x y : X} → x ≡ y → A x → A y
 transport A (refl x) = 𝑖𝑑 (A x)

open import MGS-MLTT using (𝑖𝑑; transport) public

\end{code}

As usual, we display `transport` in a hidden module and then imported the existing definition from [Type Topology][].<sup>[1](Preliminaries.Equality.html#fn1)</sup> See [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#70309) of Escardó's [HoTT/UF in Agda notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) for a discussion of transport; cf. [HoTT-Agda's definition](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda).

A function is well defined if and only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  If we have a function `f : X → Y`, two elements `x x' : X` of the domain, and an identity proof `p : x ≡ x'`, then we obtain a proof of `f x ≡ f x'` by simply applying the `ap` function like so, `ap f p : f x ≡ f x'`. Escardó defines `ap` in the [Type Topology][] library as follows.

\begin{code}

module hide-ap  {𝓤 𝓦 : Universe} where
 ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
 ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))

open import MGS-MLTT using (ap) public

\end{code}

We now define some variations of `ap` that are sometimes useful.

\begin{code}

ap-cong : {𝓤 𝓦 : Universe}{A : 𝓤 ̇ }{B : 𝓦 ̇ }{f g : A → B} {a b : A}
 →        f ≡ g  →  a ≡ b
          ---------------
 →        f a ≡ g b

ap-cong (refl _) (refl _) = refl _

\end{code}

We sometimes need a version of this that works for [dependent types][], such as the following (which we borrow from the `Relation/Binary/Core.agda` module of the [Agda Standard Library][], transcribed into MHE/UALib notation of course):

\begin{code}

cong-app : {𝓤 𝓦 : Universe}
           {A : 𝓤 ̇} {B : A → 𝓦 ̇}
           {f g : (a : A) → B a}
 →          f ≡ g   →   (a : A)
          -----------------------
 →              f a ≡ g a

cong-app (refl _) a = refl _

\end{code}




#### <a id="≡-intro-and-≡-elim-for-nondependent-pairs">≡-intro and ≡-elim for nondependent pairs</a>

We conclude the Equality module with some occasionally useful introduction and elimination rules for the equality relation on (nondependent) pair types.



\begin{code}

open import MGS-MLTT using (ap) public

≡-elim-left : {𝓤 𝓦 : Universe}
              {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →            (A₁ , B₁) ≡ (A₂ , B₂)
              ----------------------
 →                   A₁ ≡ A₂

≡-elim-left e = ap pr₁ e


≡-elim-right : {𝓤 𝓦 : Universe}
               {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇}
 →             (A₁ , B₁) ≡ (A₂ , B₂)
               -----------------------
 →                    B₁ ≡ B₂

≡-elim-right e = ap pr₂ e


≡-×-intro : {𝓤 𝓦 : Universe}
            {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇}
 →           A₁ ≡ A₂  →  B₁ ≡ B₂
           ------------------------
 →          (A₁ , B₁) ≡ (A₂ , B₂)

≡-×-intro (refl _ ) (refl _ ) = (refl _ )


≡-×-int : {𝓤 𝓦 : Universe}
          {A : 𝓤 ̇} {B : 𝓦 ̇}
          (a a' : A)(b b' : B)
 →         a ≡ a'  →  b ≡ b'
          ------------------------
 →         (a , b) ≡ (a' , b')

≡-×-int a a' b b' (refl _ ) (refl _ ) = (refl _ )
\end{code}

-------------------------------------

<sup>1</sup><span class="footnote" id="fn1">To hide code from the rest of the development, we enclose it in a named module.  In this case, we don't want the code inside the `hide-refl` module to conflict with the original definitions of these functions from Escardo's Type Topology library, which we import right after repeating their definitions.  As long as we don't invoke `open hide-refl`, the code inside the `hide-refl` model remains essentially hidden (for the purposes of resolving conflicts, though Agda *will* type-check the code). It may seem odd to both define `refl` ourselves only to immediately import the definition that we actually use. We do this in order to describe all or most of the types on which the [UALib][] depends, in a clear and self-contained way, while at the same time making sure that this cannot be misinterpreted as a claim to originality.</span>


<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. In [agda2-mode][] type `⁻¹` as `\^-\^1`, type `𝑖𝑑` as `\Mii\Mid`, and type `∙` as `\.`. In general, to get information about a given unicode character (e.g., how to type it) place the cursor over that character and type `M-x describe-char` (or `M-x h d c`).</span>



-------------------------------------


[← Prelude.Preliminaries ](Prelude.Preliminaries.html)
<span style="float:right;">[Prelude.Extensionality →](Prelude.Extensionality.html)</span>

{% include UALib.Links.md %}
