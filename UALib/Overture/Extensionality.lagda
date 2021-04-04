---
layout: default
title : Overture.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This is the [Overture.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Extensionality where

open import Overture.Equality public

\end{code}

#### <a id="background-and-motivation">Background and motivation</a>

This introduction is intended for novices.  Those already familiar with function extensionality may wish to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : A → B` are equal?

Suppose `f` and `g` are defined on `A = ℤ` (the integers) as follows: `f x := x + 2` and `g x := ((2 * x) - 8)/2 + 6`.  Should we call `f` and `g` equal? Are they the "same" function?  What does that even mean?

It's hard to resist the urge to reduce `g` to `x + 2` and proclaim that `f` and `g` are equal. Indeed, this is often an acceptable answer and the discussion normally ends there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions `f` and `g` above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions, `f` and `g`, both of which take a list as argument and produce as output a correctly sorted version of the input list?  Suppose `f` is defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while `g` uses [quick sort](https://en.wikipedia.org/wiki/Quicksort).  Probably few of us would call `f` and `g` the "same" in this case.

In the examples above, it is common to say that the two functions are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same *external* output when given the same input, but they are not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their *internal* definitions differ.

In this module, we describe types that manifest this notion of *extensional equality of functions*, or *function extensionality*.<sup>[1](Overture.Extensionality.html#fn1)</sup>

#### <a id="definition-of-function-extensionality">Definition of function extensionality</a>

As explained above, a natural notion of function equality is defined as follows:  `f` and `g` are said to be *point-wise equal* provided `∀ x → f x ≡ g x`.  Here is how this is expressed in type theory (e.g., in the [Type Topology][] library).

\begin{code}

module hide-∼ where

 _∼_ : {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } → Π B → Π B → 𝓤 ⊔ 𝓦 ̇
 f ∼ g = ∀ x → f x ≡ g x

 infix 0 _∼_

open import MGS-MLTT using (_∼_) public

\end{code}

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal. In other terms, function extensionality asserts that for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In the [Type Topology][] library the type that represents this principle is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, and import the original definition below.)

\begin{code}

module hide-funext where

 funext : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 funext 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B} → f ∼ g → f ≡ g

\end{code}

Similarly, extensionality for *dependent* function types is defined as follows.

\begin{code}

 dfunext : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 dfunext 𝓤 𝓦 = {A : 𝓤 ̇ }{B : A → 𝓦 ̇ }{f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

\end{code}

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[2](Overture.Extensionality.html#fn2)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

\begin{code}

open import MGS-FunExt-from-Univalence using (funext; dfunext) public

\end{code}


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.


#### <a id="global-function-extensionality">Global function extensionality</a>

Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.  Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Escardó denote this universe by 𝓤ω (which is an alias for Agda's `Setω` universe).<sup>[3](Overture.Extensionality.html#fn3)</sup> The types `global-funext` and `global-dfunext` defined in the [Type Topology][] library are the following.

\begin{code}

module hide-global-funext where

 global-funext : 𝓤ω
 global-funext = ∀  {𝓤 𝓥} → funext 𝓤 𝓥

 global-dfunext : 𝓤ω
 global-dfunext = ∀ {𝓤 𝓥} → dfunext 𝓤 𝓥

\end{code}


**ATTENTION!** (backward incompatibility)  
We have decided to remove from the latest version of the [UALib][] all instances of global function extensionality and limit ourselves to local applications of the principle.  This has the advantage of making transparent precisely how and where the library depends on function extensionality.  (It also prepares the way for moving to a univalence-based version of the library that we plan to undertake very soon.)  The price we pay for this precision is a library that is littered with many function extensionality postulates. We will try to clean this up in the near future (but ultimately we will probably remove all of these postulates in favor of *univalence*).



The next two types define the converse of function extensionality.

\begin{code}

extfun : {A : 𝓤 ̇}{B : 𝓦 ̇}{f g : A → B} → f ≡ g  →  f ∼ g
extfun refl _ = refl

\end{code}

Here is the analogue for dependent function types (cf. `cong-app` in [Overture.equality][]).

\begin{code}

extdfun : {A : 𝓤 ̇ }{B : A → 𝓦 ̇ }(f g : Π B) → f ≡ g → f ∼ g
extdfun _ _ refl _ = refl

\end{code}


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions we have seen so far.  We do so by comparing the definitions of `funext` and `extfun`.

In the definition of `funext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `funext` is an assertion (which may or may not hold). In the definition of `extfun`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `extfun` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `funext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : funext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

\begin{code}

module hide-tt-defs {𝓤 : Universe} where

 is-center : (A : 𝓤 ̇ ) → A → 𝓤 ̇
 is-center A c = (x : A) → c ≡ x

 is-singleton : 𝓤 ̇ → 𝓤 ̇
 is-singleton A = Σ c ꞉ A , is-center A c

 is-subsingleton : 𝓤 ̇ → 𝓤 ̇
 is-subsingleton A = (x y : A) → x ≡ y

\end{code}

We import the original definitions of the last three types as follows. (The [first footnote](Overture.Equality.html#fn1) of [Overture.Equality][] explains why we both define and import certain types.)

\begin{code}

open import MGS-Basic-UF using (is-center; is-singleton; is-subsingleton) public

\end{code}


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

\begin{code}

module hide-tt-defs' {𝓤 𝓦 : Universe} where

 fiber : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → B → 𝓤 ⊔ 𝓦 ̇
 fiber {A} f y = Σ x ꞉ A , f x ≡ y

\end{code}

A function is called an *equivalence* if all of its fibers are singletons.

\begin{code}

 is-equiv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → 𝓤 ⊔ 𝓦 ̇
 is-equiv f = ∀ y → is-singleton (fiber f y)

\end{code}

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.<sup>[4](Overture.Extensionality.html#fn4)</sup>

\begin{code}

open import MGS-Equivalences using (fiber; is-equiv) public

module hide-hfunext where

 hfunext :  ∀ 𝓤 𝓦 → (𝓤 ⊔ 𝓦)⁺ ̇
 hfunext 𝓤 𝓦 = {A : 𝓤 ̇}{B : A → 𝓦 ̇} (f g : Π B) → is-equiv (extdfun f g)

open import MGS-FunExt-from-Univalence using (hfunext) public

\end{code}

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>3</sup> <span class="footnote" id="fn3"> For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).

<sup>4</sup><span class="footnote" id="fn4">  In earlier version of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the latter, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.</span>

<br>
<br>

[← Overture.Equality](Overture.Equality.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff


extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

-->
