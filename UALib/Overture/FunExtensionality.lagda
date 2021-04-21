---
layout: default
title : Overture.FunExtensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This is the [Overture.FunExtensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.FunExtensionality where

open import Overture.Equality public

\end{code}

This introduction is intended for novices.  Those already familiar with function extensionality may wish to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : A → B` are equal?

Suppose `f` and `g` are defined on `A = ℤ` (the integers) as follows: `f x := x + 2` and `g x := ((2 * x) - 8)/2 + 6`.  Should we call `f` and `g` equal? Are they the "same" function?  What does that even mean?

It's hard to resist the urge to reduce `g` to `x + 2` and proclaim that `f` and `g` are equal. Indeed, this is often an acceptable answer and the discussion normally ends there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions `f` and `g` above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions, `f` and `g`, both of which take a list as argument and produce as output a correctly sorted version of the input list?  Suppose `f` is defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while `g` uses [quick sort](https://en.wikipedia.org/wiki/Quicksort).  Probably few of us would call `f` and `g` the "same" in this case.

In the examples above, it is common to say that the two functions are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same *external* output when given the same input, but they are not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their *internal* definitions differ.

In this module, we describe types that manifest this notion of *extensional equality of functions*, or *function extensionality*.<sup>[1](Overture.Extensionality.html#fn1)</sup>

#### <a id="function-extensionality-types">Function extensionality types</a>

As explained above, a natural notion of function equality is defined as follows:  `f` and `g` are said to be *point-wise equal* provided `∀ x → f x ≡ g x`.  Here is how this is expressed in type theory (e.g., in the [Type Topology][] library).

\begin{code}

module hide-∼ {A : Set 𝓤 } where

 _∼_ : {B : A → Set 𝓦 } → Π B → Π B → Set (𝓤 ⊔ 𝓦)
 f ∼ g = Π x ꞉ A , f x ≡ g x

 infix 0 _∼_

open import MGS-MLTT using (_∼_) public

\end{code}

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal; that is, for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In type theory this principle is represented by the types `funext` (for nondependent functions) and `dfunext` (for dependent functions)~(\cite[\S2.9]{HoTT}).  For example, the latter is defined as follows.<sup>[2](Overture.Extensionality.html#fn2)</sup>

\begin{code}

module hide-funext where

 dfunext : ∀ 𝓤 𝓦 → Set (lsuc (𝓤 ⊔ 𝓦))
 dfunext 𝓤 𝓦 = {A : Set 𝓤 }{B : A → Set 𝓦 }{f g : Π x ꞉ A , B x} →  f ∼ g  →  f ≡ g

\end{code}

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[3](Overture.Extensionality.html#fn3)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.

Before moving on to the next subsection, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].

\begin{code}

open import MGS-FunExt-from-Univalence using (funext; dfunext) public

\end{code}


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.



The next type defines the converse of function extensionality (cf. `cong-app` in [Overture.Equality][] and (2.9.2) in the [HoTT Book][]).

\begin{code}

happly : {A : Set 𝓤 }{B : A → Set 𝓦 }{f g : Π B} → f ≡ g → f ∼ g
happly refl _ = refl

\end{code}


Though it may seem obvious to some readers, we wish to emphasize the important conceptual distinction between two different forms of type definitions by comparing the definitions of `dfunext` and `happly`. In the definition of `dfunext`, the codomain is a parameterized type, namely, `𝓤 ⁺ ⊔ 𝓥 ⁺ ̇`, and the right-hand side of the defining equation of `dfunext` is an assertion (which may or may not hold). In the definition of `happly`, the codomain is an assertion, namely, `f ∼ g`, and the right-hand side of the defining equation is a proof of this assertion. As such, `happly` defines a *proof object*; it *proves* (or *inhabits the type that represents*) the proposition asserting that definitionally equivalent functions are pointwise equal. In contrast, `dfunext` is a type, and we may or may not wish to postulate an inhabitant of this type. That is, we could postulate that function extensionality holds by assuming we have a witness, say, `fe : dfunext 𝓤 𝓥`, but as noted above the existence of such a witness cannot be proved in [MLTT][].


#### <a id="alternative-extensionality-type">An alternative way to express function extensionality</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

\begin{code}

module hide-tt-defs {𝓤 : Level} where

 is-center : (A : Set 𝓤 ) → A → Set 𝓤
 is-center A c = (x : A) → c ≡ x

 is-singleton : Set 𝓤 → Set 𝓤
 is-singleton A = Σ c ꞉ A , is-center A c

 is-subsingleton : Set 𝓤 → Set 𝓤
 is-subsingleton A = (x y : A) → x ≡ y

open import MGS-Basic-UF using (is-center; is-singleton; is-subsingleton) public

\end{code}


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

\begin{code}

module hide-tt-defs' {𝓤 𝓦 : Level} where

 fiber : {A : Set 𝓤 } {B : Set 𝓦 } (f : A → B) → B → Set (𝓤 ⊔ 𝓦)
 fiber {A} f y = Σ x ꞉ A , (f x ≡ y)

\end{code}

A function is called an *equivalence* if all of its fibers are singletons.

\begin{code}

 is-equiv : {A : Set 𝓤 } {B : Set 𝓦 } → (A → B) → Set (𝓤 ⊔ 𝓦)
 is-equiv f = ∀ y → is-singleton (fiber f y)

\end{code}

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.

\begin{code}

open import MGS-Equivalences using (fiber; is-equiv) public

module hide-hfunext where

 hfunext :  ∀ 𝓤 𝓦 → Set (lsuc (𝓤 ⊔ 𝓦))
 hfunext 𝓤 𝓦 = {A : Set 𝓤}{B : A → Set 𝓦} (f g : Π B) → is-equiv (happly{f = f}{g})

open import MGS-FunExt-from-Univalence using (hfunext) public

\end{code}

------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library, so the [UALib][] imports the definitions from there; as usual, we redefine some of these types, inside hidden modules, for the purpose of explication.</span>


<sup>2</sup> <span class="footnote" id="fn2"> Previous versions of the [UALib][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates. Eventually we will probably remove these postulates in favor of an alternative approach to extensionality; e.g., *univalence* and/or Cubical Agda.

<sup>3</sup> <span class="footnote" id="fn3"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>


<br>
<br>

[← Overture.Equality](Overture.Equality.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff

<sup>3</sup> <span class="footnote" id="fn3"> For more details about the `𝓤ω` type see the [universe-levels section](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) of [agda.readthedocs.io](https://agda.readthedocs.io).


extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

-->
