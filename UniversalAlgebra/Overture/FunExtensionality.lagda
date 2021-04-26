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

_∼_ : {X : Type 𝓤 } {A : X → Type 𝓥 } → Π A → Π A → Type (𝓤 ⊔ 𝓥)
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_

\end{code}

*Function extensionality* is the principle that point-wise equal functions are *definitionally* equal; that is, for all functions `f` and `g` we have `f ∼ g → f ≡ g`. In Agda this principle is represented by the
`Extensionality` type defined in the `Axiom.Extensionality.Propositional` module of the standard library.  We show the definition here for easy reference. (Previously we called this type `dfunext`; see also §2.9 of [HoTT][].)<sup>[2](Overture.Extensionality.html#fn2)</sup>

\begin{code}

module hide-extensionality where

 funext : (𝓤 𝓦 : Level) → Type (lsuc (𝓤 ⊔ 𝓦))
 funext 𝓤 𝓦 = {A : Type 𝓤} {B : A → Type 𝓦} {f g : (x : A) → B x} → f ∼ g → f ≡ g

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext) public

\end{code}


Note that this definition does not postulate function extensionality; it merely defines what the principle is and makes it available in case we want to postulate it.

In most informal settings at least, this so-called *point-wise equality of functions* is typically what one means when one asserts that two functions are "equal."<sup>[3](Overture.Extensionality.html#fn3)</sup>
However, it is important to keep in mind the following fact (see <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Escardó's notes</a>):

*Function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.


#### <a id="alternative-extensionality-type">An alternative way to express function extensionality</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `happly` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but, as above, we exhibit them here for pedagogical reasons and to keep the presentation relatively self-contained.)

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

\begin{code}

is-center : (A : Type 𝓤 ) → A → Type 𝓤
is-center A c = Π x ꞉ A , c ≡ x

is-singleton : Type 𝓤 → Type 𝓤
is-singleton A = Σ c ꞉ A , is-center A c

is-prop : Type 𝓤 → Type 𝓤
is-prop A = (x y : A) → x ≡ y

-- open import MGS-Basic-UF using (is-center; is-singleton; is-subsingleton) public

singleton-is-prop : {𝓤 : Level}(X : Type 𝓤) → is-singleton X → is-prop X
singleton-is-prop X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎


\end{code}


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

\begin{code}

fiber : {A : Type 𝓤 } {B : Type 𝓦 } (f : A → B) → B → Type (𝓤 ⊔ 𝓦)
fiber {𝓤}{𝓦}{A} f y = Σ x ꞉ A , f x ≡ y

\end{code}

A function is called an *equivalence* if all of its fibers are singletons.

\begin{code}

is-equiv : {A : Type 𝓤 } {B : Type 𝓦 } → (A → B) → Type (𝓤 ⊔ 𝓦)
is-equiv f = ∀ y → is-singleton (fiber f y)

\end{code}

We are finally ready to fulfill our promise of a type that provides an alternative means of postulating function extensionality.

\begin{code}

hfunext :  ∀ 𝓤 𝓦 → Type (lsuc (𝓤 ⊔ 𝓦))
hfunext 𝓤 𝓦 = {A : Type 𝓤}{B : A → Type 𝓦} (f g : (x : A) → B x) → is-equiv (cong-app{f = f}{g})

\end{code}



------------------------------------

<sup>1</sup> <span class="footnote" id="fn1"> Most of these types are already defined by in the [Type Topology][] library or the [Agda Standard Library][], so we often imports the definitions; occasionally, however, we repeat the definitions here for pedagogical reasons and to keep the presentation somewhat self-contained.


<sup>2</sup> <span class="footnote" id="fn2"> Previous versions of [UniversalAlgebra][] made heavy use of a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels.
However, we decided to remove all instances of global function extensionality from the latest version of the library and limit ourselves to local applications of the principle. This has the advantage of making transparent precisely how and where the library depends on function extensionality. The price we pay for this precision is a library that is littered with extensionality postulates. Eventually we will probably remove these postulates in favor of an alternative approach to extensionality; e.g., *univalence* and/or Cubical Agda.

<sup>3</sup> <span class="footnote" id="fn3"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>


<br>
<br>

[← Overture.Equality](Overture.Equality.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>

{% include UALib.Links.md %}


