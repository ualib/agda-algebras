---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Function Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Extensionality where

open import Prelude.Equality public

\end{code}

#### <a id="background-and-motivation">Background and motivation</a>

This introduction is intended for novices.  If you're already familiar with function extensionality, you may want to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : X → Y` are equal?

Suppose f and g are defined on X = ℤ (the integers) as follows: f x := x + 2 and g x := ((2 * x) - 8)/2 + 6.  Would you say that f and g are equal?

If you know a little bit of basic algebra, then you probably can't resist the urge to reduce g to the form x + 2 and proclaim that f and g are, indeed, equal.  And you would be right, at least in middle school, and the discussion would end there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions f and g above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves, at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions f and g both of which take a list as input and produce as output a correctly sorted version of that list?  Are the functions the same?  What if f were defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while g used [quick sort](https://en.wikipedia.org/wiki/Quicksort).  I think most of us would then agree that such f and g are not equal.

In each of the examples above, it is common to say that the two functions f and g are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same (external) output when given the same input, but f and g not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their (internal) definitions differ.

In this module, we describe types (many of which were already defined by Martín Escardó in his [Type Topology][] library) that manifest this notion of *extensional equality of functions*, or *function extensionality*.

#### <a id="definition-of-function-extensionality">Definition of function extensionality</a>

The natural notion of function equality, which is often called *point-wise equality*, is defined as follows: `∀ x → f x ≡ g x`.  Here is how this notion is expressed as a type in the [Type Topology][] library.

\begin{code}

module hide-funext where

 _∼_ : {𝓤 𝓥 : Universe}{X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
 f ∼ g = ∀ x → f x ≡ g x

 infix 0 _∼_

\end{code}

**Function extensionality** is the assertion that point-wise equal functions are "definitionally" equal; that is, for all functions `f` and `g`, we have `f ∼ g → f ≡ g`. In the [Type Topology][] library, the type that represents this is `funext`, which is defined as follows. (Again, we present it here inside the `hide-funext` submodule, but we will import Martín's original definitions below.)

\begin{code}

 funext : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 funext 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B} → f ∼ g → f ≡ g

\end{code}

Similarly, extensionality for *dependent* function types is defined as follows.

\begin{code}

 dfunext : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 dfunext 𝓤 𝓦 = {A : 𝓤 ̇ }{B : A → 𝓦 ̇ }{f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

\end{code}

In most informal settings at least, this so-called "pointwise equality of functions" is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following (which is pointed out to us by <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martín Escardó in his notes</a>), *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement*.


An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

\begin{code}

 global-funext : 𝓤ω
 global-funext = ∀  {𝓤 𝓥} → funext 𝓤 𝓥

 global-dfunext : 𝓤ω
 global-dfunext = ∀ {𝓤 𝓥} → funext 𝓤 𝓥

\end{code}

More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).

Before moving on to the next section, let us pause to make a public import of the original definitions of the above types from the [Type Topology][] library so they're available through the remainder of the [UALib][].<sup>[2](Prelude.Extensionality.html#fn2)</sup>

\begin{code}

open import MGS-FunExt-from-Univalence using (_∼_; funext; dfunext) public

\end{code}


Note that this import directive does not impose any function extensionality assumptions.  It merely makes the types available in case we want to impose such assumptions.




The next function type defines the converse of function extensionality.<sup>[3](Prelude.Extensionality.html#fn3)</sup>

\begin{code}

open import MGS-MLTT using (_∼_) public

module _ {𝓤 𝓦 : Universe} where

 extfun : {A : 𝓤 ̇}{B : 𝓦 ̇}{f g : A → B} → f ≡ g  →  f ∼ g
 extfun 𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁

\end{code}

Here is the analogue for dependent function types.

\begin{code}

 extdfun : {A : 𝓤 ̇ }{B : A → 𝓦 ̇ }(f g : Π B) → f ≡ g → f ∼ g
 extdfun _ _ 𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁

\end{code}


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.

As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to <i>assume</i>.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but as noted above the existence of such a witness cannot be proved in Martin-Löf type theory.

#### <a id="alternative-extensionality-type">Alternative extensionality type</a>

Finally, a useful alternative for expressing dependent function extensionality, which is essentially equivalent to `dfunext`, is to assert that the `extdfun` function is actually an *equivalence*.  This requires a few more definitions from the `MGS-Equivalences` module of the [Type Topology][] library, which we now describe in a hidden module. (We will import the original definitions below, but we exhibit them here for pedagogical reasons and to keep the presentation relatively self contained.)

First, a type is a **singleton** if it has exactly one inhabitant and a **subsingleton** if it has *at most* one inhabitant.  These are defined in the [Type Topology][] library as follows.

\begin{code}

module hide-tt-defs {𝓤 : Universe} where

 is-center : (X : 𝓤 ̇ ) → X → 𝓤 ̇
 is-center X c = (x : X) → c ≡ x

 is-singleton : 𝓤 ̇ → 𝓤 ̇
 is-singleton X = Σ c ꞉ X , is-center X c

 is-subsingleton : 𝓤 ̇ → 𝓤 ̇
 is-subsingleton X = (x y : X) → x ≡ y

\end{code}

Before proceeding, we import the original definitions of the last three types from the [Type Topology][] library. (The [first footnote](Prelude.Equality.html#fn1) of the [Prelude.Equality][] module explains why sometimes we both define and import certain types.)

\begin{code}

open import MGS-Basic-UF using (is-center; is-singleton; is-subsingleton) public

\end{code}


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

Next, we show the definition of the type `is-equiv` which represents a function that is an equivalence in a sense that will soon become clear. The latter is defined using the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function.

In the [Type Topology][] library, a `fiber` type is defined (as a Sigma type) with inhabitants representing inverse images of points in the codomain of the given function.

\begin{code}

module hide-tt-defs' {𝓤 𝓦 : Universe} where

 fiber : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓦 ̇
 fiber {X} f y = Σ x ꞉ X , f x ≡ y

\end{code}

A function is called an **equivalence** if all of its fibers are singletons.

\begin{code}

 is-equiv : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } → (X → Y) → 𝓤 ⊔ 𝓦 ̇
 is-equiv f = ∀ y → is-singleton (fiber f y)

\end{code}

Now we are finally ready to define the type `hfunext` that gives an alternative means of postulating function extensionality.<sup>[4](Prelude.Extensionality.html#fn4)</sup>  We will precede its definition with a public import statement so that the types we described above, originally defined in the Type Topology][], will be available throughout the remainder of the [UALib][].

\begin{code}

open import MGS-Equivalences using (fiber; is-equiv) public

module hide-hfunext where

 hfunext : (𝓤 𝓦 : Universe) → (𝓤 ⊔ 𝓦)⁺ ̇
 hfunext 𝓤 𝓦 = {A : 𝓤 ̇}{B : A → 𝓦 ̇} (f g : Π B) → is-equiv (extdfun f g)
open import MGS-FunExt-from-Univalence using (hfunext) public

\end{code}

------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<sup>2</sup> <span class="footnote" id="fn2"> We won't import `global-funext` yet because we'll need to import that at the top of most of the remaining modules of the [UALib][] anyway, so that it is available when declaring the given module.</span>

<sup>3</sup><span class="footnote" id="fn3"> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`. Also, we later realized that a function called `happly`, which is nearly identical to `extdfun`, is defined in the `MGS-FunExt-from-Univalence` module of the [Type Topology][] library. We initially proved this lemma with a simple invocation of `𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁`, but discovered that this proof leads to an `efunext` type that doesn't play well with other definitions in the [Type Topology][] library (e.g., `NatΠ-is-embedding`).</span>

<sup>4</sup><span class="footnote" id="fn4">  In earlier version of the [UALib][] we defined the type `hfunext` (using another name for it) before realizing that an equivalent type was already defined in the [Type Topology][] library.  For consistency and for the benefit of anyone who might already be familiar with the latter, as well as to correctly assign credit for the original definition, we import the function `hfunext` from the [Type Topology][] library immediately after giving its definition.</span>

<p></p>
<p></p>


[← Prelude.Equality](Prelude.Equality.html)
<span style="float:right;">[Prelude.Inverses →](Prelude.Inverses.html)</span>

{% include UALib.Links.md %}



<!-- unused stuff


extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

-->
