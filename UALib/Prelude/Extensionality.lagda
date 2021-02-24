---
layout: default
title : UALib.Prelude.Extensionality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="extensionality">Extensionality</a>

This section describes the [UALib.Prelude.Extensionality][] module of the [Agda Universal Algebra Library][].

#### <a id="background-and-motivation">Background and motivation</a>

This introduction is intended for novices.  If you're already familiar with function extensionality, you may want to skip to <a href="function-extensionality">the next subsection</a>.

What does it mean to say that two functions `f g : X → Y` are equal?

Suppose f and g are defined on X = ℤ (the integers) as follows: f x := x + 2 and g x := ((2 * x) - 8)/2 + 6.  Would you say that f and g are equal?

If you know a little bit of basic algebra, then you probably can't resist the urge to reduce g to the form x + 2 and proclaim that f and g are, indeed, equal.  And you would be right, at least in middle school, and the discussion would end there.  In the science of computing, however, more attention is paid to equality, and with good reason.

We can probably all agree that the functions f and g above, while not syntactically equal, do produce the same output when given the same input so it seems fine to think of the functions as the same, for all intents and purposes. But we should ask ourselves, at what point do we notice or care about the difference in the way functions are defined?

What if we had started out this discussion with two functions f and g both of which take a list as input and produce as output a correctly sorted version of that list?  Are the functions the same?  What if f were defined using the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm, while g used [quick sort](https://en.wikipedia.org/wiki/Quicksort).  I think most of us would then agree that such f and g are not equal.

In each of the examples above, it is common to say that the two functions f and g are [extensionally equal](https://en.wikipedia.org/wiki/Extensionality), since they produce the same (external) output when given the same input, but f and g not [intensionally equal](https://en.wikipedia.org/wiki/Intension), since their (internal) definitions differ.

In this module, we describe types (mostly imported from the [Type Topology][] library) that manifest this notion of *extensional equality of functions*, or *function extensionality*.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude.Extensionality where

open import Prelude.Inverses public

\end{code}


#### <a id="function-extensionality">Function extensionality</a>

As explained above, a natural notion of function equality, sometimes called *point-wise equality*, is also known as *extensional equality* and is defined as follows: f and g are *extensionally equal* provided ∀ x → f x ≡ g x.  Here is how this notion of equality is expressed as a type in the [Type Topology][] library.

\begin{code}

open import MGS-MLTT using (Π) public

module hide where

 _∼_ : {𝓤 𝓥 : Universe}{X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
 f ∼ g = ∀ x → f x ≡ g x

 infix 0 _∼_

\end{code}


Extensional equality of functions, or *function extensionality*, means that any two point-wise equal functions are equal. In informal settings, pointwise equality is typically what one means when one asserts that two functions are "equal."<sup>[1](Prelude.Extensionality.html#fn1)</sup> However, it is important to keep in mind the following

<div class="color_box" id="mltt-ext">
  <div id="title">MLTT Foundations Note</div>
  <div id="content">As <a href="https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua">Martin Escardó points out</a>, function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory. It is an independent statement.
  </div>
</div>


In the [Type Topology][] library, function extensionality is denoted by `funext` and defined as follows.

\begin{code}

 funext : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 funext 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B} → f ∼ g → f ≡ g

\end{code}





#### <a id="dependent-function-extensionality">Dependent function extensionality</a>

Extensionality for dependent function types is defined as follows.

\begin{code}

 dfunext : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 dfunext 𝓤 𝓦 = {A : 𝓤 ̇ }{B : A → 𝓦 ̇ }{f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

\end{code}

An assumption that we adopt throughout much of the current version of the [UALib][] is a *global function extensionality principle*. This asserts that function extensionality holds at all universe levels. Agda is capable of expressing types representing global principles as the language has a special universe level for such types.  Following Escardó, we denote this universe by 𝓤ω (which is just an alias for Agda's `Setω` universe).

The types `global-funext` and `global-dfunext` are defined in the [Type Topology][] library as follows.

\begin{code}

 global-funext : 𝓤ω
 global-funext = ∀  {𝓤 𝓥} → funext 𝓤 𝓥

 global-dfunext : 𝓤ω
 global-dfunext = ∀ {𝓤 𝓥} → funext 𝓤 𝓥

\end{code}


More details about the 𝓤ω type are available at [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set).


\begin{code}

extensionality-lemma : {𝓘 𝓤 𝓥 𝓣 : Universe}{I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                       (p q : (i : I) → (X → A i) → 𝓣 ̇ )(args : X → (Π A))
 →                     p ≡ q
                       -------------------------------------------------------------
 →                     (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

extensionality-lemma p q args p≡q = ap (λ - → λ i → (- i) (λ x → args x i)) p≡q

\end{code}

The next function type defines the converse of function extensionality.<sup>[2](Prelude.Extensionality.html#fn2)</sup></a>

\begin{code}

open import MGS-MLTT using (_∼_)

extfun : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}{f g : A → B} → f ≡ g  →  f ∼ g
extfun 𝓇ℯ𝒻𝓁 _  = 𝓇ℯ𝒻𝓁

\end{code}

Here is the analogue for dependent function types.

\begin{code}

extdfun : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } {f g : Π B} → f ≡ g → f ∼ g
extdfun 𝓇ℯ𝒻𝓁 _ = 𝓇ℯ𝒻𝓁

\end{code}


Although the proofs of the `extfun` and `extdfun` lemmas are trivial, it can clarify an otherwise confusing argument to invoke such lemmas explicitly (e.g., when given a definitional equality where a point-wise equality is required).

An important conceptual distinction exists between type definitions similar in form to `funext` (or `extensionality`) and those similar to `extfun`.  Notice that the codomain of the former is a generic type, namely, `(𝓤 ⊔ 𝓥) ⁺ ̇ `, while the codomain of the latter is the assertion `f ∼ g`.  Also, the defining equation of `funext` is an assertion, while the defining equation of `extdun` is a proof.  As such, `extfun` is a proof object; it proves (inhabits the type that represents) the proposition asserting that definitionally equivalent functions are point-wise equal. In contrast, `funext` is a type that we may or may not wish to *assume*.  That is, we could assume we have a witness, say, `fe : funext 𝓤 𝓥` (that is, a proof) that point-wise equal functions are equivalent, but, as noted above, the existence of such a witness cannot be proved in Martin-L\"of type theory.

-------------------------------------

<span class="footnote" id="fn1"><sup>1</sup>If one assumes the [univalence axiom][], then the `_∼_` relation is equivalent to equality of functions.  See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).</span>

<span class="footnote" id="fn2"><sup>2</sup> In previous versions of the [UALib][] this function was called `intensionality`, indicating that it represented the concept of *function intensionality*, but we realized this isn't quite right and changed the name to the less controvertial `extfun`.</span> 


--------------------

[← Prelude.Inverses](Prelude.Inverses.html)
<span style="float:right;">[Prelude.Lifts →](Prelude.Lifts.html)</span>

{% include UALib.Links.md %}
