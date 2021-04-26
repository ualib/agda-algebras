---
layout: default
title : Overture.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="equality">Equality</a>

This is the [Overture.Equality][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Equality where

open import Overture.Preliminaries public

\end{code}

#### <a id="identity-type">The identity type of MLTT</a>

Here we discuss what is probably the most important type in [MLTT][], the *identity type*. This concept is easily understood, at least heuristically, with the following slogan:

*Definitional equality is the substitution-preserving equivalence relation generated by definitions.*

We will make this precise below, but first let us quote from a primary source.

In [An Intuitionistic Theory of Types: Predicative Part](https://www.sciencedirect.com/science/article/pii/S0049237X08719451), Per Martin-Löf offers the following definition (italics added):<sup>[1](Overture.Equality.html#fn1)</sup>

"*Definitional equality* is defined to be the equivalence relation, that is, reflexive, symmetric and transitive relation, which is generated by the principles that a definiendum is always definitionally equal to its definiens and that definitional equality is preserved under substitution."<sup>[2](Overture.Equality.html#fn2)

To be sure we understand what this means, let `:=` denote the relation with respect to which `x` is related to `y` (denoted `x := y`) if and only if `y` *is the definition of* `x`.  Then the *identity relation* `≡` is the reflexive, symmetric, transitive, substitutive closure of `:=`. By *subsitutive closure* we mean closure under the following *substitution rule*.


```agda
    {A : Type 𝓤} {B : A → Type 𝓦} {x y : A}   x ≡ y
    ------------------------------------------ (subst)
                B x ≡ B y
```

The datatype we use to represent the identity relation is imported from the Identity-Type module of the [Type Topology][] library, but apart from superficial syntactic differences, it is equivalent to the standard *Paulin-Mohring style identity type* found in most other Agda libraries.  We repeat the definition here for easy reference.

\begin{code}

module hide-refl where
 data _≡_ {A : Type 𝓤} : A → A → Type 𝓤 where refl : {x : A} → x ≡ x
open import Agda.Builtin.Equality renaming (_≡_ to infix 0 _≡_) public

\end{code}

Whenever we need to complete a proof by simply asserting that `x` is definitionally equal to itself, we invoke `refl`.  If we need to make explicit the implicit argument `x`, then we use `refl {x = x}`.



#### <a id="identity-is-an-equivalence-relation">Identity is an equivalence relation</a>

The `≡` type just defined is an equivalence relation and the formal proof of this fact is trivial. We don't need to prove reflexivity since it is the defining property of `≡`.  Here are the (trivial) proofs of symmetry and transitivity of `≡`.

\begin{code}
module hide-sym-trans {A : Type 𝓤} where
 sym : {x y : A} → x ≡ y → y ≡ x
 sym refl = refl

 trans : {A : Type 𝓤}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
 trans refl refl = refl

open import Relation.Binary.PropositionalEquality.Core using (sym; trans) public

\end{code}

We prove that `≡` obeys the substitution rule (subst) in the next subsection (see the definition of `ap` below), but first we define some syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.<sup>[3](Overture.Equality.html#fn3)</sup>

\begin{code}

_⁻¹ : {A : Type 𝓤} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infix  40 _⁻¹

\end{code}

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `≡-sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

\begin{code}

_∙_ : {A : Type 𝓤}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

_≡⟨_⟩_ : {A : Type 𝓤} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : Type 𝓤} (x : X) → x ≡ x
x ∎ = refl

infixl 30 _∙_
infixr  0 _≡⟨_⟩_
infix   1 _∎

\end{code}

#### <a id="transport">Transport (substitution)</a>

Alonzo Church characterized equality by declaring two things equal iff no property (predicate) can distinguish them.<sup>[4](Overture.Equality.html#fn4)</sup>  In other terms, `x` and `y` are equal iff for all `P` we have `P x → P y`.  One direction of this implication is sometimes called *substitution* (`subst`) or *transport along an identity*.  It asserts that if two objects are equal and one of them satisfies a predicate, then so does the other. A type representing this notion is defined in the `Relation.Binary.PropositionalEquality.Core` module of the [Agda Standard Library][] library as follows.

\begin{code}

module hide-transport where
 subst : {A : Type 𝓤}(B : A → Type 𝓦){x y : A} → x ≡ y → B x → B y
 subst B {x} refl = λ x → x

\end{code}

A function is well defined if and only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  The `cong` map, defined in the  Relation.Binary.PropositionalEquality.Core module of the [Agda Standard Library][], captures this well-definedness property as follows.

\begin{code}

module hide-cong {A : Type 𝓤}{B : Type 𝓦} where
 cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
 cong f refl = refl

\end{code}

Thus, if we have a function `f : X → Y`, two elements `a b : X` of the domain, and an identity proof `p : a ≡ b`, then we obtain a proof of `f a ≡ f b` by simply applying the `cong` function like so, `cong f p : f a ≡ f b`.

Similarly, if we have two equivalent dependent functions---say, `f g : (x : A) → B x` such that `f ≡ g`---then `f x ≡ g x` holds for all `x : A`.  This property is captured by the `cong-app` function defined in the `Relation.Binary.PropositionalEquality.Core` module of the [Agda Standard Library][] as follows.

module hide-cong-app {A : Type 𝓤}{B : A → Type 𝓦}  where
 cong-app : {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
 cong-app refl x = refl

\end{code}

As usual, we display definitions of existing types (here `subst`, `cong`, and `cong-app`) in a hidden module and then imported their original definition from the [Agda Standard Library][], like so.

\begin{code}

open import Relation.Binary.PropositionalEquality.Core using (subst; cong; cong-app) public

\end{code}




-------------------------------------


<sup>1</sup><span class="footnote" id="fn1"> Per Martin-Löf, *An intuitionistic theory of types: predicative part*, Logic Colloquium '73 (Bristol, 1973), 73--118, Studies in Logic and the Foundations of Mathematics, Vol. 80, 1975.</span>

<sup>2</sup><span class="footnote" id="fn2"> The *definiendum* is the left-hand side of a defining equation, the *definiens* is the right-hand side. For readers who have never generated an equivalence relation: the *reflexive closure* of `R ⊆ A × A `is the union of `R` and all pairs of the form `(a , a)`; the *symmetric closure* is the union of `R` and its inverse `{(y , x) : (x , y) ∈ R}`; we leave it to the reader to come up with the correct definition of transitive closure.</span>

<sup>3</sup><span class="footnote" id="fn3"> **Unicode Hints** ([agda2-mode][]). `\^-\^1 ↝ ⁻¹`; `\Mii\Mid ↝ 𝑖𝑑`; `\. ↝ ∙`. In general, for information about a character, place the cursor over that character and type `M-x describe-char` (or `M-x h d c`).</span>



<sup>4</sup><span class="footnote" id="fn4"> Alonzo Church, "A Formulation of the Simple Theory of Types," *Journal of Symbolic Logic*, (2)5:56--68, 1940 [JSOR link](http://www.jstor.org/stable/2266170). See also [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#70309) of Escardó's [HoTT/UF in Agda notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) for a discussion of transport; cf. [HoTT-Agda's definition](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda).</span>

<br>
<br>

[← Overture.Preliminaries ](Overture.Preliminaries.html)
<span style="float:right;">[Overture.FunExtensionality →](Overture.FunExtensionality.html)</span>

{% include UALib.Links.md %}


<!-- NO LONGER USED STUFF

𝑖𝑑 : (A : Type 𝓤 ) → A → A
𝑖𝑑 A = λ x → x

-->

