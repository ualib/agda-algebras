---
layout: default
title : Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="basic-definitions">Basic Definitions</a>

This section presents the [Terms.Basic][] module of the [Agda Universal Algebra Library][].

The theoretical background that begins each subsection below is based on Cliff Bergman's textbook [Bergman (2012)][], specifically, Section 4.3.  Apart from notation, our presentation is similar to Bergman's, but we will be more concise, omitting some details and all examples, in order to more quickly arrive at our objective, which is to use type theory to express the concepts and formalize them in the [Agda][] language.  We refer the reader to [Bergman (2012)][] for a more complete exposition of classical (informal) universal algebra.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product using (_,_; Σ; _×_)
open import Function.Base  using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (cong; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Unary using (Pred)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Preliminaries
 using (Type; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; Π; -Π; -Σ; _⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
open import Overture.Inverses using (IsSurjective; Image_∋_; Inv; InvIsInv; eq)


module Terms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Products{𝑆 = 𝑆} using (ov)
open import Homomorphisms.Basic {𝑆 = 𝑆} using (hom) -- ; 𝓁𝒾𝒻𝓉; 𝓁ℴ𝓌ℯ𝓇)

\end{code}

#### <a id="the-type-of-terms">The type of terms</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `𝑓 𝑡` such that `𝑓 : ∣ 𝑆 ∣` and `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ 𝑓` is the arity of the operation symbol 𝑓.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

\begin{code}

data Term (X : Type 𝓧 ) : Type(ov 𝓧)  where
 ℊ : X → Term X    -- (ℊ for "generator")
 node : (f : ∣ 𝑆 ∣)(𝑡 : ∥ 𝑆 ∥ f → Term X) → Term X

open Term public

\end{code}

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`).


**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov 𝓧` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc 𝓧`.


#### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `𝑓 : ∣ 𝑆 ∣`, denote by `𝑓 ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `𝑡 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑻 X ∣` to the formal term `𝑓 𝑡`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `𝑓 ̂ (𝑻 X)`, one for each symbol `𝑓` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one could hope.

\begin{code}

𝑻 : (X : Type 𝓧 ) → Algebra (ov 𝓧) 𝑆
𝑻 X = Term X , node

\end{code}



#### <a id="the-universal-property">The universal property</a>

The term algebra `𝑻 X` is *absolutely free* (or *universal*, or *initial*) for algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1. Every function from `𝑋` to `∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2. The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to `∣ 𝑨 ∣` lifts to a map from `∣ 𝑻 X ∣` to `∣ 𝑨 ∣` in a natural way, by induction on the structure of the given term.

\begin{code}

private variable X : Type 𝓧

free-lift : (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣) → ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
free-lift _ h (ℊ x) = h x
free-lift 𝑨 h (node f 𝑡) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h (𝑡 i))

\end{code}

Naturally, at the base step of the induction, when the term has the form `generator`
x, the free lift of `h` agrees with `h`.  For the inductive step, when the
given term has the form `node f 𝑡`, the free lift is defined as
follows: Assuming (the induction hypothesis) that we know the image of each
subterm `𝑡 i` under the free lift of `h`, define the free lift at the
full term by applying `f ̂ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

lift-hom : (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → cong (f ̂ 𝑨) refl

\end{code}

Finally, we prove that the homomorphism is unique.  This requires `funext 𝓥 𝓤` (i.e., *function extensionality* at universe levels `𝓥` and `𝓤`) which we postulate by making it part of the premise in the following function type definition.

\begin{code}

free-unique : funext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 𝑆)(g h : hom (𝑻 X) 𝑨)
 →            (∀ x → ∣ g ∣ (ℊ x) ≡ ∣ h ∣ (ℊ x))
              ----------------------------------------
 →            ∀ (t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

free-unique _ _ _ _ p (ℊ x) = p x
free-unique fe 𝑨 g h p (node 𝑓 𝑡) = ∣ g ∣ (node 𝑓 𝑡)  ≡⟨ ∥ g ∥ 𝑓 𝑡 ⟩
                                   (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)  ≡⟨ α ⟩
                                   (𝑓 ̂ 𝑨)(∣ h ∣ ∘ 𝑡)  ≡⟨ (∥ h ∥ 𝑓 𝑡)⁻¹ ⟩
                                   ∣ h ∣ (node 𝑓 𝑡)   ∎
 where
 α : (𝑓 ̂ 𝑨) (∣ g ∣ ∘ 𝑡) ≡ (𝑓 ̂ 𝑨) (∣ h ∣ ∘ 𝑡)
 α = cong (𝑓 ̂ 𝑨) (fe λ i → free-unique fe 𝑨 g h p (𝑡 i))

\end{code}

Let's account for what we have proved thus far about the term algebra.  If we postulate a type `X : Type 𝓧` (representing an arbitrary collection of variable symbols) such that for each `𝑆`-algebra `𝑨` there is a map from `X` to the domain of `𝑨`, then it follows that for every `𝑆`-algebra `𝑨` there is a homomorphism from `𝑻 X` to `∣ 𝑨 ∣` that "agrees with the original map on `X`," by which we mean that for all `x : X` the lift evaluated at `ℊ x` is equal to the original function evaluated at `x`.

If we further assume that each of the mappings from `X` to `∣ 𝑨 ∣` is *surjective*, then the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we now prove.

\begin{code}

lift-of-epi-is-epi : (𝑨 : Algebra 𝓤 𝑆){h₀ : X → ∣ 𝑨 ∣}
 →                   IsSurjective h₀ → IsSurjective ∣ lift-hom 𝑨 h₀ ∣
lift-of-epi-is-epi 𝑨 {h₀} hE y = γ
 where
 h₀⁻¹y = Inv h₀ (hE y)

 η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (ℊ h₀⁻¹y)
 η = (InvIsInv h₀ (hE y))⁻¹

 γ : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
 γ = eq (ℊ h₀⁻¹y) η

\end{code}

The `lift-hom` and `lift-of-epi-is-epi` types will be called to action when such epimorphisms are needed later (e.g., in the [Varieties][] module).


--------------------------------------

<p></p>

[↑ Terms](Terms.html)
<span style="float:right;">[Terms.Operations →](Terms.Operations.html)</span>

{% include UALib.Links.md %}
