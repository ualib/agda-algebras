---
layout: default
title : Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="basic-definitions">Basic definitions</a>

This section presents the [Terms.Basic][] module of the [Agda Universal Algebra Library][].

The theoretical background that begins each subsection below is based on Cliff Bergman's textbook [Bergman (2012)][], specifically, Section 4.3.  Apart from notation, our presentation is similar to Bergman's, but we will be more concise, omitting some details and all examples, in order to more quickly arrive at our objective, which is to use type theory to express the concepts and formalize them in the [Agda][] language.  We refer the reader to [Bergman (2012)][] for a more complete exposition of classical (informal) universal algebra.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Terms.Basic {𝑆 : Signature 𝓞 𝓥} {gfe : global-dfunext} where

open import Homomorphisms.HomomorphicImages{𝑆 = 𝑆}{gfe} public

\end{code}

#### <a id="the-type-of-terms">The type of terms</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a **word** in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of **words** over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `𝑓 𝒕` such that `𝑓 : ∣ 𝑆 ∣` and `𝒕 : ∥ 𝑆 ∥ 𝑓 → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ 𝑓` is the arity of the operation symbol 𝑓.)

We define the collection of **terms** in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-**term** we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

\begin{code}

data Term {𝓧 : Universe}(X : 𝓧 ̇ ) : ov 𝓧 ̇  where
  generator : X → Term X
  node : (f : ∣ 𝑆 ∣)(𝒕 : ∥ 𝑆 ∥ f → Term X) → Term X

open Term

\end{code}

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Throughout this module the name of the first constructor of the `Term` type will remain `generator`. However, in all of the modules that follow this one, we will use the shorthand `ℊ` to denote the `generator` constructor.



#### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the **term algebra in the signature** `𝑆` **over** `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.

* For each operation symbol `𝑓 : ∣ 𝑆 ∣`, denote by `𝑓 ̂ (𝑻 X)` the operation on `Term X` which maps a tuple `𝑡 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑻 X ∣` to the formal term `𝑓 𝑡`.

* Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `𝑓 ̂ (𝑻 X)`, one for each symbol `𝑓` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one would hope.

\begin{code}

--The term algebra 𝑻 X.
𝑻 : {𝓧 : Universe}(X : 𝓧 ̇ ) → Algebra (ov 𝓧) 𝑆
𝑻 X = Term X , node

\end{code}



#### <a id="the-universal-property">The universal property</a>

The term algebra `𝑻 X` is *absolutely free*, or *universal*, for algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1.  Every map `h : 𝑋 → ∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2.  The induced homomorphism is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to `∣ 𝑨 ∣` lifts to a map from `∣ 𝑻 X ∣` to `∣ 𝑨 ∣` in a natural way, by induction on the structure of the term.

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇ } where

 free-lift : (𝑨 : Algebra 𝓤 𝑆)(h : X → ∣ 𝑨 ∣) → ∣ 𝑻 X ∣ → ∣ 𝑨 ∣

 free-lift _ h (generator x) = h x

 free-lift 𝑨 h (node f 𝒕) = (f ̂ 𝑨) λ i → free-lift 𝑨 h (𝒕 i)

\end{code}

Next, we verify that the lift so defined is a homomorphism.

\begin{code}

 lift-hom : (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨

 lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → ap (_ ̂ 𝑨) 𝓇ℯ𝒻𝓁

\end{code}

Finally, we prove that the resulting homomorphism is unique.

\begin{code}


 free-unique : funext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 𝑆)(g h : hom (𝑻 X) 𝑨)
  →            (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
               -------------------------------------------------
  →            ∀ (t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

 free-unique _ _ _ _ p (generator x) = p x

 free-unique fe 𝑨 g h p (node 𝑓 𝒕) = ∣ g ∣ (node 𝑓 𝒕)            ≡⟨ ∥ g ∥ 𝑓 𝒕 ⟩
                                    (𝑓 ̂ 𝑨)(λ i → ∣ g ∣ (𝒕 i))   ≡⟨ α ⟩
                                    (𝑓 ̂ 𝑨)(λ i → ∣ h ∣ (𝒕 i))   ≡⟨ (∥ h ∥ 𝑓 𝒕)⁻¹ ⟩
                                    ∣ h ∣ (node 𝑓 𝒕)            ∎
  where
  α : (𝑓 ̂ 𝑨) (∣ g ∣ ∘ 𝒕) ≡ (𝑓 ̂ 𝑨) (∣ h ∣ ∘ 𝒕)
  α = ap (𝑓 ̂ 𝑨) (fe λ i → free-unique fe 𝑨 g h p (𝒕 i))

\end{code}

Since it's absolutely free, the term algebra is the domain of a homomorphism to any algebra. Moreover, if we are given a surjective mapping `h` from `X` onto an algebra `𝑨`, then the homomorphism constructed with `lift-hom 𝑨 h` will be an epimorphism from `𝑻 X` onto `𝑨`.

\begin{code}

 lift-of-epi-is-epi : {𝑨 : Algebra 𝓤 𝑆}{h₀ : X → ∣ 𝑨 ∣}
                      ---------------------------------
  →                   Epic h₀ → Epic ∣ lift-hom 𝑨 h₀ ∣

 lift-of-epi-is-epi {𝑨}{h₀} hE y = γ
  where
  h₀⁻¹y = Inv h₀ (hE y)

  η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (generator h₀⁻¹y)
  η = (InvIsInv h₀ (hE y))⁻¹

  γ : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
  γ = eq y (generator h₀⁻¹y) η

\end{code}


In the modules [Birkhoff.FreeAlgebra][] and [Birkhoff.HSPTheorem][] `lift-hom` and `lift-of-epi-is-epi` are used to construct such epimorphisms.


--------------------------------------

<p></p>

[↑ Terms](Terms.html)
<span style="float:right;">[Terms.Operations →](Terms.Operations.html)</span>

{% include UALib.Links.md %}
