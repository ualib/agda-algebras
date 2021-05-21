---
layout: default
title : Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation</a>

This section presents the [Relations.Truncation][] module of the [Agda Universal Algebra Library][].

We start with a brief discussion of standard notions of *truncation*, *h-sets* (which we just call *sets*), and the *uniqueness of identity types* principle.
We then prove that a monic function into a *set* is an embedding. The section concludes with a *uniqueness of identity proofs* principle for blocks of equivalence relations.

Readers who want to learn more about "proof-relevant mathematics" and other concepts mentioned in this module may wish to consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
open import Data.Product using (_,_; Σ; _×_; Σ-syntax)
open import Function.Base using (_∘_; id)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (trans; subst; cong-app;
  module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Unary using (Pred; _⊆_)

-- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries using (Type; 𝓤; 𝓥; 𝓦; fst; ∣_∣; ∥_∥; _⁻¹; _∼_)
open import Overture.Inverses using (IsInjective)
open import Relations.Continuous using (ContRel; DepRel)
open import Relations.Quotients using (IsBlock)



module Relations.Truncation where


\end{code}

The MGS-Quotient module of the [Type Topology][] library defines the following *uniqueness-of-proofs* principle for binary relations.

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if it has *at most* one inhabitant.  Representing these concepts are the following types (whose original definitions we import from the `MGS-Basic-UF` module of [Type Topology][]).

\begin{code}

is-center : (A : Type 𝓤 ) → A → Type 𝓤
is-center A c = (x : A) → c ≡ x

is-singleton : Type 𝓤 → Type 𝓤
is-singleton A = Σ A (is-center A)

is-prop : Type 𝓤 → Type 𝓤
is-prop A = (x y : A) → x ≡ y

is-prop-valued : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
is-prop-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

singleton-is-prop : {𝓤 : Level}(X : Type 𝓤) → is-singleton X → is-prop X
singleton-is-prop X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎

\end{code}


Next, we consider the type `is-equiv` which is used to assert that a function is an equivalence in a sense that we now describe. First we need the concept of a [fiber](https://ncatlab.org/nlab/show/fiber) of a function. In the [Type Topology][] library, `fiber` is defined as a Sigma type whose inhabitants represent inverse images of points in the codomain of the given function.

\begin{code}

fiber : {A : Type 𝓤 } {B : Type 𝓦 } (f : A → B) → B → Type (𝓤 ⊔ 𝓦)
fiber {𝓤}{𝓦}{A} f y = Σ[ x ∈ A ] f x ≡ y

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

Thus, if `R : Rel A 𝓦`, then `is-subsingleton-valued R` is the assertion that for each pair `x y : A` there can be at most one proof that `R x y` holds.

In this module ([Relations.Truncation][]) we introduce a number of similar but more general types used in the [UniversalAlgebra][] library to represent *uniqueness-of-proofs principles* for relations of arbitrary arity over arbitrary types.

#### <a id="uniqueness-of-identity-proofs">Uniqueness of identity proofs</a>

This brief introduction is intended for novices; those already familiar with the concept of *truncation* and *uniqueness of identity proofs* may want to skip to the next subsection.

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `A` and an identity relation `_≡₀_` on `A` so that, given two inhabitants of `A`, say, `a b : A`, we can form the type `a ≡₀ b`. Suppose `p` and `q` inhabit the type `a ≡₀ b`; that is, `p` and `q` are proofs of `a ≡₀ b`, in which case we write `p q : a ≡₀ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent.

We are asking about an identity type on the identity type `≡₀`, and whether there is some inhabitant, say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡₀ b` are the same. If such a proof exists for all `p q : a ≡₀ b`, then the proof of `a ≡₀ b` is unique; as a property of the types `A` and `≡₀`, this is sometimes called <a id="uniqueness-of-identity-proofs">*uniqueness of identity proofs*</a> (uip).

Now, perhaps we have two proofs, say, `r s : p ≡₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).



#### <a id="sets">Sets</a>

In [homotopy type theory](https://homotopytypetheory.org), a type `A` with an identity relation `≡₀` is called a *set* (or *0-groupoid*) if for every pair `x y : A` there is at most one proof of `x ≡₀ y`. In other words, the type `A`, along with it's equality type `≡₀`, form a *set* if for all `x y : A` there is at most one proof of `x ≡₀ y`.

This notion is formalized in the [Type Topology][] library, using the `is-subsingleton` type that we saw earlier ([Overture.Inverses][]), as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

\begin{code}

is-set : Type 𝓤 → Type 𝓤
is-set A = is-prop-valued{A = A} _≡_
-- (x y : A) → is-prop (x ≡ y)

-- is-prop-valued : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
-- is-prop-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

-- open import MGS-Embeddings using (is-set) public

\end{code}

Thus, the pair `(A , ≡₀)` forms a set if and only if it satisfies `∀ x y : A → is-subsingleton (x ≡₀ y)`.

We will also need the function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which is part of Escardó's characterization of *equality in Sigma types*.<sup>[2](Relations.Truncation.html#fn2)</sup> It is defined as follows.

\begin{code}

module _ {A : Type 𝓤}{B : A → Type 𝓦} where

 to-Σ-≡ : {σ τ : Σ A B} → (Σ[ p ∈ (fst σ ≡ fst τ) ] subst B p ∥ σ ∥ ≡ ∥ τ ∥) → σ ≡ τ
 to-Σ-≡ (refl , refl) = refl


\end{code}


#### <a id="embeddings">Embeddings</a>


The `is-embedding` type is defined in the `MGS-Embeddings` module of the [Type Topology][] library in the following way.

\begin{code}

is-embedding : {A : Type 𝓤}{B : Type 𝓦} → (A → B) → Type (𝓤 ⊔ 𝓦)
is-embedding f = ∀ b → is-prop (fiber f b)

singleton-type : {A : Type 𝓤} → A → Type 𝓤
singleton-type {𝓤}{A} x = Σ[ y ∈ A ] y ≡ x

\end{code}

Thus, `is-embedding f` asserts that `f` is a function all of whose fibers are subsingletons. Observe that an embedding is not simply an injective map. However, if we assume that the codomain `B` has *unique identity proofs* (UIP), then we can prove that a monic function into `B` is an embedding.  We will do exactly that in the [Relations.Truncation][] module when we take up the topic of *sets* and the UIP.

Finding a proof that a function is an embedding isn't always easy, but one approach that is often fairly straightforward is to first prove that the function is invertible and then invoke the `invertible-is-embedding` theorem from the [Type Topology][] library.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where
 invertible : (A → B) → Type (𝓤 ⊔ 𝓦)
 invertible f = Σ[ g ∈ (B → A) ] ((g ∘ f ∼ id) × (f ∘ g ∼ id))

 equiv-is-embedding : (f : A → B) → is-equiv f → is-embedding f
 equiv-is-embedding f i y = singleton-is-prop (fiber f y) (i y)

-- open import MGS-Retracts using (_◁⟨_⟩_; _◀; Σ-retract; retract-of-singleton; singleton-type-center; singleton-type-centered)

 -- invertible-is-equiv : (f : A → B) → invertible f → is-equiv f
 -- invertible-is-equiv f (g , η , ε) b₀ = γ
 --  where
 --  s : (b : B) → f (g b) ≡ b₀ → b ≡ b₀
 --  s b = subst (_≡ b₀) (ε b)
 --  r : (b : B) → b ≡ b₀ → f (g b) ≡ b₀
 --  r b = subst (_≡ b₀) ((ε b)⁻¹)

 --  β : (b : B) → (f (g b) ≡ b₀) ◁ (b ≡ b₀)
 --  β b = (r b) , (s b) , subst-is-section (_≡ b₀) (ε b)

  -- α : fiber f b₀ ◁ singleton-type b₀
  -- α = (λ _ → g b₀ , ε b₀) , ((λ _ → b₀ , refl) , (λ x → {!!}))
  -- (Σ a ꞉ A , (f a ≡ b₀))     ◁⟨ Σ-reindexing-retract g (f , η) ⟩
  --      (Σ b ꞉ B , f (g b) ≡ b₀) ◁⟨ Σ-retract  β                   ⟩
  --      (Σ b ꞉ B , b ≡ b₀)       ◀

  -- γ : is-singleton (fiber f b₀)
  -- γ = (g b₀ , ε b₀) , {!!}

  -- γ : is-singleton (fiber f b₀)
  -- γ = (g b₀ , ε b₀) , {!!}

 -- invertible-is-embedding : (f : A → B) → invertible f → is-embedding f
 -- invertible-is-embedding f fi = equiv-is-embedding f (invertible-is-equiv f fi)

\end{code}






We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Overture.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Overture.Inverses.html#embeddings) section of the [Overture.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.

\begin{code}

private variable A : Type 𝓤 ; B : Type 𝓦

monic-is-embedding|Set : (f : A → B) → is-set B → IsInjective f → is-embedding f
monic-is-embedding|Set f Bset fmon b (u , fu≡b) (v , fv≡b) = γ
 where
 fuv : f u ≡ f v
 fuv = trans fu≡b (fv≡b ⁻¹)

 uv : u ≡ v
 uv = fmon fuv

 arg1 : Σ[ p ∈ u ≡ v ] subst (λ a → f a ≡ b) p fu≡b ≡ fv≡b
 arg1 = uv , Bset (f v) b (subst (λ a → f a ≡ b) uv fu≡b) fv≡b

 γ : (u , fu≡b) ≡ (v , fv≡b)
 γ = to-Σ-≡ arg1

\end{code}

In stating the previous result, we introduce a new convention to which we will try to adhere. If the antecedent of a theorem includes the assumption that one of the types involved is a *set* (in the sense defined above), then we add to the name of the theorem the suffix `|Set`, which calls to mind the standard mathematical notation for the restriction of a function.


#### <a id="equivalence-class-truncation">Equivalence class truncation</a>

Recall, `IsBlock` was defined in the [Relations.Quotients][] module as follows:

```
 IsBlock : {A : Type 𝓤}(C : Pred A 𝓦){R : Rel A 𝓦} → Type(𝓤 ⊔ lsuc 𝓦)
 IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}
```

In the next module ([Relations.Extensionality][]) we will define a *quotient extensionality* principle that will require a form of unique identity proofs---specifically, we will assume that for each predicate `C : Pred A 𝓦` there is at most one proof of `IsBlock C`. We call this proof-irrelevance principle "uniqueness of block identity proofs", and define it as follows.

\begin{code}

blk-uip : (A : Type 𝓤)(R : Rel A 𝓦 ) → Type(𝓤 ⊔ lsuc 𝓦)
blk-uip {𝓤}{𝓦} A R = ∀ (C : Pred A 𝓦) → is-prop (IsBlock C {R})

\end{code}

It might seem unreasonable to postulate that there is at most one inhabitant of `IsBlock C`, since equivalence classes typically have multiple members, any one of which could serve as a class representative.  However, postulating `blk-uip A R` is tantamount to collapsing each `R`-block to a single point, and this is indeed the correct semantic interpretation of the elements of the quotient `A / R`.

----------------------------

#### <a id="general-propositions">General propositions*</a>

This section defines more general truncated predicates which we call *continuous propositions* and *dependent propositions*. Recall, above (in the [Relations.Continuous][] module) we defined types called `ContRel` and `DepRel` to represent relations of arbitrary arity over arbitrary collections of sorts.

Naturally, we define the corresponding *truncated continuous relation type* and *truncated dependent relation type*, the inhabitants of which we will call *continuous propositions* and *dependent propositions*, respectively.

\begin{code}

module _ {I : Type 𝓥} where

 IsContProp : (A : Type 𝓤) → ContRel I A 𝓦  → Type(𝓥 ⊔ 𝓤 ⊔ 𝓦)
 IsContProp A P = ∀ (𝑎 : (I → A)) → is-prop (P 𝑎)

 ContProp : Type 𝓤 → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
 ContProp A 𝓦 = Σ[ P ∈ ContRel I A 𝓦 ] IsContProp A P

 cont-prop-ext : Type 𝓤 → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
 cont-prop-ext A 𝓦 = {P Q : ContProp A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

 IsDepProp : (𝒜 : I → Type 𝓤) → DepRel I 𝒜 𝓦  → Type(𝓥 ⊔ 𝓤 ⊔ 𝓦)
 IsDepProp 𝒜 P = ∀ (𝑎 : ((i : I) → 𝒜 i)) → is-prop (P 𝑎)

 DepProp : (I → Type 𝓤) → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
 DepProp 𝒜 𝓦 = Σ[ P ∈ DepRel I 𝒜 𝓦 ] IsDepProp 𝒜 P

 dep-prop-ext : (I → Type 𝓤) → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
 dep-prop-ext 𝒜 𝓦 = {P Q : DepProp 𝒜 𝓦} → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}








----------------------------


<sup>*</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general than some of the types defined in other sections. As yet these general types are not used elsewhere in the [UniversalAlgebra][] library, so sections marked * may be safely skimmed or skipped.</span>


<sup>1</sup><span class="footnote" id="fn1"> As [Escardó][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

<sup>2</sup><span class="footnote" id="fn2"> See [https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#sigmaequality](www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#sigmaequality).</span>

<sup>3</sup><span class="footnote" id="fn3"> This is another example of proof-irrelevance. Indeed, if `R` is a binary proposition and we have two proofs of `R x y`, then the proofs are indistinguishable.
</span>

<br>
<br>

[← Relations.Quotients](Relations.Quotients.html)
<span style="float:right;">[Relations.Extensionality →](Relations.Extensionality.html)</span>


{% include UALib.Links.md %}
