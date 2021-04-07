---
layout: default
title : Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation, Sets, Propositions</a>

This section presents the [Relations.Truncation][] module of the [Agda Universal Algebra Library][].

Here we discuss *truncation* and *h-sets* (which we just call *sets*).  We first give a brief discussion of standard notions of trunction, and then we describe a viewpoint which seems useful for formalizing mathematics in Agda. Readers wishing to learn more about truncation and proof-relevant mathematics should consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Truncation where

open import Relations.Quotients public

\end{code}

#### <a id="truncation">Truncation</a>

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `A` and an identity relation `_≡₀_` on `A` so that, given two inhabitants of `A`, say, `a b : A`, we can form the type `a ≡₀ b`. Suppose `p` and `q` inhabit the type `a ≡₀ b`; that is, `p` and `q` are proofs of `a ≡₀ b`, in which case we write `p q : a ≡₀ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent.

We are asking about an identity type on the identity type `≡₀`, and whether there is some inhabitant,
say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡₀ b` are the same.
If such a proof exists for all `p q : a ≡₀ b`, then the proof of `a ≡₀ b` is unique; as a property of
the types `A` and `≡₀`, this is sometimes called <a id="uniqueness-of-identity-proofs">*uniqueness of identity proofs*</a>.

Now, perhaps we have two proofs, say, `r s : p ≡₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

In [homotopy type theory](https://homotopytypetheory.org), a type `A` with an identity relation `≡₀` is called a *set* (or *0-groupoid*) if for every pair `x y : A` there is at most one proof of `x ≡₀ y`. In other words, the type `A`, along with it's equality type `≡₀`, form a *set* if for all `x y : A` there is at most one proof of `x ≡₀ y`.

This notion is formalized in the [Type Topology][] library using the types `is-set` which is defined using the `is-subsingleton` type that we saw earlier ([Overture.Inverses][]) as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

\begin{code}

module hide-is-set {𝓤 : Universe} where

 is-set : 𝓤 ̇ → 𝓤 ̇
 is-set A = (x y : A) → is-subsingleton (x ≡ y)

open import MGS-Embeddings using (is-set) public

\end{code}

Thus, the pair `(A , ≡₀)` forms a set if and only if it satisfies `∀ x y : A → is-subsingleton (x ≡₀ y)`.

We will also need the function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which is part of Escardó's characterization of *equality in Sigma types*.<sup>[2](Relations.Truncation.html#fn2)</sup> It is defined as follows.

\begin{code}

module hide-to-Σ-≡ {𝓤 𝓦 : Universe} where

 to-Σ-≡ : {A : 𝓤 ̇ } {B : A → 𝓦 ̇ } {σ τ : Σ B}
  →       Σ p ꞉ ∣ σ ∣ ≡ ∣ τ ∣ , (transport B p ∥ σ ∥) ≡ ∥ τ ∥
  →       σ ≡ τ

 to-Σ-≡ (refl {x = x} , refl {x = a}) = refl {x = (x , a)}

open import MGS-Embeddings using (to-Σ-≡) public

\end{code}

We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Overture.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Overture.Inverses.html#embeddings) section of the [Overture.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.  To prepare for this, we define a type `_⟺_` with which to represent such equivalences.

\begin{code}

_⟺_ : {𝓤 𝓦 : Universe} → 𝓤 ̇ → 𝓦 ̇ → 𝓤 ⊔ 𝓦 ̇
A ⟺ B = (A → B) × (B → A)

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 monic-is-embedding|sets : (f : A → B) → is-set B → Monic f → is-embedding f

 monic-is-embedding|sets f Bset fmon b (u , fu≡b) (v , fv≡b) = γ
  where
  fuv : f u ≡ f v
  fuv = ≡-trans fu≡b (fv≡b ⁻¹)

  uv : u ≡ v
  uv = fmon u v fuv

  arg1 : Σ p ꞉ (u ≡ v) , (transport (λ a → f a ≡ b) p fu≡b) ≡ fv≡b
  arg1 = uv , Bset (f v) b (transport (λ a → f a ≡ b) uv fu≡b) fv≡b

  γ : u , fu≡b ≡ v , fv≡b
  γ = to-Σ-≡ arg1

\end{code}

In stating the previous result, we introduce a new convention to which we will try to adhere. If the antecedent of a theorem includes the assumption that one of the types involved is a set, then we add to the name of the theorem the suffix `|sets`, which calls to mind the standard mathematical notation for the restriction of a function to a subset of its domain.

Embeddings are always monic, so we conclude that when a function's codomain is a set, then that function is an embedding if and only if it is monic.

\begin{code}

 embedding-iff-monic|sets : (f : A → B) → is-set B → is-embedding f ⟺ Monic f
 embedding-iff-monic|sets f Bset = (embedding-is-monic f), (monic-is-embedding|sets f Bset)

\end{code}


#### <a id="propositions">Propositions</a>

Sometimes we will want to assume that a type `A` is a *set*. As we just learned, this means there is at most one proof that two inhabitants of `A` are the same.  Analogously, for predicates on `A`, we may wish to assume that there is at most one proof that an inhabitant of `A` satisfies the given predicate.  If a unary predicate satisfies this condition, then we call it a (unary) *proposition*.  We now define a type that captures this concept.<sup>[3](Relations.Truncation.html#fn3)</sup>

\begin{code}

module _ {𝓤 : Universe} where

 Pred₁ : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Pred₁ A 𝓦 = Σ P ꞉ (Pred A 𝓦) , ∀ x → is-subsingleton (P x)

\end{code}

Recall that `Pred A 𝓦` is simply the function type `A → 𝓦 ̇` , so `Pred₁` is definitionally equal to `Σ P ꞉ (A → 𝓦 ̇) , ∀ x → is-subsingleton (P x)`.

The principle of *proposition extensionality* asserts that logically equivalent propositions are equivalent.  That is, if we have `P Q : Pred₁` and `∣ P ∣ ⊆ ∣ Q ∣` and `∣ Q ∣ ⊆ ∣ P ∣`, then `P ≡ Q`.  This is formalized as follows (cf. Escardó's discussion of [Propositional extensionality and the powerset](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#250227)).

\begin{code}

prop-ext : (𝓤 𝓦 : Universe) → (𝓤 ⊔ 𝓦) ⁺ ̇
prop-ext 𝓤 𝓦 = ∀ {A : 𝓤 ̇}{P Q : Pred₁ A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

Recall, we defined the relation `_≐_` for predicates as follows: `P ≐ Q = (P ⊆ Q) × (Q ⊆ P)`.  Therefore, if we postulate `prop-ext 𝓤 𝓦` and `P ≐ Q`, then `P ≡ Q` obviously follows. Nonetheless, let us record this observation.

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇} where

 prop-ext' : prop-ext 𝓤 𝓦 → {P Q : Pred₁ A 𝓦} → ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q
 prop-ext' pe hyp = pe (fst hyp) (snd hyp)

\end{code}

Thus, for truncated predicates `P` and `Q`, if `prop-ext` holds, then `(P ⊆ Q) × (Q ⊆ P) → P ≡ Q`, which is a useful extensionality principle.


The foregoing easily generalizes to binary relations.  If `R` is a binary relation such that there is at most one way to prove that a given pair of elements is `R`-related, then we call `R` a *binary proposition*. As above, we use [Type Topology][]'s `is-subsingleton-valued` type to impose this truncation assumption on a binary relation.<sup>[4](Relations.Truncation.html#fn4)</sup>

\begin{code}

Pred₂ : {𝓤 : Universe} → 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
Pred₂ A 𝓦 = Σ R ꞉ (Rel A 𝓦) , is-subsingleton-valued R

\end{code}

Recall, `is-subsingleton-valued` is simply defined as

`is-subsingleton-valued R = ∀ x y → is-subsingleton (R x y)

which is the assertion that for all `x` `y` there is at most one proof that `x` and `y` are `R`-related. We will generalize this from binary to arbitrary (i.e., continuous and dependent) relations below (see `IsContProp` and `IsDepProp`).

#### <a id="quotient-extensionality">Quotient extensionality</a>

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  Proposition extensionality is precisely what we need to accomplish this. We now define a type called `class-extensionality` that will play a crucial role later (e.g., in the formal proof of Birkhoff's HSP theorem).<sup>[5](Relations.Truncation.html#fn5)</sup>

\begin{code}

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{R : Rel A 𝓦} where
 open IsEqv

 class-extensionality : prop-ext 𝓤 𝓦 → IsEqv R → {u v : A}
  →                     R u v  →  [ u ] R ≡ [ v ] R

 class-extensionality pe Req {u}{v} Ruv = ap fst PQ
  where
  P Q : Pred₁ A 𝓦
  P = (λ a → R u a) , (λ a → is-truncated Req u a)
  Q = (λ a → R v a) , (λ a → is-truncated Req v a)

  α : [ u ] R ⊆ [ v ] R
  α ua = fst (/-≐ (is-equivalence Req) Ruv) ua

  β : [ v ] R ⊆ [ u ] R
  β va = snd (/-≐ (is-equivalence Req) Ruv) va

  PQ : P ≡ Q
  PQ = (prop-ext' pe (α , β))


 to-subtype-⟪⟫ : (∀ C → is-subsingleton (IsBlock R C))
  →              {C D : Pred A 𝓦}{c : IsBlock R C}{d : IsBlock R D}
  →              C ≡ D  →  (C , c) ≡ (D , d)

 to-subtype-⟪⟫ ssA {C}{D}{c}{d} CD = to-Σ-≡ (CD , ssA D (transport (IsBlock R) CD c) d)


 class-extensionality' : prop-ext 𝓤 𝓦 → (∀ C → is-subsingleton (IsBlock R C))
  →                      IsEqv R → {u v : A} → R u v  →  ⟪ u ⟫ ≡ ⟪ v ⟫

 class-extensionality' pe ssA Reqv Ruv = to-subtype-⟪⟫ ssA (class-extensionality pe Reqv Ruv)

\end{code}


----------------------------

#### <a id="general-propositions">General propositions*</a>

This section presents the `general-propositions` submodule of the [Relations.Truncation][] module.<sup>[*](Relations.Truncation.html#fn0)</sup>


Recall, we defined a type called `ContRel` in the [Relations.Continuous][] module to represent relations of arbitrary arity. Naturally, we define the corresponding truncated types, the inhabitants of which we will call *continuous propositions*.

\begin{code}

module general-propositions {𝓤 : Universe}{I : 𝓥 ̇} where

 open import Relations.Continuous using (ContRel; DepRel)

 IsContProp : {A : 𝓤 ̇}{𝓦 : Universe} → ContRel I A 𝓦  → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 IsContProp {A = A} P = Π 𝑎 ꞉ (I → A) , is-subsingleton (P 𝑎)

 ContProp : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 ContProp A 𝓦 = Σ P ꞉ (ContRel I A 𝓦) , IsContProp P

 cont-prop-ext : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 cont-prop-ext A 𝓦 = {P Q : ContProp A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

To see the point of this, suppose `cont-prop-ext A 𝓦` holds. Then we can prove that logically equivalent continuous propositions of type `ContProp A 𝓦` are equivalent. In other words, under the stated hypotheses, we obtain a useful extensionality lemma for continuous propositions.

\begin{code}

 cont-prop-ext' : {A : 𝓤 ̇}{𝓦 : Universe} → cont-prop-ext A 𝓦 → {P Q : ContProp A 𝓦} → ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q
 cont-prop-ext' pe hyp = pe  ∣ hyp ∣  ∥ hyp ∥

\end{code}

While we're at it, we might as well take the abstraction one step further and define the type of *truncated dependent relations*, which we call *dependent propositions*.

\begin{code}

 IsDepProp : {I : 𝓥 ̇}{𝒜 : I → 𝓤 ̇}{𝓦 : Universe} → DepRel I 𝒜 𝓦  → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 IsDepProp {I = I} {𝒜} P = Π 𝑎 ꞉ Π 𝒜 , is-subsingleton (P 𝑎)

 DepProp : (I → 𝓤 ̇) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 DepProp 𝒜 𝓦 = Σ P ꞉ (DepRel I 𝒜 𝓦) , IsDepProp P

 dep-prop-ext : (I → 𝓤 ̇) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 dep-prop-ext 𝒜 𝓦 = {P Q : DepProp 𝒜 𝓦} → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

Applying the extensionality principle for dependent continuous relations is no harder than applying the special cases of this principle defined earlier.

\begin{code}

 module _ (𝒜 : I → 𝓤 ̇)(𝓦 : Universe) where

  dep-prop-ext' : dep-prop-ext 𝒜 𝓦 → {P Q : DepProp 𝒜 𝓦} → ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q
  dep-prop-ext' pe hyp = pe  ∣ hyp ∣  ∥ hyp ∥

\end{code}



-----------------------------------

<sup>*</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections demand a higher degree of sophistication and/or effort from the user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<sup>1</sup><span class="footnote" id="fn1"> As [Escardó][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

<sup>2</sup><span class="footnote" id="fn2"> See [https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#sigmaequality](www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#sigmaequality).</span>

<sup>3</sup><span class="footnote" id="fn3"> [Agda][] now has a type called [Prop](https://agda.readthedocs.io/en/v2.6.1.3/language/prop.html), but we have never tried to use it. It likely provides at least some of the functionality we develop here, however, our preference is to assume only a minimal MLTT foundation and build up the types we need ourselves. For details about [Prop](https://agda.readthedocs.io/en/v2.6.1.3/language/prop.html), consult the official documentation at [agda.readthedocs.io/en/v2.6.1.3/language/prop.html](https://agda.readthedocs.io/en/v2.6.1.3/language/prop.html)</span>

<sup>4</sup><span class="footnote" id="fn4"> This is another example of proof-irrelevance. Indeed, if `R` is a binary proposition and we have two proofs of `R x y`, then we can assume that the proofs are indistinguishable or that any distinctions are irrelevant. Note also that we could have used the definition of `is-subsingleton-valued` from [the section on properties of binary relations](Relations.Truncation.html#properties-of-binary-relations) to define `Pred₂` by `Σ R ꞉ (Rel A 𝓦) , is-subsingleton-valued R`, but this seems less transparent than our explicit definition.
</span>


<sup>5</sup><span class="footnote" id="fn5"> Previous proofs of the `class-extensionality` theorems required *function extensionality*; however, as the proof given here makes clear, this is unnecessary.</span>

<br>
<br>

[← Relations.Quotients](Relations.Quotients.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}


