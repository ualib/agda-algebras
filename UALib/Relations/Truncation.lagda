---
layout: default
title : UALib.Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation, Sets, Propositions</a>

This section presents the [UALib.Relations.Truncation][] module of the [Agda Universal Algebra Library][].

Here we discuss **truncation** and **h-sets** (which we just call **sets**).  We first give a brief discussion of standard notions of trunction, and then we describe a viewpoint which seems useful for formalizing mathematics in Agda. Readers wishing to learn more about truncation and proof-relevant mathematics should consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

**Remark**. [Agda][] now has a built in type called [Prop](ttps://agda.readthedocs.io/en/v2.6.1.3/language/prop.html) which may provide some or all of what we develop in this module. However, we have never tried to use it, and it seems we can do without it.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Truncation where

open import Relations.Quotients public

\end{code}

#### <a id="typical-view-of-truncation">Truncation</a>

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given
proposition. For instance, suppose we have a type `X` and an identity relation `_≡ₓ_` on `X` so that,
given two inhabitants of `X`, say, `a b : X`, we can form the type `a ≡ₓ b`. Suppose `p` and `q`
inhabit the type `a ≡ₓ b`; that is, `p` and `q` are proofs of `a ≡ₓ b`, in which case we write
`p q : a ≡ₓ b`. We might then wonder whether and in what sense are the two proofs `p` and `q`
the equivalent.

We are asking about an identity type on the identity type `≡ₓ`, and whether there is some inhabitant,
say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡ₓ b` are the same.
If such a proof exists for all `p q : a ≡ₓ b, then the proof of `a ≡ₓ b` is unique; as a property of
the types `X` and `≡ₓ`, this is sometimes called **uniqueness of identity proofs**.

Now, perhaps we have two proofs, say, `r s : p ≡ₓ₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡ₓ₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₓₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

In [homotopy type theory](https://homotopytypetheory.org), a type `X` with an identity relation `≡ₓ` is called a **set** (or **0-groupoid**) if for every pair `x y : X` there is at most one proof of `x ≡ₓ y`. In other words, the type `X`, along with it's equality type `≡ₓ`, form a *set* if for all `x y : X` there is at most one proof of `x ≡ₓ y`.

This notion is formalized in the [Type Topology][] library using the types `is-set` which is defined using the `is-subsingleton` type that we saw earlier ([Prelude.Inverses][]) as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

\begin{code}

module hide-is-set {𝓤 : Universe} where

 is-set : 𝓤 ̇ → 𝓤 ̇
 is-set X = (x y : X) → is-subsingleton (x ≡ y)

\end{code}

Thus, the pair `(X , ≡ₓ)` forms a set if and only if it satisfies `∀ x y : X → is-subsingleton (x ≡ₓ y)`.

Let's import the original definition of `is-set` from the [Type Topology][] library and make it public so it's available throughout the remainder of the [UALib][].

\begin{code}

open import MGS-Embeddings using (is-set) public

\end{code}


#### <a id="propositions">Propositions</a>

Sometimes we will want to assume that a type `X` is a *set*. As we just learned, this means there is at most one proof that two inhabitants of `X` are the same.  Analogously, for predicates on `X`, we may wish to assume that there is at most one proof that an inhabitant of `X` satisfies the given predicate.  If a unary predicate satisfies this condition, then we call it a (unary) **proposition**.  We now define a type that captures this concept.

\begin{code}

module _ {𝓤 : Universe} where

 Pred₁ : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Pred₁ A 𝓦 = Σ P ꞉ (Pred A 𝓦) , ∀ x → is-subsingleton (P x)

\end{code}

Recall that `Pred A 𝓦` is simply the function type `A → 𝓦 ̇`, so `Pred₁` is by definition equal to

`Σ P ꞉ (A → 𝓦 ̇) , ∀ x → is-subsingleton (P x)`.

The principle of **proposition extensionality** asserts that logically equivalent propositions are equivalent.  That is, if we have `P Q : Pred₁` and `∣ P ∣ ⊆ ∣ Q ∣` and `∣ Q ∣ ⊆ ∣ P ∣`, then `P ≡ Q`.  This is formalized as follows (cf. Escardó's discussion of [Propositional extensionality and the powerset](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#250227)).

\begin{code}

 prop-ext : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 prop-ext A 𝓦 = {P Q : Pred₁ A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

Recall, we defined the relation `_≐_` for predicates as follows: `P ≐ Q = (P ⊆ Q) × (Q ⊆ P)`.  Therefore, if we assume `PropExt A 𝓦 {P}{Q}` holds, then it follows that `P ≡ Q`.

\begin{code}

 prop-ext' : (A : 𝓤 ̇)(𝓦 : Universe){P Q : Pred₁ A 𝓦}
  →         prop-ext A 𝓦
            -------------------
  →         ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

 prop-ext' A 𝓦 pe hyp = pe (fst hyp) (snd hyp) 

\end{code}

Thus, for truncated predicates `P` and `Q`, if `PropExt` holds, then `P ⊆ Q × Q ⊆ P → P ≡ Q`, which is a useful extensionality principle.


#### <a id="binary-propositions">Binary propositions</a>

Given a binary relation `R`, it may be necessary or desirable to assume that there is at most one way to prove that a given pair of elements is `R`-related.  If this is true of `R`, then we call `R` a **binary proposition**.<sup>[2](Relations.Truncation.html#fn2)</sup>

As above, we use the `is-subsingleton` type of the [Type Topology][] library to impose this truncation assumption on a binary relation.

\begin{code}

 Pred₂ : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Pred₂ A 𝓦 = Σ R ꞉ (Rel A 𝓦) , ∀ x y → is-subsingleton (R x y)

\end{code}

To be clear, the type `Rel A 𝓦` is simply the function type `A → A → 𝓦 ̇`, so

`Pred₂ A 𝓦 = Σ R ꞉ (A → A → 𝓦 ̇) , ∀ x y → is-subsingleton (R x y)`.



#### <a id="quotient-extensionality">Quotient extensionality</a>

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  Proposition extensionality is precisely what we need to accomplish this.

\begin{code}

module _ {𝓤 𝓡 : Universe} {A : 𝓤 ̇}{𝑹 : Pred₂ A 𝓡} where

 class-extensionality : prop-ext A 𝓡 → dfunext 𝓤 (𝓡 ⁺) → {a a' : A}
  →                     IsEquivalence ∣ 𝑹 ∣
                        -------------------------------
  →                     ∣ 𝑹 ∣ a a'  →  [ a ] ∣ 𝑹 ∣  ≡  [ a' ] ∣ 𝑹 ∣

 class-extensionality pe dfe {a}{a'} Req Raa' = γ
  where
   P Q : Pred₁ A 𝓡
   P = (λ x → ∣ 𝑹 ∣ a x) , (λ x → ∥ 𝑹 ∥ a x)
   Q = (λ x → ∣ 𝑹 ∣ a' x) , (λ x → ∥ 𝑹 ∥ a' x)

   α : [ a ] ∣ 𝑹 ∣ ⊆ [ a' ] ∣ 𝑹 ∣
   α ax = fst (/-=̇ Req Raa') ax

   β : [ a' ] ∣ 𝑹 ∣ ⊆ [ a ] ∣ 𝑹 ∣
   β a'x = snd (/-=̇ Req Raa') a'x

   γ : [ a ] ∣ 𝑹 ∣ ≡ [ a' ] ∣ 𝑹 ∣
   γ = ap fst (prop-ext' A 𝓡 {P}{Q} pe (α , β))

 to-subtype-⟦⟧ : {C D : Pred A 𝓡}{c : 𝒞 C}{d : 𝒞 D} 
  →              (∀ C → is-subsingleton (𝒞{R = ∣ 𝑹 ∣} C))
                 -------------------------------------
  →              C ≡ D  →  (C , c) ≡ (D , d)

 to-subtype-⟦⟧ {D = D}{c}{d} ssA CD = to-Σ-≡ (CD , ssA D (transport 𝒞 CD c) d)


 class-extensionality' : prop-ext A 𝓡 → dfunext 𝓤 (𝓡 ⁺) → {a a' : A}
  →                      (∀ C → is-subsingleton (𝒞 C))
  →                      IsEquivalence ∣ 𝑹 ∣
                         -------------------------
  →                      ∣ 𝑹 ∣ a a'  →  ⟦ a ⟧ ≡ ⟦ a' ⟧

 class-extensionality' pe fe {a}{a'} ssA Req Raa' = γ
  where
   CD : [ a ] ∣ 𝑹 ∣ ≡ [ a' ] ∣ 𝑹 ∣
   CD = class-extensionality pe fe Req Raa'

   γ : ⟦ a ⟧ ≡ ⟦ a' ⟧
   γ = to-subtype-⟦⟧ ssA CD

\end{code}



#### <a id="general-and-dependent-propositions">General and dependent propositions</a>


We defined a type called `GenRel` in the [Relations.Binary][] module to represent relations of arbitrary arity. So, naturally, we define a type of *truncated general relations*, the inhabitants of which we will call **general propositions**.

\begin{code}

GenProp : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
GenProp I A 𝓦 = Σ P ꞉ (GenRel I A 𝓦) , ∀ 𝑎 → is-subsingleton (P 𝑎)

gen-prop-ext : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
gen-prop-ext I A 𝓦 = {P Q : GenProp I A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

If we assume `gen-prop-ext  I A 𝓦` holds for some `I`, `A` and `𝓦`, then we can prove that logically equivalent general propositions of type `GenProp I A 𝓦` are equivalent.

\begin{code}

gen-prop-ext' : (I : 𝓥 ̇)(A : 𝓤 ̇)(𝓦 : Universe){P Q : GenProp I A 𝓦}
 →              gen-prop-ext I A 𝓦
                -------------------
 →              ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

gen-prop-ext' I A 𝓦 pe hyp = pe (fst hyp) (snd hyp) 

\end{code}

While we're at it, we might as well take the abstraction one step further and define *truncated dependent relations*, which we'll call **dependent propositions**.

\begin{code}

DepProp : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
DepProp I A 𝓦 = Σ P ꞉ (DepRel I A 𝓦) , ∀ 𝑎 → is-subsingleton (P 𝑎)

dep-prop-ext : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
dep-prop-ext I A 𝓦 = {P Q : DepProp I A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

Applying the extensionality principle for dependent relations is no harder than applying the special cases of this principle defined earlier.

\begin{code}

dep-prop-ext' : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe){P Q : DepProp I A 𝓦}
 →              dep-prop-ext I A 𝓦
                -------------------
 →              ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

dep-prop-ext' I A 𝓦 pe hyp = pe (fst hyp) (snd hyp) 

\end{code}



-----------------------------------

<span class="footnote" id="fn1"><sup>1</sup> As [Escardó][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>


<span class="footnote" id="fn2"><sup>2</sup> This is another example of proof-irrelevance since, if `R` is a binary proposition and we have two proofs of `R x y`, then we can assume that the proofs are indistinguishable or that any distinctions are irrelevant.</span>


----------------------------------------

[← Relations.Quotients](Relations.Quotients.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}
