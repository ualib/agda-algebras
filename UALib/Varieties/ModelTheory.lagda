---
layout: default
title : UALib.Varieties.ModelTheory module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="types-for-theories-and-models">Types for Theories and Models</a>

This section presents the [UALib.Varieties.ModelTheory][] module of the [Agda Universal Algebra Library][].

In Section 4.4 of [Bergman (2012)][], having set the stage for the entrance of Equational Logic, Bergman proclaims,  ``Now, finally, we can formalize the idea we have been using since the first page of this text,'' and proceeds to define **identities of terms** as follows (paraphrasing for notational consistency):

<pre class="Agda">

Let <a class="Bound">𝑆</a> be a signature. An **identity** or **equation** in <a class="Bound">𝑆</a> is an ordered pair of terms, written <a class="Bound">𝑝</a> <a class="Function">≈</a> <a class="Bound">𝑞</a>, from the term algebra <a class="Function">𝑻</a> <a class="Bound">X</a>. If <a class="Bound">𝑨</a> is an <a class="Bound">𝑆</a>-algebra we say that <a class="Bound">𝑨 \textbf{satisfies} <a class="Bound">𝑝 <a class="Function">≈ <a class="Bound">𝑞 if <a class="Bound">𝑝</a> <a class="Function">̇</a> <a class="Bound">𝑨</a> <a class="Datatype">≡</a> <a class="Bound">𝑞</a> <a class="Function">̇</a> <a class="Bound">𝑨</a>. In this situation, we write <a class="Bound">𝑨</a> <a class="Function">⊧</a> <a class="Bound">𝑝</a> <a class="Function">≈</a> <a class="Bound">𝑞</a> and say that <a class="Bound">𝑨</a> **models** the identity <a class="Bound">𝑝</a> <a class="Function">≈</a> <a class="Bound">q</a>. If <a class="Bound">𝒦</a> is a class of algebras, all of the same signature, we write <a class="Bound">𝒦</a> <a class="Function">⊧</a> <a class="Bound">p</a> <a class="Function">≈</a> <a class="Bound">q</a> if, for every <a class="Bound">𝑨</a> <a class="Function">∈</a> <a class="Bound">𝒦</a>, <a class="Bound">𝑨</a> <a class="Function">⊧</a> <a class="Bound">𝑝</a><a class="Function">≈</a> <a class="Bound">𝑞</a>.

**Notation**. In the [Agda UALib][], because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations <a class="Function">⊧ and <a class="Function">≈. As a reasonable alternative to what we would normally express informally as 𝒦 <a class="Function">⊧ <a class="Bound">𝑝</a> <a class="Function">≈</a> <a class="Bound">𝑞</a>, we have settled on <a class="Bound">𝒦</a> <a class="Function">⊧</a> <a class="Bound">p</a> <a class="Function">≋</a> <a class="Bound">q</a> to denote this relation.  To reiterate, if <a class="Bound">𝒦</a> is a class of <a class="Bound">𝑆</a>-algebras, we write <a class="Bound">𝒦</a> <a class="Function">⊧</a> <a class="Bound">𝑝</a> <a class="Function">≋</a> <a class="Bound">𝑞</a> if every <a class="Bound">𝑨</a> <a class="Function">∈</a> <a class="Bound">𝒦</a> satisfies <a class="Bound">𝑨</a> <a class="Function">⊧</a> <a class="Bound">𝑝</a> <a class="Function">≈</a> <a class="Bound">𝑞</a>.

**Unicode Hints**. To produce the symbols <a class="Function">≈</a> and <a class="Function">⊧</a> in Emacs [agda2-mode][], type `\~~` and `\models (resp.). The symbol <a class="Function">≋</a> is produced in Emacs with `\~~~`.
</pre>

<!--

In his treatment of Birhoff's HSP theorem, Cliff Bergman (at the start of Section 4.4 of [Bergman (2012)][]) proclaims, "Now, finally, we can formalize the idea we have been using since the first page of this text." He then proceeds to define **identities of terms** as follows (paraphrasing for notational consistency):

  Let 𝑆 be a signature. An **identity** or **equation** in 𝑆 is an ordered pair of terms, written 𝑝 ≈ 𝑞, from the
  term algebra `𝑻 X`. If 𝑨 is an 𝑆-algebra we say that 𝑨 **satisfies** 𝑝 ≈ 𝑞 if `𝑝 ̇ 𝑨  ≡  𝑞 ̇ 𝑨`. In this
  situation, we write `𝑨 ⊧ 𝑝 ≈ 𝑞` and say that 𝑨 **models** the identity `𝑝 ≈ q`.

If 𝒦 is a class of structures, all of the same signature, it is standard to write `𝒦 ⊧ p ≈ q` just in case all structures in the class 𝒦 model the identity p ≈ q. However, because a class of structures has a different type than a single structure, we will need to use a different notation, and we settle for `𝒦 ⊧ p ≋ q` to denote this concept.

Thus, if 𝒦 is a class of 𝑆-algebras, we write `𝒦 ⊧ 𝑝 ≋ 𝑞` if for every `𝑨 ∈ 𝒦` we have `𝑨 ⊧ 𝑝 ≈ 𝑞`.

 Finally, if ℰ is a set of equations, we write 𝒦 ⊧ ℰ if every member of 𝒦 satisfies every member of ℰ.

In this module we formalize these notions by defining types that represent them. Before we attempt to do that, however, let us say a bit more precisely what the definition of `𝑨 ⊧ 𝑝 ≈ 𝑞` entails. When we write `𝑨 ⊧ 𝑝 ≈ 𝑞` and say that the identity `p ≈ q` is satisfied in 𝑨, we mean that for each assignment function `𝒂 : X → ∣ 𝑨 ∣`, assigning values in the domain of 𝑨 to the variable symbols in `X`, we have `(𝑝 ̇ 𝑨) 𝒂 ≡ (𝑞 ̇ 𝑨) 𝒂`.

**Notation**. To produce the symbols ≈ and ⊧ in Emacs `agda2-mode`, type `\~~` and `\models` (resp.). As mentioned, to denote "𝒦 models 𝑝 ≈ 𝑞" we will use 𝒦 ⊧ 𝑝 ≋ 𝑞 instead of the more standard 𝒦 ⊧ 𝑝 ≈ 𝑞 because we distinguish it from 𝑨 ⊧ 𝑝 ≈ 𝑞 in our Agda implementation. The symbol ≋ is produced in Emacs `agda2-mode` with `\~~~`. -->

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Varieties.ModelTheory
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Subalgebras.Subalgebras{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

---------------------------------------

#### <a id="the-models-relation">The models relation</a>

We define the binary "models" relation ⊧, with infix so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊧ p ≋ q`, relating algebras (or classes of algebras) to the identities that they satisfy. We also prove a coupld of useful facts about ⊧.  More will be proved about ⊧ in the next module, [UALib.Varieties.EquationalLogic](UALib.Varieties.EquationalLogic.html).

\begin{code}

_⊧_≈_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Algebra 𝓤 𝑆 → Term{𝓧}{X} → Term → 𝓤 ⊔ 𝓧 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)


_⊧_≋_ : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →      Term{𝓧}{X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}

-------------------------------------------

#### <a id="equational-theories-and-classes">Equational theories and models</a>

The set of identities that hold for all algebras in a class 𝒦 is denoted by `Th 𝒦`, which we define as follows.

\begin{code}

Th : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Algebra 𝓤 𝑆) (OV 𝓤)
 →   Pred (Term{𝓧}{X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)

Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

\end{code}

The class of algebras that satisfy all identities in a given set ℰ is denoted by `Mod ℰ`.  We given three nearly equivalent definitions for this below.  The only distinction between these is whether the arguments are explicit (so must appear in the argument list) or implicit (so we may let Agda do its best to guess the argument).

\begin{code}

MOD : (𝓤 𝓧 : Universe)(X : 𝓧 ̇) → Pred (Term{𝓧}{X} × Term{𝓧}{X}) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)

MOD 𝓤 𝓧 X ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

Mod : {𝓤 𝓧 : Universe}(X : 𝓧 ̇) → Pred (Term{𝓧}{X} × Term{𝓧}{X}) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)

 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)

Mod X ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q


mod : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} → Pred (Term{𝓧}{X} × Term{𝓧}{X}) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⊔ 𝓤 ⁺)
 →    Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺ ⊔ 𝓤 ⁺)

mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

\end{code}

------------------------------------------

#### <a id="computing-with-⊧">Computing with ⊧</a>

<pre class="Agda">

We have formally defined <a class="Bound">𝑨</a> <a class="Function">⊧</a> <a class="Bound">𝑝</a> <a class="Function">≈</a> <a class="Bound">𝑞</a>, which represents the assertion that <a class="Bound">p</a> <a class="Function">≈</a> <a class="Bound">q</a> holds when this identity is interpreted in the algebra <a class="Bound">𝑨</a>; syntactically, <a class="Bound">𝑝</a> <a class="Function">̇</a> <a class="Bound">𝑨</a> <a class="Function">≡</a> <a class="Bound">𝑞</a> <a class="Function">̇</a> <a class="Bound">𝑨</a>.  Hopefully we already grasp the semantic meaning of these strings of symbols, but our understanding is tenuous at best unless we have a handle on their computational meaning, since this tells us how one *uses* the definitions. We emphasize that we interpret the expression <a class="Bound">𝑝</a> <a class="Function">̇</a> <a class="Bound">𝑨</a> <a class="Function">≡</a> <a class="Bound">𝑞</a> <a class="Function">̇</a> <a class="Bound">𝑨</a> as an *extensional equality*, by which we mean that for each *assignment function* <a class="Bound">𝒂</a> <a class="Symbol">:</a> <a class="Bound">X</a> <a class="Symbol">→</a> ∣ <a class="Bound">𝑨</a> ∣---assigning values in the domain of <a class="Bound">𝑨</a> to the variable symbols in <a class="Bound">X</a>---we have (<a class="Bound">𝑝</a> <a class="Function">̇</a> <a class="Bound">𝑨</a>) <a class="Bound">𝒂</a> <a class="Function">≡</a> (<a class="Bound">𝑞</a> <a class="Function">̇</a> <a class="Bound">𝑨</a>) <a class="Bound">𝒂</a>.

</pre>


-------------------------------------

#### <a id="⊧-≅ compatibility">⊧-≅ compatibility</a>

<pre class="Agda">

The binary relation <a class="Function">⊧</a> would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism), and this fact is proved by showing that a certain term operation identity---namely, <a class="Bound">p</a> <a class="Function">̇</a> <a class="Bound">𝑩</a> <a class="Datatype">≡</a> <a class="Bound">q</a> <a class="Function">̇</a> <a class="Bound">𝑩</a>---holds *extensionally*, in the sense of the paragraph above on [Computing with ⊧](UALib.Varieties.Modeltheory.html#computing-with-⊧).

</pre>

\begin{code}

⊧-≅
 ⊧-transport : {𝓠 𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
                 (p q : Term{𝓧}{X}) → (𝑨 ⊧ p ≈ q) → (𝑨 ≅ 𝑩) → 𝑩 ⊧ p ≈ q
⊧-transport {𝓠}{𝓤}{𝓧}{X}{𝑨}{𝑩} p q Apq (f , g , f∼g , g∼f) = γ
 where
  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ x →
      (p ̇ 𝑩) x ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      (p ̇ 𝑩) (∣ 𝒾𝒹 𝑩 ∣ ∘ x) ≡⟨ ap (λ - → (p ̇ 𝑩) -) (gfe λ i → ((f∼g)(x i))⁻¹)  ⟩
      (p ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘ x) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 f p (∣ g ∣ ∘ x))⁻¹ ⟩
      ∣ f ∣ ((p ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ ap (λ - → ∣ f ∣ (- (∣ g ∣ ∘ x))) Apq ⟩
      ∣ f ∣ ((q ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ comm-hom-term gfe 𝑨 𝑩 f q (∣ g ∣ ∘ x) ⟩
      (q ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘  x) ≡⟨ ap (λ - → (q ̇ 𝑩) -) (gfe λ i → (f∼g) (x i)) ⟩
      (q ̇ 𝑩) x ∎

⊧-≅ = ⊧-transport -- (alias)

\end{code}

--------------------------------------

#### <a id="⊧-lift-compatibility">⊧-lift compatibility</a>

The ⊧ relation is also compatible with the lift operation.

\begin{code}

lift-alg-⊧ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
       (𝑨 : Algebra 𝓤 𝑆)(p q : Term{𝓧}{X})
  →    𝑨 ⊧ p ≈ q → (lift-alg 𝑨 𝓦) ⊧ p ≈ q
lift-alg-⊧ 𝑨 p q Apq = ⊧-≅ p q Apq lift-alg-≅

lower-alg-⊧ : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)
                             (p q : Term{𝓧}{X})
 →                           lift-alg 𝑨 𝓦 ⊧ p ≈ q → 𝑨 ⊧ p ≈ q
lower-alg-⊧ {𝓤}{𝓦}{𝓧}{X} 𝑨 p q lApq = ⊧-≅ p q lApq (sym-≅ lift-alg-≅)

-- lower-class : {𝓤 𝓦 : Universe} → Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(OV (𝓤 ⊔ 𝓦)) → Pred (Algebra 𝓤 𝑆)(OV (𝓤 ⊔ 𝓦))
-- lower-class {𝓤}{𝓦}𝒦 = λ (𝑨 : Algebra 𝓤 𝑆) → lift-alg 𝑨 𝓦 ∈ 𝒦

\end{code}

---------------------------------

[↑ UALib.Varieties](UALib.Varieties.html)
<span style="float:right;">[UALib.Varieties.EquationalLogic →](UALib.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}

