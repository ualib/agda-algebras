---
layout: default
title : Overture.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

The [Agda Universal Algebra Library](https://github.com/ualib/agda-algebras) (or [agda-algebras](https://github.com/ualib/agda-algebras) for short) is based on a version of [Martin-Löf type theory (MLTT)](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory), similar to the one on which on which Martín Escardó's [Type Topology Agda
library](https://github.com/martinescardo/TypeTopology) is based. We don't discuss [MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) in great detail here because there are already good and freely available resources covering the theory. (See, for example, the section of [Escardó's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes) on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda), or the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), or the [HoTT book](https://homotopytypetheory.org/book/).)


The objects and assumptions that form the foundation of [MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) are few. There are the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these type formers is defined by a *type forming rule* which specifies how that type is constructed. Lastly, we have an infinite collection of *type universes* (types of types) and *universe variables* to denote them. Following Escardó, [agda-algebras][] denotes universe levels by upper-case calligraphic letters from the second half of the English alphabet; to be precise, these are `𝓞`, `𝓠`, `𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[1](Overture.Preliminaries.html#fn1)</sup>

That's all. There are no further axioms or logical deduction (proof derivation) rules needed for the foundations of
[MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) that we take as the starting point of [agda-algebras][].  The logical semantics come from the [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types): propositions and predicates are represented by types and the inhabitants of these types are the proofs of the propositions and predicates.  As such, proofs are constructed using the type forming rules. In other words, the type forming rules *are* the proof derivation rules.

To this foundation, we add certain *extensionality principles* when and were we need them.  These will be developed as we progress.  However, classical axioms such as the [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice) or the [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are not assumed anywhere in the library.  In this sense, all theorems and proofs in [agda-algebras][] are [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)).

A few specific instances (e.g., the proof of the Noether isomorphism theorems and Birkhoff's HSP theorem) require certain *truncation* assumptions. In such cases, the theory is not [predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)). These instances are always clearly identified.



#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries. Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in [agda-algebras][] begins with the following line.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) [UniversalAlgebra][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line.

\begin{code}


-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
open import Function using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans)

module Overture.Preliminaries where

\end{code}


#### <a id="agda-universes">Agda Universes</a>

Here we import the basic primitive operations we need for working with Agda's type universes. For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

We prefer to use `Type` in place of Agda's `Set` since for us *set* will mean a very special kind of (truncated) type. (See [Relatoins.Truncation][]).

\begin{code}

Type : (𝓤 : Level) → Set (lsuc 𝓤)
Type 𝓤 = Set 𝓤

\end{code}

We adopt Escardó's convention of denoting universe levels by capital calligraphic letters.

\begin{code}

variable
 𝓘 𝓞 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level

\end{code}

Also, the standard library made an alternative notation for the dependent pair type available which allows us to write `Σ[ x ∈ A ] B x` in place of `Σ A (λ x → B)`.  In the [agda-algebras][] library we may use any one of the three alternative notations,

+ `Σ A (λ x → B)` (standard Agda notation)
+ `Σ[ x ∈ A ] B x` ([Agda Standard Library][] notation)
+ `Σ x ꞉ A , B` ([Type Topology][] notation)

**Warning!** The symbol `꞉` is not the same as `:`. Type the colon in `Σ x ꞉ A ⸲ B` as `\:4` in [agda2-mode][].
 above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.


```agda
_×_ : Type 𝓤 → Type 𝓥 → Type (𝓤 ⊔ 𝓥)
A × B = Σ[ x ꞉ A ] B
```


#### <a id="dependent-function-type">Pi types (dependent functions)</a>

Given universes `𝓤` and `𝓥`, a type `X : Type 𝓤`, and a type family `Y : X → Type 𝓥`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here.

\begin{code}

Π : {A : Type 𝓤 } (B : A → Type 𝓦 ) → Type (𝓤 ⊔ 𝓦)
Π {A = A} B = (x : A) → B x

\end{code}

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.

\begin{code}

-Π : (A : Type 𝓤 )(B : A → Type 𝓦 ) → Type(𝓤 ⊔ 𝓦)
-Π A B = Π B

infixr 3 -Π
syntax -Π A (λ x → B) = Π[ x ꞉ A ] B  -- type \,3 to get ⸲

\end{code}

**Warning!** The symbols ꞉ and ⸲ are not the same as : and ,. Type the colon (resp. comma) in `Π x ꞉ A ⸲ B` as `\:4` (resp `\,3`) in [agda2-mode][].



#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.

\begin{code}

module _ {A : Type 𝓤 }{B : A → Type 𝓥} where

 ∣_∣ fst : Σ[ x ∈ A ] B x → A
 ∣ x , y ∣ = x
 fst (x , y) = x

 ∥_∥ snd : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥ x , y ∥ = y
 snd (x , y) = y

 infix  40 ∣_∣
\end{code}

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type 𝓤`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.




We prove that `≡` obeys the substitution rule (subst) in the next subsection (see the definition of `ap` below), but first we define some syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.<sup>[2](Overture.Equality.html#fn3)</sup>

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


𝑖𝑑 : (A : Type 𝓤 ) → A → A
𝑖𝑑 A = λ x → x

id : {A : Type 𝓤} → A → A
id x = x

infixl 30 _∙_
infixr  0 _≡⟨_⟩_
infix   1 _∎

\end{code}


#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

```agda
Type 𝓤 : Type (lsuc 𝓤),   Type(lsuc 𝓤) : Type (lsuc (lsuc 𝓤)),  etc.
```

This means that the universe `Type 𝓤` has type `Type(lsuc 𝓤)`, and  `Type(lsuc 𝓤)` has type `Type(lsuc (lsuc 𝓤))`, and so on.  It is important to note, however, this does *not* imply that  `Type 𝓤 : Type(lsuc(lsuc 𝓤))`. In other words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant. Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.




#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Algebras.html#lifts-of-algebras) of the [Algebras.Algebras][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
𝓤 != 𝓞 ⊔ 𝓥 ⊔ (lsuc 𝓤) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `lsuc 𝓤`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⊔ 𝓥 ⊔ lsuc 𝓤` instead.

The general `Lift` record type that we now describe makes these situations easier to deal with. It takes a type inhabiting some universe and embeds it into a higher universe and, apart from syntax and notation, it is equivalent to the `Lift` type one finds in the `Level` module of the [Agda Standard Library][].

```agda
 record Lift {𝓦 𝓤 : Level} (A : Type 𝓤) : Type (𝓤 ⊔ 𝓦) where
  constructor lift
  field lower : A
```

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

\begin{code}

lift∼lower : ∀ {𝓤 𝓦}{A : Type 𝓤} → lift ∘ lower ≡ 𝑖𝑑 (Lift 𝓦 A)
lift∼lower = refl

lower∼lift : {𝓤 𝓦 : Level}{A : Type 𝓤} → lower {𝓤}{𝓦}(lift {𝓤}{𝓦}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

\end{code}

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.

#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion that two functions are (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have more to say about this notion of equality in the [Relations.Extensionality][] module.)

\begin{code}

_∼_ : {X : Type 𝓤 } {A : X → Type 𝓥 } → Π A → Π A → Type (𝓤 ⊔ 𝓥)
f ∼ g = ∀ x → f x ≡ g x

infix 8 _∼_

\end{code}

---------------



<sup>1</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe
variable because in some libraries `𝓟` denotes a powerset type.</span>

<sup>2</sup> <span class="footnote" id="fn2"> Most of these types are already defined by in the [Type Topology][] library or the [Agda Standard Library][], so we often imports the definitions; occasionally, however, we repeat the definitions here for pedagogical reasons and to keep the presentation somewhat self-contained.


<sup>4</sup> <span class="footnote" id="fn4"> Moreover, if one assumes the [univalence axiom][] of [Homotopy Type Theory][], then point-wise equality of functions is equivalent to definitional equality of functions. (See [Function extensionality from univalence](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua).)</span>

<sup>5</sup><span class="footnote" id="fn5">Recall, from the [Overture.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>

{% include UALib.Links.md %}

[agda-algebras]: https://github.com/ualib/agda-algebras



<!--

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an
outstanding set of notes entitled
[Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html)
which we highly recommend to anyone wanting more details than we provide here
about [MLTT][] and Univalent Foundations/HoTT in Agda.</span>

-->
