---
layout: default
title : "Demos.HSP-markdown module (Agda Universal Algebra Library)"
date : "2021-10-24"
author: "agda-algebras development team"
---

## <a id="introduction">Introduction</a>
The Agda Universal Algebra Library ([agda-algebras][]) is a collection of types and programs
(theorems and proofs) formalizing the foundations of universal algebra in dependent type
theory using the [Agda][] programming language and proof assistant.
The agda-algebras library now includes a substantial collection of definitions, theorems, and
proofs from universal algebra and equational logic and as such provides many
examples that exhibit the power of inductive and dependent types for
representing and reasoning about general algebraic and relational structures.

The first major milestone of the [agda-algebras][] project is a new formal
proof of *Birkhoff's variety theorem* (also known as the *HSP theorem*), the first version
of which was completed in [January of 2021](https://github.com/ualib/ualib.github.io/blob/b968e8af1117fc77700d3a588746cbefbd464835/sandbox/birkhoff-exp-new-new.lagda).
To the best of our knowledge, this was the first time Birkhoff's theorem had
been formulated and proved in dependent type theory and verified with a proof
assistant.

In this paper, we present a single Agda module called [Demos.HSP][].
This module extracts only those parts of the library needed to prove
Birkhoff's variety theorem. In order to meet page limit guidelines, and to
reduce strain on the reader, we omit proofs of some routine or technical
lemmas that do not provide much insight into the overall development.
However, a long version of this paper, which includes all code in the
[Demos.HSP][] module, is available on the arXiv. [reference needed]

In the course of our exposition of the proof of the HSP theorem, we discuss some of the
more challenging aspects of formalizing *universal algebra* in type theory and the
issues that arise when attempting to constructively prove some of the basic
results in this area.  We demonstrate that dependent type theory and Agda,
despite the demands they place on the user, are accessible to working
mathematicians who have sufficient patience and a strong enough desire to
constructively codify their work and formally verify the correctness of their
results.  Perhpas our presentation will be viewed as a sobering glimpse of the
painstaking process of doing mathematics in the languages of dependent type theory
using the Agda proof assistant. Nonetheless we hope to make a compelling case for
investing in these technologies. Indeed, we are excited to share the gratifying
rewards that come with some mastery of type theory and interactive theorem proving.

### Prior art
There have been a number of efforts to formalize parts of universal algebra in
type theory prior to ours, most notably

1. Capretta [@Capretta:1999] (1999) formalized the basics of universal algebra in the
   Calculus of Inductive Constructions using the Coq proof assistant;
2. Spitters and van der Weegen [@Spitters:2011] (2011) formalized the basics of universal algebra
   and some classical algebraic structures, also in the Calculus of Inductive Constructions using
   the Coq proof assistant, promoting the use of type classes;
3. Gunther, et al [@Gunther:2018] (2018) developed what seems to be (prior to the [agda-algebras][] library)
   the most extensive library of formal universal algebra to date; this work is based on dependent type
   theory and programmed in Agda; it treats multisorted algebras and goes beyond the basic Noether
   isomorphism theorems to include some basic equational logic.
4. Lynge and Spitters [@Lynge:2019] (2019) formalize basic, mutisorted universal algebra, up to the
   Noether isomorphism theorems, in homotopy type theory; in this setting, the authors can avoid using
   setoids by postulating a strong extensionality axiom called univalence.

Some other projects aimed at formalizing mathematics generally, and algebra in particular, have developed into very extensive libraries that include definitions, theorems, and proofs about algebraic structures, such as groups, rings, modules, etc.  However, the goals of these efforts seem to be the formalization of special classical algebraic structures, as opposed to the general theory of (universal) algebras. Moreover, the part of universal algebra and equational logic formalized in the [agda-algebras][] library extends beyond the scope of prior efforts.

<!-- After completing the formal proof in \agda, we learned about a constructive version of Birkhoff's theorem proved by Carlstr\"om in~\cite{Carlstrom:2008}.  The latter is presented in the informal style of standard mathematical writing, and as far as we know it was never formalized in type theory and type-checked with a proof assistant. Nonetheless, a comparison of Carlstr\"om's proof and the \ualib proof would be interesting.
-->




<!-- ----------------------------------------------------------------------------------- -->

## <a id="preliminaries">Preliminaries</a>

### <a id="logical-foundations">Logical foundations</a>

An Agda program typically begins by setting some language options and by
importing types from existing Agda libraries. The language options are specified
using the `OPTIONS` *pragma* which affect control the way Agda behaves by controlling
the deduction rules that are available to us and the logical axioms 
that are assumed when the program is type-checked by Agda to verify its
correctness. Every Agda program in the [agda-algebras](https://github.com/ualib/agda-algebras)
library, including the present module ([Demos.HSP][]), begins with the following line.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

We will provide only very terse descriptions of these options, but we also give links to more details about them.

* `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference Manual](https://agda.readthedocs.io/en/v2.6.1.3/language).

* `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities. See also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1.3/tools/) documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference](https://agda.readthedocs.io/en/v2.6.1.3/language).


<!--
### <a id="agda-modules">Agda Modules</a>
-->

The \AgdaKeyword{OPTIONS} pragma is usually followed by the start of a module and a list of `import` directives.
We won't reproduce all of the imports we use here. Rather we show only those imports that rename objects from the standard library to our own notation which might be less standard.

\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )
module Demos.HSP-markdown {𝑆 : Signature 𝓞 𝓥} where
\end{code}
\begin{code}

open import Agda.Primitive  using (_⊔_ ; lsuc) renaming (Set to Type)
open import Data.Product    using (Σ-syntax ; _×_ ; _,_ ; Σ) renaming (proj₁ to fst ; proj₂ to snd)
open import Function        using (id ; _∘_ ; flip ; Injection ; Surjection) renaming (Func to _⟶_)
open _⟶_                    using (cong) renaming (f to _⟨$⟩_)

open import  Relation.Binary.PropositionalEquality  as ≡ using (_≡_)
import       Relation.Binary.Reasoning.Setoid       as SetoidReasoning
import       Function.Definitions                   as FD

\end{code}
\begin{code}[hide]
open import Level using ( Level )
open import Relation.Binary using ( Setoid ; Rel ; IsEquivalence )
open import Relation.Binary.Definitions using ( Reflexive ; Sym ; Trans ; Symmetric ; Transitive )
open import Relation.Unary using ( Pred ; _⊆_ ; _∈_ )
open Setoid using ( Carrier ; isEquivalence )
private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ
 𝑓 : fst 𝑆
\end{code}
Note, in particular, we rename the `Set` and `Func` types of the standard library to `Type` and the infix long arrow symbol `_⟶_`, respectively, and we use `fst` and `snd` in place of `proj₁` and  `proj₂` for the first and second projections out of the product type `_×_`. In addition, when it improves readability of the code, we use the alternative notation `∣_∣` and `∥_∥` (defined elsewhere) for the first and second projections.

### <a id="setoids">Setoids</a>

A *setoid* is a type packaged with an equivalence relation on the collection
of inhabitants of that type.  Setoids are useful for representing classical
(set-theory-based) mathematics in a constructive, type-theoretic way because
most mathematical structures are assumed to come equipped with some (often
implicit) equivalence relation manifesting a notion of equality of elements,
and therefore a type-theoretic representation of such a structure should
also model its equality relation.

The [agda-algebras][] library was first developed without the use of setoids,
opting instead for specially constructed experimental quotient types.
However, this approach resulted in code that was hard to comprehend and
it became difficult to determine whether the resulting proofs were fully
constructive.  In particular, our initial proof of the Birkhoff variety theorem
required postulating function extensionality, an axiom that is not provable in
pure Martin-Löf type theory (MLTT). [reference needed]

In contrast, our current approach using setoids makes the equality relation
of a given type explicit and this transparency can make it easier to determine the
correctness and constructivity of the proofs. Using setiods we need
no additional axioms beyond MLTT; in particular, no function
extensionality axioms are postulated in our current formalization of Birkhoff's
variety theorem.

<!--
Since it plays such a central role in the present development, we
reproduce in the appendix the definition of the `Setoid` type of the [Agda
Standard Library][]. In addition to `Setoid`, much of our code employs the
standard library's `Func` record type which represents a function from one
setoid to another and packages such a function with a proof (called `cong`) that
the function respects the underlying setoid equalities. In the list
of imports above we renamed `Func` to the more visually appealing
long-arrow symbol `⟶`, and we will refer to its inhabitants as "setoid
functions" throughout the paper.

A special example of a setoid function is the identity function from a setoid to itself.
We define it, along with a binary composition operation for setoid functions, `_⟨∘⟩_`, as follows.
-->

\begin{code}[hide]
𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { f = id ; cong = id }

_⟨∘⟩_ :  {A : Setoid α ρᵃ} {B : Setoid β ρᵇ} {C : Setoid γ ρᶜ}
 →       B ⟶ C  →  A ⟶ B  →  A ⟶ C

f ⟨∘⟩ g = record  { f = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g)
                  ; cong = (cong f) ∘ (cong g) }

module _ {A : Type α }{B : A → Type β} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
\end{code}

<!--
(Here we put the definitions inside an *anonymous module*, which starts with the
`module` keyword followed by an underscore instead of a module name. The
purpose is simply to move the postulated typing judgments---the "parameters" of
the module, e.g., `A : Type α`---out of the way so they don't obfuscate the
definitions inside the module.)
-->

### <a id="inverses-of-setoid-functions">Inverses of setoid functions</a>

We define a data type that represent the semantic concept of the *image* of a function
(cf. the [Setoid.Overture.Inverses][] module of the [agda-algebras][] library).

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ (f ⟨$⟩ a) → Image f ∋ b

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and
`p : b ≈ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b`
belongs to the image of `f` is always accompanied by a witness `a : A`, we can
actually *compute* a (pseudo)inverse of `f`. For convenience, we define this
inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and
a (witness, proof)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → (f ⟨$⟩ (Inv f q)) ≈ b
 InvIsInverseʳ (eq _ p) = sym p

\end{code}

`InvIsInverseʳ` proves that `Inv f` is the range-restricted right-inverse of the setoid function `f`.


### <a id="injective-and-surjective-setoid-functions">Injective and surjective setoid functions</a>

If `f : 𝑨 ⟶ 𝑩` is a setoid function from `𝑨 = (A , ≈₀)` to `𝑩 = (B , ≈₁)`, then
we call `f` *injective* provided `∀ (a₀ a₁ : A)`, `f ⟨$⟩ a₀ ≈₁ f ⟨$⟩ a₁` implies `a₀ ≈₀ a₁`;
we call `f` *surjective* provided `∀ (b : B)`, `∃ (a : A)` such that `f ⟨$⟩ a ≈₁ b`.
We codify these definitions in Agda and prove some of their properties
inside the next submodule where we first set the stage by declaring two
setoids `𝑨` and `𝑩`, naming their equality relations, and making some
definitions from the standard library available.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈₁_ ; Carrier to A )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈₂_ ; Carrier to B )
 open FD _≈₁_ _≈₂_

\end{code}

The [Agda Standard Library][] represents injective functions on bare types by the
type `Injective`, which we now use to define `IsInjective` representing the property
of being an injective setoid function. We then define the type `IsSurjective` to
represent the property of being a surjective setoid function. Finally, we define
`SurjInv` to represent the *right-inverse* of a surjective function.
The definitions are as follows (cf. [Setoid.Overture.Injective][] and [Setoid.Overture.Surjective][] in the [agda-algebras][] library).

\begin{code}

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective (_⟨$⟩_ f)

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective F = ∀ {y} → Image F ∋ y

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → B → A
 SurjInv f fonto b = Inv f (fonto {b})
\end{code}

#### <a id="composition-of-injective-and-surjective-setoid-functions">Composition of injective and surjective setoid functions</a>

Proving that the composition of injective setoid functions is again injective
is simply a matter of composing the two assumed witnesses to injectivity.
Proving that surjectivity is preserved under composition is only slightly more involved.

\begin{code}

module _  {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ}
          (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪) where

 ∘-IsInjective : IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-IsInjective finj ginj = finj ∘ ginj

 ∘-IsSurjective : IsSurjective f → IsSurjective g → IsSurjective (g ⟨∘⟩ f)
 ∘-IsSurjective fonto gonto {y} = Goal
  where
  mp : Image g ∋ y → Image g ⟨∘⟩ f ∋ y
  mp (eq c p) = η fonto
   where
   open Setoid 𝑪 using ( trans )
   η : Image f ∋ c → Image g ⟨∘⟩ f ∋ y
   η (eq a q) = eq a (trans p (cong g q))

  Goal : Image g ⟨∘⟩ f ∋ y
  Goal = mp gonto
\end{code}


### <a id="kernels">Kernels</a>

The *kernel* of a function `f : A → B` (where `A` and `B` are bare types) is defined
informally by `{(x , y) ∈ A × A : f x = f y}`.
This can be represented in Agda in a number of ways, but for our purposes we find it most
convenient to define the kernel as an inhabitant of a (unary) predicate over the square of
the function's domain.

\begin{code}

module _ {A : Type α}{B : Type β} where

 kernel : Rel B ρ → (A → B) → Pred (A × A) ρ
 kernel _≈_ f (x , y) = f x ≈ f y

\end{code}

The kernel of a setoid function `f : 𝐴 ⟶ 𝐵` is defined informally by
`{(x , y) ∈ A × A : f ⟨$⟩ x ≈ f ⟨$⟩ y}`, where `_≈_` denotes the equality of `𝐵`.

\begin{code}

module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
 open Setoid 𝐴 using () renaming ( Carrier to A )

 ker : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
 ker g (x , y) = g ⟨$⟩ x ≈ g ⟨$⟩ y where open Setoid 𝐵 using ( _≈_ )
\end{code}





<!-- ------------------------------------------------------------------------------------- -->

## Algebras

In this section we define the notion of an algebraic structure whose *domain* (or "carrier" or "universe") is a setoid. Our first goal is to develop a working vocabulary and formal types for classical (single-sorted, set-based) universal algebra.

### <a id="signatures-of-an-algebra">Signatures of an algebra</a>

In [model theory](https://en.wikipedia.org/wiki/Model_theory), the *signature* `𝑆 = (𝐶, 𝐹, 𝑅, ρ)` of a structure consists of three (possibly empty) sets `𝐶`, `𝐹`, and `𝑅`---called *constant symbols*, *function symbols*, and *relation symbols*, respectively---along with a function `ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁` that assigns an *arity* to each symbol. Often, but not always, `𝑁` is taken to be the set of natural numbers.

As our focus here is universal algebra, we are more concerned with the restricted notion of an *algebraic signature* (or *signature* for algebraic structures), by which we mean a pair `𝑆 = (F, ρ)` consisting of a collection `𝐹` of *operation symbols* and an *arity function* `ρ : F → N` that maps each operation symbol to its arity; here, 𝑁 denotes the *arity type*. Heuristically, the arity `ρ f` of an operation symbol `f ∈ F` may be thought of as the "number of arguments" that `f` takes as "input".

If the arity of `f` is `n`, then we call `f` an `n`-*ary* operation symbol.  In case `n` is 0 (or 1 or 2 or 3, respectively) we call the function *nullary* (or *unary* or *binary* or *ternary*, respectively).

If `A` is a set and `f` is a (`ρ f`)-ary operation on `A`, then the arguments of `f` form a (`ρ f`)-tuple, say, `(a 0, a 1, …, a (ρf-1))`, which may be viewed as the graph of a function, say, `a : ρf → A`. When the codomain of `ρ` is `ℕ`, we may view `ρ f` as the finite set `{0, 1, …, ρf - 1}`. Thus, by identifying the `ρf`-th power of `A` with the type `ρ f → A` of functions from `{0, 1, …, ρf - 1}` to `A`, we identify the collection of all tuples of arguments of `f` with the function type `(ρf → A) → A`.

#### <a id="signature-type">Signature type</a>

The [agda-algebras][] library represents a *signature* as an inhabitant of the following dependent pair type.

```
Signature : (𝓞 𝓥 : Level) → Type (lsuc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)
```

Using special syntax for the first and second projections---`∣_∣` and `∥_∥`, respectively---if `𝑆 : Signature 𝓞 𝓥` is a signature, then

* `∣ 𝑆 ∣` denotes the set of operation symbols;
* `∥ 𝑆 ∥` denotes the arity function.

Thus, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, then `∥ 𝑆 ∥ 𝑓` is the arity of `𝑓`.

We need to augment the ordinary `Signature` type so that it supports algebras over setoid domains.
To do so, we define an operator `⟨_⟩` which translates an ordinary signature into a setoid signature, that is, a signature over a setoid domain.  But first we must resolve a techinical issue involving dependent types that we now describe.

Suppose we are given two operations `f` and `g` and we have a tuple of arguments for `f`, say, `u : ∥ 𝑆 ∥ f → A`, and a tuple of arguments for `g`, say, `v : ∥ 𝑆 ∥ g → A`.  If we know that `f` is identically equal to `g`---that is, `f ≡ g` (intensionally)---then we should be able to check whether `u` and `v` are pointwise equal.  The problem here is that `u` and `v` ostensibly inhabit different types.  To compare `u` and `v` we must convince Agda that, from `f ≡ g` we can deduce that `u` and `v` are actually of the same type. The type `EqArgs` (defined below, and adapted from Andreas Abel's development [ref needed]) resolves this technical issue nicely.

\begin{code}

EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)

EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )

\end{code}

Now we are ready to define the `⟨_⟩` operator, which translates an ordinary signature into a setoid signature.

\begin{code}

module _ where
 open Setoid        using ( _≈_ )
 open IsEquivalence using ( refl ; sym ; trans )

 ⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

 Carrier (⟨ 𝑆 ⟩ ξ)              = Σ[ f ∈ ∣ 𝑆 ∣ ] ((∥ 𝑆 ∥ f) → ξ .Carrier)

 _≈_ (⟨ 𝑆 ⟩ ξ) (f , u) (g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

 refl   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → Setoid.refl   ξ
 sym    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → Setoid.sym    ξ (g i)
 trans  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → Setoid.trans  ξ (g i) (h i)
\end{code}

### <a id="Algebra type">Algebra type</a>

Informally, an *algebraic structure in the signature* `𝑆 = (F, ρ)` (or `𝑆`-*algebra*) is typically denoted by `𝑨 = (A, Fᴬ)` and consists of

* `A` := a *nonempty* set (or type), called the *domain* (or *carrier* or *universe*) of the algebra;
* `Fᴬ` := `{ fᴬ ∣ f ∈ F, fᴬ : (ρf → A) → A }`, a collection of *operations* on `𝐴`;
* a (potentially empty) collection of *identities* satisfied by elements and operations of `𝐴`.

We represent an algebra in Agda using a record type with two fields:

* `Domain` is a setoid denoting the underlying *universe* of the algebra (informally, the set of elements of the algebra);
* `Interp` represents the *interpretation* in the algebra of each operation symbol of the given signature.  The record type `Func` from the Agda Standard Library provides what we need for an operation on the domain setoid.

Let us present the definition of the `Algebra` type and then discuss the definition of the `Func` type that provides the interpretation of each operation symbol.

\begin{code}

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field  Domain : Setoid α ρ
        Interp : (⟨ 𝑆 ⟩ Domain) ⟶ Domain

\end{code}

The `Interp` field actually has type `Func (⟨ 𝑆 ⟩ Domain) Domain` (recall we renamed `Func` as the infix long-arrow symbol).  The `Func` type is from the standard library and is defined as a record type with two fields. In the present instance, the fields are

1. a function  `f : Carrier (⟨ 𝑆 ⟩ Domain) → Carrier Domain`
2. a proof `cong : f Preserves _≈₁_ ⟶ _≈₂_` that `f` preserves the underlying setoid equalities.

Thus `Interp` gives, for each operation symbol in the signature `𝑆`, a setoid function `f`---namely, a function where the domain is a power of `Domain` and the codomain is `Domain`---along with a proof that all operations so interpreted respect the underlying setoid equality on `Domain`.

Next we define some syntactic sugar that will make our Agda code easier to read and comprehend.
If `𝑨` is an algebra, then

* `f ̂ 𝑨` will denote the interpretation in the algebra `𝑨` of the operation symbol `f`,
* `𝔻[ 𝑨 ]` will denote the setoid `Domain 𝑨`, and
* `𝕌[ 𝑨 ]` will be the underlying carrier or "universe" of the algebra `𝑨`.

\begin{code}

open Algebra

𝕌[_] : Algebra α ρᵃ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)

𝔻[_] : Algebra α ρᵃ →  Setoid α ρᵃ
𝔻[ 𝑨 ] = Domain 𝑨

_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρᵃ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]

f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
\end{code}


### <a id="universe-lifting-of-algebra-types">Universe lifting of algebra types</a>

A technical aspect of dealing with the noncumulativity of the hierarchy of type levels in Agda...

\begin{code}

module _ (𝑨 : Algebra α ρᵃ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )
 open Level

 Lift-Algˡ : (ℓ : Level) → Algebra (α ⊔ ℓ) ρᵃ
 Domain (Lift-Algˡ ℓ) =
  record   { Carrier = Lift ℓ 𝕌[ 𝑨 ]
           ; _≈_ = λ x y → lower x ≈ lower y
           ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }}
 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 cong (Interp (Lift-Algˡ ℓ)) (≡.refl , la=lb) = cong (Interp 𝑨) ((≡.refl , la=lb))

 Lift-Algʳ : (ℓ : Level) → Algebra α (ρᵃ ⊔ ℓ)
 Domain (Lift-Algʳ ℓ) =
  record  { Carrier = 𝕌[ 𝑨 ]
          ; _≈_ = λ x y → Lift ℓ (x ≈ y)
          ; isEquivalence = record  { refl  = lift refl
                                    ; sym   = λ x → lift (sym (lower x))
                                    ; trans = λ x y → lift (trans (lower x) (lower y)) }}
 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (Lift-Algʳ ℓ))(≡.refl , la≡lb) = lift(cong(Interp 𝑨)(≡.refl , λ i → lower (la≡lb i)))

Lift-Alg : (𝑨 : Algebra α ρᵃ)(ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁
\end{code}


### <a id="product-algebras">Product Algebras</a>

(cf. the [Setoid.Algebras.Products][] module of the [agda-algebras][] library.)

\begin{code}

module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)
 Domain (⨅ 𝒜) =
  record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
          ; _≈_ = λ a b → ∀ i → (Setoid._≈_ 𝔻[ 𝒜 i ]) (a i)(b i)
          ; isEquivalence =
            record  { refl   = λ i →      IsEquivalence.refl   (isEquivalence 𝔻[ 𝒜 i ])
                    ; sym    = λ x i →    IsEquivalence.sym    (isEquivalence 𝔻[ 𝒜 i ])(x i)
                    ; trans  = λ x y i →  IsEquivalence.trans  (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i) }}
 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong (Interp (𝒜 i)) (≡.refl , flip f=g i )
\end{code}





<!-- ------------------------------------------------------------------------------------- -->

## <a id="Homomorphisms">Homomorphisms</a>
### <a id="homomorphism-basic-definitions">Basic definitions</a>
Here are some useful definitions and theorems extracted from the [Setoid.Homomorphisms.Basic][] module of the [agda-algebras][] library.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 private ov = 𝓞 ⊔ 𝓥 ; a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ ; c = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map-op h f = ∀ {a} → (h ⟨$⟩ ((f ̂ 𝑨) a)) ≈₂ ((f ̂ 𝑩) (λ x → (h ⟨$⟩ (a x))))
  where  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ )

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type (ov ⊔ α ⊔ ρᵇ)
 compatible-map h = ∀ {f} → compatible-map-op h f

 -- The property of being a homomorphism.
 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (ov ⊔ α ⊔ ρᵇ) where
  constructor mkhom
  field compatible : compatible-map h

 -- The type of homomorphisms.
 hom : Type c
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom
\end{code}


### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

\begin{code}

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (ov ⊔ a ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h

  HomReduct : hom
  HomReduct = h , isHom

 mon : Type c
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (ov ⊔ α ⊔ b) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h

  HomReduct : hom
  HomReduct = h , isHom

 epi : Type c
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi

open IsHom ; open IsMon ; open IsEpi

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
\end{code}


### <a id="basic-properties-of-homomorphisms">Basic properties of homomorphisms</a>

Here are some definitions and theorems extracted from the [Setoid.Homomorphisms.Properties][] module of the [agda-algebras][] library.


#### <a id="composition-of-homomorphisms">Composition of homomorphisms</a>

The composition of homomorphisms is again a homomorphism. Similarly,
the composition of epimorphisms is again an epimorphism.

\begin{code}

module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ}
          {g : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]}{h : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑪 ]} where

  open Setoid 𝔻[ 𝑪 ] using ( trans )

  ∘-is-hom : IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-hom ghom hhom = mkhom c
   where
   c : compatible-map 𝑨 𝑪 (h ⟨∘⟩ g)
   c = trans (cong h (compatible ghom)) (compatible hhom)

  ∘-is-epi : IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-epi gE hE = record  { isHom = ∘-is-hom (isHom gE) (isHom hE)
                           ; isSurjective = ∘-IsSurjective g h (isSurjective gE) (isSurjective hE) }


module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where

  ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ∘-hom (h , hhom) (g , ghom) = (g ⟨∘⟩ h) , ∘-is-hom hhom ghom

  ∘-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ∘-epi (h , hepi) (g , gepi) = (g ⟨∘⟩ h) , ∘-is-epi hepi gepi
\end{code}


#### <a id="universe-lifting-of-homomorphisms">Universe lifting of homomorphisms</a>

First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}[hide]

𝒾𝒹 : {𝑨 : Algebra α ρᵃ} → hom 𝑨 𝑨
𝒾𝒹 {𝑨 = 𝑨} = 𝑖𝑑 , mkhom (reflexive ≡.refl) where open Setoid ( Domain 𝑨 ) using ( reflexive )

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 open Setoid 𝔻[ 𝑨 ]              using ( reflexive )  renaming ( _≈_ to _≈₁_ ; refl to refl₁ )
 open Setoid 𝔻[ Lift-Algˡ 𝑨 ℓ ]  using ()             renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid 𝔻[ Lift-Algʳ 𝑨 ℓ ]  using ()             renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)
 open Level

 ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ = record { f = lift ; cong = id } , mkhom (reflexive ≡.refl)

 FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = record { f = lower ; cong = id } , mkhom reflˡ

 ToFromLiftˡ : ∀ b →  (∣ ToLiftˡ ∣ ⟨$⟩ (∣ FromLiftˡ ∣ ⟨$⟩ b)) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → (∣ FromLiftˡ ∣ ⟨$⟩ (∣ ToLiftˡ ∣ ⟨$⟩ a)) ≈₁ a
 FromToLiftˡ a = refl₁

 ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ = record { f = id ; cong = lift } , mkhom (lift (reflexive ≡.refl))

 FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ = record { f = id ; cong = lower } , mkhom reflˡ

 ToFromLiftʳ : ∀ b → (∣ ToLiftʳ ∣ ⟨$⟩ (∣ FromLiftʳ ∣ ⟨$⟩ b)) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → (∣ FromLiftʳ ∣ ⟨$⟩ (∣ ToLiftʳ ∣ ⟨$⟩ a)) ≈₁ a
 FromToLiftʳ a = refl₁


module _ {𝑨 : Algebra α ρᵃ}{ℓ r : Level} where
 open  Setoid 𝔻[ 𝑨 ]               using ( refl )
 open  Setoid 𝔻[ Lift-Alg 𝑨 ℓ r ]  using ( _≈_ )
 open  Level

 ToLift : hom 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift = ∘-hom ToLiftˡ ToLiftʳ

 FromLift : hom (Lift-Alg 𝑨 ℓ r) 𝑨
 FromLift = ∘-hom FromLiftʳ FromLiftˡ

 ToFromLift : ∀ b → (∣ ToLift ∣ ⟨$⟩ (∣ FromLift ∣ ⟨$⟩ b)) ≈ b
 ToFromLift b = lift refl

 ToLift-epi : epi 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift-epi = ∣ ToLift ∣ ,  record { isHom = ∥ ToLift ∥
                            ; isSurjective = λ {y} → eq (∣ FromLift ∣ ⟨$⟩ y) (ToFromLift y) }
\end{code}


<!--

### <a id="homomorphisms-of-product-algebras">Homomorphisms of product algebras</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.
If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.  Here is how we implement these notions in dependent type theory (cf. the [Setoid.Homomorphisms.Products][] module of the [agda-algebras][] library).

-->

\begin{code}[hide]

module _ {ι : Level}{I : Type ι}{𝑨 : Algebra α ρᵃ}(ℬ : I → Algebra β ρᵇ)  where
 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom
  where
  h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
  _⟨$⟩_ h = λ a i → ∣ 𝒽 i ∣ ⟨$⟩ a
  cong h xy i = cong ∣ 𝒽 i ∣ xy
  hhom : IsHom 𝑨 (⨅ ℬ) h
  compatible hhom = λ i → compatible ∥ 𝒽 i ∥
\end{code}



### <a id="factorization-of-homomorphisms">Factorization of homomorphisms</a>

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `φ : hom 𝑪 𝑩` such that `g = φ ∘ h` (cf. the [Setoid.Homomorphisms.Factor][] module of the [agda-algebras][] library).

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ){𝑪 : Algebra γ ρᶜ}
         (gh : hom 𝑨 𝑩)(hh : hom 𝑨 𝑪) where
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ ; sym to sym₂ )
 open Setoid 𝔻[ 𝑪 ] using ( trans ) renaming ( _≈_ to _≈₃_ ; sym to sym₃ )
 open SetoidReasoning 𝔻[ 𝑩 ]
 private gfunc = ∣ gh ∣ ; g = _⟨$⟩_ gfunc ; hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 HomFactor :  kernel _≈₃_ h ⊆ kernel _≈₂_ g → IsSurjective hfunc
  →           Σ[ φ ∈ hom 𝑪 𝑩 ] ∀ a → (g a) ≈₂ ∣ φ ∣ ⟨$⟩ (h a)

 HomFactor Khg hE = (φmap , φhom) , gφh
  where
  kerpres : ∀ a₀ a₁ → h a₀ ≈₃ h a₁ → g a₀ ≈₂ g a₁
  kerpres a₀ a₁ hyp = Khg hyp

  h⁻¹ : 𝕌[ 𝑪 ] → 𝕌[ 𝑨 ]
  h⁻¹ = SurjInv hfunc hE

  η : ∀ {c} → h (h⁻¹ c) ≈₃ c
  η = InvIsInverseʳ hE

  ζ : ∀{x y} → x ≈₃ y → h (h⁻¹ x) ≈₃ h (h⁻¹ y)
  ζ xy = trans η (trans xy (sym₃ η))

  φmap : 𝔻[ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
  _⟨$⟩_ φmap = g ∘ h⁻¹
  cong φmap = Khg ∘ ζ
  open _⟶_ φmap using () renaming (cong to φcong)

  gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φmap ⟨$⟩ (h a)
  gφh a = Khg (sym₃ η)

  φcomp : compatible-map 𝑪 𝑩 φmap
  φcomp {f}{c} =
   begin
    φmap ⟨$⟩ ((f ̂ 𝑪) c)            ≈˘⟨  φcong (cong (Interp 𝑪) (≡.refl , λ _ → η))  ⟩
    g (h⁻¹ ((f ̂ 𝑪)(h ∘ h⁻¹ ∘ c)))  ≈˘⟨  φcong (compatible ∥ hh ∥)                   ⟩
    g (h⁻¹ (h ((f ̂ 𝑨)(h⁻¹ ∘ c))))  ≈˘⟨  gφh ((f ̂ 𝑨)(h⁻¹ ∘ c))                      ⟩
    g ((f ̂ 𝑨)(h⁻¹ ∘ c))            ≈⟨   compatible ∥ gh ∥                           ⟩
    (f ̂ 𝑩)(g ∘ (h⁻¹ ∘ c))          ∎

  φhom : IsHom 𝑪 𝑩 φmap
  compatible φhom = φcomp
\end{code}



### <a id="isomorphisms">Isomorphisms</a>

(cf. the [Setoid.Homomorphisms.Isomorphisms] of the [agda-algebras][] library).

Two structures are *isomorphic* provided there are homomorphisms going back and forth between them which compose to the identity map.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; sym ; trans )
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ ; sym to symᵇ ; trans to transᵇ)

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ) where
  constructor mkiso
  field
   to : hom 𝑨 𝑩
   from : hom 𝑩 𝑨
   to∼from : ∀ b → (∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ b)) ≈ᵇ b
   from∼to : ∀ a → (∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ a)) ≈ a

  toIsSurjective : IsSurjective ∣ to ∣
  toIsSurjective {y} = eq (∣ from ∣ ⟨$⟩ y) (symᵇ (to∼from y))

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x} {y} xy = Goal
   where
   ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
   ξ = cong ∣ from ∣ xy
   Goal : x ≈ y
   Goal = trans (sym (from∼to x)) (trans ξ (from∼to y))

  fromIsSurjective : IsSurjective ∣ from ∣
  fromIsSurjective {y} = eq (∣ to ∣ ⟨$⟩ y) (sym (from∼to y))

  fromIsInjective : IsInjective ∣ from ∣
  fromIsInjective {x} {y} xy = Goal
   where
   ξ : ∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ x) ≈ᵇ ∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ y)
   ξ = cong ∣ to ∣ xy
   Goal : x ≈ᵇ y
   Goal = transᵇ (symᵇ (to∼from x)) (transᵇ ξ (to∼from y))

open _≅_
\end{code}


#### <a id="properties-of-isomorphisms">Properties of isomorphisms</a>

\begin{code}

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl
 where open Setoid 𝔻[ 𝑨 ] using ( refl )

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ})(_≅_{β}{ρᵇ})(_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
 where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; trans )
  open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈ᶜ_ ; trans to transᶜ )
  f : hom 𝑨 𝑪
  f = ∘-hom (to ab) (to bc)
  g : hom 𝑪 𝑨
  g = ∘-hom (from bc) (from ab)
  τ : ∀ b → (∣ f ∣  ⟨$⟩ (∣ g ∣ ⟨$⟩ b)) ≈ᶜ b
  τ b = transᶜ (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)
  ν : ∀ a → (∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a)) ≈ a
  ν a = trans (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)

\end{code}

Fortunately, the lift operation preserves isomorphism (i.e., it's an *algebraic invariant*). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of Agda's universe hierarchy.

\begin{code}[hide]
module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})

 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ
\end{code}


### Homomorphic Images

We begin with what for our purposes is the most useful way to represent the class of *homomorphic images* of an algebra in dependent type theory (cf. the [Setoid.Homomorphisms.HomomorphicImages][] module of
the [agda-algebras][] library). (The first definition is merely a short-hand.)

\begin{code}
ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : Algebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : Algebra α ρ`, the type `HomImages 𝑨` denotes the class of algebras `𝑩 : Algebra β ρ` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.

\begin{code}[hide]
module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 Lift-HomImage-lemma : ∀{γ} → (Lift-Alg 𝑨 γ γ) IsHomImageOf 𝑩 → 𝑨 IsHomImageOf 𝑩
 Lift-HomImage-lemma {γ} φ = ∘-hom ∣ φ ∣ (from Lift-≅) ,
                             ∘-IsSurjective _ _ ∥ φ ∥ (fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

module _ {𝑨 𝑨' : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 HomImage-≅ : 𝑨 IsHomImageOf 𝑨' → 𝑨 ≅ 𝑩 → 𝑩 IsHomImageOf 𝑨'
 HomImage-≅ φ A≅B = ∘-hom ∣ φ ∣ (to A≅B) , ∘-IsSurjective _ _ ∥ φ ∥ (toIsSurjective A≅B)
\end{code}




<!-- ------------------------------------------------------------------------------------- -->

## <a id="subalgebras">Subalgebras</a>
### <a id="subalgebras-basic-definitions">Basic definitions</a>

\begin{code}

_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
\end{code}

### <a id="subalgebras-basic-properties">Basic properties</a>

\begin{code}

≤-reflexive : {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id

mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} where
 ≤-trans : 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans ( f , finj ) ( g , ginj ) = (∘-hom f g ) , ∘-IsInjective ∣ f ∣ ∣ g ∣ finj ginj

 ≅-trans-≤ : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-IsInjective ∣ to A≅B ∣ ∣ h ∣ (toIsInjective A≅B) hinj)
\end{code}

### <a id="products-of-subalgebras">Products of subalgebras</a>

\begin{code}

module _ {ι : Level} {I : Type ι}{𝒜 : I → Algebra α ρᵃ}{ℬ : I → Algebra β ρᵇ} where

 ⨅-≤ : (∀ i → ℬ i ≤ 𝒜 i) → ⨅ ℬ ≤ ⨅ 𝒜
 ⨅-≤ B≤A = (hfunc , hhom) , hM
  where
  hi : ∀ i → hom (ℬ i) (𝒜 i)
  hi i = ∣ B≤A i ∣

  hfunc : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
  (hfunc ⟨$⟩ x) i = ∣ hi i ∣ ⟨$⟩ (x i)
  cong hfunc = λ xy i → cong ∣ hi i ∣ (xy i)

  hhom : IsHom (⨅ ℬ) (⨅ 𝒜) hfunc
  compatible hhom = λ i → compatible ∥ hi i ∥

  hM : IsInjective hfunc
  hM = λ xy i → ∥ B≤A i ∥ (xy i)
\end{code}




<!-- ------------------------------------------------------------------------------------- -->

## Terms

### <a id="terms-basic-definitions">Basic definitions</a>

Fix a signature `𝑆` and let `X` denote an arbitrary nonempty collection of variable symbols. Assume the symbols in `X` are distinct from the operation symbols of `𝑆`, that is `X ∩ ∣ 𝑆 ∣ = ∅`.

By a *word* in the language of `𝑆`, we mean a nonempty, finite sequence of members of `X ∪ ∣ 𝑆 ∣`. We denote the concatenation of such sequences by simple juxtaposition.

Let `S₀` denote the set of nullary operation symbols of `𝑆`. We define by induction on `n` the sets `𝑇ₙ` of *words* over `X ∪ ∣ 𝑆 ∣` as follows (cf. [Bergman (2012)][] Def. 4.19):

`𝑇₀ := X ∪ S₀` and `𝑇ₙ₊₁ := 𝑇ₙ ∪ 𝒯ₙ`

where `𝒯ₙ` is the collection of all `f t` such that `f : ∣ 𝑆 ∣` and `t : ∥ 𝑆 ∥ f → 𝑇ₙ`. (Recall, `∥ 𝑆 ∥ f` is the arity of the operation symbol f.)

We define the collection of *terms* in the signature `𝑆` over `X` by `Term X := ⋃ₙ 𝑇ₙ`. By an 𝑆-*term* we mean a term in the language of `𝑆`.

The definition of `Term X` is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.
\begin{code}

data Term (X : Type χ ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X
open Term

\end{code}

This is a very basic inductive type that represents each term as a tree with an operation symbol at each `node` and a variable symbol at each leaf (`generator`); hence the constructor names (`ℊ` for "generator" and `node` for node).

**Notation**. As usual, the type `X` represents an arbitrary collection of variable symbols. Recall, `ov χ` is our shorthand notation for the universe level `𝓞 ⊔ 𝓥 ⊔ lsuc χ`.


### <a id="equality-of-terms">Equality of terms</a>

We take a different approach here, using Setoids instead of quotient types.
That is, we will define the collection of terms in a signature as a setoid
with a particular equality-of-terms relation, which we must define.
Ultimately we will use this to define the (absolutely free) term algebra
as a Algebra whose carrier is the setoid of terms.

\begin{code}

module _ {X : Type χ } where

 data _≐_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≐ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≐ (t i)) → (node f s) ≐ (node f t)

\end{code}

It is easy to show that the equality-of-terms relation `_≐_` is an equivalence relation, so we omit the formal proof. (See the [Setoid.Terms.Basic][] module of the [agda-algebras][] library for details.)

\begin{code}[hide]
 ≐-isRefl : Reflexive _≐_
 ≐-isRefl {ℊ _} = rfl ≡.refl
 ≐-isRefl {node _ _} = gnl (λ _ → ≐-isRefl)

 ≐-isSym : Symmetric _≐_
 ≐-isSym (rfl x) = rfl (≡.sym x)
 ≐-isSym (gnl x) = gnl (λ i → ≐-isSym (x i))

 ≐-isTrans : Transitive _≐_
 ≐-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≐-isTrans (gnl x) (gnl y) = gnl (λ i → ≐-isTrans (x i) (y i))

 ≐-isEquiv : IsEquivalence _≐_
 ≐-isEquiv = record { refl = ≐-isRefl ; sym = ≐-isSym ; trans = ≐-isTrans }
\end{code}


### <a id="the-term-algebra">The term algebra</a>

For a given signature `𝑆`, if the type `Term X` is nonempty (equivalently, if `X` or `∣ 𝑆 ∣` is nonempty), then we can define an algebraic structure, denoted by `𝑻 X` and called the *term algebra in the signature* `𝑆` *over* `X`.  Terms are viewed as acting on other terms, so both the domain and basic operations of the algebra are the terms themselves.


+ For each operation symbol `f : ∣ 𝑆 ∣`, denote by `f ̂ (𝑻 X)` the operation on `Term X` that maps a tuple `t : ∥ 𝑆 ∥ f → ∣ 𝑻 X ∣` to the formal term `f t`.
+ Define `𝑻 X` to be the algebra with universe `∣ 𝑻 X ∣ := Term X` and operations `f ̂ (𝑻 X)`, one for each symbol `f` in `∣ 𝑆 ∣`.

In [Agda][] the term algebra can be defined as simply as one might hope.

\begin{code}

TermSetoid : (X : Type χ) → Setoid (ov χ) (ov χ)
TermSetoid X = record { Carrier = Term X ; _≈_ = _≐_ ; isEquivalence = ≐-isEquiv }

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Algebra.Domain (𝑻 X) = TermSetoid X
Algebra.Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Algebra.Interp (𝑻 X)) (≡.refl , ss≐ts) = gnl ss≐ts
\end{code}

### <a id="interpretation-of-terms">Interpretation of terms</a>

The approach to terms and their interpretation in this module was inspired by
[Andreas Abel's formal proof of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).

A substitution from `X` to `Y` associates a term in `X` with each variable in `Y`.  The definition of `Sub` given here is essentially the same as the one given by Andreas Abel, as is the recursive definition of the syntax `t [ σ ]`, which denotes a term `t` applied to a substitution `σ`.

\begin{code}

Sub : Type χ → Type χ → Type (ov χ)
Sub X Y = (y : Y) → Term X

_[_] : {X Y : Type χ}(t : Term Y) (σ : Sub X Y) → Term X
(ℊ x) [ σ ] = σ x
(node f ts) [ σ ] = node f (λ i → ts i [ σ ])

\end{code}

An environment for an algebra `𝑨` in a context `X` is a map that assigns to each variable `x : X` an element in the domain of `𝑨`, packaged together with an equality of environments, which is simply pointwise equality (relatively to the setoid equality of the underlying domain of `𝑨`).

\begin{code}

module Environment (𝑨 : Algebra α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )
 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ ρ' → (x : X) → ρ x ≈ ρ' x
                 ; isEquivalence = record  { refl   = λ _ → refl
                                           ; sym    = λ h x → sym (h x)
                                           ; trans  = λ g h x → trans (g x)(h x) }}

\end{code}

Next we define *evaluation of a term* in an environment `ρ`, interpreted in the algebra `𝑨`.

\begin{code}

 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧ ⟨$⟩ ρ = ρ x
 ⟦ node f args ⟧ ⟨$⟩ ρ = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v = u≈v x
 cong ⟦ node f args ⟧ x≈y = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

\end{code}

An equality between two terms holds in a model if the two terms are equal under all valuations of their free variables (cf. [Andreas Abel's formal proof of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)).

\begin{code}

 Equal : ∀ {X : Type χ} (s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) →  ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

 ≐→Equal : {X : Type χ}(s t : Term X) → s ≐ t → Equal s t
 ≐→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≐→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≐→Equal(s i)(t i)(x i)ρ )

\end{code}

The proof that `Equal` is an equivalence relation is trivial, so we omit it. (See the [Setoid.Varieties.SoundAndComplete][] module of the [agda-algebras][] library for details.)

\begin{code}[hide]
 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 IsEquivalence.refl  EqualIsEquiv = λ _ → refl
 IsEquivalence.sym   EqualIsEquiv = λ x=y ρ → sym (x=y ρ)
 IsEquivalence.trans EqualIsEquiv = λ ij jk ρ → trans (ij ρ) (jk ρ)
\end{code}

Evaluation of a substitution gives an environment (cf. [Andreas Abel's formal proof of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf))

\begin{code}

 ⟦_⟧s : {X Y : Type χ} → Sub X Y → Carrier(Env X) → Carrier (Env Y)
 ⟦ σ ⟧s ρ x = ⟦ σ x ⟧ ⟨$⟩ ρ

\end{code}

Next we prove that ⟦t[σ]⟧ρ ≃ ⟦t⟧⟦σ⟧ρ (cf. [Andreas Abel's formal proof of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)).

\begin{code}

 substitution : {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : Carrier( Env X ) )
  →             ⟦ t [ σ ] ⟧ ⟨$⟩ ρ  ≈  ⟦ t ⟧ ⟨$⟩ (⟦ σ ⟧s ρ)

 substitution (ℊ x) σ ρ = refl
 substitution (node f ts) σ ρ = cong (Interp 𝑨)(≡.refl , λ i → substitution (ts i) σ ρ)
\end{code}


### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Setoid 𝔻[ 𝑩 ] using ( _≈_ ; refl )
 open SetoidReasoning 𝔻[ 𝑩 ]
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc
 open Environment 𝑨 using ( ⟦_⟧ )
 open Environment 𝑩 using () renaming ( ⟦_⟧ to ⟦_⟧ᴮ )

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a = goal
  where
  goal : h (⟦ node f t ⟧ ⟨$⟩ a) ≈ (⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a))
  goal = begin
          h (⟦ node f t ⟧ ⟨$⟩ a)              ≈⟨  compatible ∥ hh ∥                                     ⟩
          (f ̂ 𝑩)(λ i → h (⟦ t i ⟧ ⟨$⟩ a))     ≈⟨  cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term (t i) a)  ⟩
          (f ̂ 𝑩)(λ i → ⟦ t i ⟧ᴮ ⟨$⟩ (h ∘ a))  ≈⟨  refl                                                  ⟩
          (⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a))         ∎
\end{code}

<!--
### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>
-->
\begin{code}[hide]
module _ {X : Type χ}{ι : Level} {I : Type ι} (𝒜 : I → Algebra α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ] using ( _≈_ )
 open Environment (⨅ 𝒜) using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment using ( ⟦_⟧ ; ≐→Equal )

 interp-prod : (p : Term X) → ∀ ρ → ⟦ p ⟧₁ ⟨$⟩ ρ ≈ (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (ρ x) i))
 interp-prod (ℊ x) = λ ρ i → ≐→Equal (𝒜 i) (ℊ x) (ℊ x) ≐-isRefl λ x' → (ρ x) i
 interp-prod (node f t) = λ ρ i → cong (Interp (⨅ 𝒜))(≡.refl , (λ j k → interp-prod (t j) ρ k)) i
\end{code}





<!-- ------------------------------------------------------------------------------------- -->

## <a id="model-theory-and-equational-logic">Model Theory and Equational Logic</a>

(cf. the [Setoid.Varieties.SoundAndComplete][] module of the [agda-algebras][] library)

### <a id="model-theory-basic-definitions">Basic definitions</a>

Let `𝑆` be a signature. By an *identity* or *equation* in `𝑆` we mean an ordered pair of terms in a given context.  For instance, if the context happens to be the type `X : Type χ`, then an equation will be a pair of inhabitants of the domain of term algebra `𝑻 X`.

We define an equation in Agda using the following record type with fields denoting the left-hand and right-hand sides of the equation, along with an equation "context" representing the underlying collection of variable symbols (cf. [Andreas Abel's formal proof of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)).

\begin{code}

record Eq : Type (ov χ) where
 constructor _≈̇_
 field  {cxt}  : Type χ
        lhs    : Term cxt
        rhs    : Term cxt

open Eq public

\end{code}

We now define a type representing the notion of an equation `p ≈̇ q` holding (when `p` and `q` are interpreted) in algebra `𝑨`.

If `𝑨` is an `𝑆`-algebra we say that `𝑨` *satisfies* `p ≈ q` provided for all environments `ρ : X → ∣ 𝑨 ∣` (assigning values in the domain of `𝑨` to variable symbols in `X`) we have `⟦ p ⟧⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ`.  In this situation, we write `𝑨 ⊧ (p ≈̇ q)` and say that `𝑨` *models* the identity `p ≈ q`.

If `𝒦` is a class of algebras, all of the same signature, we write `𝒦 ⊫ (p ≈̇ q) if, for every `𝑨 ∈ 𝒦`, we have `𝑨 ⊧ (p ≈̇ q)`.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations `⊧` and `≈`. As a reasonable alternative to what we would normally express informally as `𝒦 ⊧ p ≈ q`, we have settled on `𝒦 ⊫ (p ≈̇ q)` to denote this relation.  To reiterate, if `𝒦` is a class of `𝑆`-algebras, we write `𝒦 ⊫ (p ≈̇ q)` provided every `𝑨 ∈ 𝒦` satisfies `𝑨 ⊧ (p ≈̇ q)`.

\begin{code}

_⊧_ : (𝑨 : Algebra α ρᵃ)(term-identity : Eq{χ}) → Type _
𝑨 ⊧ (p ≈̇ q) = Equal p q where open Environment 𝑨

_⊫_ : Pred (Algebra α ρᵃ) ℓ → Eq{χ} → Type (ℓ ⊔ χ ⊔ ov(α ⊔ ρᵃ))
𝒦 ⊫ equ = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ equ

\end{code}

We denote by `𝑨 ⊨ ℰ` the assertion that the algebra 𝑨 models every equation in a collection `ℰ` of equations.

\begin{code}

_⊨_ : (𝑨 : Algebra α ρᵃ) → {ι : Level}{I : Type ι} → (I → Eq{χ}) → Type _
𝑨 ⊨ ℰ = ∀ i → Equal (lhs (ℰ i))(rhs (ℰ i)) where open Environment 𝑨
\end{code}

### <a id="equational-theories-and-models">Equational theories and models</a>

If `𝒦` denotes a class of structures, then `Th 𝒦` represents the set of identities
modeled by the members of `𝒦`.

\begin{code}

Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ (p ≈̇ q)

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨
\end{code}

### <a id="the-entailment-relation">The entailment relation</a>

Based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

\begin{code}

module _ {χ ι : Level} where

 data _⊢_▹_≈_ {I : Type ι}(ℰ : I → Eq) : (X : Type χ)(p q : Term X) → Type (ι ⊔ ov χ) where
  hyp : ∀ i → let p ≈̇ q = ℰ i in ℰ ⊢ _ ▹ p ≈ q
  app : ∀ {ps qs} → (∀ i → ℰ ⊢ Γ ▹ ps i ≈ qs i) → ℰ ⊢ Γ ▹ (node 𝑓 ps) ≈ (node 𝑓 qs)
  sub : ∀ {p q} → ℰ ⊢ Δ ▹ p ≈ q → ∀ (σ : Sub Γ Δ) → ℰ ⊢ Γ ▹ (p [ σ ]) ≈ (q [ σ ])

  ⊢refl   : ∀ {p}               → ℰ ⊢ Γ ▹ p ≈ p
  ⊢sym    : ∀ {p q : Term Γ}    → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ p
  ⊢trans  : ∀ {p q r : Term Γ}  → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ r → ℰ ⊢ Γ ▹ p ≈ r

 ⊢▹≈IsEquiv : {X : Type χ}{I : Type ι}{ℰ : I → Eq} → IsEquivalence (ℰ ⊢ X ▹_≈_)
 ⊢▹≈IsEquiv = record { refl = ⊢refl ; sym = ⊢sym ; trans = ⊢trans }
\end{code}

### <a id="soundness">Soundness</a>

In any model 𝑨 that satisfies the equations ℰ, derived equality is actual equality
(cf. [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

\begin{code}

module Soundness  {χ α ι : Level}{I : Type ι} (ℰ : I → Eq{χ})
                  (𝑨 : Algebra α ρᵃ)     -- We assume an algebra 𝑨
                  (V : 𝑨 ⊨ ℰ)            -- that models all equations in ℰ.
                  where

 open SetoidReasoning 𝔻[ 𝑨 ]
 open Environment 𝑨
 open IsEquivalence using ( refl ; sym ; trans )

 sound : ∀ {p q} → ℰ ⊢ Γ ▹ p ≈ q → 𝑨 ⊧ (p ≈̇ q)
 sound (hyp i) = V i
 sound (app es) ρ = cong (Interp 𝑨) (≡.refl , λ i → sound (es i) ρ)
 sound (sub {p = p}{q} Epq σ) ρ =
  begin
   ⟦ p [ σ ] ⟧ ⟨$⟩         ρ ≈⟨   substitution p σ ρ    ⟩
   ⟦ p       ⟧ ⟨$⟩ ⟦ σ ⟧s  ρ ≈⟨   sound Epq (⟦ σ ⟧s ρ)  ⟩
   ⟦ q       ⟧ ⟨$⟩ ⟦ σ ⟧s  ρ ≈˘⟨  substitution  q σ ρ   ⟩
   ⟦ q [ σ ] ⟧ ⟨$⟩         ρ ∎
 sound ( ⊢refl   {p = p}                 ) = refl   EqualIsEquiv {x = p}
 sound ( ⊢sym    {p = p}{q}     Epq      ) = sym    EqualIsEquiv {x = p}{q}     (sound Epq)
 sound ( ⊢trans  {p = p}{q}{r}  Epq Eqr  ) = trans  EqualIsEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)
\end{code}


### <a id="the-closure-operators-h-s-p-and-v">The Closure Operators H, S, P and V</a>

Fix a signature `𝑆`, let `𝒦` be a class of `𝑆`-algebras, and define

* `H 𝒦` = algebras isomorphic to a homomorphic image of a member of `𝒦`;
* `S 𝒦` = algebras isomorphic to a subalgebra of a member of `𝒦`;
* `P 𝒦` = algebras isomorphic to a product of members of `𝒦`.

A straight-forward verification confirms that `H`, `S`, and `P` are *closure operators* (expansive, monotone, and idempotent).  A class `𝒦` of `𝑆`-algebras is said to be *closed under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, `𝒦` is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`). The operators `H`, `S`, and `P` can be composed with one another repeatedly, forming yet more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under isomorphism.

A *variety* is a class of `𝑆`-algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define a type `V` which represents closure under all three operators, `H`, `S`, and `P`.



We now define the type `H` to represent classes of algebras that include all homomorphic images of algebras in the class---i.e., classes that are closed under the taking of homomorphic images---the type `S` to represent classes of algebras that closed under the taking of subalgebras, and the type `P` to represent classes of algebras closed under the taking of arbitrary products.

\begin{code}

module _  {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ

 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ ⊔ ι))
 P _ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))

\end{code}

A class `𝒦` of `𝑆`-algebras is called a *variety* if it is closed under each of the closure operators `H`, `S`, and `P` defined above. The corresponding closure operator is often denoted `𝕍` or `𝒱`, but we will denote it by `V`.

\begin{code}

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ ; c = γ ⊔ ρᶜ ; d = δ ⊔ ρᵈ

 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) (d ⊔ ov(a ⊔ b ⊔ c ⊔ ℓ ⊔ ι))
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

module _ {α ρᵃ ℓ : Level}(𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ))
         (𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)) where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 V-≅-lc : Lift-Alg 𝑨 ι ι ∈ V{β = ι}{ι} ℓ ι 𝒦 → 𝑨 ∈ V{γ = ι}{ι} ℓ ι 𝒦
 V-≅-lc (𝑨' , spA' , lAimgA') = 𝑨' , (spA' , AimgA')
  where
  AimgA' : 𝑨 IsHomImageOf 𝑨'
  AimgA' = Lift-HomImage-lemma lAimgA'
\end{code}


#### <a id="idempotence-of-s">Idempotence of S</a>

`S` is a closure operator.  The facts that S is monotone and expansive won't be needed, so we omit the proof of these facts.  However, we will make use of idempotence of `S`, so we prove that property as follows.

\begin{code}

S-idem : {𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}
 →       S{β = γ}{ρᶜ} (α ⊔ ρᵃ  ⊔ ℓ) (S{β = β}{ρᵇ} ℓ 𝒦) ⊆ S{β = γ}{ρᶜ} ℓ 𝒦

S-idem (𝑨 , (𝑩 , sB , A≤B) , x≤A) = 𝑩 , (sB , ≤-trans x≤A A≤B)
\end{code}

#### <a id="algebraic-invariance-of-models">Algebraic invariance of ⊧</a>

The binary relation `⊧` would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism). Let us now verify that the models relation we defined above has this essential property.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where

 ⊧-I-invar : 𝑨 ⊧ (p ≈̇ q)  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ (p ≈̇ q)
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ =
  begin
   ⟦ p ⟧₂ ⟨$⟩ ρ              ≈˘⟨  cong ⟦ p ⟧₂ (λ x → f∼g (ρ x))  ⟩
   ⟦ p ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)     ⟩
   f (⟦ p ⟧₁ ⟨$⟩ (g ∘ ρ))    ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))      ⟩
   f (⟦ q ⟧₁ ⟨$⟩ (g ∘ ρ))    ≈⟨   comm-hom-term fh q (g ∘ ρ)     ⟩
   ⟦ q ⟧₂ ⟨$⟩ (f ∘ (g ∘ ρ))  ≈⟨   cong ⟦ q ⟧₂ (λ x → f∼g (ρ x))  ⟩
   ⟦ q ⟧₂ ⟨$⟩ ρ              ∎
  where
  open Environment 𝑨     using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment 𝑩     using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
  open SetoidReasoning 𝔻[ 𝑩 ]
  private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
\end{code}

#### <a id="subalgebraic-invariance-of-models">Subalgebraic invariance of ⊧</a>
Identities modeled by an algebra `𝑨` are also modeled by every subalgebra of `𝑨`, which fact can be formalized as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where

 ⊧-S-invar : 𝑨 ⊧ (p ≈̇ q) →  𝑩 ≤ 𝑨  →  𝑩 ⊧ (p ≈̇ q)
 ⊧-S-invar Apq B≤A b = goal
  where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
  open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧ᵃ )
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ )
  open Environment 𝑩 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]
  hh : hom 𝑩 𝑨
  hh = ∣ B≤A ∣
  h = _⟨$⟩_ ∣ hh ∣
  ξ : ∀ b → h (⟦ p ⟧ ⟨$⟩ b) ≈ h (⟦ q ⟧ ⟨$⟩ b)
  ξ b = begin
         h (⟦ p ⟧ ⟨$⟩ b)     ≈⟨ comm-hom-term hh p b   ⟩
         ⟦ p ⟧ᵃ ⟨$⟩ (h ∘ b)  ≈⟨ Apq (h ∘ b)            ⟩
         ⟦ q ⟧ᵃ ⟨$⟩ (h ∘ b)  ≈˘⟨ comm-hom-term hh q b  ⟩
         h (⟦ q ⟧ ⟨$⟩ b)     ∎
  goal : ⟦ p ⟧ ⟨$⟩ b ≈ᵇ ⟦ q ⟧ ⟨$⟩ b
  goal = ∥ B≤A ∥ (ξ b)
\end{code}

#### <a id="product-invariance-of-models">Product invariance of ⊧</a>
An identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in that collection.

 \begin{code}


module _ {X : Type χ}{I : Type ℓ}(𝒜 : I → Algebra α ρᵃ){p q : Term X} where

 ⊧-P-invar : (∀ i → 𝒜 i ⊧ (p ≈̇ q)) → ⨅ 𝒜 ⊧ (p ≈̇ q)
 ⊧-P-invar 𝒜pq a = goal
  where
  open Environment (⨅ 𝒜) using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ] using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]
  ξ : (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (a x) i)) ≈ (λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ (λ x → (a x) i))
  ξ = λ i → 𝒜pq i (λ x → (a x) i)
  goal : ⟦ p ⟧₁ ⟨$⟩ a ≈ ⟦ q ⟧₁ ⟨$⟩ a
  goal = begin
          ⟦ p ⟧₁ ⟨$⟩ a                             ≈⟨ interp-prod 𝒜 p a   ⟩
          (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (a x) i))  ≈⟨ ξ                   ⟩
          (λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ (λ x → (a x) i))  ≈˘⟨ interp-prod 𝒜 q a  ⟩
          ⟦ q ⟧₁ ⟨$⟩ a                             ∎
\end{code}


#### <a id="PS-subset-SP">PS ⊆ SP</a>

Another important fact we will need about the operators `S` and `P` is that a product of subalgebras of algebras in a class `𝒦` is a subalgebra of a product of algebras in `𝒦`. We denote this inclusion by `PS⊆SP`, which we state and prove as follows.

\begin{code}

module _  {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private
  a = α ⊔ ρᵃ
  oaℓ = ov (a ⊔ ℓ)

 PS⊆SP : P (a ⊔ ℓ) oaℓ (S{β = α}{ρᵃ} ℓ 𝒦) ⊆ S oaℓ (P ℓ oaℓ 𝒦)
 PS⊆SP {𝑩} (I , ( 𝒜 , sA , B≅⨅A )) = Goal
  where
  ℬ : I → Algebra α ρᵃ
  ℬ i = ∣ sA i ∣
  kB : (i : I) → ℬ i ∈ 𝒦
  kB i =  fst ∥ sA i ∥
  ⨅A≤⨅B : ⨅ 𝒜 ≤ ⨅ ℬ
  ⨅A≤⨅B = ⨅-≤ λ i → snd ∥ sA i ∥
  Goal : 𝑩 ∈ S{β = oaℓ}{oaℓ}oaℓ (P {β = oaℓ}{oaℓ} ℓ oaℓ 𝒦)
  Goal = ⨅ ℬ , (I , (ℬ , (kB , ≅-refl))) , (≅-trans-≤ B≅⨅A ⨅A≤⨅B)
\end{code}

#### <a id="identity-preservation">Identity preservation</a>

The classes `H 𝒦`, `S 𝒦`, `P 𝒦`, and `V 𝒦` all satisfy the same set of equations.  We will only use a subset of the inclusions used to prove this fact. (For a complete proof, see the
[Setoid.Varieties.Preservation][] module of the [agda-algebras][] library.)


##### <a id="h-preserves-identities">H preserves identities</a>

First we prove that the closure operator H is compatible with identities that hold in the given class.

\begin{code}

module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where

 H-id1 : 𝒦 ⊫ (p ≈̇ q) → (H {β = α}{ρᵃ}ℓ 𝒦) ⊫ (p ≈̇ q)
 H-id1 σ 𝑩 (𝑨 , kA , BimgOfA) ρ = B⊧pq
  where
  IH : 𝑨 ⊧ (p ≈̇ q)
  IH = σ 𝑨 kA
  open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁)
  open Environment 𝑩 using ( ⟦_⟧ )
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ )
  open SetoidReasoning 𝔻[ 𝑩 ]

  φ : hom 𝑨 𝑩
  φ = ∣ BimgOfA ∣
  φE : IsSurjective ∣ φ ∣
  φE = ∥ BimgOfA ∥
  φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
  φ⁻¹ = SurjInv ∣ φ ∣ φE

  ζ : ∀ x → (∣ φ ∣ ⟨$⟩ (φ⁻¹ ∘ ρ) x ) ≈ ρ x
  ζ = λ _ → InvIsInverseʳ φE

  B⊧pq : (⟦ p ⟧ ⟨$⟩ ρ) ≈ (⟦ q ⟧ ⟨$⟩ ρ)
  B⊧pq = begin
         ⟦ p ⟧ ⟨$⟩ ρ                                ≈˘⟨ cong ⟦ p ⟧ ζ                 ⟩
         ⟦ p ⟧ ⟨$⟩ (λ x → (∣ φ ∣ ⟨$⟩ (φ⁻¹ ∘ ρ) x))  ≈˘⟨ comm-hom-term φ p (φ⁻¹ ∘ ρ)  ⟩
         ∣ φ ∣ ⟨$⟩ (⟦ p ⟧₁ ⟨$⟩ (φ⁻¹ ∘ ρ))           ≈⟨ cong ∣ φ ∣ (IH (φ⁻¹ ∘ ρ))     ⟩
         ∣ φ ∣ ⟨$⟩ (⟦ q ⟧₁ ⟨$⟩ (φ⁻¹ ∘ ρ))           ≈⟨ comm-hom-term φ q (φ⁻¹ ∘ ρ)   ⟩
         ⟦ q ⟧ ⟨$⟩ (λ x → (∣ φ ∣ ⟨$⟩ (φ⁻¹ ∘ ρ) x))  ≈⟨ cong ⟦ q ⟧ ζ                  ⟩
         ⟦ q ⟧ ⟨$⟩ ρ                                ∎
\end{code}


##### <a id="s-preserves-identities">S preserves identities</a>

\begin{code}

 S-id1 : 𝒦 ⊫ (p ≈̇ q) → (S {β = α}{ρᵃ} ℓ 𝒦) ⊫ (p ≈̇ q)
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

\end{code}

The obvious converse is barely worth the bits needed to formalize it, but we will use it below, so let's prove it now.

\begin{code}

 S-id2 : S ℓ 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))
\end{code}


##### <a id="p-preserves-identities">P preserves identities</a>

\begin{code}

 P-id1 : ∀{ι} → 𝒦 ⊫ (p ≈̇ q) → P {β = α}{ρᵃ}ℓ ι 𝒦 ⊫ (p ≈̇ q)
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
  where
  ih : ∀ i → 𝒜 i ⊧ (p ≈̇ q)
  ih i = σ (𝒜 i) (kA i)
  IH : ⨅ 𝒜 ⊧ (p ≈̇ q)
  IH = ⊧-P-invar 𝒜 {p}{q} ih
\end{code}


##### <a id="v-preserves-identities">V preserves identities</a>

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

\begin{code}

module _ {X : Type χ}{ι : Level}{𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private
  aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

 V-id1 : 𝒦 ⊫ (p ≈̇ q) → V ℓ ι 𝒦 ⊫ (p ≈̇ q)
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA))
   where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ (p ≈̇ q)
   spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)
\end{code}

#### <a id="th-k-subset-th-v">Th 𝒦 ⊆ Th (V 𝒦)</a>

From `V-id1` it follows that if 𝒦 is a class of algebras, then the set of identities modeled by the algebras in `𝒦` is contained in the set of identities modeled by the algebras in `V 𝒦`.  In other terms, `Th 𝒦 ⊆ Th (V 𝒦)`.  We formalize this observation as follows.

\begin{code}

 classIds-⊆-VIds : 𝒦 ⊫ (p ≈̇ q)  → (p , q) ∈ Th (V ℓ ι 𝒦)
 classIds-⊆-VIds pKq 𝑨 = V-id1 pKq 𝑨
\end{code}




<!-- ------------------------------------------------------------------------------------- -->

## <a id="free-algebras">Free Algebras</a>

### <a id="the-absolutely-free-algebra-tx">The absolutely free algebra 𝑻 X</a>

The term algebra `𝑻 X` is *absolutely free* (or *universal*, or *initial*) for algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1. Every function from `𝑋` to `∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2. The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to `∣ 𝑨 ∣` lifts to a map from `∣ 𝑻 X ∣` to `∣ 𝑨 ∣` in a natural way, by induction on the structure of the given term.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; reflexive ; refl ; trans )

 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x) = h x
 free-lift (node f t) = (f ̂ 𝑨) (λ i → free-lift (t i))

 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong
  where
  flcong : ∀ {s t} → s ≐ t →  free-lift s ≈ free-lift t
  flcong (_≐_.rfl x) = reflexive (≡.cong h x)
  flcong (_≐_.gnl x) = cong (Interp 𝑨) (≡.refl , (λ i → flcong (x i)))

\end{code}

Naturally, at the base step of the induction, when the term has the form `generator`
x, the free lift of `h` agrees with `h`.  For the inductive step, when the
given term has the form `node f t`, the free lift is defined as
follows: Assuming (the induction hypothesis) that we know the image of each
subterm `t i` under the free lift of `h`, define the free lift at the
full term by applying `f ̂ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func , hhom
  where
  hfunc : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
  hfunc = free-lift-func

  hcomp : compatible-map (𝑻 X) 𝑨 free-lift-func
  hcomp {f}{a} = cong (Interp 𝑨) (≡.refl , (λ i → (cong free-lift-func){a i} ≐-isRefl))

  hhom : IsHom (𝑻 X) 𝑨 hfunc
  hhom = mkhom (λ{f}{a} → hcomp{f}{a})


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ} where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl )
 open Environment 𝑨 using ( ⟦_⟧ )

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift {𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x) = refl
 free-lift-interp η (node f t) = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
\end{code}

### <a id="the-relatively-free-algebra-f">The relatively free algebra 𝔽</a>

We now define the algebra `𝔽[ X ]`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽[ X ]` from `𝑻 X` to `𝔽[ X ]`.

\begin{code}

module FreeAlgebra {χ : Level}{ι : Level}{I : Type ι}(ℰ : I → Eq) where
 open Algebra

 FreeDomain : Type χ → Setoid _ _
 FreeDomain X = record  { Carrier        = Term X
                        ; _≈_            = ℰ ⊢ X ▹_≈_
                        ; isEquivalence  = ⊢▹≈IsEquiv }
\end{code}

The interpretation of an operation is simply the operation itself.
This works since `ℰ ⊢ X ▹_≈_` is a congruence.

\begin{code}

 FreeInterp : ∀ {X} → ⟨ 𝑆 ⟩ (FreeDomain X) ⟶ FreeDomain X
 FreeInterp ⟨$⟩ (f , ts) = node f ts
 cong FreeInterp (≡.refl , h) = app h

 𝔽[_] : Type χ → Algebra (ov χ) (ι ⊔ ov χ)
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp
\end{code}

### <a id="basic-properties-of-free-algebras">Basic properties of free algebras</a>

In the code below, `X` will play the role of an arbitrary collection of variables; it would suffice to take `X` to be the cardinality of the largest algebra in 𝒦, but since we don't know that cardinality, we leave `X` aribtrary for now.

\begin{code}

module FreeHom (χ : Level) {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(χ ⊔ α ⊔ ρᵃ ⊔ ℓ)
 open Eq

 ℐ : Type ι -- indexes the collection of equations modeled by 𝒦
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

 ℰ⊢[_]▹Th𝒦 : (X : Type χ) → ∀{p q} → ℰ ⊢ X ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
 ℰ⊢[ X ]▹Th𝒦 x 𝑨 kA = sound (λ i ρ → ∥ i ∥ 𝑨 kA ρ) x
  where open Soundness ℰ 𝑨
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
\end{code}


#### <a id="the-natural-epimorphism-from-tx-to-f">The natural epimorphism from 𝑻 X to 𝔽[ X ]</a>
Next we define an epimorphism from `𝑻 X` onto the relatively free algebra `𝔽[ X ]`.  Of course, the kernel of this epimorphism will be the congruence of `𝑻 X` defined by identities modeled by (`S 𝒦`, hence) `𝒦`.

\begin{code}

 epi𝔽[_] : (X : Type χ) → epi (𝑻 X) 𝔽[ X ]
 epi𝔽[ X ] = h , hepi
  where
  open Algebra (𝑻 X) using () renaming (Domain to TX)
  open Setoid TX using () renaming ( _≈_ to _≈₀_ ; refl to refl₀ )
  open Algebra 𝔽[ X ] using () renaming ( Domain to F )
  open Setoid F using () renaming ( _≈_  to _≈₁_ ; refl to refl₁ )
  open _≐_

  c : ∀ {x y} → x ≈₀ y → x ≈₁ y
  c (rfl {x}{y} ≡.refl) = refl₁
  c (gnl {f}{s}{t} x) = cong (Interp 𝔽[ X ]) (≡.refl , c ∘ x)

  h : TX ⟶ F
  h = record { f = id ; cong = c }

  hepi : IsEpi (𝑻 X) 𝔽[ X ] h
  compatible (isHom hepi) = cong h refl₀
  isSurjective hepi {y} = eq y refl₁

 hom𝔽[_] : (X : Type χ) → hom (𝑻 X) 𝔽[ X ]
 hom𝔽[ X ] = IsEpi.HomReduct ∥ epi𝔽[ X ] ∥

 hom𝔽[_]-is-epic : (X : Type χ) → IsSurjective ∣ hom𝔽[ X ] ∣
 hom𝔽[ X ]-is-epic = IsEpi.isSurjective (snd (epi𝔽[ X ]))
\end{code}


#### <a id="the-kernel-of-the-natural-epimorphism">The kernel of the natural epimorphism</a>

\begin{code}

 class-models-kernel : ∀{X p q} → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣ → 𝒦 ⊫ (p ≈̇ q)
 class-models-kernel {X = X}{p}{q} pKq = ℰ⊢[ X ]▹Th𝒦 pKq

 kernel-in-theory : {X : Type χ} → ker ∣ hom𝔽[ X ] ∣ ⊆ Th (V ℓ ι 𝒦)
 kernel-in-theory {X = X} {p , q} pKq vkA x = classIds-⊆-VIds {ℓ = ℓ}{p = p}{q}
                                               (class-models-kernel pKq) vkA x

 module _ {X : Type χ} {𝑨 : Algebra α ρᵃ}{sA : 𝑨 ∈ S {β = α}{ρᵃ} ℓ 𝒦} where
  open Environment 𝑨 using ( Equal )
  ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣ → Equal p q
  ker𝔽⊆Equal{p = p}{q} x = S-id1{ℓ = ℓ}{p = p}{q} (ℰ⊢[ X ]▹Th𝒦 x) 𝑨 sA

 𝒦⊫→ℰ⊢ : {X : Type χ} → ∀{p q} → 𝒦 ⊫ (p ≈̇ q) → ℰ ⊢ X ▹ p ≈ q
 𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp ((p ≈̇ q) , pKq) where open _⊢_▹_≈_ using (hyp)
\end{code}

#### <a id="the-universal-property">The universal property</a>

\begin{code}

module _  {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom {ℓ = ℓ}(α ⊔ ρᵃ ⊔ ℓ) {𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ  using ( 𝔽[_] )
 open Setoid 𝔻[ 𝑨 ]                 using ( trans ; sym ; refl ) renaming ( Carrier to A )


 𝔽-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦))
  →            epi 𝔽[ A ] 𝑨
 𝔽-ModTh-epi A∈ModThK = φ , isEpi
  where
   φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
   _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
   cong φ {p} {q} pq  = trans  ( sym (free-lift-interp{𝑨 = 𝑨} id p) )
                      ( trans  ( A∈ModThK{p = p}{q} (kernel-in-theory pq) id )
                               ( free-lift-interp{𝑨 = 𝑨} id q ) )
   isEpi : IsEpi 𝔽[ A ] 𝑨 φ
   compatible (isHom isEpi) = cong (Interp 𝑨) (≡.refl , (λ _ → refl))
   isSurjective isEpi {y} = eq (ℊ y) refl

 𝔽-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 𝔽-ModTh-epi-lift A∈ModThK = ∘-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi
\end{code}



<!-- ------------------------------------------------------------------------------------- -->

## <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

We want to pair each `(𝑨 , p)` (where p : 𝑨 ∈ S 𝒦) with an environment
`ρ : X → ∣ 𝑨 ∣` so that we can quantify over all algebras *and* all
assignments of values in the domain `∣ 𝑨 ∣` to variables in `X`.

\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)
 open FreeHom {ℓ = ℓ} (α ⊔ ρᵃ ⊔ ℓ){𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
 open Environment   using ( Env )

 ℑ⁺ : Type ι
 ℑ⁺ = Σ[ 𝑨 ∈ (Algebra α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → Algebra α ρᵃ
 𝔄⁺ i = ∣ i ∣

 ℭ : Algebra ι ι
 ℭ = ⨅ 𝔄⁺

\end{code}

Next we define a useful type, `skEqual`, which we use to represent a term identity `p ≈ q` for any
given `i = (𝑨 , sA , ρ)` (where `𝑨` is an algebra, `sA : 𝑨 ∈ S 𝒦` is a proof that `𝑨` belongs
to `S 𝒦`, and `ρ` is a mapping from `X` to the domain of `𝑨`). Then we prove `AllEqual⊆ker𝔽` which
asserts that if the identity `p ≈ q` holds in all `𝑨 ∈ S 𝒦` (for all environments), then `p ≈ q`
holds in the relatively free algebra `𝔽[ X ]`; equivalently, the pair `(p , q)` belongs to the
kernel of the natural homomorphism from `𝑻 X` onto `𝔽[ X ]`. We will use this fact below to prove
that there is a monomorphism from `𝔽[ X ]` into `ℭ`, and thus `𝔽[ X ]` is a subalgebra of ℭ,
so belongs to `S (P 𝒦)`.

\begin{code}

 skEqual : (i : ℑ⁺) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where
  open Setoid 𝔻[ 𝔄⁺ i ] using ( _≈_ )
  open Environment (𝔄⁺ i) using ( ⟦_⟧ )

 AllEqual⊆ker𝔽 : ∀ {p q} → (∀ i → skEqual i {p}{q}) → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣
 AllEqual⊆ker𝔽 {p} {q} x = Goal
  where
  open Setoid 𝔻[ 𝔽[ X ] ] using ( _≈_ )
  S𝒦⊫pq : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x (𝑨 , sA , ρ)
  Goal : p ≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{ℓ = ℓ}{p = p}{q} S𝒦⊫pq)

 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄⁺ h
  where
  h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
  h i = lift-hom (snd ∥ i ∥)

 ker𝔽⊆kerℭ : ker ∣ hom𝔽[ X ] ∣ ⊆ ker ∣ homℭ ∣
 ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; sym ; trans )
  open Environment 𝑨 using ( ⟦_⟧ )
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t
  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = trans (sym (fl p)) (trans subgoal (fl q))


 hom𝔽ℭ : hom 𝔽[ X ] ℭ
 hom𝔽ℭ = ∣ HomFactor ℭ homℭ hom𝔽[ X ] ker𝔽⊆kerℭ hom𝔽[ X ]-is-epic ∣

 kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ ker ∣ homℭ ∣ → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣
 kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
  where
  pqEqual : ∀ i → skEqual i {p}{q}
  pqEqual i = goal
   where
   open Environment (𝔄⁺ i) using ( ⟦_⟧ )
   open Setoid 𝔻[ 𝔄⁺ i ] using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
   goal = trans (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
           (trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))
  E⊢pq : ℰ ⊢ X ▹ p ≈ q
  E⊢pq = AllEqual⊆ker𝔽 pqEqual

 mon𝔽ℭ : mon 𝔽[ X ] ℭ
 mon𝔽ℭ = ∣ hom𝔽ℭ ∣ , isMon
  where
  isMon : IsMon 𝔽[ X ] ℭ ∣ hom𝔽ℭ ∣
  isHom isMon = ∥ hom𝔽ℭ ∥
  isInjective isMon {p} {q} φpq = kerℭ⊆ker𝔽 φpq

\end{code}

Now that we have proved the existence of a monomorphism from `𝔽[ X ]` to `ℭ` we are in a position
to prove that `𝔽[ X ]` is a subalgebra of ℭ, so belongs to `S (P 𝒦)`.  In fact, we will show
that `𝔽[ X ]` is a subalgebra of the *lift* of `ℭ`, denoted `ℓℭ`.

\begin{code}

 𝔽≤ℭ : 𝔽[ X ] ≤ ℭ
 𝔽≤ℭ = mon→≤ mon𝔽ℭ

 SP𝔽 : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SP𝔽 = S-idem SSP𝔽
  where
  PSℭ : ℭ ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  PSℭ = ℑ⁺ , (𝔄⁺ , ((λ i → fst ∥ i ∥) , ≅-refl))
  SPℭ : ℭ ∈ S ι (P ℓ ι 𝒦)
  SPℭ = PS⊆SP {ℓ = ℓ} PSℭ
  SSP𝔽 : 𝔽[ X ] ∈ S ι (S ι (P ℓ ι 𝒦))
  SSP𝔽 = ℭ , (SPℭ , 𝔽≤ℭ)
\end{code}



<!-- ------------------------------------------------------------------------------------- -->

## <a id="the-hsp-theorem">The HSP Theorem</a>

Finally, we are in a position to prove Birkhoff's celebrated variety theorem.

\begin{code}

module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)
 open FreeHom {ℓ = ℓ}(α ⊔ ρᵃ ⊔ ℓ){𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

 Birkhoff : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Birkhoff 𝑨 ModThA = V-≅-lc{α}{ρᵃ}{ℓ} 𝒦 𝑨 VlA
  where
  open Setoid 𝔻[ 𝑨 ] using () renaming ( Carrier to A )
  sp𝔽A : 𝔽[ A ] ∈ S{ι} ι (P ℓ ι 𝒦)
  sp𝔽A = SP𝔽{ℓ = ℓ} 𝒦
  epi𝔽lA : epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
  epi𝔽lA = 𝔽-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})
  lAimg𝔽A : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ A ]
  lAimg𝔽A = epi→ontohom 𝔽[ A ] (Lift-Alg 𝑨 ι ι) epi𝔽lA
  VlA : Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦
  VlA = 𝔽[ A ] , sp𝔽A , lAimg𝔽A

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

\begin{code}

 module _ {𝑨 : Algebra α ρᵃ} where
  Birkhoff-converse : 𝑨 ∈ V{α}{ρᵃ}{α}{ρᵃ}{α}{ρᵃ} ℓ ι 𝒦 → 𝑨 ∈ Mod{X = 𝕌[ 𝑨 ]} (Th (V ℓ ι 𝒦))
  Birkhoff-converse vA pThq = pThq 𝑨 vA

\end{code}

We have thus proved that every variety is an equational class.

Readers familiar with the classical formulation of the Birkhoff HSP theorem as an
"if and only if" assertion might worry that the proof is still incomplete. However,
recall that in the [Setoid.Varieties.Preservation][] module we proved the following
identity preservation lemma:

`V-id1 : 𝒦 ⊫ p ≈̇ q → V 𝒦 ⊫ p ≈̇ q`

Thus, if `𝒦` is an equational class---that is, if `𝒦` is the class of algebras
satisfying all identities in some set---then `V 𝒦` ⊆ 𝒦`.  On the other hand, we
proved that `V` is expansive in the [Setoid.Varieties.Closure][] module:

`V-expa : 𝒦 ⊆ V 𝒦`

so `𝒦` (= `V 𝒦` = `HSP 𝒦`) is a variety.

Taken together, `V-id1` and `V-expa` constitute formal proof that every equational
class is a variety.

This completes the formal proof of Birkhoff's variety theorem.





--------------------------------

<span style="float:left;">[← Setoid.Varieties.FreeAlgebras](Setoid.Varieties.FreeAlgebras.html)</span>
<span style="float:right;">[Structures →](Structures.html)</span>

{% include UALib.Links.md %}

