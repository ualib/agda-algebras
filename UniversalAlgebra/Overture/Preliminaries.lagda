---
layout: default
title : Overture.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

The [Agda Universal Algebra Library](https://github.com/ualib/agda-algebras) (or
[agda-algebras](https://github.com/ualib/agda-algebras) for short) is based on
a version of [Martin-Löf type theory (MLTT)](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory),
similar to the one on which on which Martín Escardó's [Type Topology Agda
library](https://github.com/martinescardo/TypeTopology) is based. We don't
discuss [MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) in
great detail here because there are already good and freely available resources covering the theory.
(See, for example, the section of
[Escardó's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes) on
[A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda),
or the
[ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory),
or the
[HoTT book](https://homotopytypetheory.org/book/).)


The objects and assumptions that form the foundation of
[MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) are few.
There are the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type,
one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`,
denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these
type formers is defined by a *type forming rule* which specifies how that type
is constructed. Lastly, we have an infinite collection of *type universes*
(types of types) and *universe variables* to denote them. Following Escardó,
[agda-algebras][] denotes universe levels by upper-case calligraphic letters
from the second half of the English alphabet; to be precise, these are `𝓞`, `𝓠`,
`𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[0](Overture.Preliminaries.html#fn0)</sup>

That's all. There are no further axioms or logical deduction (proof derivation)
rules needed for the foundations of
[MLTT](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)
that we take as the starting point of [agda-algebras][].  The logical semantics
come from the [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types):
propositions and predicates are represented by types and the inhabitants of
these types are the proofs of the propositions and predicates.  As such, proofs
are constructed using the type forming rules. In other words, the type forming
rules *are* the proof derivation rules.

To this foundation, we add certain *extensionality principles* when and were we
need them.  These will be developed as we progress.  However, classical axioms
such as the [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice)
or the [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are
not assumed anywhere in the library.  In this sense, all theorems and proofs in
[agda-algebras][] are [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics)
(according to [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)). 

A few specific instances (e.g., the proof of the Noether isomorphism theorems
and Birkhoff's HSP theorem) require certain *truncation* assumptions. In such
cases, the theory is not
[predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according 
to [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)).
These instances are always clearly identified.



#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types
from existing Agda libraries. Options are specified with the `OPTIONS` *pragma*
and control the way Agda behaves by, for example, specifying the logical axioms
and deduction rules we wish to assume when the program is type-checked to verify
its correctness. Every Agda program in [agda-algebras][] begins with the following line.

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

module Overture.Preliminaries where

\end{code}


#### <a id="agda-universes">Agda Universes</a>

Here we import the basic primitive operations we need for working with Agda's type universes. For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

\begin{code}

open import Agda.Primitive using (_⊔_; lzero; lsuc; Level; Setω) public
open import Data.Empty public

{-
open import Agda.Builtin.Equality renaming (_≡_ to infix 0 _≡_)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product renaming (_,_ to infixr 50 _,_) using (Σ; Σ-syntax; _×_)
open import Data.Sum.Base using (_⊎_) public
open import Function.Related
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; subst; cong; cong-app)
open import Relation.Unary using (Pred; ∅; _∪_; _∈_; _⊆_) public


-}

\end{code}

We prefer to use `Type` in place of Agda's `Set` since for us *set* will mean a very special kind of (truncated) type. (See [Relatoins.Truncation][]).

\begin{code}

Type : (𝓤 : Level) → Set (lsuc 𝓤)
Type 𝓤 = Set 𝓤

\end{code}

We adopt Escardó's convention of denoting universe levels by capital calligraphic letters.

\begin{code}

variable
 𝓞 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level

\end{code}


#### <a id="dependent-pair-type">Sigma types (dependent pairs)</a>

Given universes 𝓤 and 𝓥, a type `A : Type 𝓤`, and a type family `B : A → Type 𝓥`, the *Sigma type* (or *dependent pair type*), denoted by `Σ[x ∈ A] B x`, generalizes the Cartesian product `A × B` by allowing the type `B x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, an inhabitant of the type `Σ[x ∈ A] B x` is a pair `(x , y)` such that `x : A` and `y : B x`.

For pedagogical reasons, we given the definition of the dependent product type here, inside a hidden module, but it is already defined in the `Data.Product` module of the [Agda Standard Library][], so ultimately we import it from there.

\begin{code}

module hide-sigma where

 record Σ {𝓤 𝓥} {A : Type 𝓤 } (B : A → Type 𝓥 ) : Type(𝓤 ⊔ 𝓥)  where
  constructor _,_
  field
   pr₁ : A
   pr₂ : B pr₁

 infixr 50 _,_

open import Data.Product renaming (_,_ to infixr 50 _,_) using (Σ; Σ-syntax) public

\end{code}


Agda's default syntax for this type is `Σ A (λ x → B)`, but we prefer the notation `Σ x ꞉ A , B`, which is closer to the syntax in the preceding paragraph and the notation used in the [HoTT book][], for example. Fortunately, we can make the preferred syntax available; this is done in the [Type Topology][] library with the following type definition and `syntax` declaration.

\begin{code}

-Σ : {𝓤 𝓥 : Level} (A : Type 𝓤 ) (B : A → Type 𝓥 ) → Type(𝓤 ⊔ 𝓥)
-Σ = Σ

syntax -Σ A (λ x → B) = Σ x ꞉ A , B

infixr -1 -Σ

\end{code}

Also, the standard library made an alternative notation for the dependent pair type available which allows us to write `Σ[ x ∈ A ] B x` in place of `Σ A (λ x → B)`.  In the [agda-algebras][] library we may use any one of the three alternative notations,

+ `Σ A (λ x → B)` (standard Agda notation)
+ `Σ[ x ∈ A ] B x` ([Agda Standard Library][] notation)
+ `Σ x ꞉ A , B` ([Type Topology][] notation)

**Warning!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

\begin{code}

module hode-× where

 _×_ : Type 𝓤 → Type 𝓥 → Type (𝓤 ⊔ 𝓥)
 A × B = Σ x ꞉ A , B

open import Data.Product using (_×_)

\end{code}


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

infixr -1 -Π
syntax -Π A (λ x → B) = Π x ꞉ A , B

\end{code}

**Warning!** The symbol ꞉ is not the same as :. Type the colon in `Π x ꞉ A , B` as `\:4` in [agda2-mode][].



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

\end{code}

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type 𝓤`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

----------------------------------------

<sup>0</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe
variable because in some libraries `𝓟` denotes a powerset type.</span>

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an
outstanding set of notes entitled
[Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html)
which we highly recommend to anyone wanting more details than we provide here
about [MLTT][] and Univalent Foundations/HoTT in Agda.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout [UniversalAlgebra][]. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Equality →](Overture.Equality.html)</span>

[agda-algebras]: https://github.com/ualib/agda-algebras

{% include UALib.Links.md %}


