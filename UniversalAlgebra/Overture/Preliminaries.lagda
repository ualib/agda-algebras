---
layout: default
title : Overture.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

The [Agda UniversalAlgebra][] library (or [UniversalAlgebra][]) is based on a type theory that is the same or very close to the one on which on which Martín Escardó's [Type Topology][] Agda library is based. We don't discuss [MLTT][] in great detail here because there are already nice and freely available resources covering the theory. (See, for example, the section of [Escardó's notes][] on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda), the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), or the [HoTT Book][].)

The objects and assumptions that form the foundation of [MLTT][] are few.  There are the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these type formers is defined by a *type forming rule* which specifies how that type is constructed. Lastly, we have an infinite collection of *type universes* (types of types) and *universe variables* to denote them. Following Escardó, [UniversalAlgebra][] denotes universe levels by upper-case calligraphic letters from the second half of the English alphabet; to be precise, these are `𝓞`, `𝓠`, `𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[0](Overture.Preliminaries.html#fn0)</sup>

That's all. There are no further axioms or logical deduction (proof derivation) rules needed for the foundation of [MLTT][] that we take as the starting point of [UniversalAlgebra][].  The logical semantics come from the [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types): propositions and predicates are represented by types and the inhabitants of these types are the proofs of the propositions and predicates.  As such, proofs are constructed using the type forming rules. In other words, the type forming rules *are* the proof derivation rules.

To this foundation, we add certain *extensionality principles* when and were we need them.  These will be developed as we progress.  However, classical axioms such as the [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice) or the [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are not assumed anywhere in the library.  In this sense, all theorems and proofs in [UniversalAlgebra][] are [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)).

A few specific instances (e.g., the proof of the Noether isomorphism theorems and Birkhoff's HSP theorem) require certain *truncation* assumptions. In such cases, the theory is not [predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)). These instances are always clearly identified.



#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in [UniversalAlgebra][] begins with the following line.

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

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="agda-universes">Agda Universes</a>

Here we import the basic primitive operations we need for working with Agda's type universes. For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

\begin{code}

open import Agda.Primitive using (_⊔_; lzero; lsuc; Level; Setω) public

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

Given universes 𝓤 and 𝓥, a type `A : Type 𝓤`, and a type family `B : A → Type 𝓥`, the *Sigma type* (or *dependent pair type*), denoted by `Σ(x ꞉ A), B x`, generalizes the Cartesian product `A × B` by allowing the type `B x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, an inhabitant of the type `Σ(x ꞉ A), B x` is a pair `(x , y)` such that `x : A` and `y : B x`.

The dependent product type is defined in other libraries (e.g., the [Agda Standard Library][] and the [Type Topology][] library). For pedagogical purposes we repeat this definition here.

\begin{code}

module hide-sigma where

 record Σ {𝓤 𝓥} {A : Type 𝓤 } (B : A → Type 𝓥 ) : Type(𝓤 ⊔ 𝓥)  where
  constructor _,_
  field
   pr₁ : A
   pr₂ : B pr₁

 infixr 50 _,_

\end{code}

Agda's default syntax for this type is `Σ A (λ x → B)`, but we prefer the notation `Σ x ꞉ A , B`, which is closer to the syntax in the preceding paragraph and the notation used in the HoTT book~\cite{HoTT}, for example. Fortunately, the [Type Topology][] library makes the preferred notation available with the following type definition and `syntax` declaration.

\begin{code}

 -Σ : {𝓤 𝓥 : Level} (A : Type 𝓤 ) (B : A → Type 𝓥 ) → Type(𝓤 ⊔ 𝓥)
 -Σ A B = Σ B

 syntax -Σ A (λ x → B) = Σ x ꞉ A , B

\end{code}

**Warning!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

\begin{code}

 _×_ : Type 𝓤 → Type 𝓥 → Type (𝓤 ⊔ 𝓥)
 A × B = Σ x ꞉ A , B

\end{code}


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : Type 𝓤`, and a type family `Y : X → Type 𝓥`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).

\begin{code}

module hide-pi where

 Π : {A : Type 𝓤 } (B : A → Type 𝓦 ) → Type (𝓤 ⊔ 𝓦)
 Π {A = A} B = (x : A) → B x

 -Π : (A : Type 𝓤 )(B : A → Type 𝓦 ) → Type(𝓤 ⊔ 𝓦)
 -Π A B = Π B

 infixr -1 -Π
 syntax -Π A (λ x → B) = Π x ꞉ A , B

\end{code}

**Warning!** The symbol ꞉ is not the same as :. Type the colon in `Π x ꞉ A , B` as `\:4` in [agda2-mode][].

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Overture.Preliminaries][].

\begin{code}

open import Sigma-Type renaming (_,_ to infixr 50 _,_) public
open import MGS-MLTT using (pr₁; pr₂; _×_; -Σ; Π; -Π) public

\end{code}

#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.


\begin{code}

module _ {A : Type 𝓤 }{B : A → Type 𝓥} where

 ∣_∣ fst : Σ B → A
 ∣ x , y ∣ = x
 fst (x , y) = x

 ∥_∥ snd : (z : Σ B) → B (pr₁ z)
 ∥ x , y ∥ = y
 snd (x , y) = y

\end{code}

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type 𝓤`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

----------------------------------------

<sup>0</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe variable because in the [Type Topology][] library `𝓟` denotes a powerset type.</span>

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes entitled [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html) which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout [UniversalAlgebra][]. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3"> To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which [UniversalAlgebra][] depends while ensuring that this cannot be misinterpreted as a claim to originality.</span>

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Equality →](Overture.Equality.html)</span>


{% include UALib.Links.md %}


