---
layout: default
title : The Agda Universal Algebra Library (UALib)
date : 2020-10-10
---
<!--

LICENSE:

The software in this file is subject to the GNU General Public License v3.0.

The text and software is copyright of the author. It can be used for scholarly purposes subject to the usual academic conventions of citation.

-->

<!--

  * The file ualib.lagda is *not* meant to be read by people.

  * It is used to automatically generate the following files, which are meant to be read by people:

    - https://ualib.org/ualib.html

    - https://ualib.org/ualib.pdf

  * The html file is better rendered and probably easier to read than the pdf file, but both have internal links, including to the Agda definitions.

  * Warning: this file takes a long time to be checked by Agda.  We are avoiding a modular development so that a single pdf file with internal links, including to the Agda definitions, can be produced. This works by first using Agda to generate html for the Agda code, then using jekyll to process the markdown code to generate html for everything else, and finally using google-chrome in headless mode to generate pdf from the html code.  See the makefile.

-->

# The Agda Universal Algebra Library (UALib)

version of {{ "now" | date: "%d %B %Y, %H:%M" }}.

+ [William DeMeo](https://williamdemeo.gitlab.io), Department of Algebra, Faculty of Mathematics and Physics, Charles University, Czech Republic
+ [Hyeyoung Shin](https://hyeyoungshin.github.io), Faculty of Information Technology, Czech Technical University, Czech Republic
+ [Siva Somayyajula](http://www.cs.cmu.edu/~ssomayya/), Department of Computer Science, Carnegie Mellon University, USA

----------------------------

[<sub>Table of contents ⇓</sub>](ualib.html#contents)
## Preface

To support formalization in type theory of research level mathematics in universal algebra and related fields, we are developing a software library, called the [Agda Universal Algebra Library](https://github.com/UniversalAlgebra/agda-ualib/) ([UALib][] ). Our library contains formal statements and proofs of some of the core, foundational definitions and results universal algebra and is written in [Agda][].

[Agda][] is a programming language and [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant), or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful *proof tactics* for proving things about the objects that inhabit these types.

### Vision and Goals

The idea for the the Agda Universal Algebra Library ([UALib][]) originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of [type theory](https://en.wikipedia.org/wiki/Type_theory) ---in particular, [dependent types](https://en.wikipedia.org/wiki/Dependent_type) and [inductive types](https://en.wikipedia.org/wiki/Intuitionistic_type_theory#Inductive_types)) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### Primary Goals

The first goal of the [UALib][] project is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and possibly risky investment of time and resources. However, we believe our subject is well served by a new, modern, constructive presentation of its foundations. Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

#### Secondary Goals

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language. Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our intermediate-term objectives include

-   developing domain specific "proof tactics" to express the idioms of universal algebra,
-   incorporating automated proof search for universal algebra, and
-   formalizing theorems emerging from our own mathematics research,
-   documenting the resulting software libraries so they are usable by other working mathematicians.

For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.

### Intended audience

This document describes the Agda Universal Algebra Library ([UALib][]) in enough detail so that working mathematicians (and possibly some normal people, too) might be able to learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying new mathematics.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, Bergman:2012 or McKenzie:1987, and to a lesser extent category theory, as presented in [categorytheory.gitlab.io](https://categorytheory.gitlab.io) or Riehl:2017.

Some prior exposure to [type theory](https://en.wikipedia.org/wiki/Type_theory) and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to the appendix and glossary, while simultaneously consulting one or more of the references mentioned in references to fill in gaps as needed.

Finally, it is assumed that while reading these materials the reader is actively experimenting with [Agda][] using
[emacs][] with its [agda2-mode][] extension installed. If not, follow the directions on [the main Agda website](Agda) to install them.

### Installing the library

The main repository for the [UALib][] is [https://gitlab.com/ualib/ualib.gitlab.io](https://gitlab.com/ualib/ualib.gitlab.io).

There are installation instructions in the main README.md file in that repository, but really all you need to do is have a working Agda (and [agda2-mode][]) installation and clone the [UALib][] repository with, e.g.,

```shell
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
```

OR

```shell
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
```

### Unicode hints

Information about unicode symbols is readily available in Emacs [agda2-mode][]; simply place the cursor on the character of interest and enter the command `M-x describe-char` (or `M-m h d c`). To see a full list of available characters, enter `M-x describe-input-method` (or `C-h I`).

### Acknowledgments

Besides the main authors and developers of [UALib][], a number of other people have contributed to the project in one way or another.

Special thanks go to [Clifford Bergman](https://orion.math.iastate.edu/cbergman/), [Venanzio Capretta](https://www.duplavis.com/venanzio/), [Andrej Bauer](http://www.andrej.com/index.html), [Miklós Maróti](http://www.math.u-szeged.hu/~mmaroti/), and [Ralph Freese](https://math.hawaii.edu/~ralph/), for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project, often without even knowing it.

The first author would also like to thank his postdoctoral advisors and their institutions for supporting (sometimes without their knowledge) work on this project. These include [Peter Mayr](http://math.colorado.edu/~mayr/) and University of Colorado in Boulder (Aug 2017--May 2019), [Ralph Freese](https://math.hawaii.edu/~ralph/) and the University of Hawaii in Honolulu (Aug 2016--May 2017), [Cliff Bergman](https://orion.math.iastate.edu/cbergman/) and Iowa State University in Ames (Aug 2014--May 2016).

### Attributions and citations

Regarding the mathematical results that are implemented in the [UALib][] library, as well as the presentation and informal statements of these results in the documentation, The Authors makes no claims to originality.

Regarding the Agda source code in the [UALib][] library, this is mainly due to The Authors.

HOWEVER, we have benefited from the outstanding lecture notes on [Univalent Foundations and Homotopy Type Theory][] and the [Type Topology][] Agda Library, both by [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe). The first author is greatly indebted to Martin for teaching him about type theory in Agda at the [Midlands Graduate School in the Foundations of Computing Science](http://events.cs.bham.ac.uk/mgs2019/) in Birmingham in 2019.

The development of the [UALib][] and its documentation is informed by and benefits from the references listed in the references section below.

### References

The following Agda documentation and tutorials are excellent. They have been quite helpful to The Author of
[UALib][], and have informed the development of the latter and its documentation.

-   Altenkirk, [Computer Aided Formal Reasoning](http://www.cs.nott.ac.uk/~psztxa/g53cfr/)
-   Bove and Dybjer, [Dependent Types at Work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)
-   Escardo, [Introduction to Univalent Foundations of Mathematics with Agda][]
-   Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda](http://www.sciencedirect.com/science/article/pii/S1571066118300768)
-   János, [Agda Tutorial](https://people.inf.elte.hu/pgj/agda/tutorial/Index.html)
-   Norell and Chapman, [Dependently Typed Programming in Agda](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf)
-   Wadler, [Programming Language Foundations in Agda](https://plfa.github.io/)

Finally, the official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the (open source) [Agda Standard Library][] source code are also quite useful.

### How to cite this work

#### Chicago Style

DeMeo, William. *The Agda Universal Algebra Library*. Available at [https://ualib.org](http://ualib.org), 2020.

#### BibTeX

```@Book{demeo2020,
   AUTHOR = {William DeMeo},
   TITLE  = {The {A}gda {U}niversal {A}lgebra {L}ibrary},
   NOTE   = {Available at \url{https://ualib.org}},
   year   = 2020
   }
```

------------------------------------------------------------------------

### <a id="contents"></a> Table of contents

  1. [Preface](#preface)
     1. [Vision and Goals](#vision-and-goals)
     1. [Intended audience](#intended-audience)
     1. [Installing the library](#installing-the-library)
     1. [Unicode hints](#unicode-hints)
     1. [Acknowledgments](#acknowledgments)
     1. [Attributions and citations](#attributions-and-citations)
     1. [References](#references)
     1. [Table of contents](ualib.html#contents)
  1. [Agda Preliminaries](#agda-preliminaries)
     1. [Universes](#universes)
     1. [Public imports](#public-imports)
     1. [Dependent pair type](#dependent-pair-type)
     1. [Dependent function type](#dependent-function-type)
     1. [Application](#application)
     1. [Function extensionality](#function-extensionality)
     1. [Predicates, Subsets](#predicates-subsets)
     1. [The membership relation](#the-membership-relation)
     1. [Subset relations and operations](#subset-relations-and-operations)
     1. [Miscellany](#miscellany)
     1. [More extensionality](#more-extensionality)
  1. [Algebras in Agda](#algebras-in-agda)
     1. [Operation type](#operation-type)
     1. [Signature type](#signature-type)
     1. [Algebra type](#algebra-type)
     1. [Example](#example)
     1. [Syntactic sugar for operation interpretation](#syntactic-sugar-for-operation-interpretation)
     1. [Products of algebras](#products-of-algebras)
     1. [Arbitrarily many variable symbols](#arbitrarily-many-variable-symbols)
     1. [Unicode Hints 1](#unicode-hints-1)
  1. [Congruences in Agda](#congruences-in-agda)
     1. [Binary relation type](#binary-relation-type)
     1. [Kernels](#kernels)
     1. [Implication](#implication)
     1. [Properties of binary relations](#properties-of-binary-relations)
     1. [Types for equivalences](#types-for-equivalences)
     1. [Types for congruences](#types-for-congruences)
     1. [The trivial congruence](#the-trivial-congruence)
     1. [Unicode Hints 2](#unicode-hints-2)
  1. [Homomorphisms in Agda](#homomorphisms-in-agda)
     1. [Types for homomorphisms](#types-for-homomorphisms)
     1. [Composition](#composition)
     1. [Factorization](#factorization)
     1. [Isomorphism](#isomorphism)
     1. [Homomorphic images](#homomorphic-images)
     1. [Unicode Hints 3](#unicode-hints-3)
  1. [Terms in Agda](#terms-in-agda)
     1. [Types for terms](#types-for-terms)
     1. [The term algebra](#the-term-algebra)
     1. [The universal property](#the-universal-property)
     1. [Interpretation](#interpretation)
     1. [Compatibility of terms](#compatibility-of-terms)
  1. [Subalgebras in Agda](#subalgebras-in-agda)
     1. [Preliminaries](#preliminaries)
     1. [Types for subuniverses](#types-for-subuniverses)
     1. [Subuniverse generation](#subuniverse-generation)
     1. [Closure under intersection](#closure-under-intersection)
     1. [Generation with terms](#generation-with-terms)
     1. [Homomorphic images are subuniverses](#homomorphic-images-are-subuniverses)
     1. [Types for subalgebras](#types-for-subalgebras)
     1. [Unicode Hints 4](#unicode-hints-4)
  1. [Equational Logic in Agda](#equational-logic-in-agda)
     1. [Closure operators and varieties](#closure-operators-and-varieties)
     1. [Types for identities](#types-for-identities)
     1. [Equational theories and classes](#equational-theories-and-classes)
     1. [Compatibility of identities](#compatibility-of-identities)
     1. [Axiomatization of a class](#axiomatization-of-a-class)
     1. [The free algebra in Agda](#the-free-algebra-in-agda)
     1. [More tools for Birkhoff's theorem](#more-tools-for-birkhoffs-theorem)
     1. [Unicode Hints 5](#unicode-hints-5)
  1. [HSP Theorem in Agda](#hsp-theorem-in-agda)
     1. [Equalizers in Agda](#equalizers-in-agda)
     1. [Homomorphism determination](#homomorphism-determination)
     1. [A formal proof of Birkhoff's theorem](#a-formal-proof-of-birkhoffs-theorem)

------------------------------------------------------------------------

## Mathematical Preliminaries

This section reviews the informal language of universal algebra, presenting foundational definitions and theorems about such basic objects as subalgebras, terms, and clones. Later, beginning in the section on [Algebras in Agda](#algebras-in-agda), we show how each of the definitions and results presented here can be formalized (or "implemented") in type theory using [Agda][].

The idea is to demonstrate the power and utility of implementing our mathematical areas of expertise in a formal language that supports dependent and inductive types, which are essential for expressing and working with mathematical objects (both finite and infinite) in a constructive and computable way, and for proving properties of such objects.

One goal of our project is to provide, as a "proof of concept," a formal implementation of some deep results in universal algebra. As the first such result, we have chosen what is probably the first major result of universal algebra---namely, the celebrated [HSP Theorem](https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem)
that [Garrett Birkhoff proved in 1933](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/_static/lit/Birkhoff-OnTheStructureOfAbstractAlgebras.pdf). (The original paper is available
[here](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/_static/lit/Birkhoff-OnTheStructureOfAbstractAlgebras.pdf).)

In order to get as directly as possible to a formal proof of the HSP Theorem, we will review all the needed ingredients as a list of results at the end of this chapter, and then later, in the [HSP Theorem in Agda](#hsp-theorem-in-agda) section, we formalize each of these results in [Agda][].

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Operations

The symbols ℕ, ω, and `nat` are used interchangeably; they all denote the set of natural numbers.

If 𝑚 is a natural number, we write 𝑚 : ℕ and say that 𝑚 *has type* ℕ. We typically denote and define natural numbers by 𝑚 := {0, 1, …, 𝑚-1}.

It is sometimes convenient to formally identify a function with its graph. For example, the function 𝑎 : 𝑚 → 𝐴 may be identified with the tuple (𝑎 0, 𝑎 1, …, 𝑎(𝑚-1)) : 𝐴ᵐ.

If ℎ : 𝐴 → 𝐴 and 𝑎 : 𝑚 → 𝐴 are functions, then ℎ ∘ 𝑎 : 𝑚 → 𝐴 denotes the composition of ℎ with 𝑎; this is the function that maps each 𝑖 < 𝑚 to the element (ℎ ∘ 𝑎)(𝑖) = ℎ(𝑎 𝑖) of 𝐴.

We may formally identify the function ℎ ∘ 𝑎 : 𝑚 → 𝐴 with its graph, which of course is the 𝑚-tuple, (ℎ(𝑎 0), ℎ(𝑎 1), …, ℎ(𝑎 (𝑚-1))).

Suppose 𝐴 is a nonempty set and 𝑛 ∈ ℕ is a natural number. An 𝑛-**ary operation** on 𝐴 is a function 𝑓 : 𝐴ⁿ → 𝐴 which (for 𝑛 > 0) maps each 𝑛-tuple (𝑎₀, 𝑎₁, …, 𝑎ₙ₋₁) in 𝐴ⁿ to a particular element 𝑓(𝑎₀, 𝑎₁, …, 𝑎ₙ₋₁) in 𝐴. If 𝑛 = 0, then 𝑓 : () → 𝐴 is a function that takes no arguments and returns an element of 𝐴, so 𝑓 in this case is merely notation for a particular element of 𝐴, and we may write 𝑓 : 𝐴 in this case. An operation is called **nullary** (or constant) if its arity is zero. **Unary**, **binary**, and **ternary** operations have arities 1, 2, and 3, respectively.

An operation gives rise to a special kind of (𝑛+1)-ary relation, namely

𝑓<sup>*</sup> := {(𝑎<sub>0</sub>, 𝑎<sub>1</sub>, …, 𝑎<sub>𝑛-1</sub>, 𝑏) ∈ 𝐴<sup>𝑛+1</sup> : 𝑏 = 𝑓(𝑎<sub>0</sub>, 𝑎<sub>1</sub>, …, 𝑎<sub>𝑛-1</sub>)},

which is sometimes called the **graph** of 𝑓.

For two sets 𝐴 and 𝐵, the collection of all functions 𝑓 : 𝐵 → 𝐴 is, for obvious reasons, denoted by 𝐴<sup>𝐵</sup>. If 𝐵 = 𝐴ⁿ, then we have 𝐴<sup>A<sup>𝑛</sup></sup>, the collection of all 𝑛-ary operations on 𝐴; as noted above, this can be represented by the function type (𝑛 → 𝐴) → 𝐴.

If we let Op(𝐴) denote the collection of all finitary operations on 𝐴, then,

  Op(𝐴) = ⋃<sub>𝑛 ∈ ℕ</sub> 𝐴<sup>𝐴<sup>𝑛</sup></sup> = ⋃<sub>𝑛 < ω</sub> ((𝑛 → 𝐴) → 𝐴).

If 𝐹 ⊆ Op(𝐴) is a set of operations on 𝐴, let us denote by 𝐹ₙ the 𝑛-ary operations in 𝐹. Clearly, 𝐹<sub>𝑛</sub> = 𝐹 ∩ 𝐴<sup>𝐴<sup>𝑛</sup></sup>.

Given an 𝑛-tuple 𝑎 = (𝑎<sub>0</sub>, 𝑎<sub>1</sub>, …, 𝑎<sub>𝑛-1</sub>) ∈ 𝐴<sup>𝑛</sup>, it sometimes helps to be able to refer to the set {𝑎<sub>𝑖</sub> : 0 ≤ 𝑖 < 𝑛} of elements that occur in the tuple without explicitly naming each element in this set. Since an 𝑛-tuple is a function, with domain 𝑛 := {0, 1, …, 𝑛-1}, and image the set of elements occuring in the tuple, the natural notation is im 𝑎 := {𝑎₀, 𝑎₁, …, 𝑎ₙ₋₁}, where each value is included in the set only once (no repetitions). In particular, ∣im 𝑎∣ is a convenient way to write the number of distinct elements that occur in the tuple 𝑎. For example, if 𝑎 = (1, 1, 3), then im 𝑎 = {1, 3}, and ∣im 𝑎∣ = 2.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### General composition

In universal algebra we mainly deal with *finitary* operations in **Set** (the category of sets). We will identify the `ntuple` type with the function type 𝑛 → 𝐴. Thus, the type of 𝑛-ary operations on 𝐴 is (𝑛 → 𝐴) → 𝐴. Evaluating such an operation at the tuple 𝑎 : 𝑛 → 𝐴 is simply function application.

As above, we denote and define the collection of all finitary operations on 𝐴 by Op(𝐴) = ⋃<sub>n < ω</sub> ((𝑛 → 𝐴) → 𝐴). Let us now develop a general formulation of composition of operations that is more elegant and computationally practical than the standard formulation.

Recall, the standard description of operation composition: if 𝑓 : (𝑛 → 𝐴) → 𝐴 is an 𝑛-ary operation and 𝑔<sub>𝑖</sub> : (𝑘<sub>𝑖</sub> → 𝐴) → 𝐴 is a 𝑘<sub>𝑖</sub>-ary operation for each 0 ≤ 𝑖 < 𝑛, then the **composition of** 𝑓 **with** (𝑔<sub>0</sub>, …, 𝑔<sub>𝑛-1</sub>, denoted 𝑓 ∘ (𝑔<sub>0</sub>, …, 𝑔<sub>𝑛-1</sub>, is usually expressed as follows: for each 𝑛-tuple of tuples,

{((𝑎<sub>00</sub>, …, 𝑎<sub>0(𝑘<sub>0</sub>-1)</sub>), …, (𝑎<sub>(𝑛-1)0</sub>, …, 𝑎<sub>(𝑛-1)(𝑘<sub>𝑛-1</sub>-1)</sub>): 𝐴<sup>𝑘<sub>0</sub></sup> × ⋯ × 𝐴<sup>𝑘<sub>𝑛-1</sub></sup>},

𝑓 ∘ (𝑔<sub>0</sub>, …, 𝑔<sub>𝑛-1</sub>)((𝑎<sub>00</sub>, …, 𝑎<sub>0(𝑘<sub>0</sub>-1)</sub>), …, (𝑎<sub>(𝑛-1)0</sub>, …, 𝑎<sub>(𝑛-1)(𝑘<sub>𝑛-1</sub>-1)</sub>)) ,

which, by definition, is equal to 

𝑓 (𝑔<sub>0</sub>(𝑎<sub>00</sub>, …, 𝑎<sub>0(𝑘<sub>0</sub>-1)</sub>), …, 𝑔<sub>𝑛-1</sub>(𝑎<sub>(𝑛-1)0</sub>, …, 𝑎<sub>(𝑛-1)(𝑘<sub>𝑛-1</sub>-1)</sub>)).

This notation is quite ugly; moreover, it lends itself poorly to computation. Let us clean it up.

Consider the 𝑛-tuple (𝑔<sub>0</sub>, …, 𝑔<sub>𝑛-1</sub>) Op(𝐴).

Let 𝑔 : ∏<sub>(𝑖:𝑛)</sub> ((𝑘<sub>𝑖</sub> → 𝐴) → 𝐴) be the function with domain the set 𝑛 = {0, 1, …, 𝑛-1}, codomain Op(𝐴), and defined for each 0 ≤ 𝑖 < 𝑛 by 𝑔 𝑖 = 𝑔<sub>𝑖</sub>.

Let 𝑎 :  ∏<sub>(𝑖:𝑛)</sub> (𝑘<sub>𝑖</sub> → 𝐴) be such that for each 0 ≤ 𝑖< 𝑛 we have a function 𝑎 𝑖 : 𝑘ᵢ → 𝐴 which is defined for each 0 ≤ 𝑗 < 𝑘ᵢ by 𝑎 𝑖 𝑗 = 𝑎ᵢⱼ. Then the 𝑛-tuple of arguments in expression args above can be identified with the 𝑛-tuple 𝑎 = (𝑎 0, …, 𝑎 (𝑛-1)) of functions.

Using *fork* and *eval* operators, it is not hard to define general composition using these operators along with dependent types.

If 𝑔 : ∏<sub>(𝑖:𝑛)</sub> ((𝑘<sub>𝑖</sub> → 𝐴) → 𝐴) and 𝑎 ∏<sub>(𝑖:𝑛)</sub> (𝑘<sub>𝑖</sub> → 𝐴), then

**fork** 𝑔 𝑎 : ∏<sub>(𝑖:𝑛)</sub> ((𝑘<sub>𝑖</sub> → 𝐴) → 𝐴) × (𝑘<sub>𝑖</sub> → 𝐴)

is the function that maps each 0 ≤ 𝑖 < 𝑛 to the pair 

**fork** 𝑔 𝑎 𝑖 = (𝑔 𝑖, 𝑎 𝑖): ((𝑘<sub>𝑖</sub> → 𝐴) → 𝐴) × (𝑘<sub>𝑖</sub> → 𝐴).

Applying 𝑔 𝑖 to 𝑎 𝑖 with the eval function, we have

**eval** **fork** 𝑔 𝑎 𝑖 = **eval** (𝑔 𝑖, 𝑎 𝑖) = (𝑔 𝑖)(𝑎 𝑖).

Observe that the codomain 𝐴 of the function eval fork 𝑔 𝑎 does not depend on 𝑖, so the type ∏<sub>(𝑖:𝑛)</sub>𝐴 simplifies to 𝑛 → 𝐴 in this case, resulting in the typing judgment, **eval fork** 𝑔 𝑎 : 𝑛 → 𝐴.

Thus, if 

+ 𝑓 : (𝑛 → 𝐴) → 𝐴 (an 𝑛-ary operation) and

+ 𝑔 : ∏<sub>(𝑖:𝑛)</sub> ((𝑘<sub>𝑖</sub> → 𝐴) → 𝐴) (an 𝑛-tuple of operations)

then we denote and define the **composition of** 𝑓 **with** 𝑔 as follows:

𝑓 **comp** 𝑔 := 𝑓 **eval fork** 𝑔: ∏<sub>(𝑖:𝑛)</sub> (𝑘<sub>𝑖</sub> → 𝐴) → 𝐴.

Indeed, if 𝑎 : ∏<sub>(𝑖:𝑛)</sub> (𝑘<sub>𝑖</sub> → 𝐴) is a tuple of elements from 𝐴, then **eval fork** 𝑔 𝑎 has type 𝑛 → 𝐴, which is the domain type of 𝑓; therefore, 𝑓 **eval fork** 𝑔 𝑎 has type 𝐴, as desired.

<!-- ### Greater generality -->
<!-- In the last section we looked at an operation 𝑓 on a set 𝐴. We took the domain of 𝑓 to be 𝑛 → 𝐴 (the type of 𝑛-tuples over 𝐴) for some 𝑛. In particular, we assumed that 𝐴 was a set, and that the arity of 𝑓 was some natural number, say, 𝑛. This is the standard setup in universal algebra. However, it is not necessary to be so specific about the arities, domains, and codomains of operations. -->
<!-- In this section we start with two types α and γ and consider γ-**ary operations on** α---e.g., f : (γ → α) → α---and show how to express composition of operations in this general context. -->
<!-- Suppose that for each 𝑖 : γ we have a type γᵢ and an operation $g_i$ of type (γᵢ → α) → α on α. -->
<!-- Denote by 𝐺 the "γ-tuple" of these operations; that is, for each 𝑖 : γ the "𝑖-th component" of 𝐺 is 𝐺 𝑖 = $g_i$. Evidently, this results in the typing judgment, -->
<!-- $$G: ∏_{(i:γ)} ((γ_i → α) → α).$$ -->
<!-- Even in this more general context, we can still use the fork and eval maps introduced in the appendix (see general-composition) to express composition of operations. Indeed, we *define* the **composition of** 𝑓 **with** 𝐺 to be -->
<!-- $$f \, \mathrm{eval} \, \mathrm{fork} \, G.$$ -->
<!-- Let us adopt the following convenient notation: -->
<!-- > *Denote by* comp *the general composition operation* eval fork. -->
<!-- Then, given 𝑓 : (γ → α) → α and $G: ∏_{(i:γ)} ((γ_i → α) → α)$, the **general composition of** 𝑓 **with** 𝐺 is 𝑓 comp 𝐺 := 𝑓 eval fork 𝐺. Evidently, this yields the typing judgment, -->
<!-- $$f\, \mathrm{comp}\, G : \bigl(∏_{(i:γ)}(γ_i → α)\bigr) → α.$$ -->
<!-- Indeed, if $a: ∏_{(i:γ)}(γ_i → α)$, then for each 𝑖 : γ we have, -->
<!-- $$a\, i : γ_i → α \quad \text{ and } \quad  G\, i : (γ_i → α) → α,$$ -->
<!-- so evaluation of comp 𝐺 𝑎 at a particular 𝑖 : γ is simply function application. That is, -->
<!-- $$\mathrm{comp} \,G \, a \, i:= \mathrm{eval} \, \mathrm{fork} \, G \, a \, i = (G\, i)(a\, i): α.$$ -->
<!-- Thus, comp 𝐺 𝑎 has type γ → α, which is precisely the domain type of 𝑓. -->
<!-- To summarize, we have the following typing judgments: -->
<!-- $$\mathrm{comp}\, G \, a : γ → α \quad \text{ and } \quad f: (γ → α) → α,$$ -->
<!-- whence 𝑓 comp 𝐺 𝑎 : α is well-typed. -->

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Signatures


Recall (from model theory) that a **signature** 𝑆 = (𝐶, 𝐹, 𝑅, ρ) consists of three (possibly empty) sets 𝐶, 𝐹, and 𝑅---called **constant symbols**, **function symbols**, and **relation symbols**, respectively---along with a function ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁 that assigns an arity to each symbol. Often (but not always) 𝑁 = ℕ.

As our focus here is universal algebra, we are more concerned with the restricted notion of an **algebraic signature** (or **signature** for algebraic structures), by which we mean a pair 𝑆 = (𝐹, ρ) consisting of a collection 𝐹 of *operation symbols* and
an arity function $ρ : 𝐹 → 𝑁$ that maps each operation symbol to its arity; here, 𝑁 denotes the "arity type" (which is sometimes taken to be ℕ). (Intuitively, the arity ρ 𝑓 of an operation symbol 𝑓 ∈ 𝐹 may be thought of as the "number of arguments" that 𝑓 takes as "input".)

If the arity of 𝑓 is 𝑛, then we call 𝑓 an 𝑛-**ary** operation. In case 𝑛 is 0 (or 1 or 2 or 3, resp.) we call the function *nullary* (or *unary* or *binary* or *ternary*, resp.).

If 𝐴 is a set and 𝑓 is a (ρ 𝑓)-ary operation on 𝐴, we often indicate this by writing 𝑓 : 𝐴<sup>ρf</sup> → 𝐴. On the other hand, the arguments of such an operation form a (ρ 𝑓)-tuple, say, (𝑎₀, 𝑎₁, …, 𝑎<sub>ρf-1</sub>), which may be viewed as the graph of the function 𝑎 : ρ𝑓 → 𝐴, where 𝑎 𝑖 = 𝑎ᵢ.

(When the codomain of ρ is ℕ, we may view ρ𝑓 as the finite set {0, 1, …, ρ𝑓 - 1}. Thus, by identifying the ρ𝑓-th power $A^{ρf}$ with the type ρ𝑓 → 𝐴 of functions from {0, 1, …, ρ𝑓 - 1} to 𝐴, we identify the function type 𝐴<sup>ρf</sup> → 𝐴 with the function (or "functional") type (ρ𝑓 → 𝐴) → 𝐴.

Our formal implementation of the concept of signature in [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) is described in the [Signature type](#signature-type) section below.)


### Algebraic Structures

Our first goal is to develop a working vocabulary and formal library for classical (single-sorted, set-based) universal algebra. In this section we define the main objects of study.

An **algebraic structure** (or **algebra**) in the signature 𝑆 = (𝐹, ρ) is denoted by 𝑨 = (𝐴, 𝐹<sup>𝑨</sup>) and consists of

1.  𝐴 := a set (or type), called the **carrier** (or **universe**) of the algebra,
2.  𝐹<sup>𝑨</sup> := { 𝑓<sup>𝑨</sup> ∣ 𝑓 ∈ 𝐹,  𝑓<sup>𝑨</sup> : (ρ𝑓 → A) → A }, a collection of **operations** on 𝐴,
3.  a collection of identities satisfied by elements of 𝐴 and the operations in 𝐹<sup>𝑨</sup>.
𝑓<sup>𝑨</sup>
Note that to each operation symbol 𝑓 ∈ 𝐹 corresponds an operation 𝑓<sup>𝑨</sup> on 𝐴 of arity ρ𝑓; we call such 𝑓<sup>𝑨</sup> an **interpretation** of the symbol 𝑓 in the algebra 𝑨. We call an algebra in the signature 𝑆 an 𝑆-**algebra**. An algebra is called **finite** if it has a finite universe, and is called **trivial** if its universe is a singleton.

Given two algebras 𝑨 and 𝑩, we say that 𝑩 is a **reduct** of 𝑨 if both algebras have the same universe and 𝑩 can be obtained from 𝑨 by removing some operations.

Our formal implementation of the concept of algebraic structure is described in the [Algebra type](#algebra-type) section below.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Subalgebras

This section introduces two important concepts in universal algebra, **subuniverse** and **subalgebra**. Suppose $𝑨 = ⟨A, F^𝑨⟩$ is an algebra. Recall, the (nonempty) set 𝐴 is called the **universe** of 𝑨.

We call a subset 𝐵 ⊆ 𝐴 **closed under** (the operations in) 𝑓<sup>𝑨</sup> if for each 𝑓 ∈ 𝐹 and all 𝑏 : ρ𝑓 → 𝐵 we have 𝑓<sup>𝑨</sup>, 𝑏 ∈ 𝐵.

If a subset 𝐵 ⊆ 𝐴 is closed under 𝑓<sup>𝑨</sup>, then we call 𝐵 a **subuniverse** of 𝑨.

If 𝐵 ≠ ∅ is a subuniverse of 𝑨, and if we let 𝐹<sup>𝑩</sup> = { 𝑓<sup>𝑨</sup> ↾ B : f ∈ F \}$, then $𝑩 = ⟨ B, F^𝑩 ⟩$ is an algebra, called a **subalgebra** of 𝑨. Conversely, all subalgebras are of this form.

If 𝑩 is a subalgebra of 𝑨, we denote this fact by 𝑩 ≤ 𝑨. Similarly, we write 𝐵 ≤ 𝑨 if 𝐵 is a subuniverse of 𝑨 (relying on context and notation to disambiguate). It helps to keep in mind the following consequence of the definitions:

*The empty set is a subuniverse of every algebra, but the universe of an algebra is never empty*.

In other terms, if S(𝑨) denotes the collection of all subalgebras of 𝑨, then

S(𝑨) = {⟨B, 𝐹<sup>𝑩</sup>⟩ : ∅ ≠ B ≤ 𝑨\}.$$

If 𝒦 is a class of 𝑆-algebras, then the class of all subalgebras of algebras in 𝒦 is denoted by S(𝒦).

It is obvious that the intersection of subuniverses is again a subuniverse, a fact we will record below and formalize in [Agda][] later.

#### Subuniverse generation

As above S(𝑨) denotes the collection of all subalgebras of 𝑨. If 𝑨 is an algebra and 𝐴₀ ⊆ 𝐴 a subset of the universe of 𝑨, then the **subuniverse of** 𝑨 **generated by** 𝐴₀ is denoted by Sg<sup>𝑨</sup>(𝐴₀) and defined to be the smallest subuniverse of 𝑨 containing 𝐴₀. Equivalently,

Sg<sup>𝑨</sup>(𝐴₀)  =  ⋂ { U ∈ S(𝑨) ∣ 𝐴₀ ⊆ U }.

We can also use recursion to define the **subuniverse of** 𝑨 **generated by a set** and prove that this new definition is equivalent to the one given above. We do so below.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Subdirect products


If 𝑘, 𝑛 ∈ ℕ, if 𝐴 = (𝐴₀, 𝐴₁, …, 𝐴<sub>𝑛-1</sub>) is a list of sets, and if σ : 𝑘 → 𝑛 is a 𝑘-tuple, then a relation 𝑅 over 𝐴 with scope σ is a subset of the Cartesian product

𝐴<sub>σ(0)</sub> × 𝐴<sub>σ(1)</sub> × ⋯ × 𝐴<sub>σ(𝑘-1)</sub>.

Let 𝑆 = (𝐹, ρ) be a signature and for each 𝑖 < 𝑛 let 𝑨ᵢ = (𝐴ᵢ, 𝐹) be an 𝑆-algebra. If 𝑨 = ∏<sub>𝑖 < 𝑛</sub>𝑨ᵢ is the product of these algebras, then a relation 𝑅 over 𝐴 with scope σ is called **compatible with** 𝐴 if it is closed under the basic operations in 𝐹. In other words, 𝑅 is compatible if the induced algebra 𝑹 = (𝑅, 𝐹) is a subalgebra of Π<sub>𝑗 < 𝑘</sub>𝑨<sub>σ(𝑗)</sub>.

If 𝑅 is compatible with the product algebra and if the projection of 𝑅 onto each factor is surjective, then 𝑹 is called a **subdirect product** of the algebras in the list (𝐴<sub>σ(0)</sub>, 𝐴<sub>σ(1)</sub>, …, 𝐴<sub>σ(𝑘-1)</sub>). We denote this situation by writing 𝑹 ≤<sub>sd</sub> Π<sub>𝑗 < 𝑘</sub>𝑨<sub>σ(𝑗)</sub>.

**Formalization**. (not yet implemented)

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Homomorphisms
Let 𝑩 = (B, 𝐹<sup>𝑩</sup>) and 𝑪 = (C, 𝐹<sup>𝑪</sup>) be algebras of the same signature, and let ℎ : 𝐵 → 𝐶 be a function (e.g., on sets).

Take an operation symbol 𝑓 ∈ 𝐹, and suppose that for all ρ𝑓-tuples 𝑏: ρ𝑓 → 𝐵 of 𝐵 the following equation holds:

ℎ (𝑓<sup>𝑩</sup> 𝑏) = 𝑓<sup>𝑪</sup> (ℎ ∘ 𝑏).

Then ℎ is said to **respect the interpretation of** 𝑓.

If ℎ respects the interpretation of every 𝑓 ∈ 𝐹, then we call ℎ a **homomorphism** from 𝑩 to 𝑪, and we write ℎ ∈ Hom(𝑩, 𝑪), or simply, ℎ : 𝑩 → 𝑪. (Later, in [Agda][], we will typically use notation like `h : hom B C`, or sometimes `h : Hom 𝑩 𝑪`.)

A homomorphism ℎ : 𝑩 → 𝑪 is called an **epimorphism** if for every algebra 𝑫 and pair 𝑔₁, 𝑔₂ : 𝑪 → 𝑫 of homomorphisms, the equation 𝑔₁ ∘ ℎ = 𝑔₂ ∘ ℎ implies 𝑔₁ = 𝑔₂. We often write ℎ : 𝑩 ↠ 𝑪, and say that "ℎ is **epi**" and "ℎ maps 𝑩 **homomorphically onto** 𝑪" in this case.

A homomorphism ℎ : 𝑩 → 𝑪 is called a **monomorphism** if for every algebra 𝑨 and every pair 𝑔₁, 𝑔₂ : 𝑨 → 𝑩 of homomorphisms, the equation ℎ ∘ 𝑔₁ = ℎ ∘ 𝑔₂ implies 𝑔₁ = 𝑔₂. We sometimes write ℎ : 𝑨 ↣ 𝑩, and say that "ℎ is **mono**" and "ℎ maps 𝑩 **homomorphically into** 𝑪" in this case.

If 𝑨, 𝑩 are 𝑆-algebras and ℎ : 𝑨 → 𝑩 is a homomorphism, then the image ℎ(𝐴) of 𝐴 under ℎ is called a **homomorphic image** of 𝑨. The collection of all homomorphic images of an 𝑆-algebra 𝑨 is the class denoted and defined by

H(𝑨) := {ℎ(𝐴) : ℎ is a homomorphism from 𝑨 to some other 𝑆-algebra}.

If 𝒦 is a class of 𝑆-algebras, then the class of all homomorphic images of algebras in 𝒦 is denoted by H(𝒦).

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Clones

An **operational clone** (or just **clone**) on a nonempty set 𝐴 is a collection of operations on 𝐴 that contains the projection operations and is closed under general composition.

Let 𝓒𝓵(𝐴) denote the collection of all clones on 𝐴.

The smallest clone on 𝐴 is the **clone of projections**, which we denote and define as follows:

**Proj** 𝐴 = ⋃<sub>𝑖 < 𝑛 < ω</sub>  {π<sup>𝑛<sub>𝑖</sub></sup> : ∀ 𝑎 ∈ 𝐴<sup>𝑛</sup>,  π<sup>𝑛<sub>𝑖</sub></sup>, 𝑎 = 𝑎(𝑖)}.

Recall, the natural number 𝑘 < ω can be constructed as (or at least identified with) the set {0, 1, …, 𝑘-1}. For each 𝑘 < ω, denote and define the tuple πᵏ : (𝑘 → 𝐴) → 𝐴 of all 𝑘-ary projections on 𝐴 as follows: for each 0 ≤ 𝑖 < 𝑘, πᵏ(𝑖) is the 𝑖-th 𝑘-ary projection operation that takes each 𝑘-tuple 𝑎 : 𝑘 → 𝐴 to its entry at index 𝑖,

π<sup>𝑘</sup>(𝑖) 𝑎 = 𝑎(𝑖).

The **clone of term operations** of an 𝑆-algebra 𝑨 is the smallest clone on 𝐴 containing the basic operations of 𝑨; this is denoted and defined by

Clo(𝐹<sup>𝑨</sup>) = ⋂ { U ∈ 𝓒𝓵 𝐴 ∣ 𝐹<sup>𝑨</sup> ⊆ U}.$$

The set of 𝑛-ary members of Clo(𝐹<sup>𝑨</sup>) is sometimes denoted by Clo𝑛(𝐹<sup>𝑨</sup>) (despite the fact that the latter is not a clone).

The **clone of polynomial operations** (or **polynomial clone**) of an 𝑆-algebra 𝑨 is denoted by Pol(𝐹<sup>𝑨</sup>) and is defined to be the clone generated by the collection consisting of the basic operations (i.e., 𝐹<sup>𝑨</sup>) of 𝑨 along with the **constants** on 𝐴.

The set of 𝑛-ary members of Pol(𝐹<sup>𝑨</sup>) is sometimes denoted by Polₙ(𝐹<sup>𝑨</sup>).

The clone Clo(𝐹<sup>𝑨</sup>) is associated with the algebra 𝑨 only insofar as the former is constructed out of the basic operations of 𝑨 and the set 𝐴 on which those operations are defined. However, all that is required when defining a clone is a set 𝐴 and some collection 𝐹 of operations defined on 𝐴; from only these ingredients, we can construct the clone generated by 𝐹, which we denote by Clo(𝐹).

Thus *the clone of terms operations can be implemented as an inductive type*. We will make this precise below.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Terms and free algebras

This section is based on the section of the same title in Cliff Bergman's excellent textbook (Bergman:2012). Apart from notation, our presentation is quite similar in style and content to Cliff's, but we have attempted to give a more compact, abridged treatment in order to get more quickly to our ultimate goal (in the next chapter), which is to show how it is possible to express the concepts and theorems of universal algebra in type theory and to formalize them in the Agda language. We refer the reader to Section 4.3 of Bergman:2012 for more details and examples about "classical" (informal) universal algebra than we present here.

#### Terms

Fix a signature 𝑆 = (𝐹, ρ), let 𝑋 be a set of **variables**, and assume 𝑋 ∩ 𝐹 = ∅.

By a **word** on 𝑋 ∪ 𝐹 we mean a nonempty, finite sequence of members of 𝑋 ∪ 𝐹, and we will denote the concatenation of such sequences by simple juxtaposition.

Let 𝐹₀ denote the set of nullary operation symbols of 𝑆. We define by induction on 𝑛 the sets 𝑇ₙ of **terms on** 𝑋 ∪ 𝐹 as follows (cf. Bergman:2012 Def. 4.19):

𝑇₀ = X ∪ 𝐹₀;

𝑇<sub>𝑛+1</sub> = 𝑇ₙ ∪ { 𝑓 𝑠 ∣ 𝑓 ∈ 𝐹, 𝑠: ρ𝑓 → 𝑇ₙ },

and we define the collection of **terms of signature** 𝑆 **over** 𝑋 by 𝑇(𝑋) = ⋃<sub>𝑛 < ω</sub>𝑇ₙ.

By an 𝑆-**term** we mean a term in the signature 𝑆.

The definition of 𝑇(𝑋) is recursive, indicating that *terms could be implemented as an inductive type*. We will confirm this below when we implement terms in Agda. Moreover, we will formalize an algebraic structure on 𝑇(𝑋), called the **term algebra** in the signature 𝑆. We describe it here and then state and prove some basic facts about this important algebra. The formalization of these objects in [Agda][] will give us a chance to show off inductively defined types in Agda.

If 𝑡 is a term, then the **height** of 𝑡 is denoted by ∣𝑡∣ and defined to be the least 𝑛 such that 𝑡 ∈ 𝑇ₙ. The height is a useful index for recursion and induction.

If 𝑇(𝑋) is nonempty (equivalently, 𝑋 ∪ 𝐹₀ is nonempty), then we can impose upon it an algebraic structure, which we will denote by 𝑻(𝑋). We call 𝑻(𝑋) the **term algebra in the signature** 𝑆 **over** 𝑋; it is constructed as follows:

+ for each operation symbol 𝑓 ∈ 𝐹, let 𝑓<sup>𝑻(𝑋)</sup> be the operation on 𝑇(𝑋) that maps each tuple 𝑠 : ρ𝑓 → 𝑇(𝑋) to the formal term 𝑓 𝑠;
+ define 𝑻(𝑋) to be the algebra with universe 𝑇(𝑋) and operations {𝑓<sup>𝑻(X)</sup> | 𝑓 ∈ 𝐹}.

#### Free algebras

Fix a signature 𝑆 = (𝐹, ρ), let 𝒦 be a class of 𝑆-algebras, let 𝑼 = (𝑈, 𝐹<sup>𝑼</sup>) be an 𝑆-algebra, and let 𝑋 be a subset of 𝑈. We say that

1.  𝑼 has the universal mapping property for 𝒦 over 𝑋 if for every 𝑨 ∈ 𝒦 and every function ℎ : 𝑋 → 𝐴, there is a homomorphism
ℎ' : 𝑼 → 𝑨 that agrees with ℎ on 𝑋;
2.  𝑼 is free for 𝒦 over 𝑋 if it has the universal mapping property and is generated by 𝑋;
3.  𝑼 is free in 𝒦 over 𝑋 if it is free for 𝒦 over 𝑋 and belongs to 𝒦.

We use the next definition to take a free algebra *for* a class 𝒦 and produce the free algebra *in* 𝒦.

Let 𝒦 be a class of 𝑆-algebras and 𝑨 an 𝑆-algebra. Define

+ ψ(𝒦, 𝑨) := {θ ∈ Con 𝑨 : 𝑨/θ ∈ S(𝒦)} and

+ Ψ(𝒦, 𝑨) := ⋀ ψ(𝒦, 𝑨).

Notice that ψ(𝒦, 𝑨) may be empty, in which case Ψ(𝒦, 𝑨) = 1<sub>𝐴</sub> and 𝑨/Ψ(𝒦, 𝑨) is trivial.

The free algebra is constructed using the above definitions for the special case in which 𝑨 is the algebra 𝑻(𝑋) of 𝑆-terms over 𝑋.

Since 𝑻(𝑋) is free for the class 𝓚(𝑆) of all 𝑆-algebras, it follows that 𝑻(𝑋) is free for every subclass 𝒦 of 𝓚(𝑆).

Of course, 𝑻(𝑋) is not necessarily a member of 𝒦, but we can form the quotient of 𝑻(𝑋) modulo the congruence Ψ(𝒦, 𝑻(𝑋)), which we denote by

𝔽(𝒦, 𝑋) := 𝑻(𝑋)/Ψ(𝒦, 𝑻(𝑋)).

The algebra 𝔽(𝒦, 𝑋) is called the **free algebra over** 𝒦 **generated by** 𝑋.

It should be clear that 𝔽(𝒦, 𝑋) is a subdirect product of the algebras {𝑻(𝑋)/θ}, where θ ranges over ψ(𝒦, 𝑻(𝑋))}, so it belongs to SP(𝒦). Therefore, we say that 𝔽(𝒦, 𝑋) is free *in* SP(𝒦).

We formalize the free algebra in the [Equational Logic in Agda](#equational-logic-in-agda) section.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Arity

We denote and define the set 𝑋 := {𝑥₀, 𝑥₁, … } of variable symbols, and for each natural number 𝑛 we let 𝑋ₙ := {𝑥₀, 𝑥₁, …, 𝑥ₙ}.

Let 𝑆 = (𝐹, ρ) be a signature, 𝑨 an 𝑆-algebra, and 𝑻(X) the term algebra over 𝑋; that is,

𝑨 := (A, 𝐹<sup>𝑨</sup>) and 𝑻(X) := (T(X), 𝐹<sup>𝑻(X)</sup>).

Each operation symbol 𝑓 ∈ 𝐹 gives rise to

1. a ρ𝑓-ary operation on 𝑇(𝑋), denoted by 𝑓<sup>𝑻(X)</sup>, which maps each tuple 𝑠 : ρ𝑓 → 𝑇(𝑋) to the formal term 𝑓 𝑠 in 𝑇(𝑋), and
2. a ρ𝑓-ary operation on 𝐴, denoted by 𝑓<sup>𝑨</sup>, which maps each tuple 𝑎 : ρ𝑓 → 𝐴 to the element 𝑓<sup>𝑨</sup>(𝑎) in 𝐴. The operation 𝑓<sup>𝑨</sup> is called the **interpretation of** 𝑓 **in the algebra** 𝑨.

<!-- #### Essential arity -->

<!-- The definition of arity of an operation or term is a bit nuanced as the next example demonstrates. -->

<!-- **Example**. -->

<!-- > Suppose 𝑓 is a binary term, and 𝑝 and 𝑞 are ternary terms. -->
<!-- > -->
<!-- > What is the arity of the following term? -->
<!-- > -->
<!-- > $$𝑡(𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧) = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))$$ -->
<!-- > -->
<!-- > On the face of it, it seems safe to say that 𝑡 has arity 6, since it -->
<!-- > is expressible as a function of 6 variables. -->
<!-- > -->
<!-- > But what if we decided to throw in some useless (or "dummy") -->
<!-- > variables, like so, -->
<!-- > -->
<!-- > $$t'(𝑢', 𝑣', 𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧, 𝑧') = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))?$$ -->
<!-- > -->
<!-- > And what happens if $𝑝(𝑥, 𝑦, 𝑧) = 𝑧$, so that 𝑝 depends on just one of -->
<!-- > its arguments? Then we could replace it with $𝑝'(𝑧) = 𝑝(𝑥, 𝑦, 𝑧)$, and -->
<!-- > 𝑡 could be expressed as, -->
<!-- > -->
<!-- > $$𝑡''(𝑢, 𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))).$$ -->
<!-- > -->
<!-- > The respective arities of $𝑡, 𝑡'$ and $𝑡''$ are 6, 9, and 5, yet -->
<!-- > arity1--arity3 merely give three different ways to present the term -->
<!-- > $𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))$. -->

<!-- As the example demonstrates, the notion of arity of a term is not -->
<!-- uniquely defined (modulo equivalence of terms). As such, it is sometimes -->
<!-- useful to speak of the **essential arity** of a term, which is defined -->
<!-- to be the minimum number of variables required to express that term; it -->
<!-- should be clear that this is equal to the number of arguments with -->
<!-- respect to which the term is not constant. -->

<!-- **Example**. -->

<!-- > It is impossible to know the essential arity of a term until we know -->
<!-- > that of each of its subterms. -->
<!-- > -->
<!-- > Picking up where we left off in the previous example, suppose 𝑓 -->
<!-- > depends on both of its arguments and $𝑞(𝑢, 𝑣, 𝑤) = 𝑓(𝑣, 𝑤)$. Then 𝑡 is -->
<!-- > expressible as -->
<!-- > -->
<!-- > $$s(𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑓(𝑣, 𝑤))$$ -->
<!-- > -->
<!-- > and we finally see the lower bound on the number of variables required -->
<!-- > to express 𝑡, namely 4. Therefore, 𝑡 has essential arity 4. -->

-------------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Term Operations

Above we defined a term in a given signature. When we interpret such a term in a particular algebraic structure, we get what is known as a term operation. In this section we explain how one defines the interpretation of an 𝑆-term in an 𝑆-algebra, and thus how one obtains a term *operation*.

As usual, for each 0 < 𝑛 < ω we identify the 𝑛-tuple (𝑥₀, 𝑥₁, …, 𝑥<sub>𝑛-1</sub>) with the function 𝑥 : 𝑛 → 𝑋ₙ defined by
$x\, i = x_i$ (0 ≤ 𝑖 < 𝑛).

Recall, a term 𝑡 is either a variable, say, 𝑡 = 𝑥, or has the form 𝑡 = 𝑓 𝑠 for some operation symbol 𝑓 ∈ 𝐹, and some ρ𝑓-tuple 𝑠 : ρ𝑓 → 𝑇(𝑋) of terms.

Let 𝑡 ∈ 𝑇(𝑋) be an 𝑆-term. Given an arbitrary 𝑆-algebra 𝑨, we will define a **term operation** on 𝑨 by giving 𝑡 an *interpretation* in 𝑨. Diverging from standard notation slightly, we will denote this operation by 𝑡 ̇ 𝑨 for reasons that will hopefully be clear when we define term operations in [Agda][]. Similarly, 𝑡 ̇ 𝑩 will denote the interpretation of the term 𝑡 in the algebra 𝑩.

The **term operation** 𝑡 ̇ 𝑨 is defined by recursion on the height ∣𝑡∣ of 𝑡 as follows: for each assignment 𝑎 : 𝑋 → 𝐴 (of values in 𝐴 to variables in 𝑋),

1.  (∣𝑡∣ = 0) if 𝑡 is the variable 𝑥, then (𝑡 ̇ 𝑨) 𝑎 = 𝑎 𝑥,
2.  (∣𝑡∣ = 𝑛+1) if 𝑡 = 𝑓 𝑠 where 𝑓 is an operation symbol and 𝑠 : ρ𝑓 → 𝑇(X) is a tuple of terms whose heights are at most 𝑛 (i.e., ∀ 𝑖, ∣𝑠 𝑖∣ ≤ 𝑛), then 𝑡 ̇ 𝑨 = 𝑓<sup>𝑨</sup> 𝑠<sup>𝑨</sup>.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Models and theories

Let 𝑆 = (𝐹, ρ) be a signature and 𝑋 := {𝑥₀, 𝑥₁, … } a countable collection of variable symbols.

An **identity in the signature** 𝑆 (or "𝑆-identity") is an ordered pair of terms (𝑝, 𝑞) ∈ 𝑇(𝑋) × 𝑇(𝑋). We usually write 𝑝 ≈ 𝑞 to indicate such an identity. Although, when we have a collection of identities, say, Σ, we could indicate that 𝑝 ≈ 𝑞 is among the identities in Σ by writing (𝑝, 𝑞) ∈ Σ. We sometimes refer to an identity as an **equation**; for us, the words "identity" and "equation" are synonyms.

Let 𝓚(𝑆) and 𝓔(𝑆) denote the classes of all 𝑆-algebras and 𝑆-identities, respectively.

For 𝑨 ∈ 𝒦 ⊆ 𝓚(𝑆) and (𝑝, 𝑞) ∈ ℰ ⊆ 𝓔(𝑆), we say that

+ 𝑨 **models** 𝑝 ≈ 𝑞, denoted 𝑨 ⊧ 𝑝 ≈ 𝑞, just in case 𝑝 ̇ 𝑨 = 𝑞 ̇ 𝑨 extensionally (i.e., ∀ 𝑎 : 𝑋 → 𝐴, (𝑝 ̇ 𝑨) 𝑎 = (𝑞 ̇ 𝑨) 𝑎);
+ 𝑨 **models** ℰ, denoted 𝑨 ⊧ ℰ, just in case 𝑨 ⊧ 𝑝 ≈ 𝑞 holds for every (𝑝, 𝑞) ∈ ℰ;
+ 𝒦 **models** 𝑝 ≈ 𝑞 just in case 𝑨 ⊧ 𝑝 ≈ 𝑞 holds for every 𝑨 in 𝒦;
+ 𝒦 **models** ℰ just in case 𝑨 ⊧ ℰ for every 𝑨 ∈ 𝒦.

**Notation**. To produce the symbols ≈ and ⊧ in Emacs `agda2-mode`, type`\~~` and `\models` (resp.). To denote "𝒦 models 𝑝 ≈ 𝑞" we will use 𝒦 ⊧ 𝑝 ≋ 𝑞 instead of the more standard 𝒦 ⊧ 𝑝 ≈ 𝑞 because we distinguish it from 𝑨 ⊧ 𝑝 ≈ 𝑞 in our Agda implementation. The symbol ≋ is produced in Emacs `agda2-mode` with `\~~~`.

The binary relation ⊧ induces an obvious Galois connection. Indeed, the Galois pair (Mod, Th) is defined as follows: for all ℰ ⊆ 𝓔(𝑆) and 𝒦 ⊆ 𝓚(𝑆),

Mod ℰ := { 𝑨 ∈ 𝓚(𝑆) : 𝑨 ⊧ ℰ } and Th 𝒦 := {ℯ ∈ 𝓔(𝑆) : 𝒦 ⊧ ℯ }.

The first of these, the class of **models** of ℰ, contains those and only those algebras modeling every identity in ℰ. It is called an **equational class**, and ℰ is called an **equational base** for, or an **axiomatization** of, the class.

Dually, Th 𝒦 is the class of identities modeled by every algebra in 𝒦. Such a class of identities is called an **equational theory**.

Alternatively and equivalently we could define "equational class" and "equational theory" in terms of the two closure operators induced by the Galois pair (Mod, Th). Indeed, Mod Th : 𝒫 𝓚(𝑆) → 𝒫 𝓚(𝑆) is a closure operator on 𝓚(𝑆) and Th Mod : 𝒫 𝓔(𝑆) → 𝒫 𝓔(𝑆) is a closure operator on 𝓔(𝑆), and

+ an **equational class** is a Mod Th-closed class of 𝑆-algebras;
+ an **equational theory** is a Th Mod-closed set of 𝑆-identities

(Here, 𝒫 denotes the powerset operator.)

**N.B.** An equational class is sometimes referred to as a **variety**; this is because of the celebrated Birkhoff theorem which states that a class of algebraic structures is an equational class if and only if it is closed under the taking of homomorphic images (H), subalgebras (S), and products (P). A formal Agda proof of Birkhoff's theorem is one of our main goals which we achieve in the birkhoff module described below.

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
### Basic facts

We conclude this chapter with a list of basic facts and their (informal) proofs. These results are classical, straightforward consequences of the definitions above. Each of these observations is formalized in [Agda][] in the [UALib](https://gitlab.com/ualib/ualib.gitlab.io).

Throughout this section,

𝑨 = (𝐴, 𝐹<sup>𝑨</sup>), 𝑩 = (𝐵, 𝐹<sup>𝑩</sup>), 𝑪 = (𝐶, 𝐹<sup>𝑪</sup>⟩ are algebras in the same signature 𝑆 = (𝐹, ρ).

#### Equalizers

We start with the simple observation that equalizers of homomorphisms are subuniverses.

**Ex 1.4.6.a** (Bergman:2012)

If $g, h : \mathrm{Hom}(𝑨, 𝑩)$ are homomorphisms from 𝑨 to 𝑩, then the **equalizer** of $g$ and $h$, which we denote
$𝖤(g,h) = \{a: A ∣ g\, a = h\, a\}$, is a subuniverse of 𝑨.

*Proof*. Fix arbitrary $f ∈ F$ and $a : ρf → 𝖤(g,h)$. We show that $g (f^𝑨 \, a) = h (f^𝑨 \, a)$, as this will show that
$𝖤(g, h)$ is closed under the operation $f^𝑨$ of $𝑨$. For all $i<ρ f$ we have $a \, i ∈ 𝖤(g,h)$, so $g\, a \, i= h\, a\, i$.
Therefore (by function extensionality) $g ∘ a = h ∘ a$ and so, by definition of homomorphism,

$$g  (f^𝑨\,a) = f^𝑩 (g ∘ a) = f^𝑩 (h ∘ a) = h (f^𝑨\, a).$$

☐

<!-- The Agda formalization of this result and its proof is presented in obs 1 in agda. -->

#### Homomorphisms

Another easy fact is that composing homomorphisms results in a homomorphism.

**Composing homs gives a hom** If $g: \mathrm{Hom}(𝑨, 𝑩)$ and $h: \mathrm{Hom}(𝑩, 𝑪)$ (homomorphisms from 𝑨 to 𝑩 and 𝑩 to 𝑪, resp.), then $h \circ g : \mathrm{Hom}(𝑩, 𝑪)$ (a homomorphisms from 𝑨 to 𝑪).

Another elementary result is that homomorphisms are uniquely determined by the values they take on generating sets.

**Ex 1.4.6.b** (Bergman:2012) Let 𝑨 = ⟨𝐴, …⟩ and 𝑩 be 𝑆-algebras and $f, g$ homomorphisms from 𝑨 to 𝑩. If the subset 𝐴₀ ⊆ 𝐴 generates 𝑨, and if $f$ and $g$ agree on 𝐴₀, then $f = g$.

*Proof*. We show that $f$ and $g$ are extensionally equal (that is, $f\, a = g\, a$ for every $a \in A$). So, fix an arbitrary $a \in A$. Since $𝐴₀$ generates 𝑨, there exists a term $t$ and a tuple $𝒂 : X → 𝐴₀$ of generators such that $a = t^𝑨\, 𝒂$.

Since $f|_{𝐴₀} = g|_{𝐴₀}$, we have

$$f ∘ 𝒂 = (f\, 𝒂(0), f\, 𝒂(1), \dots) = (g \, 𝒂(0), g\, 𝒂(1), \dots) = g ∘ 𝒂,$$

so

$$f\, a = f(t^𝑨 \, 𝒂) = t^𝑩 (f ∘ 𝒂) = t^𝑩 (g ∘ 𝒂) = g(t^𝑨 \,𝒂) = g\, a.$$

☐

A corollary of the last result is an easily proved bound on the cardinality of $|\mathrm{Hom}(𝑨, 𝑩)|$.

**Ex 1.4.6.c** (Bergman:2012) If $A, B$ are finite and $X$ generates 𝑨, then $|\mathrm{Hom}(𝑨, 𝑩)| ≤ |B|^{|X|}$.

*Proof*. A homomorphism is uniquely determined by its restriction to a generating set. If $X$ generates 𝑨, then since there are exactly $|B|^{|X|}$ functions from $X$ to $B$ we have $|\mathrm{Hom}(𝑨, 𝑩)| ≤ |B|^{|X|}$. ☐

Here is an elementary result about factorability of homomorphisms. 

**Factorization Theorem**. If $g ∈$ Hom(𝑨, 𝑩) is surjective, if ℎ ∈ Hom (𝑨, 𝑪), and if ker $g$ ⊆ ℎ, then $∃ f ∈ \mathrm{Hom}(𝑩, 𝑪), \ h = f ∘ g$.

*Proof*. We define 𝑓 ∈ Hom(𝑩, 𝑪) as follows: Fix 𝑏 ∈ 𝐵. Since $g$ is surjective, the set $g^{-1}\{b\} ⊆ A$ is nonempty, and
since ker $g$ ⊆ ker ℎ, it is clear that every element of $g^{-1}\{b\}$ is mapped by ℎ to a single element of 𝐶.

Label this element $c_b$. That is, $h(a) = c_b$, for all $a ∈ g^{-1}\{b\}$.

For each such 𝑏, and its associated $c_b$, define $f(b) = c_b$.

It is then easy to see that $f ∘ g = h$. Indeed, for each 𝑎 ∈ 𝐴, we have $a ∈ g^{-1}\{g(a)\}$, so $f\,g(a) = h(a)$ by definition.

Finally, to prove that $k$ is a homomorphism, fix an operation symbol $f ∈ F$ and a tuple $b:ρf → B$; we will show that $f^𝑪 (k ∘ b) = k (f^𝑩(b))$.

Let $a: ρf → A$ be such that $g ∘ a = b$. Then the left hand side of hom1 is $f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a)$, which is equal to $h (f^𝑨 (a))$ since $h$ is a homomorphism.

Therefore,

$$f^𝑪 (k ∘ b) &= f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a)\\
        & = h (f^𝑨 (a)) = (k ∘ g)(f^𝑨 (a))\\
        & = k (f^𝑩 (g ∘ a)) = k (f^𝑩 (b)),$$

as desired, where the penultimate equality holds by virtue of the fact that $g$ is a homomorphism. ☐

Next we observe that the intersection of subuniverses is again a subuniverse.

**Subuniverse Intersection Lemma**. Suppose $A_i ≤ 𝑨$ for all $i$ in some set $I$. Then $⋂_{i∈ I} A_i$ is a subuniverse of $𝑨$.

*Proof*. (easy exercise)

#### Subuniverse Generation

Next is a theorem that provides a means of generating subuniverses recursively.

**Thm 1.14** (Bergman:2012) Let $𝑨 = ⟨A, F^{𝑨}⟩$ be an algebra in the signature $σ = (F, ρ)$ and let $A_0$ be a subset of $A$. Define, by recursion on $n$, the sets $A_n$ as follows:

+ If $A_0 = ∅$, then $A_n = ∅$ for all $n<ω$.

+ If $A_0 ≠ ∅$, then $A_{n+1} =  A_n ∪ \{ f\, a ∣ f ∈ F, \ a : ρf → A_n\}$.

Then the subuniverse of 𝑨 generated by $A_0$ is $\mathrm{Sg}^𝑨(A_0) = ⋃_{n<ω} A_n$.

*Proof*. Let $Y := ⋃_{n < ω} A_n$. Clearly $A_n ⊆ Y ⊆ A$, for every $n < ω$. In particular $A = A_0 ⊆ Y$. We first show that Y is a subuniverse of 𝑨. Let $f$ be a basic $k$-ary operation and let $a: k → Y$ be a $k$-tuple of elements of $Y$. From the construction of $Y$, there is an $n < ω$ such that $∀ i,\ a,\ i ∈ A_n$. From its definition, $f \,a ∈ A_{n+1} ⊆ Y$. Since $f$ was arbitrary, it follows that $Y$ is a subuniverse of 𝑨 containing $A_0$. Thus, by SgDef, $\mathrm{Sg}^𝑨(A_0) ⊆ Y$.

For the opposite inclusion, it is enough to check, by induction on $n$, that $A_n ⊆ \mathrm{Sg}^𝑨(A_0)$. Clearly, $A_0 ⊆ \mathrm{Sg}^𝑨(A_0)$. Assume $A_n ⊆ \mathrm{Sg}^𝑨(A_0)$. We show $A_{n+1} ⊆ \mathrm{Sg}^𝑨(A_0)$. If $b ∈ A_{n+1} - A_n$, then $b = f\, a$ for a basic $k$-ary operation $f$ and some $a: k) → A_n$. But $∀ i, \ a i ∈ \mathrm{Sg}^𝑨(A_0)$ and since this latter object is a subuniverse, $b ∈ \mathrm{Sg}^𝑨(X)$ as well. Therefore, $A_{n+1} ⊆ \mathrm{Sg}^𝑨(A_0)$, as desired. ☐

**Lem 3.1** and **Thm 3.2** (Bergman:2012)

Let ℎ : 𝑨 → 𝑩 be a homomorphism.

+ If 𝑈 is a subuniverse of 𝑨, then ℎ(𝑈) = {ℎ(𝑢) : 𝑢 ∈ 𝑈} is a subuniverse of 𝑩.
+ If 𝑉 is a subuniverse of 𝑩, then ℎ⁻¹{𝑉} is a subuniverse of 𝑨.
+ If 𝑋 is a subset of 𝐴, then $ℎ(\mathrm{Sg}^𝑨(𝑋)) = \mathrm{Sg}^𝑩(ℎ(𝑋))$.

*Proof*. The first two items are easy to prove (exercise). For the third item, it is easy to check that ℎ is order-preserving on subsets. This and the first two items yield

$$𝑋 ⊆ \mathrm{Sg}^𝑨(𝑋) \; ⇒ \; ℎ(𝑋) ⊆ ℎ(\mathrm{Sg}^𝑨(𝑋)) \; ⇒ \; \mathrm{Sg}^𝑩(ℎ(𝑋)) ⊆ ℎ(\mathrm{Sg}^𝑨(𝑋)).$$

Conversely, using the lemma again,

$$X ⊆ h⁻¹ h(𝑋) ⊆ h⁻¹(\mathrm{Sg}^𝑩(h(X))) \; ⇒ \; \mathrm{Sg}^𝑨(𝑋) ⊆ h⁻¹(\mathrm{Sg}^𝑩(h(X)))$$

and this implies

$$h(\mathrm{Sg}^𝑨(𝑋)) ⊆ h(h⁻¹(\mathrm{Sg}^𝑩(h(X)))) ⊆ \mathrm{Sg}^𝑩(h(X)).$$

**Thm 4.3** (Bergman:2012)
Let 𝐴 be a set and let $F ⊆ \mathrm{Op}(A):= ⋃_{n<ω} A^{A^n}$ be a collection of operations on 𝐴. Define $F_0 := \mathrm{Proj} (A)$ (the set of projections on $A$) and for all $0 ≤ n < ω$ let

$$F_{n+1} := F_n ∪ \{ f g \mid f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.$$

Then $\mathrm{Clo}(F) = ⋃_n F_n$.

*Proof*. Let $F̄ = ⋃_n F_n$. It is easy to argue by induction that every $F_n$ is a subset of $\mathrm{Clo}(F)$. Thus, $F ⊆ \mathrm{Clo}(F)$.

For the converse, we must show that $F̄$ is a clone that contains $F$. Obviously $F̄$ contains the projection operations, $F_0 ⊆ F̄$. For every $f ∈ F$, we have $f π^k ∈ F_1 ⊆ F̄$, where $k:= ρ f$. We are reduced to showing that $F̄$ is closed under generalized composition. This holds by the following claim.

**Claim**. If $f ∈ F_n$ and $g_0, \dots, g_{ρ f-1} ∈ F_m$ are all $k$-ary, then $f g \in F_{n+m}$, where we have defined
$g: ρf → (k → A) → A$ to be the tuple given by $g\,i = g_i$ for each $0 ≤ i < ρ f$.

Note that the types match up; indeed, for each $a: (k → A) → A$, we have

$$f (g ∘ a) = f(g_0(a_0, \dots, a_{k-1}),$$

We prove the claim by induction on $n$. If $n = 0$ then $f$ is a projection, so $f g = g_i ∈ F_{0+m}$ for some $0≤ i < ρ f$. Assume the claim holds for $n$ and that $f ∈ F_{n+1} - F_n$. From the definition, there is a $t$-ary operation $f_i ∈ F$ and a $t$-tuple $h = (h_0, \dots, h_{t-1}) ∈ t → F_n$, such that $f = f_i h$. (Note that $h: t → (ρf → A) → A$ is given by $h(j) = h_j$, and that the arity of each $h_i$ must be equal to that of $f$, namely $ρ f$.)

By the induction hypothesis, for each $i ≤ k$, $h_i' = h_i g \in F_{n+m}$ (where, as above, $g = (g_0, \dots, g_{k-1})$).

Applying the definition, $f_1 h' ∈ F_{n+m+1} = F_{(n+1)+m}$. Since

$$f_1 h' = f_1 ∘ (h_1 g, \dots, h_t g) = f g,$$

the claim is proved. □

**Thm 4.21** (Bergman:2012)

1. 𝑇(𝑋) is generated by 𝑋.
2. For every 𝑆-algebra 𝑨 = $⟨𝐴, 𝐹^𝑨⟩$ and function $g: X → A$ there is a unique homomorphism ℎ : 𝑻(𝑋) → 𝑨 such that $h|_X = g$. We call such ℎ the **lift of** $g$ **from** 𝑋 **to** 𝑻(𝑋) (or, more simply, the **lift of** $g$ **to** 𝑻(𝑋)).

*Proof*. The definition of 𝑻(𝑋) exactly parallels the construction in Obs. 7. That accounts for the first assertion. For the
second, define ℎ 𝑡 by induction on the height of 𝑡. Suppose ∣𝑡∣ = 0. Then 𝑡 ∈ 𝑋 ∪ 𝐹₀. If 𝑡 ∈ 𝑋, then define ℎ 𝑡 = 𝑔 𝑡. If 𝑡
∈ 𝐹₀, then let $h\,t = t^𝑨$. For the induction step, assume ∣𝑡∣ = 𝑛 + 1. Then 𝑡 = 𝑓 𝑠 for some 𝑓 ∈ 𝐹 and 𝑠 : ρ 𝑓 → 𝑇ₙ, where for each 0 ≤ 𝑖 &lt; ρ𝑓 the term 𝑠 𝑖 has height at most 𝑛. We define $h\,t = f^𝑨(h ∘ s) = f^𝑨(h\,s_1, …, h\,s_k)$. By its very definition, ℎ is a homomorphism that agrees with $g$ on 𝑋. The uniqueness of ℎ follows from Obs 3.

Let 𝒦 be the class of 𝑆-algebras. Then Obs %s &lt;obs 9&gt; can be restated as: 𝑻(𝑋) is free in 𝒦 over 𝑋. This is sometimes expressed by saying that 𝑻(𝑋) is **absolutely free** over 𝑋.

**Prop 4.23** (Bergman:2012) Let 𝑼 be free for 𝒦 over 𝑋. Then for every 𝑨 ∈ 𝒦 and $𝑔 : 𝑋 → 𝐴$, the lift of $g$ from 𝑋 to 𝑼 (defined in the second part of Obs %s &lt;obs 9&gt;) is unique.

*Proof*. The universal mapping property asserts the existence of the lift. The fact that 𝑼 is generated by 𝑋 accounts for uniqueness.

**Prop 4.24** (Bergman:2012) Let 𝑼₁ and 𝑼₂ be free in 𝒦 over 𝑋₁ and 𝑋₂ respectively. If ∣ 𝑋₁ ∣ = ∣ 𝑋₂ ∣, then 𝑼₁ ≅ 𝑼₂.

*Proof*. If ∣ 𝑋₁ ∣ = ∣ 𝑋₂ ∣, then there are mutually inverse bijections ℎ : 𝑋₁ → 𝑋₂ and ℎ⁻¹ : 𝑋₂ → 𝑋₁. Since 𝑼₂ ∈ 𝒦 and 𝑼₁ is free for 𝒦, there is a homomorphism ℎ̃₁ : 𝑼₁ → 𝑼₂ extending ℎ and, by the symmetric argument, a homomorphism ℎ̃₂ : 𝑼₂ → 𝑼₁ extending ℎ⁻¹. Now, ℎ̃₂ ∘ ℎ̃₁ is an endomorphism of 𝑼₁ extending the identity map, and so is the identity morphism on 𝑼₁. Thus, by unicity (Obs %s &lt;obs 9.1&gt;), ℎ̃₂ ∘ ℎ̃₁ is the identity morphism on 𝑼₁. By the symmetric argument, ℎ̃₁ ∘ ℎ̃₂ is the identity morphism on 𝑼₂. Thus 𝑼₁ ≅ 𝑼₂. It follows from Obs %s &lt;obs 9.2&gt; that, up to isomorphism, a free algebra is determined by the cardinality of a free generating set.

Next we observe that freeness extends from a class 𝒦 to the variety it generates.

**Prop 4.25** (Bergman:2012)
If 𝑼 is free for 𝒦 over 𝑋, then it is free for HSP(𝒦) over 𝑋.

*Proof*. Let 𝑼 be free for 𝒦 over 𝑋. It suffices to show that if C is one of H, S
or P, then 𝑼 has the universal mapping property for C(𝒦) over 𝑋.

Consider the case 𝑨 ∈ H(𝒦). There is 𝑩 ∈ 𝒦 and a surjective homomorphism 𝑓 : 𝑩 → 𝑨. Let ℎ : 𝑋 → 𝐴 be a function. We must find an extension of h to a homomorphism from 𝑼 to 𝑨. For each 𝑥 ∈ 𝑋 choose an element 𝑏ₓ ∈ 𝑓⁻¹{ℎ(𝑥)}. Define the function $𝑔 : 𝑋 → 𝐵$ by $g(x) = b_x$. Since 𝑼 is free for 𝒦 over 𝑋, and since 𝑩 ∈ 𝒦, $g$ extends to a homomorphism $g' : 𝑼 → 𝑩$, and $𝑓 ∘ g'$ is the desired extension of ℎ.

Next assume 𝑨 ∈ S(𝒦). Then, 𝑨 ≤ 𝑩 ∈ 𝒦, and a mapping ℎ : 𝑋 → 𝐴 clearly maps 𝑋 into 𝐵. By freeness of 𝑈 for 𝒦 over 𝑋, ℎ extends to a homomorphism $ℎ' : 𝑼 → 𝑩$, and since 𝑋 generates 𝑼, we have

$$ℎ'(𝑈) = \{h'(u) : u ∈ 𝑈\} = ℎ'(\mathrm{Sg}^𝑼(X)) = \mathrm{Sg}^𝑩(h'(X)) ⊆ 𝐴,$$

by Obs %s &lt;obs 7.1&gt;. Consequently, $ℎ'$ is actually a homomorphism from 𝑈 to 𝐴.

Finally, let 𝒜 : 𝐼 → 𝒦 denote a collection of algebras in 𝒦 (indexed by 𝐼), let 𝑨 = ∏ 𝒜 be their product, and let πᵢ : ∏ 𝒜 → (𝒜 𝑖) be the 𝑖-th projection map (which of course is a homomorphism). If ℎ : 𝑋 → 𝐴, then for each 𝑖, the mapping πᵢ ∘ ℎ takes 𝑋 to 𝒜 𝑖. Since 𝑼 is free for 𝒦 over 𝑋, we get homomorphisms $ℎᵢ' : 𝑼 → 𝒜 𝑖$. As one easily verifies, these can be assembled into the desired homomorphism $ℎ' = ∏ ℎᵢ' : 𝑼 → 𝑨$.

**Lem 4.27** (Bergman:2012)
If 𝒦 is a class of 𝑆-algebras and 𝑨 an 𝑆-algebra, then 𝑨/Ψ(𝒦, 𝑨) ∈ SP(𝒦).

*Proof*. Observe that

$$𝑨/Ψ(𝒦, 𝑨) ↪ Π ⟨ 𝑨/θ : θ ∈ ψ(𝒦, 𝑨) ⟩ ∈ \mathrm{PS}(𝒦),$$

so $𝑨/Ψ(𝒦, 𝑨)$ ∈ SPS(𝒦) = SP(𝒦).

**Thm 4.28** (Bergman:2012)
Let 𝑼 be free for 𝒦 over 𝑋. Then 𝑼/Ψ(𝒦, 𝑼) is free in SP(𝒦) over 𝑋/Ψ(𝒦, 𝑼).

*Proof*. Let $𝑼' = 𝑼/Ψ(𝒦, 𝑼)$ and $𝑋' = 𝑋/(Ψ(𝒦, 𝑼) ∩ 𝑋²)$. Since 𝑋 generates 𝑼, it follows from Obs 7.1 that 𝑋 generates $𝑼'$. From Obs 9.4, $𝑼'$ ∈ SP(𝒦). If we can show that 𝑼 has the universal mapping property for 𝑋, then by Obs 9.3 $𝑼'$ will be free in SP(𝒦) over 𝑋.

Fix 𝑨 ∈ 𝒦 and $ℎ : 𝑋' → 𝐴$, and let 𝑞 be the canonical map from 𝑼 to $𝑼'$. Since 𝑼 is free over 𝑋, there is a homomorphism ℎ̃ : 𝑼 → 𝑨 extending ℎ ∘ 𝑞. Let η = ker ℎ̃. Then 𝑼/η ∈ S(𝑨) ⊆ S(𝒦), so $η ∈ ψ(𝒦, 𝑼)$ and therefore $Ψ(𝒦, 𝑼) ≤ η$. Since $Ψ(𝒦, 𝑼) = ker 𝑞$, there is a homomorphism $ℎ' : 𝑼' → 𝑨$ such that $ℎ̃ = h' ∘ q$. But now it follows easily that $h'$ restricted to $X'$ is equal to ℎ.

As Bergman notes (see the remark after Def 4.29 in Bergman:2012), "strictly speaking, 𝑋 is not a subset of 𝔽(𝒦, X), so it doesn’t make sense to talk about 𝑋 generating 𝔽(𝒦, X), but as long as 𝒦 contains a nontrivial algebra, $Ψ(𝒦, 𝑋) ∩ 𝑋² = 0_X$. In light of Obs 9.2, we can identify 𝑋 with 𝑋/Ψ(𝒦, 𝑋) in 𝔽(𝒦, 𝑋). All of these considerations are accounted for in the following
corollary."

**Cor 4.30** (Bergman:2012)
Let 𝒱 be a variety of 𝑆-algebras. If 𝑋 ∪ 𝐹₀ ≠ ∅, then 𝔽(𝒱, 𝑋) is free in 𝒱 over 𝑋. If 𝒱 = 𝕍(𝒦), the variety generated by 𝒦, then 𝔽(𝒱, 𝑋) = 𝔽(𝒦, 𝑋) ∈ SP(𝒦).

In the next observation, assume 𝑨 = $⟨A, F^𝑨⟩$ and 𝑩 = $⟨B, F^𝑩⟩$ are 𝑆-algebras , and let 𝑡 ∈ 𝑇(𝑋) be a term in the language of 𝑆. In particular, as explained in term operations, 𝑡 has an interpretation in 𝑨, which (for reasons that will become clear when we define term operations in Agda) we will denote by 𝑡 ̇ 𝑨 and we call a **term operation**. Similarly, $t^𝑩$ is the interpretation of 𝑡 in 𝑩.

**Hom-term Compatibility Lemma**. If 𝑓 : 𝑨 → 𝑩 is a homomorphism, then $g ∘ a : 𝑛 → B$ is the 𝑛-tuple whose 𝑖-th component is $(g ∘ a)\, i = g(a\, i)$, and $g(t^𝑨 a) = t^𝑩(g ∘ a)$.

*Proof*. This is an easy induction on ∣𝑡∣.

**Con-term Compatibility Lemma**. Let 𝑨 be an 𝑆-algebra, 𝑡 a term in the language of 𝑆, and θ a congruence of 𝑨. Then for all tuples 𝒂, 𝒃 : 𝑋 → 𝑨, we have (∀ 𝑖, (𝒂 𝑖) θ (𝒃 i)) → $(t^𝑨 𝒂) \mathrel{θ} (t^𝑨 𝒃)$.

*Proof*. This follows from Obs 10 by taking $⟨B, F^𝑩⟩ = ⟨A, F^𝑨⟩/θ = ⟨A/θ, F^{𝑨/θ}⟩$ and $g=$ the canonical homomorphism. ☐

**Lem 4.36** (Bergman:2012) If 𝒦 is a class of 𝑆-algebras, then each of the classes S(𝒦), H(𝒦), P(𝒦), 𝕍(𝒦) satisfies the same set of identities as does 𝒦.

*Proof*. (to do)

**Lem 4.37** (Bergman:2012) Let 𝓚 be a class of 𝑆-algebras, 𝑻(𝑋) the term algebra over 𝑋, and 𝑝, 𝑞
terms in the language of 𝑆. Then,

$$𝒦 ⊧ p ≈ q \; ⇔ \; ∀ 𝑨 ∈ 𝒦, ∀ h ∈ \mathrm{Hom}(𝑻(X), 𝑨), h ∘ p^{𝑻(X)} = h ∘ q^{𝑻(X)}.$$

*Proof*. Let 𝑻(X) denote the term algebra over 𝑋, 𝑇(𝑋) the collection of terms, in the language of 𝑆.

(⇒) Assume 𝒦 ⊧ 𝑝 ≈ 𝑞. Fix 𝑨 ∈ 𝒦, ℎ : 𝑻(𝑋) → 𝑨, and 𝒂 : X → ∣ 𝑻(𝑋) ∣. By 𝑨 ⊧ 𝑝 ≈ 𝑞 we have $p^𝑨 = q^𝑨$ which implies $p^𝑨(h ∘ 𝒂) = q^𝑨(h ∘ 𝒂)$. Since ℎ is a homomorphism, we obtain $h (p^{𝑻(X)} 𝒂) = h (q^{𝑻(X)} 𝒂)$, as desired.

(⇐) Assume ∀ 𝑨 ∈ 𝒦, ∀ ℎ : Hom 𝑻(𝑋) 𝑨, we have $h ∘ p^{𝑻(X)} = h ∘ q^{𝑻(X)}$. Fix 𝑨 ∈ 𝒦 and 𝒂 : X → ∣ 𝑨 ∣. We prove $p^𝑨 𝒂 = q^𝑨 𝒂$. By Obs. %s &lt;obs 9&gt;, 𝒂 extends to a homomorphism from 𝑻(𝑋) to 𝑨. Denote this extension by 𝒂̂. By assumption $𝒂̂ ∘ p^{𝑻(X)} = 𝒂̂ ∘ q^{𝑻(X)}$, and since 𝒂̂ is a homomorphism, $p^𝑨 𝒂 =  p^𝑨(𝒂̂ ∘ x) = 𝒂̂ (p^𝑨 x) = 𝒂̂ (q^𝑨 x) = q^𝑨 (𝒂̂ ∘ x) = q^𝑨 𝒂$.

**Thm 4.38** (Bergman:2012) Let 𝒦 be a class of algebras and 𝑝 ≈ 𝑞 an equation. The following are equivalent.

1. 𝒦 ⊧ 𝑝 ≈ 𝑞.
2. (𝑝, 𝑞) belongs to the congruence Ψ(𝒦, 𝑋) on 𝑻(𝑋).
3. 𝔽(𝒦, 𝑋) ⊧ 𝑝 ≈ 𝑞.

*Proof*. To simplify notation, let 𝔽 := 𝔽(𝒦, 𝑋) and Ψ := Ψ(𝒦, 𝑋). Recall that 𝔽 = 𝑻(𝑋)/Ψ ∈ SP(𝒦). We show (1) ⟹ (3) ⟹ (2) ⟹ (1).

+ (1) ⟹ (3). From (1) and Obs %s &lt;obs 13&gt; we have SP(𝒦) ⊧ 𝑝 ≈ 𝑞. Thus (3) holds.

+ (2) ⟹ (2). From (3), $p^𝔽 [x] = q^𝔽 [x]$, where \[x\]: 𝑋 → 𝔽is defined by \[x\] 𝑖 = 𝑥ᵢ/Ψ. 
  From the definition of 𝔽, $p^𝑻 𝑥 Ψ q^𝑻 𝑥$, from which (2) follows since $p = p^𝑻 𝑥$ and $q = q^𝑻 𝑥$.

+ (3) ⟹ (1). We wish to apply Obs %s &lt;obs 14&gt;. Let 𝑨 ∈ 𝒦 and ℎ ∈ Hom(𝑻(𝑋), 𝑨). 
  Then 𝑻(𝑋)/(ker ℎ) ∈ S(𝑨) ⊆ S(𝒦) so ker h ⊇ Ψ. Thus, (2) implies ℎ 𝑝 = ℎ 𝑞 hence (1) holds.

The last result tells us that we can determine whether an identity is true in a variety 𝒱 by consulting a particular algebra, namely 𝔽(𝒱, 𝑋), the free algebra in 𝒱.

Let 𝒦 be a class of algebras, 𝑝, 𝑞 terms (say, 𝑛-ary), 𝑋 a set, and 𝑥 a tuple of distinct elements of 𝑋. Then 𝒦 ⊧ 𝑝 ≈ 𝑞 if and only if $p^{𝔽(𝒦, 𝑋)} 𝑥 = q^{𝔽(𝒦, 𝑋)} 𝑥$. In particular, 𝒦 ⊧ 𝑝 ≈ 𝑞 iff 𝔽(𝒦, 𝑋) ⊧ 𝑝 ≈ 𝑞.

*Proof*. Since 𝔽(𝒦, 𝑋) ∈ SP(𝒦), the left-to-right direction uses the same argument as in Obs %s &lt;obs 15&gt;. So assume that $p^{𝔽(𝒦, 𝑋)} 𝑥 = q^{𝔽(𝒦, 𝑋)} 𝑥$. To show that 𝒦 ⊧ 𝑝 ≈ 𝑞, we fix $𝑨 = ⟨𝐴, 𝑓^𝑨⟩ ∈ 𝒦$ and ℎ₀ : 𝑋 → 𝐴, and show that $p^𝑨 ℎ₀ = q^𝑨 ℎ₀$. By Obs %s &lt;obs 9&gt;, ℎ₀ extends to a homomorphism $ℎ' : 𝑻(𝑋) → 𝑨$, so there is a homomorphism $h : 𝔽(𝒦, 𝑋) → (A, f^𝑨)$ such that ℎ(𝑥 𝑖) = ℎ₀(𝑥 𝑖) for all 𝑖 ≤ 𝑛. Therefore,

$$p^𝑨\, ℎ₀ = p^𝑨\, ℎ = ℎ \, p^{𝔽(𝒦, 𝑋)} = ℎ\, q^{𝔽(𝒦, 𝑋)} = q^𝑨 \, ℎ = q^𝑨\, ℎ₀.$$

------------------------------------------------------------------------

### Birkhoff's theorem

It follows from Obs 13 that every equational class is a variety. The converse is Birkhoff's celebrated HSP theorem which we
present next.

The statement and proof we give here is essentially the same as that given in Theorem 4.41 of Cliff Bergman's textbook Bergman:2012. It is this statement and proof that we will formalize in [Agda][].

**Thm 4.41** (Bergman:2012) Every variety is an equational class.

*Proof*. Let 𝒲 be a class of algebras closed under H, S, and P (i.e., a variety). We must find a set ℰ of equations that axiomatizes 𝒲 (that is 𝒲 = Mod ℰ), as this will prove that 𝒲 is the class of algebras satisfying the set of equations ℰ and thus establish that 𝒲 is an equational class. The obvious choice for ℰ is Th 𝒲, the set of all equations that hold in 𝒲.

Let 𝒲† = Mod ℰ. Clearly, 𝒲 ⊆ 𝒲†, so we must prove the reverse inclusion.

Let 𝑨 ∈ 𝒲† and let 𝑋 be a set of cardinality max(∣𝐴∣, ω).

Choose a surjection ℎ₀ : 𝑋 → 𝐴. By Obs %s &lt;obs 9&gt;, ℎ₀ extends to an epimorphism ℎ : 𝑻(𝑋) → 𝑨. Since 𝔽(𝒲, 𝑋) = 𝑻(𝑋)/Ψ(𝒲, 𝑋), there is an epimorphism ε : 𝑻(𝑋) → 𝔽(𝒲, 𝑋).

If ker ε ⊆ ker ℎ, then by Obs %s &lt;obs 5&gt; there would be a map 𝑓 : 𝔽(𝒲, 𝑋) → 𝐴 such that 𝑓 ∘ ε = ℎ; moreover, 𝑓 would be epic (since ℎ is) and this would give 𝑨 ∈ H(𝔽(𝒲, 𝑋)) ⊆ 𝒲, as desired. So it suffices to prove that ker ε ⊆ ker ℎ.

Let 𝑢, 𝑣 be terms in 𝑻 := 𝑻(𝑋) and assume ε(𝑢) = ε(𝑣). Since 𝑻 is generated by 𝑋, there are 𝑝, 𝑞 ∈ 𝑻 and 𝑥 such that 𝑢 = (𝑝 ̇ 𝑻)(𝑥) and 𝑣 = (𝑞 ̇ 𝑻)(𝑥). Therefore, applying the hom ε, we have

(𝑝 ̇ 𝔽(𝒲, 𝑋)) 𝑥 = ε(𝑢) = ε(𝑣) = (𝑞 ̇ 𝔽(𝒲, 𝑋)) 𝑥.

Therefore, 𝒲 ⊧ 𝑝 ≈ 𝑞, so (𝑝, 𝑞) ∈ ℰ and 𝑨 ⊧ 𝑝 ≈ 𝑞, since 𝑨 ∈ Mod ℰ. Combining these facts yields the desired conclusion that (𝑢, 𝑣) belongs to ker ℎ; viz.,

ℎ(𝑢) = ℎ ((𝑝 ̇ 𝑻) 𝑥) = (𝑝 ̇ 𝑨)(ℎ ∘ 𝑥) = (𝑞 ̇ 𝑨)(ℎ ∘ 𝑥) = ℎ ((𝑞 ̇ 𝑻) 𝑥) = ℎ(𝑣).

------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Agda Preliminaries

**Notation**. Here are some acronyms that we use frequently.

-   MHE = [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe/)
-   MLTT = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

All but the most trivial Agda programs begin by setting some options that effect how Agda behaves and importing from existing libraries (e.g., the [Agda Standard Library][] or, in our case, MHE's [Type Topology][] library). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, we begin our agda development with the line

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module ualib where

module prelude where

 open import Universes public
\end{code}

This specifies Agda `OPTIONS` that we will use throughout the library.

- `without-K` disables [Streicher's K axiom][]; see also the [section on axiom K][] in the [Agda Language Reference][] manual.
- `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities. MHE explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.
- `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

### Universes

We import the `Universes` module from MHE's [Type Topology][] library.

\begin{code}
 open import Universes public
\end{code}

This `Universes` module provides, among other things, an elegant notation for type universes that we have fully adopted and we use MHE's notation throughout the [UALib][].

MHE has authored an outstanding set of notes on [HoTT-UF-in-Agda][] called [Introduction to Univalent Foundations of Mathematics with Agda][]. We highly recommend these notes to anyone wanting more details than we provide here about MLTT and the Univalent Foundations/HoTT extensions thereof.

Following MHE, we refer to universes using capitalized script letters 𝓤,𝓥,𝓦,𝓣. We add a few more to Martin's list.

\begin{code}
 variable 𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓧 : Universe
\end{code}

In the `Universes` module, MHE defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`. The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero`.

Although it is nice and short, we won't show all of the `Universes` module here. Instead, we highlight the few lines of code from MHE's `Universes.lagda` file that makes available the notational devices that we just described and will adopt throughout the [UALib][].

Thus, 𝓤 ̇ is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`. Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which (MHE and) we denote by `𝓤₀ ⁺ ̇`.

The following dictionary translates between standard Agda syntax and MHE/[UALib][].

```agda
Agda              MHE/UALib
====              ==============
Level             Universe
lzero             𝓤₀
𝓤 : Level         𝓤 : Universe
Set lzero         𝓤₀ ̇
Set 𝓤             𝓤 ̇
lsuc lzero        𝓤₀ ⁺
lsuc 𝓤            𝓤 ⁺
Set (lsuc lzero)  𝓤₀ ⁺ ̇
Set (lsuc 𝓤)      𝓤 ⁺ ̇
Setω              𝓤ω
```

To justify the introduction of this somewhat nonstandard notation for universe levels, MHE points out that the Agda library uses `Level` for universes (so what we write as 𝓤 ̇ is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the standard Agda notation can be misleading. Furthermore, the standard notation places emphasis on levels rather than universes themselves.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound. Here 𝓤 ⊔ 𝓥 is used to denote the universe level corresponding to the least upper bound of the levels 𝓤 and 𝓥, where the `_⊔_` is an Agda primitive designed for
precisely this purpose.

### Public imports

Next we import other parts of MHE's [Type Topology][] library, using the Agda directive `public`, which means these imports will be available wherever the `prelude` module in imported. We describe some of these imports later, when making use of them, but we don't describe each one in detail. (The interested or confused reader should consult
[HoTT-UF-in-Agda][] to learn more.)

\begin{code}
 open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁) public

 pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

 open import Sigma-Type renaming (_,_ to infixr 50 _,_) public

 open import MGS-MLTT using (_∘_; domain; codomain; transport;
  _≡⟨_⟩_; _∎; pr₁; pr₂; -Σ; Π; ¬; _×_; 𝑖𝑑; _∼_; _+_; 𝟘; 𝟙; 𝟚;
  _⇔_; lr-implication; rl-implication; id; _⁻¹; ap) public

 open import MGS-Equivalences using (is-equiv; inverse;
  invertible) public

 open import MGS-Subsingleton-Theorems using (funext;
  dfunext; is-singleton; is-subsingleton; is-prop; Univalence;
  global-dfunext; univalence-gives-global-dfunext; _●_; _≃_;
  logically-equivalent-subsingletons-are-equivalent;
  Π-is-subsingleton) public

 open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_)
  using (𝓟; ∈-is-subsingleton; equiv-to-subsingleton;
  powersets-are-sets'; subset-extensionality'; propext) public

 open import MGS-Embeddings using (is-embedding; pr₁-embedding;
  is-set; _↪_; embedding-gives-ap-is-equiv; embeddings-are-lc;
  ×-is-subsingleton) public

 open import MGS-Solved-Exercises using (to-subtype-≡) public

 open import MGS-Subsingleton-Truncation hiding (refl; _∈_; _⊆_) public
\end{code}


### Dependent pair type

Our preferred notations for the first and second projections of a
product are `∣_∣` and `∥_∥`, respectively; however, we will sometimes
use the more standard `pr₁` and `pr₂`, or even `fst` and `snd`, for
emphasis, readability, or compatibility with other libraries.

\begin{code}
 ∣_∣ fst : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇} → Σ Y → X
 ∣ x , y ∣ = x
 fst (x , y) = x

 ∥_∥ snd : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
 ∥ x , y ∥ = y
 snd (x , y) = y
\end{code}

For the dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which
is more pleasing (and more standard in the literature) than Agda's
default syntax (`Σ λ(x ꞉ X) → y`), and MHE has a useful trick that makes
the preferred notation available by making index type explicit.

```agda
infixr -1 -Σ
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`
```

<div class="admonition warning">

The symbol ꞉ is not the same as : despite how similar they may appear.
The correct colon in the expression `Σ x ꞉ X , y` above is obtained by
typing `\:4` in
[agda2-mode](https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html).

</div>

MHE explains Sigma induction as follows: "To prove that `A z` holds for
all `z : Σ Y`, for a given property `A`, we just prove that we have
`A (x , y)` for all `x : X` and `y : Y x`. This is called `Σ` induction
or `Σ` elimination (or `uncurry`).

```agda
Σ-induction : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
 →            ((x : X)(y : Y x) → A (x , y))
              -------------------------------
 →            ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
 →      (((x , y) : Σ Y ) → A (x , y))
       ---------------------------------
 →      ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
```

The special case in which the type `Y` doesn't depend on `X` is of
course the usual Cartesian product.

```agda
infixr 30 _×_
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y
```


### Dependent function type

To make the syntax for `Π` conform to the standard notation for "Pi
types" (or dependent function type), MHE uses the same trick as the one
used above for "Sigma types."

```agda
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇ )(Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y
infixr -1 -Π
syntax -Π A (λ x → b) = Π x ꞉ A , b
```


### Application

An important tool that we use often in Agda proofs is application of a
function to an identification `p : x ≡ x'`. We apply the `ap` operator
to obtain the identification `ap f p : f x ≡ f x'` when given
`p : x ≡ x'` and `f : X → Y`.

Since `ap` is already defined in MHE's Type Topolgy library, we don't
redefine it here. However, we do define some variations of `ap` that are
sometimes useful.

\begin{code}
 ap-cong : {X : 𝓤 ̇}{Y : 𝓥 ̇}{f g : X → Y} {a b : X}
  →        f ≡ g  →  a ≡ b
           -----------------
  →        f a ≡ g b

 ap-cong (refl _) (refl _) = refl _
\end{code}

Here is a related tool that we borrow from the [Relation/Binary/PropositionalEquality.agda][] module of the [Agda standard library](https://agda.github.io/agda-stdlib/).

\begin{code}
 cong-app : {A : 𝓤 ̇}{B : A → 𝓦 ̇}{f g : (a : A) → B a}
  →          f ≡ g   →   (a : A)
           -----------------------
  →              f a ≡ g a

 cong-app (refl _) a = refl _
\end{code}


### Function extensionality

Extensional equality of functions, or function extensionality, means that any two point-wise equal functions are equal. As MHE points out, this is known to be not provable or disprovable in Martin-Löf Type Theory (MLTT).

Nonetheless, we will mainly work with pointwise equality of functions, which MHE defines (in [Type Topology](%3Chttps://github.com/martinescardo/TypeTopology%3E%60_) ) as follows:

```agda
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇ 
f ∼ g = ∀ x → f x ≡ g x
infix 0 _∼_
```

(The `_∼_` relation will be equivalent to equality of functions, once we have the principle of *univalence* at our disposal.)


### Predicates, Subsets

We need a mechanism for implementing the notion of subsets in Agda. A typical one is called `Pred` (for predicate). More generally, `Pred A 𝓤` can be viewed as the type of a property that elements of type `A` might satisfy. We write `P : Pred A 𝓤` (read "`P` has type `Pred A 𝓤`") to represent the subset of elements of `A` that satisfy property `P`.

Here is the definition (which is similar to the one found in the `Relation/Unary.agda` file of [Agda standard
library](https://agda.github.io/agda-stdlib/) ).

\begin{code}
 Pred : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
 Pred A 𝓥 = A → 𝓥 ̇
\end{code}

Below we will often consider predicates over the class of all algebras
of a particular type. We will define the type of algebras `Algebra 𝓤 𝑆`
(for some universe level 𝓤). Like all types, `Algebra 𝓤 𝑆` itself has a
type which happens to be 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ (as we will see in algebra type).
Therefore, the type of `Pred (Algebra 𝓤 𝑆) 𝓤` will be 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ as
well.

The inhabitants of the type `Pred (Algebra 𝓤 𝑆) 𝓤` are maps of the form
𝑨 → 𝓤 ̇; indeed, given an algebra 𝑨 : Algebra 𝓤 𝑆, we have Pred 𝑨 𝓤 = 𝑨 →
𝓤 ̇.

### The membership relation

We introduce notation so that we may indicate that `x` "belongs to" a
"subset" `P`, or that `x` "has property" `P`, by writing either `x ∈ P`
or `P x` (cf. `Relation/Unary.agda` in the [Agda standard
library](https://agda.github.io/agda-stdlib/) ).

\begin{code}
 infix 4 _∈_ _∉_
 _∈_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
 x ∈ P = P x

 _∉_ : {A : 𝓤 ̇ } → A → Pred A 𝓦 → 𝓦 ̇
 x ∉ P = ¬ (x ∈ P)
\end{code}


### Subset relations and operations

The subset relation is then denoted, as usual, with the `⊆` symbol (cf. `Relation/Unary.agda` in the [Agda standard
library](https://agda.github.io/agda-stdlib/) ).

\begin{code}
 infix 4 _⊆_ _⊇_
 _⊆_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

 _⊇_ : {A : 𝓤 ̇ } → Pred A 𝓦 → Pred A 𝓣 → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 P ⊇ Q = Q ⊆ P

 infixr 1 _⊎_

 -- Disjoint Union.
 data _⊎_ (A : 𝓤 ̇) (B : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
   inj₁ : (x : A) → A ⊎ B
   inj₂ : (y : B) → A ⊎ B

 -- Union.
 infixr 6 _∪_
 _∪_ : {A : 𝓤 ̇} → Pred A 𝓥 → Pred A 𝓦 → Pred A _
 P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q


 -- The empty set.
 ∅ : {A : 𝓤 ̇} → Pred A 𝓤₀
 ∅ = λ _ → 𝟘
\end{code}


### Miscellany

Finally, we include the following list of "utilities" that will come in
handy later. Most of these are self-explanatory, but we make a few
remarks below when we feel there is something worth noting.

\begin{code}
 _∈∈_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A  →  B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
 _∈∈_ f S = (x : _) → f x ∈ S

 Im_⊆_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → Pred B 𝓣 → 𝓤 ⊔ 𝓣 ̇
 Im_⊆_ {A = A} f S = (x : A) → f x ∈ S

 img : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
       (f : X → Y) (P : Pred Y 𝓤)
  →    Im f ⊆ P →  X → Σ P
 img {Y = Y} f P Imf⊆P = λ x₁ → f x₁ , Imf⊆P x₁

 ≡-elim-left : {A₁ A₂ : 𝓤 ̇ } {B₁ B₂ : 𝓦 ̇ }
  →            (A₁ , B₁) ≡ (A₂ , B₂)
               ----------------------
  →                   A₁ ≡ A₂
 ≡-elim-left e = ap pr₁ e

 ≡-elim-right : {A₁ A₂ : 𝓤 ̇ }{B₁ B₂ : 𝓦 ̇ }
  →             (A₁ , B₁) ≡ (A₂ , B₂)
               -----------------------
  →                    B₁ ≡ B₂
 ≡-elim-right e = ap pr₂ e

 ≡-×-intro : {A₁ A₂ : 𝓤 ̇ } {B₁ B₂ : 𝓦 ̇ }
  →           A₁ ≡ A₂  →  B₁ ≡ B₂
           ------------------------
  →          (A₁ , B₁) ≡ (A₂ , B₂)
 ≡-×-intro (refl _ ) (refl _ ) = (refl _ )

 cong-app-pred : ∀{A : 𝓤 ̇ }{B₁ B₂ : Pred A 𝓤}
                 (x : A) →  x ∈ B₁  →  B₁ ≡ B₂
                ------------------------------
  →                         x ∈ B₂
 cong-app-pred x x∈B₁ (refl _ ) = x∈B₁

 cong-pred : {A : 𝓤 ̇ }{B : Pred A 𝓤}
             (x y : A) →  x ∈ B  →  x ≡ y
             ----------------------------
  →                       y ∈ B
 cong-pred x .x x∈B (refl _ ) = x∈B


 data Image_∋_ {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B) : B → 𝓤 ⊔ 𝓦 ̇
   where
   im : (x : A) → Image f ∋ f x
   eq : (b : B) → (a : A) → b ≡ f a → Image f ∋ b

 ImageIsImage : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                (f : A → B) (b : B) (a : A)
  →              b ≡ f a
               ----------------------------
  →              Image f ∋ b
 ImageIsImage {A = A}{B = B} f b a b≡fa = eq b a b≡fa
\end{code}

N.B. the assertion `Image f ∋ y` must come with a proof, which is of the
form `∃a f a = y`, so we have a witness. Thus, the inverse can be
"computed" in the following way:

\begin{code}
 Inv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(f : A → B)(b : B) → Image f ∋ b  →  A
 Inv f .(f a) (im a) = a
 Inv f b (eq b a b≡fa) = a
\end{code}

The special case for Set (i.e., `𝓤₀ ̇`) is

\begin{code}
 inv : {A B : 𝓤₀ ̇ }(f : A → B)(b : B) → Image f ∋ b → A
 inv {A} {B} = Inv {𝓤₀}{𝓤₀}{A}{B}

 InvIsInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B)
            (b : B) (b∈Imgf : Image f ∋ b)
           ---------------------------------
  →         f (Inv f b b∈Imgf) ≡ b
 InvIsInv f .(f a) (im a) = refl _
 InvIsInv f b (eq b a b≡fa) = b≡fa ⁻¹
\end{code}

An epic (or surjective) function from 𝓤 ̇ to 𝓦 ̇ (and the special case for `𝓤₀ ̇`) is defined as follows.

\begin{code}
 Epic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) →  𝓤 ⊔ 𝓦 ̇
 Epic g = ∀ y → Image g ∋ y

 epic : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
 epic = Epic {𝓤₀} {𝓤₀}
\end{code}

The (pseudo-)inverse of an epic function is

\begin{code}
 EpicInv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → Epic f → B → A
 EpicInv f fEpic b = Inv f b (fEpic b)

 -- The (psudo-)inverse of an epic is the right inverse.
 EInvIsRInv : funext 𝓦 𝓦 → {A : 𝓤 ̇ } {B : 𝓦 ̇ }
              (f : A → B)  (fEpic : Epic f)
             ---------------------------------
  →           f ∘ (EpicInv f fEpic) ≡ 𝑖𝑑 B
 EInvIsRInv fe f fEpic = fe (λ x → InvIsInv f x (fEpic x))
\end{code}

Monics (or injective) functions are defined this way.

\begin{code}
 monic : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (g : A → B) → 𝓤 ⊔ 𝓦 ̇
 monic g = ∀ a₁ a₂ → g a₁ ≡ g a₂ → a₁ ≡ a₂
 monic₀ : {A B : 𝓤₀ ̇ } (g : A → B) → 𝓤₀ ̇
 monic₀ = monic {𝓤₀}{𝓤₀}

 --The (pseudo-)inverse of a monic function
 monic-inv : {A : 𝓤 ̇ } {B : 𝓦 ̇ } (f : A → B) → monic f
  →           (b : B) → Image f ∋ b → A
 monic-inv f fmonic  = λ b Imf∋b → Inv f b Imf∋b

 --The (psudo-)inverse of a monic is the left inverse.
 monic-inv-is-linv : {A : 𝓤 ̇ }{B : 𝓦 ̇ }
                     (f : A → B) (fmonic : monic f)(x : A)
                    ----------------------------------------
   →                 (monic-inv f fmonic) (f x) (im x) ≡ x
 monic-inv-is-linv f fmonic x = refl _
\end{code}

Finally, we define bijective functions as follows.

\begin{code}
 bijective : {A B : 𝓤₀ ̇ }(g : A → B) → 𝓤₀ ̇
 bijective g = epic g × monic g

 Bijective : {A : 𝓤 ̇ }{B : 𝓦 ̇ }(g : A → B) → 𝓤 ⊔ 𝓦 ̇
 Bijective g = Epic g × monic g
\end{code}


### More extensionality

Here we collect miscellaneous definitions and proofs related to
extensionality that will come in handy later.

\begin{code}
 --Ordinary function extensionality
 extensionality : ∀ 𝓤 𝓦  → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
  →                f ∼ g   →   f ≡ g

 --Opposite of function extensionality
 intensionality : ∀ {𝓤 𝓦} {A : 𝓤 ̇ } {B : 𝓦 ̇ } {f g : A → B}
  →                f ≡ g  →  (x : A)
                   ------------------
  →                    f x ≡ g x

 intensionality  (refl _ ) _  = refl _

 --Dependent intensionality
 dep-intensionality : ∀ {𝓤 𝓦}{A : 𝓤 ̇ }{B : A → 𝓦 ̇ }
                      {f g : ∀(x : A) → B x}
  →                   f ≡ g  →  (x : A)
                     ------------------
  →                    f x ≡ g x

 dep-intensionality (refl _ ) _ = refl _

 --------------------------------------
 --Dependent function extensionality
 dep-extensionality : ∀ 𝓤 𝓦 → 𝓤 ⁺ ⊔ 𝓦 ⁺ ̇
 dep-extensionality 𝓤 𝓦 = {A : 𝓤 ̇ } {B : A → 𝓦 ̇ }
   {f g : ∀(x : A) → B x} →  f ∼ g  →  f ≡ g

 ∀-extensionality : 𝓤ω
 ∀-extensionality = ∀  {𝓤 𝓥} → extensionality 𝓤 𝓥

 ∀-dep-extensionality : 𝓤ω
 ∀-dep-extensionality = ∀ {𝓤 𝓥} → dep-extensionality 𝓤 𝓥

 extensionality-lemma : {I : 𝓘 ̇ }{X : 𝓤 ̇ }{A : I → 𝓥 ̇ }
                        (p q : (i : I) → (X → A i) → 𝓣 ̇ )
                        (args : X → (Π A))
  →                     p ≡ q
    -------------------------------------------------------------
  → (λ i → (p i)(λ x → args x i)) ≡ (λ i → (q i)(λ x → args x i))

 extensionality-lemma p q args pq = ap (λ - → λ i → (- i) (λ x → args x i)) pq
\end{code}

-------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Algebras in Agda

This chapter describes the [basic module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/basic.lagda.rst)
of the [UALib][] , which begins our [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) formalization of the basic concepts and theorems of universal algebra. In this module we will codify such notions as operation, signature, and algebraic structure.

\begin{code}
module basic where

 open prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; 𝓧;
   _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Π; _≡_; Epic) public
\end{code}

### Operation type

We define the type of **operations**, and give an example (the
projections).

\begin{code}
 --The type of operations
 Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 Op I A = (I → A) → A

 --Example. the projections
 π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
 π i x = x i
\end{code}

The type `Op` encodes the arity of an operation as an arbitrary type `I : 𝓥 ̇`, which gives us a very general way to represent an operation as a function type with domain `I → A` (the type of "tuples") and codomain `A`.

The last two lines of the code block above codify the `i`-th `I`-ary projection operation on `A`.


### Signature type

We define the signature of an algebraic structure in Agda like this.

\begin{code}
 --𝓞 is the universe in which operation symbols live
 --𝓥 is the universe in which arities live
 Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
 Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )
\end{code}

In the [prelude module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/prelude.lagda.rst) we defined the syntax ∣\_∣ and ∥\_∥ for the first and second projections, resp. Consequently, if `𝑆 : Signature 𝓞 𝓥` is a signature, then

> ∣ 𝑆 ∣ denotes the set of operation symbols (which is often called 𝐹), and
>
> ∥ 𝑆 ∥ denotes the arity function (which is often called ρ).

Thus, if 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.


### Algebra type

Finally, we are ready to define the type of algebras in the signature `S` (which we also call "S-algebras").

\begin{code}
 Algebra : (𝓤 : Universe){𝓞 𝓥 : Universe}
           (𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

 Algebra 𝓤 {𝓞}{𝓥} 𝑆 = Σ A ꞉ 𝓤 ̇ , ((𝑓 : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ 𝑓) A)
\end{code}

Thus, algebras---in the signature 𝑆 (or 𝑆-algebras) and with carrier types in the universe 𝓤---inhabit the type `Algebra 𝓤 {𝓞}{𝓥} 𝑆`. (We may also write `Algebra 𝓤 𝑆` since 𝓞 and 𝓥 can be infered from the given signature `𝑆`.)

In other words,

> *the type* `Algebra 𝓤 𝑆` *collects all the algebras of a particular
> signature* 𝑆 *and carrier type* 𝓤, *and this collection of algebras
> has type* 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ .

Recall, 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ denotes the smallest universe containing 𝓞, 𝓥, and the successor of 𝓤.

**N.B.** The type `Algebra 𝓤 𝑆` doesn't define what an algebra *is* as a property. It defines a type of algebras; certain algebras inhabit this type---namely, the algebras consisting of a universe (say, `A`) of type 𝓤 ̇ , and a collection `(𝑓 : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ 𝑓) A` of operations on `A`.

Here's an alternative syntax that might seem more familiar to readers of the standard universal algebra literature.

```agda
Algebra 𝓤 (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  ((𝑓 : F )  → Op (ρ 𝑓) A )
```

Here `𝑆 = (F , ρ)` is the signature, `F` the type of operation symbols, and ρ the arity function.

Although this syntax would work equally well, we mention it merely for comparison and to demonstrate the flexibility of Agda. Throughout the library we stick to the syntax `𝑓 : ∣ 𝑆 ∣` for an operation symbol of the signature 𝑆, and `∥ 𝑆 ∥ 𝑓` for the arity of that symbol. We find these conventions a bit more convenient for programming.

### Example

A monoid signature has two operation symbols, say, `e` and `·`, of
arities 0 and 2 (thus, of types `(𝟘 → A) → A` and `(𝟚 → A) → A`), resp.

\begin{code}
 data monoid-op : 𝓤₀ ̇ where
  e : monoid-op
  · : monoid-op

 monoid-sig : Signature _ _
 monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }
\end{code}

The types indicate that `e` is nullary (i.e., takes no arguments, equivalently, takes args of type `𝟘 → A`), while `·` is binary (as indicated by argument type `𝟚 → A`).

We will have more to say about the type of algebras later. For now, we continue defining the syntax used in the `agda-ualib` to represent the basic objects of universal algebra.

### Syntactic sugar for operation interpretation

Before proceding, we define syntax that allows us to replace `∥ 𝑨 ∥ 𝑓` with the slightly more standard-looking `𝑓 ̂ 𝑨`, where 𝑓 is an operation symbol of the signature 𝑆 of 𝑨.

\begin{code}
open basic

module _ {𝑆 : Signature 𝓞 𝓥}  where

 _̂_ : (𝑓 : ∣ 𝑆 ∣)
  →   (𝑨 : Algebra 𝓤 𝑆)
  →   (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ x → (∥ 𝑨 ∥ 𝑓) x

 infix 40 _̂_
\end{code}

Now we can use `𝑓 ̂ 𝑨` to represent the interpretation of the basic
operation symbol 𝑓 in the algebra 𝑨.

Below, we will need slightly different notation, namely, 𝑡 ̇ 𝑨, to
represent the interpretation of a term 𝑡 in the algebra 𝑨. (In
future releases of the [UALib](https://gitlab.com/ualib/ualib.gitlab.io) we may
reconsider making it possible to use the same notation
interpretations of operation symbols and terms.)


### Products of algebras

The (indexed) product of a collection of algebras is also an algebra if
we define such a product as follows:

\begin{code}
 ⨅ : {I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓤 ⊔ 𝓘) 𝑆
 ⨅ 𝒜 =  ((i : _) → ∣ 𝒜 i ∣) ,  λ 𝑓 x i → (𝑓 ̂ 𝒜 i) λ 𝓥 → x 𝓥 i

 infixr -1 ⨅
\end{code}

(In `agda2-mode` ⨅ is typed as `\Glb`.)


### Arbitrarily many variable symbols

Finally, since we typically want to assume that we have an arbitrary
large collection `X` of variable symbols at our disposal (so that, in
particular, given an algebra 𝑨 we can always find a surjective map h₀ :
X → ∣ 𝑨 ∣ from X to the universe of 𝑨), we define a type for use when
making this assumption.

\begin{code}
 _↠_ : 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
 X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h
\end{code}

------------------------------------------------------------------------------

### Unicode Hints 1

Table of some special characters used in the [basic
module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/basic.lagda.rst).

> +--------|------------------------+
> | To get | Type                   |
> +--------|------------------------+
> | 𝓘      | `\MCI`                |
> +--------|------------------------+
> | 𝓤₀     | `\MCU\_0`             |
> +--------|------------------------+
> | ⊔      | `\sqcup`               |
> +--------|------------------------+
> | 𝟘, 𝟚   | `\b0`, `\b2`           |
> +--------|------------------------+
> | 𝑎, 𝑏   |  `\Mia`, `\Mib`        |
> +--------|------------------------+
> | 𝒂, 𝒃   |  `\MIa`, `\MIb`        |
> +--------|------------------------+
> | 𝒜      | `\McA`                 |
> +--------|------------------------+
> | 𝑓 ̂ 𝑨   | `\Mif \^ \MIA`         |
> +--------|------------------------+
> | ≅      | `≅` or `\cong`         |
> +--------|------------------------+
> | ∘      | `\comp` or `\circ`     |
> +--------|------------------------+
> | 𝒾𝒹     | `\Mci\Mcd`             |
> +--------|------------------------+
> | ℒ𝒦     | `\McL\McK`            |
> +--------|------------------------+
> | ϕ      | `\phi`                 |
> +--------|------------------------+
> | ⨅      | `\Glb`                 |
> +--------|------------------------+


**Emacs commands providing information about characters or input method**:

+ `M-x describe-char` (or `M-m h d c`) with the cursor on the character of interest
+ `M-x describe-input-method` (or `C-h I`)

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Congruences in Agda

This chapter describes the [congruences module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst)
of the [UALib][].

**N.B.** Some of the code in this first part of this chapter pertaining to relations is borrowed from similar code in the [Agda standard library](https://agda.github.io/agda-stdlib/) (in the file [Relation/`Binary/Core.agda][]) that we translate into our notation for consistency.

\begin{code}
open basic

module congruences where

 open prelude using (Pred; 𝓡; 𝓢; is-prop; 𝟙; _≡⟨_⟩_; _∎; refl; _⁻¹; funext; ap) public
\end{code}

### Binary relation type

Heterogeneous binary relations.

\begin{code}
 REL : 𝓤 ̇ → 𝓥 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇
\end{code}

Homogeneous binary relations.

\begin{code}
 Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
 Rel A 𝓝 = REL A A 𝓝
\end{code}

### Kernels

The kernel of a function can be defined in many ways. For example,

\begin{code}
 KER : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → 𝓤 ⊔ 𝓦 ̇
 KER {𝓤}{𝓦}{A} f = Σ x ꞉ A , Σ y ꞉ A , f x ≡ f y

 ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
 ker {𝓤} = KER{𝓤}{𝓤}
\end{code}

or as a relation...

\begin{code}
 KER-rel : {A : 𝓤 ̇ } {B : 𝓦 ̇ } → (A → B) → Rel A 𝓦
 KER-rel g x y = g x ≡ g y

 -- (in the special case 𝓦 ≡ 𝓤)
 ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
 ker-rel {𝓤} = KER-rel {𝓤} {𝓤}
\end{code}

or a binary predicate...

\begin{code}
 KER-pred : {A : 𝓤 ̇ }{B : 𝓦 ̇ } → (A → B) → Pred (A × A) 𝓦
 KER-pred g (x , y) = g x ≡ g y

 -- (in the special case 𝓦 ≡ 𝓤)
 ker-pred : {A : 𝓤 ̇ }{B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
 ker-pred {𝓤} = KER-pred {𝓤} {𝓤}
\end{code}

### Implication

We denote and define implication or containment (which could also be
written \_⊆\_) as follows.

\begin{code}
 _⇒_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
  →    REL A B 𝓡 → REL A B 𝓢
  →    𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇

 P ⇒ Q = ∀ {i j} → P i j → Q i j

 infixr 4 _⇒_

 _on_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
  →     (B → B → C) → (A → B) → (A → A → C)
 _*_ on f = λ x y → f x * f y
\end{code}

Here is a more general version of implication

\begin{code}
 _=[_]⇒_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
  →        Rel A 𝓡 → (A → B) → Rel B 𝓢
  →        𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇

 P =[ f ]⇒ Q = P ⇒ (Q on f)

 infixr 4 _=[_]⇒_
\end{code}

### Properties of binary relations

Reflexivity of a binary relation (say, `≈`) on `X`, can be defined without an underlying equality as follows.

\begin{code}
 reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 reflexive _≈_ = ∀ x → x ≈ x
\end{code}

Similarly, we have the usual notion of symmetric (resp., transitive) binary relation.

\begin{code}
 symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z
\end{code}

For a binary relation ≈ on A, denote a single ≈-class (containing a) by \[ a \] ≈,

\begin{code}
 [_]_ :  {A : 𝓤 ̇ } →  (a : A) → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 [ a ] _≈_ = Σ x ꞉ _ ,  a ≈ x
\end{code}

and denote the collection of all ≈-classes of A by A // ≈.

\begin{code}
 _//_ :  (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
 A // ≈ = Σ C ꞉ _ ,   Σ a ꞉ A ,  C ≡ ( [ a ] ≈ )

 is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)
\end{code}

The "trivial" or "diagonal" or "identity" relation is,

\begin{code}
 𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎{𝓤} {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

 𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
 𝟎-rel a b = a ≡ b
\end{code}

or, in various other guises,

\begin{code}
 -- ...as a binary predicate:
 𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
 𝟎-pred (a , a') = a ≡ a'

 --...as a binary predicate:
 𝟎'' : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎'' {𝓤} {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥
\end{code}

The "universal" or "total" or "all" relation.

\begin{code}
 𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
 𝟏 a b = 𝟙
\end{code}

### Types for equivalences

Here are two ways to define an equivalence relation in Agda.

First, we use a record.

\begin{code}
 record IsEquivalence {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
   field
     rfl  : reflexive _≈_
     sym   : symmetric _≈_
     trans : transitive _≈_
\end{code}

Here's an alternative.

\begin{code}
 is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-equivalence-relation _≈_ =
  is-subsingleton-valued _≈_
   × reflexive _≈_ × symmetric _≈_ × transitive _≈_
\end{code}

Of course, 𝟎 is an equivalence relation, a fact we can prove as follows.

\begin{code}
 𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence {𝓤}{𝓤}{A} 𝟎-rel
 𝟎-IsEquivalence = record { rfl = ρ ; sym = σ ; trans = τ }
  where
   ρ : reflexive 𝟎-rel
   ρ x =  x ≡⟨ refl _ ⟩ x ∎

   σ : symmetric 𝟎-rel
   σ x y x≡y = x≡y ⁻¹

   τ : transitive 𝟎-rel
   τ x y z x≡y y≡z = x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎
\end{code}

We define the **lift** of a binary relation from pairs to pairs of tuples as follows:

\begin{code}
 lift-rel : {γ : 𝓥 ̇ } {Z : 𝓤 ̇ }
  →         Rel Z 𝓦 → (γ → Z) → (γ → Z)
  →         𝓥 ⊔ 𝓦 ̇
 lift-rel R 𝒇 𝒈 = ∀ x → R (𝒇 x) (𝒈 x)
\end{code}

We define **compatibility** of a given function-relation pair as follows:

\begin{code}
 compatible-fun : {γ : 𝓥 ̇ } {Z : 𝓤 ̇ }
                  (𝒇 : (γ → Z) → Z)(𝑹 : Rel Z 𝓦)
  →               𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun 𝒇 𝑹 = (lift-rel 𝑹) =[ 𝒇 ]⇒ 𝑹
\end{code}


### Types for congruences

Finally, we come to the definition of a congruence, which we define in a module so we have an ambient signature 𝑆 available.

\begin{code}
open congruences

module _ {𝑆 : Signature 𝓞 𝓥}  where

 -- relation compatible with an operation
 compatible-op : {𝑨 : Algebra 𝓤 𝑆}
  →              ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓤
  →              𝓥 ⊔ 𝓤 ̇
 compatible-op {𝓤} {𝑨} 𝑓 𝓻 = (lift-rel 𝓻) =[ (∥ 𝑨 ∥ 𝑓) ]⇒ 𝓻

 --The given relation is compatible with all ops of an algebra.
 compatible : (𝑨 : Algebra 𝓤 𝑆) -> Rel ∣ 𝑨 ∣ 𝓤 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇
 compatible {𝓤} 𝑨 𝓻 = ∀ 𝑓 → compatible-op{𝓤}{𝑨} 𝑓 𝓻

 𝟎-compatible-op : funext 𝓥 𝓤
  →                {𝑨 : Algebra 𝓤 𝑆} (𝑓 : ∣ 𝑆 ∣)
  →                compatible-op {𝓤}{𝑨} 𝑓 𝟎-rel
 𝟎-compatible-op fe {𝑨 = 𝑨} 𝑓 ptws𝟎  =
  ap (𝑓 ̂ 𝑨)(fe (λ x → ptws𝟎 x))

 𝟎-compatible : funext 𝓥 𝓤
  →             {𝑨 : Algebra 𝓤 𝑆}
  →             compatible 𝑨 𝟎-rel
 𝟎-compatible fe {𝑨} =
  λ 𝑓 args → 𝟎-compatible-op fe {𝑨} 𝑓 args

 -- Congruence relations
 Con : (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 Con {𝓤} 𝑨 =
  Σ θ ꞉ ( Rel ∣ 𝑨 ∣ 𝓤 ) , IsEquivalence θ × compatible 𝑨 θ

 con : (𝑨 : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ 𝑨 ∣ 𝓤) _
 con 𝑨 = λ θ → IsEquivalence θ × compatible 𝑨 θ

 record Congruence (𝑨 : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
   constructor mkcon
   field
     ⟨_⟩ : Rel ∣ 𝑨 ∣ 𝓤
     Compatible : compatible 𝑨 ⟨_⟩
     IsEquiv : IsEquivalence ⟨_⟩
 open Congruence
\end{code}


### The trivial congruence

We construct the "trivial" or "diagonal" or "identity" relation and prove it is a congruence as follows.

\begin{code}
 Δ : funext 𝓥 𝓤 → (𝑨 : Algebra 𝓤 𝑆) → Congruence 𝑨
 Δ fe 𝑨 = mkcon 𝟎-rel
               (𝟎-compatible fe {𝑨})
               (𝟎-IsEquivalence)

 _╱_ : (𝑨 : Algebra 𝓤 𝑆) → Congruence 𝑨
       ---------------------------------
  →    Algebra (𝓤 ⁺) 𝑆

 𝑨 ╱ θ = (( ∣ 𝑨 ∣ // ⟨ θ ⟩ ) , -- carrier
           (λ 𝑓 args        -- operations
             → ([ (𝑓 ̂ 𝑨) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
               ((𝑓 ̂ 𝑨)(λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
           )
          )
\end{code}

We would like to round out this chapter with a formalization of the trivial congruence of the free algebra 𝔽(𝒦, 𝑋), which we called Ψ(𝒦, 𝑻(𝑋)) in free algebras.

Unfortunately, this will have to wait until we have formalized the concepts of subalgebra and closure on which this congruence depends. Thus, our Agda definition of Ψ(𝒦, 𝑻(𝑋)) will appear in the [closure module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst) described in Chapter %s equational logic in agda.

-------------------------------------------------------------------------

### Unicode Hints 2

Table of some special characters used in the [congruences module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst).

 +--------|-------------------------------------------+
 | To get | Type                                      |
 +--------|-------------------------------------------+
 | ≈      | `\~~` or `\approx`                        |
 +--------|-------------------------------------------+
 | ⇒      | `\r2` or `\=>`                            |
 +--------|-------------------------------------------+
 | 𝟎, 𝟏   | `\B0`, `\B1`                              |
 +--------|-------------------------------------------+
 | θ, Δ   | `\theta`, `\Delta`                        |
 +--------|-------------------------------------------+
 | ⟨\_⟩    | `\<_\>`                                   |
 +--------|-------------------------------------------+
 | ╱      | `\---` then right arrow a number of times |
 +--------|-------------------------------------------+

**Emacs commands providing information about special characters/input methods**:

+ `M-x describe-char` (or `M-m h d c`) with the cursor on the character of interest
+ `M-x describe-input-method` (or `C-h I`)

------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Homomorphisms in Agda

This chapter describes the [homomorphisms
module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/homomorphisms.lagda.rst)
of the [UALib][].


### Types for homomorphisms

Our implementation of the notion of homomorphisms in the [UALib][] is an extensional one. What this means will become clear once we have presented the definitions. 

Here we say what it means for an operation 𝑓, interpreted in the algebras 𝑨 and 𝑩, to commute with a function $g : A → B$.

\begin{code}
module homomorphisms {𝑆 : Signature 𝓞 𝓥} where

 open prelude using (_∘_; _∈_; _⊆_; EpicInv; cong-app; EInvIsRInv; Image_∋_) public

 op_interpreted-in_and_commutes-with :
  (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
  (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

 op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g =
  ∀( 𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣ ) → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)

 all-ops-in_and_commute-with :
  (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
   →   (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

 all-ops-in 𝑨 and 𝑩 commute-with g = ∀ (𝑓 : ∣ 𝑆 ∣)
  → op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g

 is-homomorphism : (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
  →                (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

 is-homomorphism 𝑨 𝑩 g =
  all-ops-in 𝑨 and 𝑩 commute-with g
\end{code}

And now we define the type of homomorphisms.

\begin{code}
 hom : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
 hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g
\end{code}

An example of such a homomorphism is the identity map.

\begin{code}
 𝒾𝒹 :  (A : Algebra 𝓤 𝑆) → hom A A
 𝒾𝒹 _ = (λ x → x) , λ _ _ → refl _
\end{code}

### Composition

The composition of homomorphisms is again a homomorphism.

\begin{code}
 HCompClosed : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}{𝑪 : Algebra 𝓣 𝑆}
  →            hom 𝑨 𝑩   →   hom 𝑩 𝑪
               ---------------------
  →                  hom 𝑨 𝑪

 HCompClosed {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪}
  (g , ghom) (h , hhom) = h ∘ g , γ
   where
    γ : (𝑓 : ∣ 𝑆 ∣) (𝒂 : ∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣)
     →  (h ∘ g) ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ 𝒂)

    γ 𝑓 𝒂 = (h ∘ g) ((𝑓 ̂ 𝑨) 𝒂) ≡⟨ ap h (ghom 𝑓 𝒂) ⟩
           h ((𝑓 ̂ 𝑩)(g ∘ 𝒂))  ≡⟨ hhom 𝑓 (g ∘ 𝒂) ⟩
           (𝑓 ̂ 𝑪)(h ∘ g ∘ 𝒂)  ∎

\end{code}

### Factorization

If
+ `g : hom 𝑨 𝑩`,
+ `h : hom 𝑨 𝑪`,
+ `h` is surjective, and
+ `ker h ⊆ ker g`,

then there exists `ϕ : hom 𝑪 𝑩` such that `g = ϕ ∘ h`, that is, such that the following diagram commutes;

```
𝑨---- h -->>𝑪
 \         .
  \       .
   g     ∃ϕ
    \   .
     \ .
      V
      𝑩
```

We now formalize the statement and proof of this basic fact. (Notice
that the proof is fully constructive.)

\begin{code}
 homFactor : funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
             (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
  →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣ → Epic ∣ h ∣
            ---------------------------------------------
  →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

 homFactor fe {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪}
  (g , ghom) (h , hhom) Kh⊆Kg hEpic = (ϕ , ϕIsHomCB) , g≡ϕ∘h
   where
    hInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
    hInv = λ c → (EpicInv h hEpic) c

    ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
    ϕ = λ c → g ( hInv c )

    ξ : (x : ∣ 𝑨 ∣) → ker-pred h (x , hInv (h x))
    ξ x =  ( cong-app (EInvIsRInv fe h hEpic) ( h x ) )⁻¹

    g≡ϕ∘h : g ≡ ϕ ∘ h
    g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

    ζ : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)(x : ∥ 𝑆 ∥ 𝑓)
     →  𝒄 x ≡ (h ∘ hInv)(𝒄 x)

    ζ 𝑓 𝒄 x = (cong-app (EInvIsRInv fe h hEpic) (𝒄 x))⁻¹

    ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)
     →  (λ x → 𝒄 x) ≡ (λ x → h (hInv (𝒄 x)))

    ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EInvIsRInv fe h hEpic)⁻¹

    useker : (𝑓 : ∣ 𝑆 ∣)  (𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)
     → g (hInv (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄)))) ≡ g ((𝑓 ̂ 𝑨) (hInv ∘ 𝒄))

    useker = λ 𝑓 𝒄
     → Kh⊆Kg (cong-app
              (EInvIsRInv fe h hEpic)
              (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))))


    ϕIsHomCB : (𝑓 : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)
     →         ϕ ((𝑓 ̂ 𝑪) 𝒂)  ≡  (𝑓 ̂ 𝑩)(ϕ ∘ 𝒂)

    ϕIsHomCB 𝑓 𝒄 =
     g (hInv ((𝑓 ̂ 𝑪) 𝒄))                ≡⟨ i   ⟩
     g (hInv ((𝑓 ̂ 𝑪) (h ∘ (hInv ∘ 𝒄)))) ≡⟨ ii  ⟩
     g (hInv (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))))    ≡⟨ iii ⟩
     g ((𝑓 ̂ 𝑨) (hInv ∘ 𝒄))              ≡⟨ iv  ⟩
     (𝑓 ̂ 𝑩)(λ x → g (hInv (𝒄 x)))       ∎
     where
      i   = ap (g ∘ hInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
      ii  = ap (λ - → g (hInv -)) (hhom 𝑓 (hInv ∘ 𝒄))⁻¹
      iii = useker 𝑓 𝒄
      iv  = ghom 𝑓 (hInv ∘ 𝒄)
\end{code}

### Isomorphism

\begin{code}
 _≅_ : (𝑨 𝑩 : Algebra 𝓤 𝑆) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
 𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) ,
             (∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝒾𝒹 𝑨 ∣)
\end{code}

### Homomorphic images

The following seem to be (for our purposes) the two most useful types for representing homomomrphic images of an algebra.

\begin{code}
 HomImage : {𝑨 : Algebra 𝓤 𝑆} (𝑩 : Algebra 𝓤 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓤 ̇

 HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b


 HomImagesOf : {𝓤 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

 HomImagesOf {𝓤} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
                          is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ
\end{code}

Here are some further definitions, derived from the one above, that will come in handy later.

\begin{code}
 _is-hom-image-of_ : (𝑩 : Algebra 𝓤 𝑆)
   →                (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

 𝑩 is-hom-image-of 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf 𝑨) , 𝑩 ≅ ∣ 𝑪ϕ ∣

 _is-hom-image-of-class_ : {𝓤 : Universe}
  →                       Algebra 𝓤 𝑆
  →                       Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)
  →                       𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

 _is-hom-image-of-class_ {𝓤} 𝑩 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
                            (𝑨 ∈ 𝒦) × (𝑩 is-hom-image-of 𝑨)

 HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

 HomImagesOfClass 𝒦 = Σ 𝑩 ꞉ (Algebra _ 𝑆) , (𝑩 is-hom-image-of-class 𝒦)

 H : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 H 𝒦 = HomImagesOfClass 𝒦
\end{code}

In the following definition ℒ𝒦 represents a (universe-indexed) collection of classes.

\begin{code}
 H-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
  →         (𝓤 : Universe) → Algebra 𝓤 𝑆
  →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

 H-closed ℒ𝒦 =
  λ 𝓤 𝑩 → _is-hom-image-of-class_ {𝓤 = 𝓤} 𝑩 (ℒ𝒦 𝓤) → 𝑩 ∈ (ℒ𝒦 𝓤)
\end{code}

--------------------------------------------------------------------------------------

### Unicode Hints 3

Table of some special characters used in the [homomorphisms module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/homomorphisms.lagda.rst).

 |--------|---------------------|
 |  To get |          Type      |
 |--------|---------------------|
 |  𝒂, 𝒃  |  `\MIa`, `\MIb`     |
 |  𝑓 ̂ 𝑨 |   `\Mif \^ \MIA`    |
 |  ≅     |   `\~=` or `\cong` |
 |  ∘     |  `\comp` or `\circ` |
 |  𝒾𝒹   |   `\Mci\Mcd`        |
 |  ℒ𝒦  |  `\McL\McK`         |
 |  ϕ    | `\phi`              |
 | ------|---------------------|


**Emacs commands providing information about special characters/input methods**:

+ `M-x describe-char` (or `M-m h d c`) with the cursor on the character of interest
+ `M-x describe-input-method` (or `C-h I`)


----------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Terms in Agda

This chapter describes the [terms module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/terms.lagda.rst)
of the [UALib][].

### Types for terms

We start by declaring the module and importing the required dependencies.

\begin{code}
open basic
open congruences
open prelude using (global-dfunext)

module terms
 {𝑆 : Signature 𝓞 𝓥}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext} where

 open homomorphisms {𝑆 = 𝑆}

 open prelude using (intensionality; pr₂; Inv; InvIsInv; eq; fst; snd; 𝓇ℯ𝒻𝓁; _∙_) public
\end{code}

Next, we define a datatype called `Term` which, not surprisingly, represents the type of terms. The type `X :  𝒰 ̇` represents an arbitrary collection of "variables."

\begin{code}
 data Term {𝓤 : Universe}{X : 𝓤 ̇} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
   generator : X → Term{𝓤}{X}
   node : (f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓤}{X}) → Term

 open Term
\end{code}

### The term algebra

The term algebra was described informally in terms. We denote this
important algebra by 𝑻(X) and we implement it in Agda as follows.

\begin{code}
 --The term algebra 𝑻(X).
 𝑻 : {𝓤 : Universe}{X : 𝓤 ̇} → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) 𝑆
 𝑻 {𝓤}{X} = Term{𝓤}{X} , node

 term-op : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓤}{X} ) → Term
 term-op f args = node f args
\end{code}


### The universal property

We prove

1. every map `h : 𝑋 → ∣ 𝑨 ∣` lifts to a homomorphism from 𝑻(X) to 𝑨, and
2. the induced homomorphism is unique.

First, every map `X → ∣ 𝑨 ∣` lifts to a homomorphism.

\begin{code}
 --1.a. Every map (X → 𝑨) lifts.
 free-lift : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}{𝑨 : Algebra 𝓦 𝑆} (h : X → ∣ 𝑨 ∣)
  →          ∣ (𝑻{𝓤}{X}) ∣ → ∣ 𝑨 ∣

 free-lift {X = X} h (generator x) = h x
 free-lift {𝑨 = 𝑨} h (node f args) = (f ̂ 𝑨) λ i → free-lift{𝑨 = 𝑨} h (args i)

 --1.b. The lift is (extensionally) a hom
 lift-hom : {𝓤 𝓦 : Universe}{X : 𝓤 ̇}{𝑨 : Algebra 𝓦 𝑆}(h : X → ∣ 𝑨 ∣)
  →         hom (𝑻{𝓤}{X}) 𝑨

 lift-hom {𝑨 = 𝑨} h = free-lift{𝑨 = 𝑨} h , λ f a → ap (_ ̂ 𝑨) 𝓇ℯ𝒻𝓁
\end{code}
Next, the lift to (𝑻 X → 𝑨) is unique.
\begin{code}
 --2. The lift to (free → 𝑨) is (extensionally) unique.
 free-unique : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → funext 𝓥 𝓦
  →            {𝑨 : Algebra 𝓦 𝑆}(g h : hom (𝑻{𝓤}{X}) 𝑨)
  →            (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
  →            (t : Term{𝓤}{X})
              ---------------------------
  →            ∣ g ∣ t ≡ ∣ h ∣ t

 free-unique fe g h p (generator x) = p x
 free-unique {𝓤}{𝓦} {X} fe {𝑨 = 𝑨} g h p (node f args) =
    ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
    (f ̂ 𝑨)(λ i → ∣ g ∣ (args i))  ≡⟨ ap (_ ̂ 𝑨) γ ⟩
    (f ̂ 𝑨)(λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
    ∣ h ∣ (node f args)             ∎
    where γ = fe λ i → free-unique {𝓤}{𝓦} fe {𝑨} g h p (args i)
\end{code}

Next we note the easy fact that the lift induced by `h₀` agrees with
`h₀` on `X` and that the lift is surjective if the `h₀` is.

\begin{code}
 --lift agrees on X
 lift-agrees-on-X : {𝓤 : Universe}{X : 𝓤 ̇}{𝑨 : Algebra 𝓤 𝑆}(h₀ : X → ∣ 𝑨 ∣)(x : X)
         ----------------------------------------
  →       h₀ x ≡ ∣ lift-hom{𝑨 = 𝑨} h₀ ∣ (generator x)

 lift-agrees-on-X h₀ x = 𝓇ℯ𝒻𝓁

 --Of course, the lift of a surjective map is surjective.
 lift-of-epic-is-epic : {𝓤 : Universe}{X : 𝓤 ̇}{𝑨 : Algebra 𝓤 𝑆}(h₀ : X → ∣ 𝑨 ∣)
  →                     Epic h₀
                       ----------------------
  →                     Epic ∣ lift-hom{𝑨 = 𝑨} h₀ ∣

 lift-of-epic-is-epic{X = X}{𝑨 = 𝑨} h₀ hE y = γ
  where
   h₀pre : Image h₀ ∋ y
   h₀pre = hE y

   h₀⁻¹y : X
   h₀⁻¹y = Inv h₀ y (hE y)

   η : y ≡ ∣ lift-hom{𝑨 = 𝑨} h₀ ∣ (generator h₀⁻¹y)
   η =
    y                               ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
    h₀ h₀⁻¹y                        ≡⟨ lift-agrees-on-X{𝑨 = 𝑨} h₀ h₀⁻¹y ⟩
    ∣ lift-hom{𝑨 = 𝑨} h₀ ∣ (generator h₀⁻¹y) ∎

   γ : Image ∣ lift-hom h₀ ∣ ∋ y
   γ = eq y (generator h₀⁻¹y) η
\end{code}
Finally, we prove that for every 𝑆-algebra 𝑪, there exists an epimorphism from 𝑻 onto 𝑪.
\begin{code}
 𝑻hom-gen : {𝓤 : Universe}{X : 𝓤 ̇} (𝑪 : Algebra 𝓤 𝑆)
  →         Σ h ꞉ (hom 𝑻 𝑪), Epic ∣ h ∣
 𝑻hom-gen {X = X}𝑪 = h , lift-of-epic-is-epic h₀ hE
  where
   h₀ : X → ∣ 𝑪 ∣
   h₀ = fst (𝕏 𝑪)

   hE : Epic h₀
   hE = snd (𝕏 𝑪)

   h : hom 𝑻 𝑪
   h = lift-hom{𝑨 = 𝑪} h₀
\end{code}

### Interpretation

Let `t : Term` be a term and `𝑨` an 𝑆-algebra. We define the 𝑛-ary operation `t ̇ 𝑨` on `𝑨` by structural recursion on `t`.

1.  if `t = x ∈ X` (a variable) and `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then `(t ̇ 𝑨) a = a x`.
2.  if `t = f args`, where `f ∈ ∣ 𝑆 ∣` is an op symbol and `args : ∥ 𝑆 ∥ f → Term` is an (`∥ 𝑆 ∥ f`)-tuple of terms and
    `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then `(t ̇ 𝑨) a = ((f args) ̇ 𝑨) a = (f ̂ 𝑨) λ{ i → ((args i) ̇ 𝑨) a }`

\begin{code}
 _̇_ : {𝓤 𝓦 : Universe}{X : 𝓤 ̇ } → Term{𝓤}{X}
  →   (𝑨 : Algebra 𝓦 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 ((generator x) ̇ 𝑨) 𝒂 = 𝒂 x

 ((node f args) ̇ 𝑨) 𝒂 = (f ̂ 𝑨) λ i → (args i ̇ 𝑨) 𝒂
\end{code}
Next we show that if `p : ∣ 𝑻(X) ∣` is a term, then there exists `𝓅 : ∣ 𝑻(X) ∣` and `𝒕 : X → ∣ 𝑻(X) ∣` such that

  `p ≡ (𝓅 ̇ 𝑻(X)) 𝒕`. 

\begin{code}
 term-op-interp1 : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term{𝓤}{X}) →
  node f args ≡ (f ̂ 𝑻) args

 term-op-interp1 = λ f args → 𝓇ℯ𝒻𝓁


 term-op-interp2 : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term{𝓤}{X}}
                 ------------------------------------------------------------------
  →                a1 ≡ a2   →   node f a1 ≡ node f a2

 term-op-interp2 f a1≡a2 = ap (node f) a1≡a2


 term-op-interp3 : {𝓤 : Universe}{X : 𝓤 ̇}(f : ∣ 𝑆 ∣){a1 a2 : ∥ 𝑆 ∥ f → Term{𝓤}{X}}
                  ----------------------------------------------------------------
  →                a1 ≡ a2   →   node f a1 ≡ (f ̂ 𝑻) a2

 term-op-interp3 f {a1}{a2} a1≡a2 =
  node f a1     ≡⟨ term-op-interp2 f a1≡a2 ⟩
  node f a2     ≡⟨ term-op-interp1 f a2 ⟩
  (f ̂ 𝑻) a2    ∎

 term-gen : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻{𝓤}{X} ∣)
  →         Σ 𝓅 ꞉ ∣ 𝑻{𝓤}{X} ∣ , p ≡ (𝓅 ̇ 𝑻{𝓤}{X}) generator

 term-gen (generator x) = (generator x) , 𝓇ℯ𝒻𝓁
 term-gen (node f args) =
   node f (λ i → ∣ term-gen (args i) ∣ ) ,
     term-op-interp3 f (gfe λ i → ∥ term-gen (args i) ∥)

 tg : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻{𝓤}{X} ∣) → Σ 𝓅 ꞉ ∣ 𝑻 ∣ , p ≡ (𝓅 ̇ 𝑻) generator
 tg p = term-gen p

 term-gen-agreement : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻{𝓤}{X} ∣)
  →                   (p ̇ 𝑻)generator ≡ (∣ term-gen p ∣ ̇ 𝑻)generator

 term-gen-agreement (generator x) = 𝓇ℯ𝒻𝓁
 term-gen-agreement (node f args) = ap (f ̂ 𝑻) (gfe λ x → term-gen-agreement (args x))

 term-agreement : {𝓤 : Universe}{X : 𝓤 ̇}(p : ∣ 𝑻{𝓤}{X} ∣) → p ≡ (p ̇ 𝑻) generator
 term-agreement p = snd (tg p) ∙ (term-gen-agreement p)⁻¹
\end{code}
Here are some definitions that are useful when dealing with the interpretations of terms in a product structure.

\begin{code}
 interp-prod : {𝓤 𝓦 : Universe}{X : 𝓤 ̇} → funext 𝓥 𝓦
  →            {I : 𝓦 ̇}(p : Term{𝓤}{X})
               (𝒜 : I → Algebra 𝓦 𝑆)
               (x : X → ∀ i → ∣ (𝒜 i) ∣)
  →            (p ̇ (⨅ 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

 interp-prod fe (generator x₁) 𝒜 x = 𝓇ℯ𝒻𝓁

 interp-prod fe (node f t) 𝒜 x =
  let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
   (f ̂ ⨅ 𝒜)(λ x₁ → (t x₁ ̇ ⨅ 𝒜) x)                          ≡⟨ ap (f ̂ ⨅ 𝒜)(fe IH)⟩
   (f ̂ ⨅ 𝒜)(λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁)(λ j₁ → x j₁ i₁)))  ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
   (λ i₁ → (f ̂ 𝒜 i₁)(λ x₁ → (t x₁ ̇ 𝒜 i₁)(λ j₁ → x j₁ i₁))) ∎

 interp-prod2 : global-dfunext
  →             {𝓤 : Universe}{X : 𝓤 ̇}{I : 𝓤 ̇}(p : Term)(𝒜 : I → Algebra 𝓤 𝑆)
                ----------------------------------------------------------------------
  →             (p ̇ ⨅ 𝒜) ≡ λ(args : X → ∣ ⨅ 𝒜 ∣) → (λ i → (p ̇ 𝒜 i)(λ x → args x i))

 interp-prod2 fe (generator x₁) 𝒜 = 𝓇ℯ𝒻𝓁

 interp-prod2 fe {𝓤}{X} (node f t) 𝒜 =
  fe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
   let IH = λ x → interp-prod fe (t x) 𝒜  in
   let tA = λ z → t z ̇ ⨅ 𝒜 in
    (f ̂ ⨅ 𝒜)(λ s → tA s tup)                           ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (f ̂ ⨅ 𝒜)(λ s →  tA s tup)                          ≡⟨ ap (f ̂ ⨅ 𝒜)(fe  λ x → IH x tup)⟩
    (f ̂ ⨅ 𝒜)(λ s → (λ j → (t s ̇ 𝒜 j)(λ ℓ → tup ℓ j)))  ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ ℓ → tup ℓ i)))  ∎ 
\end{code}

### Compatibility of terms

In this section we present the formal proof of the fact that homomorphisms commute with terms. More precisely, if 𝑨 and 𝑩 are
𝑆-algebras, ℎ : 𝑨 → 𝑩 a homomorphism, and 𝑡 a term in the language of 𝑆, then for all 𝑎 : 𝑋 → ∣ 𝑨 ∣ we have

  ℎ (𝑡<sup>𝑨</sup> 𝑎) = 𝑡<sup>𝑩</sup> (ℎ ∘ 𝑎).

#### Homomorphisms commute with terms

\begin{code}
 comm-hom-term : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇} → funext 𝓥 𝓦
  →       (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
  →       (h : hom 𝑨 𝑩) (t : Term{𝓧}{X}) (a : X → ∣ 𝑨 ∣)
          --------------------------------------------
  →         ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

 comm-hom-term {𝓤}{𝓦}{𝓧}{X} fe 𝑨 𝑩 h (generator x) a = 𝓇ℯ𝒻𝓁

 comm-hom-term fe 𝑨 𝑩 h (node f args) a =
  ∣ h ∣((f ̂ 𝑨)(λ i₁ → (args i₁ ̇ 𝑨) a))  ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a ) ⟩
  (f ̂ 𝑩)(λ i₁ →  ∣ h ∣((args i₁ ̇ 𝑨) a)) ≡⟨ ap (_ ̂ 𝑩)(fe (λ i₁ → comm-hom-term fe 𝑨 𝑩 h (args i₁) a))⟩
  (f ̂ 𝑩)(λ r → (args r ̇ 𝑩)(∣ h ∣ ∘ a))   ∎
\end{code}

#### Congruences commute with terms

Rounding out this chapter is an formal proof of the fact that terms respect congruences. More precisely, we show that for every term `t`, every `θ ∈ Con(𝑨)`, and all tuples `a, b : 𝑋 → A`, we have

  (∀ x, a(x) θ b(x)) → (t ̇ 𝑨) a θ (t ̇ 𝑨) b.


\begin{code}
 compatible-term : {𝓤 : Universe}{X : 𝓤 ̇}
                   (𝑨 : Algebra 𝓤 𝑆) (t : Term{𝓤}{X}) (θ : Con 𝑨)
                  ------------------------------------------
  →                compatible-fun (t ̇ 𝑨) ∣ θ ∣

 compatible-term 𝑨 (generator x) θ p = p x

 compatible-term 𝑨 (node f args) θ p = pr₂( ∥ θ ∥ ) f λ{x → (compatible-term 𝑨 (args x) θ) p}
\end{code}


---------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Subalgebras in Agda

This chapter describes the [subuniverses module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/subuniverses.lagda.rst)
of the [UALib][].

We define subuniverses and subalgebras and prove some basic facts about them in this, the [subuniverses.lagda.rst](subuniverses%20module) file of the [UALib][].


### Preliminaries

The [subuniverses.lagda.rst](subuniverses%20module) file starts, as usual, by fixing a signature 𝑆 and satisfying some dependencies.

\begin{code}
open basic
open congruences
open prelude using (global-dfunext)

module subuniverses {𝑆 : Signature 𝓞 𝓥}
                    {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
                    {fe : global-dfunext} where

 open homomorphisms {𝑆 = 𝑆}

 open terms {𝑆 = 𝑆}{𝕏 = 𝕏}{gfe = fe} renaming (generator to ℊ)

 open import Relation.Unary using (⋂)

 open prelude using (Im_⊆_; Univalence; embeddings-are-lc; univalence-gives-global-dfunext; 
  𝓟; _∈₀_; _⊆₀_; pr₁; domain; is-subsingleton; Π-is-subsingleton;is-equiv; lr-implication; 
  ×-is-subsingleton; ∈-is-subsingleton; is-embedding; pr₁-embedding; rl-implication; inverse;
  embedding-gives-ap-is-equiv; is-set;_⇔_;transport; subset-extensionality'; equiv-to-subsingleton; 
  powersets-are-sets'; _≃_; id; _●_; logically-equivalent-subsingletons-are-equivalent) public
\end{code}

### Types for subuniverses

We begin the [subuniverses module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/subuniverses.lagda.rst) with a straightforward definition of the collection of subuniverses of an algebra A. Since a subuniverse is a subset of the domain of A, it is defined as a predicate on ∣ A ∣. Thus, the collection of subuniverses is a predicate on predicates on ∣ A ∣.

\begin{code}
 Subuniverses : (𝑨 : Algebra 𝓤 𝑆) → Pred (Pred ∣ 𝑨 ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)

 Subuniverses 𝑨 B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → Im a ⊆ B → (f ̂ 𝑨) a ∈ B
\end{code}

### Subuniverse generation

Next we formalize the important theorem about subuniverse generation. Recall, if 𝑨 = ⟨𝐴, …⟩ is an 𝑆-algebra, if ∅ ≠ 𝐴₀ ⊆ 𝐴, and if we define by recursion the sets 𝐴<sub>n+1</sub> = 𝐴ₙ ∪ {𝑓 𝑎 ∣ 𝑓 : ∣ 𝑆 ∣, 𝑎 : ∥ 𝑆 ∥ 𝑓 → 𝐴ₙ }, then the subuniverse of 𝐴 generated by 𝐴₀ is Sg<sup>𝑨</sup>(𝐴₀) = ⋃ₙ 𝐴ₙ.

\begin{code}
 record Subuniverse {𝑨 : Algebra 𝓤 𝑆} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ where
  constructor mksub
  field
    sset  : Pred ∣ 𝑨 ∣ 𝓤
    isSub : sset ∈ Subuniverses 𝑨

 data Sg (𝑨 : Algebra 𝓤 𝑆) (X : Pred ∣ 𝑨 ∣ 𝓣) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣) where
  var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
  app : (f : ∣ 𝑆 ∣){a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣} → Im a ⊆ Sg 𝑨 X
        ---------------------------------------------
   →       (f ̂ 𝑨) a ∈ Sg 𝑨 X

\end{code}
Of course, we should be able to prove that Sg 𝑨 𝑋 is indeed a subuniverse of 𝑨.
\begin{code}
 sgIsSub : {𝑨 : Algebra 𝓤 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓤} → Sg 𝑨 X ∈ Subuniverses 𝑨
 sgIsSub f a α = app f α
\end{code}
And, as the subuniverse *generated by* 𝑋, it had better be the smallest subuniverse of 𝑨 containing 𝑋. We prove this by induction, as follows:
\begin{code}
 sgIsSmallest : {𝑨 : Algebra 𝓤 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓡} {Y : Pred ∣ 𝑨 ∣ 𝓢}
  →             Y ∈ Subuniverses 𝑨  →   X ⊆ Y
               -------------------------------
  →                     Sg 𝑨 X ⊆ Y

 -- By induction on x ∈ Sg X, show x ∈ Y
 sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X

 sgIsSmallest {𝑨 = 𝑨}{Y = Y} YIsSub X⊆Y (app f {a} ima⊆SgX) = app∈Y
  where
   -- First, show the args are in Y
   ima⊆Y : Im a ⊆ Y
   ima⊆Y i = sgIsSmallest YIsSub X⊆Y (ima⊆SgX i)

   --Since Y is a subuniverse of 𝑨, it contains the application
   app∈Y : (f ̂ 𝑨) a ∈ Y          --           of f to said args.
   app∈Y = YIsSub f a ima⊆Y
\end{code}

### Closure under intersection

Recall that the intersection ⋂ᵢ 𝐴ᵢ of a collection {𝐴ᵢ ∣ 𝐴ᵢ ≤ 𝑨} of subuniverses of an algebra 𝑨 is again a subuniverse of 𝑨. We formalize the statement and proof of this easy fact in Agda as follows.

\begin{code}
 sub-inter-is-sub : {𝑨 : Algebra 𝓤 𝑆}
                    {I : 𝓘 ̇}{𝒜 : I → Pred ∣ 𝑨 ∣ 𝓣}
  →                 ((i : I) → 𝒜 i ∈ Subuniverses 𝑨)
                   -------------------------------------
  →                  ⋂ I 𝒜 ∈ Subuniverses 𝑨

 sub-inter-is-sub {𝑨 = 𝑨} {I = I} {𝒜 = 𝒜} Ai-is-Sub f a ima⊆⋂A = α
  where
   α : (f ̂ 𝑨) a ∈ ⋂ I 𝒜
   α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i
\end{code}

### Generation with terms

Recall that subuniverse can be generated using the images of terms: If 𝑌 is a subset of 𝐴, then

  Sg<sup>𝑨</sup>(𝑌) = {𝑡<sup>𝑨</sup> 𝑎 : 𝑡 ∈ 𝑻(𝑋), 𝑎 : 𝑋 → 𝑌}.
  
To formalize this idea in Agda, we first prove that subuniverses are closed under the action of term operations.

\begin{code}
 sub-term-closed : {X : 𝓤 ̇}{𝑨 : Algebra 𝓤 𝑆}{B : Pred ∣ 𝑨 ∣ 𝓤}
  →                B ∈ Subuniverses 𝑨
  →                (t : Term)(b : X → ∣ 𝑨 ∣)
  →                (∀ x → b x ∈ B)
                 ---------------------------
  →                ((t ̇ 𝑨) b) ∈ B

 sub-term-closed B≤A (ℊ x) b b∈B = b∈B x

 sub-term-closed {𝑨 = 𝑨} {B = B} B≤A (node f t) b b∈B =
    B≤A f (λ z → (t z ̇ 𝑨) b)
           (λ x → sub-term-closed {𝑨 = 𝑨} {B = B} B≤A (t x) b b∈B)
\end{code}
This proves Sg<sup>𝑨</sup>(𝑌) ⊇ {𝑡<sup>𝑨</sup> 𝑎 : 𝑡 ∈ 𝑇(𝑋), 𝑎 : 𝑋 → 𝑌 }.

Next we prove Sg<sup>𝑨</sup>(𝑌) ⊆ {𝑡<sup>𝑨</sup> 𝑎 : 𝑡 ∈ 𝑇(𝑋), 𝑎 : 𝑋 → 𝑌 } by the following steps:

1.  The image of 𝑌 under all terms, which we call TermImage 𝑌, is a subuniverse of 𝑨; i.e.,

    TermImage 𝑌 ={𝑡<sup>𝑨</sup> 𝑎 : 𝑡 ∈ 𝑇(𝑋), 𝑎 : 𝑋 → 𝑌 } ≤ 𝑨.
    
2.  𝑌 ⊆ TermImage 𝑌 (obvious)

3.  Sg<sup>𝑨</sup>(𝑌) is the smallest subuniverse containing 𝑌 (see sgIsSmallest) so 

    Sg<sup>𝑨</sup>(𝑌) ⊆ TermImage 𝑌.

(The last item was already proved above; see `sgIsSmallest`.)

\begin{code}
 data TermImage (𝑨 : Algebra 𝓤 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤) where
  var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
  app : (f : ∣ 𝑆 ∣) (t : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → (∀ i  →  t i ∈ TermImage 𝑨 Y)
       ---------------------------------------------------------------
   →                (f ̂ 𝑨) t ∈ TermImage 𝑨 Y

 --1. TermImage is a subuniverse
 TermImageIsSub : {𝑨 : Algebra 𝓤 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
  →               TermImage 𝑨 Y ∈ Subuniverses 𝑨

 TermImageIsSub = λ f a x → app f a x

 --2. Y ⊆ TermImageY
 Y⊆TermImageY : {𝑨 : Algebra 𝓤 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
  →             Y ⊆ TermImage 𝑨 Y

 Y⊆TermImageY {a} a∈Y = var a∈Y

 -- 3. Sg^A(Y) is the smallest subuniverse containing Y. (Proof: see `sgIsSmallest`)
\end{code}
Finally, we can prove the desired inclusion.
\begin{code}
 SgY⊆TermImageY : {𝑨 : Algebra 𝓤 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
  →               Sg 𝑨 Y ⊆ TermImage 𝑨 Y
 SgY⊆TermImageY = sgIsSmallest TermImageIsSub Y⊆TermImageY
\end{code}

<!-- **Exercise**. Prove the following by generalizing the relation ≃ to predicates: -->
<!-- ```agda -->
<!-- SgY≃TermImageY : (Y : Pred ∣ 𝑨 ∣ k) → (TermImage Y) ≃ (Sg Y) -->
<!-- SgY≃TermImageY {x} Y = ? -->
<!-- ``` -->


### Homomorphic images are subuniverses

In this subsection we show that the image of an (extensional) homomorphism is a subuniverse. Before implementing the result formally in Agda, let us recall the steps of the informal proof.

Let 𝑓 be an operation symbol, let 𝑏 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝐵 ∣ be a (∥ 𝑆 ∥ 𝑓)-tuple of elements of ∣ 𝑩 ∣, and assume the image Im 𝑏 of 𝑏 belongs to the image `Image ℎ` of ℎ. We must show that 𝑓<sup>𝑩</sup> 𝑏 ∈ Image ℎ. The assumption Im 𝑏 ⊆ Image ℎ implies that there is a (∥ 𝑆 ∥ 𝑓)-tuple 𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣ such that ℎ ∘ 𝑎 = 𝑏. Since ℎ is a homomorphism, we have 𝑓<sup>𝑩</sup> 𝑏 = 𝑓<sup>𝑩</sup> (ℎ ∘ 𝑎) = ℎ (𝑓<sup>𝑨</sup> 𝑎) ∈ Image ℎ.

Recall the definition of `HomImage` from the [homomorphisms module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/homomorphisms.lagda.rst),

```agda
HomImage : ∣ B ∣ → 𝓤 ̇
HomImage = λ b → Image ∣ h ∣ ∋ b
```

We are now ready to formalize the proof that homomorphic images are subuniverses.

\begin{code}
 hom-image-is-sub : {fe : funext 𝓥 𝓤} {𝑨 𝑩 : Algebra 𝓤 𝑆} (ϕ : hom 𝑨 𝑩)
                   -------------------------------------------------
  →                 (HomImage{𝑨 = 𝑨} 𝑩 ϕ) ∈ Subuniverses 𝑩

 hom-image-is-sub {fe = fe}{𝑨 = 𝑨}{𝑩 = 𝑩} ϕ f b b∈Imf = eq ((f ̂ 𝑩) b) ((f ̂ 𝑨) ar) γ
  where
   ar : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
   ar = λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)

   ζ : ∣ ϕ ∣ ∘ ar ≡ b
   ζ = fe (λ x → InvIsInv ∣ ϕ ∣(b x)(b∈Imf x))

   γ : (f ̂ 𝑩) b ≡ ∣ ϕ ∣((f ̂ 𝑨)(λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)))

   γ = (f ̂ 𝑩) b          ≡⟨ ap (f ̂ 𝑩)(ζ ⁻¹) ⟩
       (f ̂ 𝑩)(∣ ϕ ∣ ∘ ar)  ≡⟨(∥ ϕ ∥ f ar)⁻¹ ⟩
       ∣ ϕ ∣((f ̂ 𝑨) ar)   ∎
\end{code}


### Types for subalgebras

Finally, we define, once and for all, the type of subalgebras of an algebra (resp., subalgebras of algebras in a class of algebras) that we will use in the sequel.

\begin{code}
 SubalgebrasOf : {𝓢 : Universe} → Algebra 𝓢 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺ ̇
 SubalgebrasOf {𝓢} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓢 𝑆) , Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) , is-embedding h × is-homomorphism 𝑩 𝑨 h

 SubalgebrasOfClass : {𝓢 : Universe} → Pred (Algebra 𝓢 𝑆)(𝓢 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺ ̇
 SubalgebrasOfClass 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , (𝑨 ∈ 𝒦) × SubalgebrasOf 𝑨

 SubalgebrasOfClass' : {𝓢 : Universe} → Pred (Algebra 𝓢 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓢 ⁺ ̇
 SubalgebrasOfClass' 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , (𝑨 ∈ 𝒦) × SubalgebrasOf 𝑨
\end{code}

----------------------------------------------------------------------------------

### Unicode Hints 4

Table of some special characters used in the [subuniverses module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/subuniverses.lagda.rst).

   ------------|----------------------------|
   | To get    |  Type                      |
   ------------|----------------------------|
   | 𝓘, 𝓣     |   `\MCI`, `\MCT`           |
   | \_⊧\_≈\_  |  `_\models_\~~_`           |
   | \_⊧\_≋\_  |   `_\models_\~~~_`        |
   | ⊆         |   `\subseteq` or `\sub=`  |
   | ⋂         |   `\bigcap` or `\I`      |
   | ξ         |    `\xi`                 |
   ------------|--------------------------|

**Emacs commands providing information about special characters/input methods**:

+ `M-x describe-char` (or `M-m h d c`) with the cursor on the character of interest
+ `M-x describe-input-method` (or `C-h I`)

-----------------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## Equational Logic in Agda

This chapter describes the [closure module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst)
of the [agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io).

### Closure operators and varieties

Fix a signature 𝑆 and let 𝒦 be a class of 𝑆-algebras. Define

+ H(𝒦) = homomorphic images of members of 𝒦;
+ S(𝒦) = algebras isomorphic to a subalgebra of a member of 𝒦;
+ P(𝒦) = algebras isomorphic to a direct product of members of 𝒦.

As a straight-forward verification confirms, H, S, and P are closure operators. A class 𝒦 of 𝑆-algebras is said to be *closed under the formation of homomorphic images* if H(𝒦) ⊆ 𝒦. Similarly, 𝒦 is *closed under the formation of subalgebras* (resp., *products*) provided S(𝒦) ⊆ 𝒦 (resp., P(𝒦) ⊆ 𝒦).

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class H(𝒦) (resp., S(𝒦); resp., P(𝒦)) is closed under isomorphism.

The operators H, S, and P can be composed with one another repeatedly, forming yet more closure operators. If C₁ and C₂ are closure operators on classes of structures, let us say that C₁ ≤ C₂ if for every class 𝒦 we have C₁(𝒦) ⊆ C₂(𝒦).

A class 𝒦 of 𝑆-algebras is called a **variety** if it is closed under each of the closure operators H, S, and P introduced above; the corresponding closure operator is often denoted 𝕍. Thus, if 𝒦 is a class of similar algebras, then the **variety generated by** 𝒦 is denoted by 𝕍(𝒦) and defined to be the smallest class that contains 𝒦 and is closed under H, S, and P.

We would like to know how to construct 𝕍(𝒦) directly from 𝒦, but it's not immediately obvious how many times we would have to apply the operators H, S, P before the result stabilizes to form a variety---the **variety generated by** 𝒦. Fortunately, Garrett Birkhoff proved that if we apply the operators in the correct order, then it suffices to apply each one only once.

### Types for identities

In his treatment of Birhoff's HSP theorem, Cliff Bergman (at the start of Section 4.4 of his universal algebra textbook Bergman:2012) proclaims, "Now, finally, we can formalize the idea we have been using since the first page of this text." He then proceeds to define **identities of terms** as follows (paraphrasing for notational consistency):

Let 𝑆 be a signature. An **identity** or **equation** in 𝑆 is an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝑻(X). If A is an 𝑆-algebra we say that A **satisfies** 𝑝 ≈ 𝑞 if 𝑝 ̇ A ≡ 𝑞 ̇ A. In this situation, we write A ⊧ 𝑝 ≈ 𝑞.

If 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if, for every A ∈ 𝒦, A ⊧ 𝑝 ≈ 𝑞. Finally, if 𝓔 is a set of equations, we write 𝒦 ⊧ 𝓔 if every member of 𝒦 satisfies every member of 𝓔.

We formalize these notions in Agda in the [closure module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst), which begins as follows. (Note the imports that were postponed until after the start of the closure module so that the imports share the same signature 𝑆 with the [closure module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst).

\begin{code}
open basic
open congruences
open prelude using (global-dfunext; dfunext; im; _∪_; inj₁; inj₂)

module closure
 {𝑆 : Signature 𝓞 𝓥}
 {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

 open homomorphisms {𝑆 = 𝑆} public
 open terms {𝑆 = 𝑆}{𝕏 = 𝕏}{gfe = gfe} renaming (generator to ℊ) public
 open subuniverses {𝑆 = 𝑆}{𝕏 = 𝕏}{fe = gfe} public
\end{code}

Our first definition in the [closure module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst)
is notation that represents the satisfaction of equations.

The standard notation is `𝑨 ⊧ p ≈ q`, which means that the identity `p ≈ q` is satisfied in 𝑨. In otherwords, for all assignments `a : X → ∣ 𝑨 ∣` of values to variables, we have `(p ̇ 𝑨) a ≡ (q ̇ 𝑨) a`.

If 𝒦 is a class of structures, it is standard to write `𝒦 ⊧ p ≈ q` just in case all structures in the class 𝒦 model the identity p ≈ q. However, because a class of structures has a different type than a single structure, we will need different notation, so we have settled on writing `𝒦 ⊧ p ≋ q` to denote this concept.

\begin{code}
 _⊧_≈_ : Algebra 𝓤 𝑆 → Term{𝓤}{X} → Term → 𝓤 ̇
 𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

 _⊧_≋_ : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Term → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 _⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q
\end{code}

### Equational theories and classes

Here we define the notation `Th` for the identities satisfied by all structures in a given class, and `Mod` for all structures that satisfy a given collection of identities.

\begin{code}
 Th :  Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

 Mod : Pred (Term × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) → Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q
\end{code}

### Compatibility of identities

Identities are compatible with the formation of subalgebras, homomorphic images and products. More precisely, for every class 𝒦 of structures, each of the classes S(𝒦), H(𝒦), P(𝒦), 𝕍(𝒦) satisfies the same set of identities as does 𝒦.

Here we formalize the notion of closure under the taking of products, subalgebras, and homomorphic images, and we prove that each of these closures preserves identities.

First a data type that represents classes of algebraic structures that are closed under the taking of products of algebras in the class can be defined in [Agda][] as follows.

\begin{code}
 --Closure under products
 data PClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  pbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo
  prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ PClo) → ⨅ 𝒜 ∈ PClo
\end{code}
A datatype that represents classes of structures that are closed under the taking of subalgebras is
\begin{code}
 -- Subalgebra Closure
 data SClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
  sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo
  sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo
\end{code}
Next, a datatype representing classes of algebras that are closed under homomorphic images of algebras in the class,
\begin{code}
 --Closure under hom images
 data HClo : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  hbase : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo
  hhom : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ HClo → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo
\end{code}
And, finally, an inductive type representing classes that are closed under all three, H, S, and P,
\begin{code}
 -- Variety Closure
 data VClo : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) where
  vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo
  vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ VClo) → ⨅ 𝒜 ∈ VClo
  vsub : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo
  vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo
\end{code}

#### Products preserve identities

We prove that identities satisfied by all factors of a product are also satisfied by the product.

\begin{code}
 products-preserve-identities : (p q : Term{𝓤}{X}) (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
  →                             ((i : I) → (𝒜 i) ⊧ p ≈ q)
                                ------------------------------------------------------
  →                             ⨅ 𝒜 ⊧ p ≈ q

 products-preserve-identities p q I 𝒜 𝒜⊧p≈q = γ
   where
    γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
    γ = gfe λ a →
     (p ̇ ⨅ 𝒜) a                           ≡⟨ interp-prod{𝓤 = 𝓤} fevu p 𝒜 a ⟩
     (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (a x) i)) ⟩
     (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
     (q ̇ ⨅ 𝒜) a                           ∎

 products-in-class-preserve-identities : (p q : Term{𝓤}{X}) (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
  →                                      𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
                                         -----------------------------------------------------
  →                                       ⨅ 𝒜 ⊧ p ≈ q

 products-in-class-preserve-identities p q I 𝒜 𝒦⊧p≋q all𝒜i∈𝒦 = γ
   where
    𝒜⊧p≈q : ∀ i → (𝒜 i) ⊧ p ≈ q
    𝒜⊧p≈q i = 𝒦⊧p≋q (all𝒜i∈𝒦 i)

    γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
    γ = products-preserve-identities p q I 𝒜 𝒜⊧p≈q
\end{code}

#### Subalgebras preserve identities
We now show that every term equation, `p ≈ q`, that is satisfied by all algebras in 𝒦 is also satisfied by every subalgebra of every member of 𝒦.  In other words, the collection of identities modeled by a given class of algebras is also modeled by all of the subalgebras of algebras in that class.

\begin{code}
 subalgebras-preserve-identities : {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}(p q : Term)
                                   ((_ , _ , (𝑩 , _ , _)) : SubalgebrasOfClass' 𝒦)
  →                                𝒦 ⊧ p ≋ q
                                   -------------
  →                                𝑩 ⊧ p ≈ q

 subalgebras-preserve-identities {𝒦} p q (𝑨 , KA , (𝑩 , h , (hem , hhm))) Kpq = γ
  where
   β : 𝑨 ⊧ p ≈ q
   β = Kpq KA

   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
   ξ b =
    h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality β (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ 𝑩) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : 𝑩 ⊧ p ≈ q
   γ = gfe λ b → hlc (ξ b)
\end{code}

#### Closure under hom images

Recall that an identity is satisfied by all algebras in a class if and only if that identity is compatible with all
homomorphisms from the term algebra 𝑻(𝑋) into algebras of the class. More precisely, if 𝓚 is a class of 𝑆-algebras and 𝑝, 𝑞 terms in the language of 𝑆, then,

  𝒦 ⊧ p ≈ q  ⇔  ∀𝑨 ∈ 𝒦, ∀h ∈ Hom(𝑻(X), 𝑨), h ∘ p<sup>𝑻(X)</sup> = h ∘ q<sup>𝑻(X)</sup>.

We now formalize this result in Agda.  We begin with the "only if" direction.

\begin{code}
 identities-compatible-with-homs : (p q : Term{𝓤}{X})
                                   (p≋q : 𝒦 ⊧ p ≋ q)
                                  ------------------------------------------------------
  →                                ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝒦 𝑨)(h : hom (𝑻{𝓤}{X}) 𝑨)
                                   →  ∣ h ∣ ∘ (p ̇ 𝑻{𝓤}{X}) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)

 identities-compatible-with-homs p q p≋q 𝑨 KA h = γ
  where
   pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
   pA≡qA = p≋q KA

   pAh≡qAh : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
   pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

   hpa≡hqa : ∀(𝒂 : X → ∣ 𝑻 ∣ ) → ∣ h ∣ ((p ̇ 𝑻) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻) 𝒂)
   hpa≡hqa 𝒂 =
    ∣ h ∣ ((p ̇ 𝑻) 𝒂)  ≡⟨ comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺} fevu (𝑻{𝓤}{X}) 𝑨 h p 𝒂 ⟩
    (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term{𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺} fevu 𝑻 𝑨 h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ 𝑻) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻)
   γ = gfe hpa≡hqa
\end{code}
And now for the "if" direction.
\begin{code}
 homs-compatible-with-identities : (p q : Term{𝓤}{X})
                                   (hp≡hq : ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦) (h : hom (𝑻{𝓤}{X}) 𝑨)
                                            → ∣ h ∣ ∘ (p ̇ 𝑻) ≡ ∣ h ∣ ∘ (q ̇ 𝑻))
                                   ----------------------------------------------------------------
  →                                 𝒦 ⊧ p ≋ q

 homs-compatible-with-identities p q hp≡hq {𝑨} KA = γ
  where
   h : (𝒂 : X → ∣ 𝑨 ∣) → hom 𝑻 𝑨
   h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

   γ : 𝑨 ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ 𝑨) 𝒂            ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨(comm-hom-term gfe 𝑻 𝑨 (h 𝒂) p ℊ)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻)) ℊ  ≡⟨ ap (λ - → - ℊ) (hp≡hq 𝑨 KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻)) ℊ  ≡⟨ (comm-hom-term gfe 𝑻 𝑨 (h 𝒂) q ℊ) ⟩
    (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (q ̇ 𝑨) 𝒂             ∎
\end{code}
Of course, we can easily combine the last two results into a single "iff" theorem.
\begin{code}
 compatibility-of-identities-and-homs : (p q : Term{𝓤}{X})
                                        -------------------------------------------------
  →                                     (𝒦 ⊧ p ≋ q) ⇔ (∀(𝑨 : Algebra 𝓤 𝑆)
                                                           (KA : 𝑨 ∈ 𝒦)(hh : hom 𝑻 𝑨)
                                                          →   ∣ hh ∣ ∘ (p ̇ 𝑻) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻))

 compatibility-of-identities-and-homs p q = identities-compatible-with-homs p q , homs-compatible-with-identities p q
\end{code}
Next we prove a fact that might seem obvious or at least intuitive---namely, that identities modeled by an algebra are compatible with the interpretation of terms in that algebra.

\begin{code}
 hom-id-compatibility : (p q : ∣ 𝑻{𝓤}{X} ∣ ) (𝑨 : Algebra 𝓤 𝑆)
                        (ϕ : hom 𝑻 𝑨) (p≈q : 𝑨 ⊧ p ≈ q)
                       ----------------------------------------
  →                     ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q

 hom-id-compatibility p q 𝑨 ϕ p≈q =
  ∣ ϕ ∣ p              ≡⟨ ap ∣ ϕ ∣ (term-agreement p) ⟩
  ∣ ϕ ∣ ((p ̇ 𝑻) ℊ)    ≡⟨ (comm-hom-term fevu (𝑻{𝓤}{X}) 𝑨 ϕ p ℊ) ⟩
  (p ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ intensionality p≈q (∣ ϕ ∣ ∘ ℊ)  ⟩
  (q ̇ 𝑨) (∣ ϕ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term fevu (𝑻{𝓤}{X}) 𝑨 ϕ q ℊ)⁻¹ ⟩
  ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)    ≡⟨ (ap ∣ ϕ ∣ (term-agreement q))⁻¹ ⟩
  ∣ ϕ ∣ q              ∎
\end{code}


#### Identities for product closure
Next we prove 

+ `pclo-id1`: if every algebra in the class 𝒦 satisfies a particular identity, say 𝑝 ≈ 𝑞, then every algebra in the closure PClo of 𝒦 under the taking of arbitrary products also satisfies 𝑝 ≈ 𝑞, and, conversely,
+ `pclo-id2`: if every algebra of the product closure PClo of 𝒦 satisfies 𝑝 ≈ 𝑞, then so does every algebra in 𝒦.

Here's proof of the first item.
\begin{code}
 pclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (PClo ⊧ p ≋ q)
 pclo-id1 {p} {q} α (pbase x) = α x
 pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
   IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝒦  i )

   γ : p ̇ (⨅ 𝒜) ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH
\end{code}
The second item is even easier to prove since 𝒦 ⊆ PClo.
\begin{code}
 pclo-id2 : ∀{p q} → ((PClo) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
 pclo-id2 p A∈𝒦 = p (pbase A∈𝒦)
\end{code}

#### Identities for subalgebra closure
Here we prove

+ `sclo-id1`: if every algebra in the class 𝒦 satisfies 𝑝 ≈ 𝑞, then so does every algebra in the closure SClo of 𝒦 under the taking of subalgebras; and, conversely,
+ `sclo-id2`: if every algebra of the subalgebra closure SClo of 𝒦 satisfies 𝑝 ≈ 𝑞, then so does every algebra in 𝒦.

First we need to define a type that represents singletons containing exactly one algebra.
\begin{code}
 ｛_｝ : Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 ｛ 𝑨 ｝ 𝑩 = 𝑨 ≡ 𝑩
\end{code}
The formal statement and proof of the first item above is as follows.
\begin{code}
 sclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (SClo ⊧ p ≋ q)
 sclo-id1 {p} {q} 𝒦⊧p≋q (sbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 sclo-id1 {p} {q} 𝒦⊧p≋q (sub {𝑨 = 𝑨} A∈SClo𝒦 sa) = 

  -- (We apply subalgebras-preserve-identities to the class 𝒦 ∪ ｛ 𝑨 ｝)
  subalgebras-preserve-identities p q (𝑨 , inj₂ 𝓇ℯ𝒻𝓁 , sa) 𝒦A⊧p≋q 

   where
    A⊧p≈q : 𝑨 ⊧ p ≈ q
    A⊧p≈q = sclo-id1{p}{q} 𝒦⊧p≋q A∈SClo𝒦

    Asingleton⊧p≋q : ｛ 𝑨 ｝ ⊧ p ≋ q
    Asingleton⊧p≋q (refl _)  = A⊧p≈q

    𝒦A⊧p≋q : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    𝒦A⊧p≋q {𝑩} (inj₁ x) = 𝒦⊧p≋q x
    𝒦A⊧p≋q {𝑩} (inj₂ y) = Asingleton⊧p≋q y
\end{code}
As with the analogous result for products, proving the second item from the list above is trivial.
\begin{code}
 sclo-id2 : ∀ {p q} → (SClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 sclo-id2 p A∈𝒦 = p (sbase A∈𝒦)
\end{code}

#### Identities for hom image closure
We prove

+ `hclo-id1`: if every algebra in the class 𝒦 satisfies a 𝑝 ≈ 𝑞, then so does every algebra in the closure HClo of 𝒦 under the taking of homomorphic images; and, conversely,
+ `hclo-id2`: if every algebra of the homomorphic image closure HClo of 𝒦 satisfies 𝑝 ≈ 𝑞, then so does every algebra in 𝒦.

\begin{code}
 hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo ⊧ p ≋ q)
 hclo-id1 {p}{q} α (hbase KA) = α KA
 hclo-id1 {p}{q} α (hhom{𝑨} HCloA (𝑩 , ϕ , (ϕhom , ϕsur))) = γ
  where
   β : 𝑨 ⊧ p ≈ q
   β = (hclo-id1{p}{q} α) HCloA

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur (𝒃 x)))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur (𝒃 x))

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃              ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality β (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃               ∎

 hclo-id2 : ∀ {p q} → (HClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 hclo-id2 p KA = p (hbase KA)
\end{code}

#### Identities for HSP closure

Finally, we prove

+ `vclo-id1`: if every algebra in the class 𝒦 satisfies a 𝑝 ≈ 𝑞, then so does every algebra in the closure VClo of 𝒦 under the taking of homomorphic images, subalgebras, and products; and, conversely,
+ `vclo-id2`: if every algebra of the varietal closure VClo of 𝒦 satisfies 𝑝 ≈ 𝑞, then so does every algebra in 𝒦.

\begin{code}
 vclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (VClo ⊧ p ≋ q)
 vclo-id1 {p} {q} α (vbase A∈𝒦) = α A∈𝒦
 vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} 𝒜∈VClo) = γ
  where
   IH : (i : I) → 𝒜 i ⊧ p ≈ q
   IH i = vclo-id1{p}{q} α (𝒜∈VClo i)

   γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} A∈VClo sa ) =
  subalgebras-preserve-identities  p q (𝑨 , inj₂ 𝓇ℯ𝒻𝓁 , sa) 𝒦A⊧p≋q 
   where
    A⊧p≈q : 𝑨 ⊧ p ≈ q
    A⊧p≈q = vclo-id1{p}{q} α A∈VClo

    Asingleton⊧p≋q : ｛ 𝑨 ｝ ⊧ p ≋ q
    Asingleton⊧p≋q (refl _)  = A⊧p≈q

    𝒦A⊧p≋q : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
    𝒦A⊧p≋q {𝑩} (inj₁ x) = α x
    𝒦A⊧p≋q {𝑩} (inj₂ y) = Asingleton⊧p≋q y


 vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨} A∈VClo (𝑩 , ϕ , (ϕh , ϕE))) = γ
  where
   β : 𝑨 ⊧ p ≈ q
   β = vclo-id1{p}{q} α A∈VClo

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕE (𝒃 x)))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕE (𝒃 x))

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality β (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))   ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃                ∎

 vclo-id2 : ∀ {p q} → (VClo ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 vclo-id2 p A∈𝒦 = p (vbase A∈𝒦)
\end{code}


### Class Identities

If 𝒦 is a class of structures, then it follows from `vclo-id1` that the set Th 𝒦 of identities modeled by all structures in 𝒦 is the same as the set Th VClo 𝒦 of identities modeled by all structures in VClo 𝒦.

-- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
class-identities : (p q : ∣ 𝑻 ∣)
       ---------------------------------------
 →       𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo))

class-identities p q = (λ α VCloA → vclo-id1{p}{q} α VCloA) ,  λ Thpq KA → Thpq (vbase KA)

### The free algebra in Agda

Recall that term algebra 𝑻(𝑋) is the absolutely free algebra in the class 𝓚(𝑆) of all 𝑆-structures. In this section, we
formalize, for a given class 𝒦 of 𝑆-algebras, the (relatively) free algebra in SP(𝒦) over 𝑋. Recall, this is defined as follows:

  𝔽(𝒦, 𝑋) := 𝑻(𝑋)/Ψ(𝒦, 𝑻(𝑋)).

Thus, we must first formalize the congruence Ψ(𝒦, 𝑻(𝑋)) which is defined by

  Ψ(𝒦, 𝑻(𝑋)) := ⋀ ψ(𝒦, 𝑻(𝑋)) := ⋀ {θ ∈ Con 𝑻(𝑋) : 𝑨/θ ∈ S(𝒦)}.

Strictly speaking, 𝑋 is not a subset of 𝔽(𝒦, 𝑋) so it doesn't make sense to say that "𝑋 generates 𝔽(𝒦, 𝑋)." But as long as 𝒦 contains a nontrivial algebra, we will have Ψ(𝒦, 𝑻(𝑋)) ∩ 𝑋² ≠ ∅, and we can identify 𝑋 with 𝑋/Ψ(𝒦, 𝑻(𝑋)) in 𝔽(𝒦, 𝑋).

\begin{code}
 𝑻HI = HomImagesOf (𝑻{𝓤}{X})

 𝑻img : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑻img = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
         Σ ϕ ꞉ hom (𝑻{𝓤}{X}) 𝑨 , (𝑨 ∈ SClo) × Epic ∣ ϕ ∣

 𝑻𝑨 : (ti : 𝑻img) → Algebra 𝓤 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 𝑻𝑨∈SClo𝒦 : (ti : 𝑻img) → (𝑻𝑨 ti) ∈ SClo
 𝑻𝑨∈SClo𝒦 ti = ∣ pr₂ ∥ ti ∥ ∣

 𝑻ϕ : (ti : 𝑻img) → hom 𝑻 (𝑻𝑨 ti)
 𝑻ϕ ti = pr₁ ∥ ti ∥

 𝑻ϕE : (ti : 𝑻img) → Epic ∣ (𝑻ϕ ti) ∣
 𝑻ϕE ti = ∥ pr₂ ∥ ti ∥ ∥

 𝑻KER : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑻KER = Σ (p , q) ꞉ (∣ 𝑻 ∣ × ∣ 𝑻 ∣) ,
    ∀ ti → (p , q) ∈ KER-pred{B = ∣ (𝑻𝑨 ti) ∣} ∣ 𝑻ϕ ti ∣

 Ψ : Pred (∣ 𝑻{𝓤}{X} ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Ψ (p , q) =
  ∀ ti → ∣ (𝑻ϕ ti) ∣ ∘ (p ̇ 𝑻) ≡ ∣ (𝑻ϕ ti) ∣ ∘ (q ̇ 𝑻)

 Ψ' : Pred (∣ 𝑻 ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
 Ψ' (p , q) = ∀ ti → ∣ (𝑻ϕ ti) ∣ p ≡ ∣ (𝑻ϕ ti) ∣ q
\end{code}

N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻), it suffices to show that the kernel of the lift h : 𝑻 → 𝑨 contains Ψ.

```
    𝑻---- g --->>𝔽  (ker g = Ψ)
     \         .
      \       .
       h     ∃ϕ     (want: Ψ ⊆ ker h)
        \   .
         \ .
          V
          𝑨
```

### More tools for Birkhoff's theorem

Here are some of the key facts and identities we need to complete the proof of Birkhoff's HSP theorem.

\begin{code}
 SClo𝒦→𝑻img : (𝑪 : Algebra 𝓤 𝑆) → 𝑪 ∈ SClo → 𝑻img

 SClo𝒦→𝑻img 𝑪 𝑪∈SClo𝒦 = 𝑪 , (fst (𝑻hom-gen 𝑪)) , (𝑪∈SClo𝒦 , (snd (𝑻hom-gen 𝑪)))

 𝑻img→𝑻⊧ : ∀ p q → (p , q) ∈ Ψ' → (ti : 𝑻img)
          ----------------------------------------------------
  →        ∣ (𝑻ϕ ti) ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ (𝑻ϕ ti) ∣ ((q ̇ 𝑻) ℊ)

 𝑻img→𝑻⊧ p q pΨq ti = goal1
  where
   𝑪 : Algebra 𝓤 𝑆
   𝑪 = ∣ ti ∣

   ϕ : hom 𝑻 𝑪
   ϕ = 𝑻ϕ ti

   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
   pCq = pΨq ti

   𝓅 𝓆 : ∣ 𝑻 ∣  -- Notation: 𝓅 = \Mcp
   𝓅 = ∣ tg p ∣
   𝓆 = ∣ tg q ∣

   p≡𝓅 : p ≡ (𝓅 ̇ 𝑻) ℊ
   p≡𝓅 = ∥ tg p ∥

   q≡𝓆 : q ≡ (𝓆 ̇ 𝑻) ℊ
   q≡𝓆 = ∥ tg q ∥

   ξ : ∣ ϕ ∣ ((𝓅 ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((𝓆 ̇ 𝑻) ℊ)
   ξ = (ap ∣ ϕ ∣ p≡𝓅)⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣ q≡𝓆)

   goal1 : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
   goal1 = (ap ∣ ϕ ∣ (term-gen-agreement p)) ∙ ξ ∙ (ap ∣ ϕ ∣ (term-gen-agreement q))⁻¹

 Ψ⊆ThSClo𝒦 : Ψ ⊆ (Th SClo)
 Ψ⊆ThSClo𝒦 {p , q} pΨq {𝑪} 𝑪∈SClo𝒦 = 𝑪⊧p≈q
  where
   ti : 𝑻img
   ti = SClo𝒦→𝑻img 𝑪 𝑪∈SClo𝒦

   ϕ : hom 𝑻 𝑪
   ϕ = 𝑻ϕ ti

   ϕE : Epic ∣ ϕ ∣
   ϕE = 𝑻ϕE ti

   ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
   ϕsur 𝒄 x = ϕE (𝒄 x)

   pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 ∣
   pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

   ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
   ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

   γ : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
   γ = pΨq ti

   𝑪⊧p≈q : (p ̇ 𝑪) ≡ (q ̇ 𝑪)

   𝑪⊧p≈q = gfe λ 𝒄 →
    (p ̇ 𝑪) 𝒄                ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
    (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))   ≡⟨ (comm-hom-term gfe 𝑻 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
    ∣ ϕ ∣ ((p ̇ 𝑻)(pre 𝒄))     ≡⟨ intensionality γ (pre 𝒄) ⟩
    ∣ ϕ ∣ ((q ̇ 𝑻)(pre 𝒄))     ≡⟨ comm-hom-term gfe 𝑻 𝑪 ϕ q (pre 𝒄) ⟩
    (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))   ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
    (q ̇ 𝑪) 𝒄                ∎

 Ψ⊆Th𝒦 : ∀ p q → (p , q) ∈ Ψ → 𝒦 ⊧ p ≋ q
 Ψ⊆Th𝒦 p q pΨq {𝑨} KA = Ψ⊆ThSClo𝒦{p , q} pΨq (sbase KA)
\end{code}

------------------------------------------------------------------------

### Unicode Hints 5

Table of some special characters used in the [closure module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/congruences.lagda.rst).

 |-----------|---------------------------|
 |  To get   |   Type                    |
 | ---       | ---                       | 
 |   𝒂, 𝒃    |        `\MIa`, `\MIb`     |
 |   𝑓 ̂ 𝑨   |           `\Mif \^ \MIA`  |
 |   ≅       |           `≅` or `\cong`  |
 |   ∘       |        `\comp` or `\circ` |
 |   𝒾𝒹      |        `\Mci\Mcd`         |
 |   ℒ𝒦     |        `\McL\McK`        |
 |   ϕ       |      `\phi`              |
 |-----------|--------------------------|

**Emacs commands providing information about special characters/input methods**:

+ `M-x describe-char` (or `M-m h d c`) with the cursor on the character of interest
+ `M-x describe-input-method` (or `C-h I`)


----------------------------------------------------------------------------

[<sub>Table of contents ⇑</sub>](ualib.html#contents)
## HSP Theorem in Agda

Here we give a formal proof in Agda of Birkhoff's theorem, which says that a variety is an equational class. In other words, if a class 𝒦 of algebras is closed under the operators 𝑯, 𝑺, 𝑷, then 𝒦 is an equational class (i.e., 𝒦 is the class of all algebras that model a particular set of identities).

In addition to the usual importing of dependencies, the [birkhoff module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/birkhoff.lagda.rst) begins with a fixed signature along with a few other components that will remain fixed throughout the module.

<!-- As in the `terms` module, `X` represents an arbitrary (infinite) collection of "variables" (which will serve as the generators of the term algebra 𝑻(X)). -->

\begin{code}
open basic
open congruences
open prelude using (global-dfunext; dfunext; funext; Pred)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

 open closure {𝑆 = 𝑆}{X = X}{𝒦 = 𝒦}{𝕏 = 𝕏}{gfe = gfe}{dfe = dfe}{fevu = fevu}
\end{code}

### Equalizers in Agda

The equalizer of two functions (resp., homomorphisms) `g h : A → B` is the subset of `A` on which the values of the functions `g` and `h` agree. We formalize this notion in Agda as follows.

\begin{code}
 --Equalizers of functions
 𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
 𝑬 g h x = g x ≡ h x

 --Equalizers of homomorphisms
 𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 𝑆} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
 𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x
\end{code}

It turns out that the equalizer of two homomorphisms is closed under the operations of `A` and is therefore a subalgebra of the common domain, as we now prove.

\begin{code}
 𝑬𝑯-is-closed : funext 𝓥 𝓤
  →     {𝑓 : ∣ 𝑆 ∣ } {𝑨 𝑩 : Algebra 𝓤 𝑆}
        (g h : hom 𝑨 𝑩)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
  →     ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
        --------------------------------------------------
  →      ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 p =
  (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂))    ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)     ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)     ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)      ∎
\end{code}
Thus, `𝑬𝑯` is a subuniverse of `A`.
\begin{code}
 𝑬𝑯-is-subuniverse : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}

 𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h = mksub (𝑬𝑯 {𝑨}{𝑩} g h) λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 x
\end{code}


### Homomorphism determination

The [homomorphisms module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/homomorphisms.lagda.rst) formalizes the notion of homomorphism and proves some basic facts about them. Here we show that homomorphisms are determined by their values on a generating set. This is proved here, and not in the [homomorphisms module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/homomorphisms.lagda.rst) because we need `Sg` from the `subuniverses` module.

\begin{code}
 HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
             (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
  →          (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
             ---------------------------------------------
  →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

 HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x

 HomUnique fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
   ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
   (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
   (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
   ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )    ∎
  where 
   induction-hypothesis = λ x → HomUnique fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )
\end{code}


### A formal proof of Birkhoff's theorem

Here's the statement we wish to prove:

```agda
 birkhoff : (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ Mod (Th VClo)
           ---------------------------------------
  →                      𝑨 ∈ VClo
```

Here's the partial proof:

```agda
 birkhoff 𝑨 A∈ModThV = 𝑨∈VClo
  where
   ℋ : X ↠ 𝑨
   ℋ = 𝕏 𝑨

   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst ℋ

   h : hom 𝑻 𝑨
   h = lift-hom{𝑨 = 𝑨} h₀

   Ψ⊆ThVClo : Ψ ⊆ Th VClo
   Ψ⊆ThVClo {p , q} pΨq =
    (lr-implication (class-identities p q)) (Ψ⊆Th𝒦 p q pΨq)

   Ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ Ψ → 𝑨 ⊧ p ≈ q
   Ψ⊆A⊧ {p} {q} pΨq = A∈ModThV p q (Ψ⊆ThVClo {p , q} pΨq)

   Ψ⊆Kerh : Ψ ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
   Ψ⊆Kerh {p , q} pΨq = hp≡hq
    where
     hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
     hp≡hq = hom-id-compatibility p q 𝑨 h (Ψ⊆A⊧{p}{q} pΨq)

   --We need to find 𝑪 : Algebra 𝒰 𝑆 such that 𝑪 ∈ VClo and ∃ ϕ : hom 𝑪 𝑨 with ϕE : Epic ∣ ϕ ∣.
   --Then we can prove 𝑨 ∈ VClo 𝒦 by vhom 𝑪∈VClo (𝑨 , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE))
   -- since vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦
   𝑪 : Algebra 𝓤 𝑆
   𝑪 = {!!}

   ϕ : Σ h ꞉ (hom 𝑪 𝑨) , Epic ∣ h ∣
   ϕ = {!!}

   hic : HomImagesOf 𝑪
   hic = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

   𝑨∈VClo : 𝑨 ∈ VClo
   𝑨∈VClo = vhom{𝑪} {!!} hic
```


------------------------------------------------------------------------

[UALib]: https://ualib.org
[Agda Universal Algebra Library]: https://github.com/UniversalAlgebra/agda-ualib/
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[emacs]: https://www.gnu.org/software/emacs/
[agda2-mode]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html
[Agda Standard Library]: https://agda.github.io/agda-stdlib/
[Agda Wiki]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Agda User's Manual]: https://agda.readthedocs.io/en/v2.6.1/
[Agda Language Reference]: https://agda.readthedocs.io/en/v2.6.1/language 
[Agda Standard Library]: https://agda.github.io/agda-stdlib/
[Agda Tools]: https://agda.readthedocs.io/en/v2.6.1/tools/
[Streicher's K axiom]: https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29
[section on axiom K]: https://agda.readthedocs.io/en/v2.6.1/language/without-k.html
[Type Topology]: https://github.com/martinescardo/TypeTopology
[HoTT-UF-in-Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
[Univalent Foundations and Homotopy Type Theory]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html)
[Relation/Binary/PropositionalEquality.agda]: https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html
[Relation/Binary/Core.agda]: https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.Core.html
