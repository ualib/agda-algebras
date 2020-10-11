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

# <a id="ualib">The Agda Universal Algebra Library (UALib)</a>

10 Oct 2020, version of {{ "now" | date: "%d %B %Y, %H:%M" }}.

[William DeMeo](https://williamdemeo.gitlab.io)

## Preface

To support formalization in type theory of research level mathematics in universal algebra and related fields, we are developing a software library, called the [Agda Universal Algebra Library](https://github.com/UniversalAlgebra/agda-ualib/) ([agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) ). Our library contains formal statements and proofs of some of the core, foundational definitions and results universal algebra and is written in [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).

[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) is a programming language and [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant), or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful *proof tactics* for proving things about the objects that inhabit these types.

### Vision and Goals

The idea for the the Agda Universal Algebra Library ([UALib](https://gitlab.com/ualib/ualib.gitlab.io)) originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of [type theory](https://en.wikipedia.org/wiki/Type_theory) ---in particular, [dependent types](https://en.wikipedia.org/wiki/Dependent_type) and [inductive types](https://en.wikipedia.org/wiki/Intuitionistic_type_theory#Inductive_types)) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### Primary Goals

The first goal of the [UALib][] project is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical
research depends, and demonstrate that our research can also be
expressed in type theory and formally implemented in such a way that we
and other working mathematicians can understand and verify the results.
The resulting library will also serve to educate our peers, and
encourage and help them to formally verify their own mathematics
research.

Our field is deep and wide and codifying all of its foundations may seem
like a daunting task and possibly risky investment of time and
resources. However, we believe our subject is well served by a new,
modern, [constructive](constructive%20mathematics) presentation of its
foundations. Our new presentation expresses the foundations of universal
algebra in the language of type theory, and uses the Agda proof
assistant to codify and formally verify everything.

#### Secondary Goals

We wish to emphasize that our ultimate objective is not merely to
translate existing results into a more modern and formal language.
Indeed, one important goal is to develop a system that is useful for
conducting research in mathematics, and that is how we intend to use our
library once we have achieved our immediate objective of implementing
the basic foundational core of universal algebra in Agda.

To this end, our intermediate-term objectives include

-   developing domain specific "proof tactics" to express the idioms of universal algebra,
-   incorporating automated proof search for universal algebra, and
-   formalizing theorems emerging from our own mathematics research,
-   documenting the resulting software libraries so they are usable by
    other working mathematicians.

For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.

### Intended audience

This document describes the Agda Universal Algebra Library
([agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io)) in enough
detail so that working mathematicians (and possibly some normal people,
too) might be able to learn enough about Agda and its libraries to put
them to use when creating, formalizing, and verifying new mathematics.

While there are no strict prerequisites, we expect anyone with an
interest in this work will have been motivated by prior exposure to
universal algebra, as presented in, say, Bergman:2012 or McKenzie:1987,
and to a lesser extent category theory, as presented in
[categorytheory.gitlab.io](https://categorytheory.gitlab.io) or
Riehl:2017.

Some prior exposure to [type
theory](https://en.wikipedia.org/wiki/Type_theory) and Agda would be
helpful, but even without this background one might still be able to get
something useful out of this by referring to the appendix and glossary,
while simultaneously consulting one or more of the references mentioned
in references to fill in gaps as needed.

Finally, it is assumed that while reading these materials the reader is
actively experimenting with Agda using
[emacs](https://www.gnu.org/software/emacs/) with its
[agda2-mode](https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html)
extension installed.

### Installing the library

The main repository for the
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) is
<https://gitlab.com/ualib/ualib.gitlab.io> (which will become publicly
available again in the summer of 2020).

There are installation instructions in the main README.md file in that
repository, but really all you need to do is have a working Agda (and
agda2-mode) installation and clone the
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) repository with,
e.g.,

``` {.sourceCode .bash}
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
```

OR

``` {.sourceCode .bash}
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
```

(We assume you have
[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) and
[agda2-mode](https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html)
installed on your machine. If not, follow the directions on [the main
Agda website](Agda) to install them.)


### Unicode hints

At the end of each chapter of this documentation we show how to produce
in Emacs
[agda2-mode](https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html)
some of the fancy unicode characters that we use in our code. For
example, we might say "type `\MCI` to produce the symbol 𝓘". We hope
these occasional hints are convenient for the reader, but they are not
meant to be comprehensive. Instead, information about unicode symbols is
readily available in Emacs
[agda2-mode](https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html);
simply place the cursor on the character of interest and enter the
command `M-x describe-char`; alternatively, use the shortcut
`M-m h d c`. To see a full list of available characters, enter
`M-x describe-input-method` (or `C-h I`).

### Acknowledgments

Besides the main authors and developers of
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) (William DeMeo
and Siva Somayyajula), a number of other people have contributed to the
project in one way or another.

Special thanks go to [Clifford Bergman](https://orion.math.iastate.edu/cbergman/), [Venanzio Capretta](https://www.duplavis.com/venanzio/), [Andrej Bauer](http://www.andrej.com/index.html), [Miklós Maróti](http://www.math.u-szeged.hu/~mmaroti/), and [Ralph Freese](https://math.hawaii.edu/~ralph/), for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project, often without even knowing it.

The first author would also like to thank his postdoctoral advisors and
their institutions for supporting (sometimes without their knowledge)
work on this project. These include [Libor
Barto](http://www.karlin.mff.cuni.cz/~barto/) and Charles University in
Prague (Nov 2019--Jun 2021), [Peter
Mayr](http://math.colorado.edu/~mayr/) and University of Colorado in
Boulder (Aug 2017--May 2019), [Ralph
Freese](https://math.hawaii.edu/~ralph/) and the University of Hawaii in
Honolulu (Aug 2016--May 2017), [Cliff
Bergman](https://orion.math.iastate.edu/cbergman/) and Iowa State
University in Ames (Aug 2014--May 2016).

### Attributions and citations

William DeMeo and Siva Somayyajula (hereinafter, "The Authors") are the
developers of the [Agda Universal Algebra
Library](https://github.com/UniversalAlgebra/agda-ualib/)
([agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io)).

Regarding the mathematical results that are implemented in the
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) library, as well
as the presentation and informal statements of these results in the
documentation, The Authors makes no claims to originality.

Regarding the Agda source code in the
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) library, this is
mainly due to The Authors.

HOWEVER, we have benefited from the outstanding lecture notes on
[Univalent Foundations and Homotopy Type
Theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes)
and the [Type
Topology](%3Chttps://github.com/martinescardo/TypeTopology%3E%60_) Agda
Library, both by [Martin Hötzel
Escardo](https://www.cs.bham.ac.uk/~mhe). The first author is greatly
indebted to Martin for teaching him about type theory in Agda at the
[Midlands Graduate School in the Foundations of Computing
Science](http://events.cs.bham.ac.uk/mgs2019/) in Birmingham in 2019.

The development of the
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io) and its
documentation is informed by and benefits from the references listed in
the references section below.


### References

The following Agda documentation and tutorials are excellent. They have
been quite helpful to The Author of
[agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io), and have
informed the development of the latter and its documentation.

-   Altenkirk, [Computer Aided Formal
    Reasoning](http://www.cs.nott.ac.uk/~psztxa/g53cfr/)
-   Bove and Dybjer, [Dependent Types at
    Work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)
-   Escardo, [Introduction to Univalent Foundations of Mathematics with
    Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html)
-   Gunther, Gadea, Pagano, [Formalization of Universal Algebra in
    Agda](http://www.sciencedirect.com/science/article/pii/S1571066118300768)
-   János, [Agda
    Tutorial](https://people.inf.elte.hu/pgj/agda/tutorial/Index.html)
-   Norell and Chapman, [Dependently Typed Programming in
    Agda](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf)
-   Wadler, [Programming Language Foundations in
    Agda](https://plfa.github.io/)

Finally, the official [Agda
Wiki](https://wiki.portal.chalmers.se/agda/pmwiki.php), [Agda User's
Manual](https://agda.readthedocs.io/en/v2.6.1/), [Agda Language
Reference](https://agda.readthedocs.io/en/v2.6.1/language), and the
(open source) [Agda Standard
Library](https://agda.github.io/agda-stdlib/) source code are also quite
useful.

------------------------------------------------------------------------

## Agda Preliminaries

This chapter describes the [prelude
module](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/prelude.lagda.rst)
of the [agda-ualib](https://gitlab.com/ualib/ualib.gitlab.io). The
source code for this module comprises the (literate)
[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) program that was
used to generate the html page displaying the sentence you are now
reading. This source code inhabits the file
[prelude.lagda.rst](prelude%20module), which resides in the [git
repository of the agda-ualib](agda-ualib).

**Notation**. Here are some acronyms that we use frequently.

-   MHE = [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe/)
-   MLTT = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

------------------------------------------------------------------------

Options and imports
-------------------

All but the most trivial Agda programs begin by setting some options
that effect how Agda behaves and importing from existing libraries
(e.g., the [Agda Standard Library](https://agda.github.io/agda-stdlib/)
or, in our case, MHE's [Type
Topology](%3Chttps://github.com/martinescardo/TypeTopology%3E%60_)
library). In particular, logical axioms and deduction rules can be
specified according to what one wishes to assume.

For example, we begin our agda development with the line

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module ualib where
\end{code}

This specifies Agda `OPTIONS` that we will use throughout the library.

- `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29);
  see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html)
  in the [Agda Language Reference](https://agda.readthedocs.io/en/v2.6.1/language) manual.
- `exact-split` makes Agda accept only those definitions that behave
  like so-called *judgmental* or *definitional* equalities. MHE
  explains this by saying it "makes sure that pattern matching
  corresponds to Martin-Löf eliminators;" see also the [Pattern
  matching and equality
  section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality)
  of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1/tools/)
  documentation.
- `safe` ensures that nothing is postulated outright---every
  non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module);
  see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe)
  of the [Agda Tools](https://agda.readthedocs.io/en/v2.6.1/tools/) documentation and the
  [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda)
  of the [Agda Language Reference](https://agda.readthedocs.io/en/v2.6.1/language).

### Universes

We import the `Universes` module from MHE's [Type Topology](%3Chttps://github.com/martinescardo/TypeTopology%3E%60_)
library.

\begin{code}
open import Universes public
\end{code}

This `Universes` module provides, among other things, an elegant notation for type universes that we have fully adopted and we use MHE's notation throughout the [UALib](https://gitlab.com/ualib/ualib.gitlab.io).

MHE has authored an outstanding set of notes on [HoTT-UF-in-Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) called [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html). We highly recommend these notes to anyone wanting more details than we provide here about MLTT and the Univalent Foundations/HoTT extensions thereof.

Following MHE, we refer to universes using capitalized script letters 𝓤,𝓥,𝓦,𝓣. We add a few more to Martin's list.

\begin{code}
variable 𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓞 𝓠 𝓡 𝓢 𝓧 : Universe
\end{code}

In the `Universes` module, MHE defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in [Lean](https://leanprover.github.io/)).

Although it is nice and short, we won't show all of the `Universes` module here. Instead, we highlight the few lines of code from MHE's `Universes.lagda` file that makes available the notational devices that we just described and will adopt throughout the [UALib](https://gitlab.com/ualib/ualib.gitlab.io).

Thus, 𝓤 ̇ is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`.

Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which (MHE and) we denote by `𝓤₀ ⁺ ̇`.

The following dictionary translates between standard Agda syntax and MHE/[UALib](https://gitlab.com/ualib/ualib.gitlab.io) notation.

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

To justify the introduction of this somewhat nonstandard notation for
universe levels, MHE points out that the Agda library uses `Level` for
universes (so what we write as 𝓤 ̇ is written `Set 𝓤` in standard Agda),
but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the
standard Agda notation can be misleading. Furthermore, the standard
notation places emphasis on levels rather than universes themselves.

There will be many occasions calling for a type living in the universe
that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The
universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound. Here 𝓤 ⊔ 𝓥 is used to
denote the universe level corresponding to the least upper bound of the
levels 𝓤 and 𝓥, where the `_⊔_` is an Agda primitive designed for
precisely this purpose.

### Public imports

Next we import other parts of MHE's [Type
Topology](%3Chttps://github.com/martinescardo/TypeTopology%3E%60_)
library, using the Agda directive `public`, which means these imports
will be available wherever the `prelude` module in imported. We describe
some of these imports later, when making use of them, but we don't
describe each one in detail. (The interested or confused reader should
consult
[HoTT-UF-in-Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html)
to learn more.)

\begin{code}
open import Identity-Type renaming (_≡_ to infix 0 _≡_ ;
 refl to 𝓇ℯ𝒻𝓁) public

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

------------------------------------------------------------------------

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

------------------------------------------------------------------------

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

------------------------------------------------------------------------

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

Here is a related tool that we borrow from the `Relation/Binary/Core.agda` module of the [Agda standard library](https://agda.github.io/agda-stdlib/).

\begin{code}
cong-app : {A : 𝓤 ̇}{B : A → 𝓦 ̇}{f g : (a : A) → B a}
 →          f ≡ g   →   (a : A)
          -----------------------
 →              f a ≡ g a

cong-app (refl _) a = refl _
\end{code}

------------------------------------------------------------------------

### Function extensionality

Extensional equality of functions, or function extensionality, means
that any two point-wise equal functions are equal. As MHE points out,
this is known to be not provable or disprovable in Martin-Löf Type
Theory (MLTT).

Nonetheless, we will mainly work with pointwise equality of functions,
which MHE defines (in [Type
Topology](%3Chttps://github.com/martinescardo/TypeTopology%3E%60_) ) as
follows:

```agda
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇ 
f ∼ g = ∀ x → f x ≡ g x
infix 0 _∼_
```

(The `_∼_` relation will be equivalent to equality of functions, once we
have the principle of *univalence* at our disposal.)

------------------------------------------------------------------------

### Predicates, Subsets

We need a mechanism for implementing the notion of subsets in Agda. A
typical one is called `Pred` (for predicate). More generally, `Pred A 𝓤`
can be viewed as the type of a property that elements of type `A` might
satisfy. We write `P : Pred A 𝓤` (read "`P` has type `Pred A 𝓤`") to
represent the subset of elements of `A` that satisfy property `P`.

Here is the definition (which is similar to the one found in the
`Relation/Unary.agda` file of [Agda standard
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

----------------------------------------------

### Subset relations and operations

The subset relation is then denoted, as usual, with the `⊆` symbol (cf.
`Relation/Unary.agda` in the [Agda standard
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

------------------------------------------------------------------------

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

------------------------------------------------------------------------

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


[UALib]: https://ualib.org
[Agda Universal Algebra Library](https://github.com/UniversalAlgebra/agda-ualib/)
