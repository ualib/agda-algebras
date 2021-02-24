---
layout: default
title : Preface (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

<!--
FILE      : Preface.lagda
AUTHOR    : William DeMeo  <williamdemeo@gmail.com>
DATED     : 17 May 2019
UPDATED   : 14 Jan 2021
COPYRIGHT : (c) 2021 William DeMeo
-->

## <a id="preface">Preface</a>

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

module Preface where

\end{code}

To support formalization in type theory of research level mathematics in universal algebra and related fields, we present the [Agda Universal Algebra Library][] ([gitlab/ualib][] ), a library for the [Agda][] proof assistant which contains statements and proofs of many foundational definitions and results from universal algebra. In particular, the library includes formal statements and proofs the First (Noether) Isomorphism Theorem and the Birkhoff HSP Theorem asserting that every variety is an equational class.

[Agda][] is a programming language and proof assistant, or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful *proof tactics* for proving things about the objects that inhabit these types.

### <a id="vision-and-goals">Vision and Goals</a>

The idea for the [UALib][] project originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of type theory---in particular, [dependent types][] and [inductive types][]) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### <a id="primary-goals">Primary Goals</a>

The first goal of [UALib][] is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and a possibly risky investment of time and energy.  However, we believe our subject is well served by a new, modern, [constructive](https://ncatlab.org/nlab/show/constructive+mathematics) presentation of its foundations.  Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

#### <a id="secondary-goals">Secondary Goals</a>

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our intermediate-term objectives include

+ developing domain specific "proof tactics" to express the idioms of universal algebra,
+ incorporating automated proof search for universal algebra, and
+ formalizing theorems emerging from our own mathematics research,
+ documenting the resulting software libraries so they are usable by other working mathematicians.

For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.




### <a id="Logical-foundations">Logical foundations</a>

The [Agda UALib][] is based on a minimal version of [Martin-Löf dependent type theory][] (MLTT) that is the same or very close to the type theory on which Martin Escardo's [Type Topology][] Agda library is based.  This is also the type theory that Escardo taught us in the short course [Introduction to Univalent Foundations of Mathematics with Agda][] at the [Midlands Graduate School in the Foundations of Computing Science][] at University of Birmingham in 2019.

We won't go into great detail here because there are already other very nice resources available, such as the section [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#mlttinagda) of the lecture notes by MHE just mentioned, as well as the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory).

We will have much more to say about types and type theory as we progress. For now, suffice it to recall the handfull of objects that are assumed at the jumping-off point for MLTT: "primitive" **types** (𝟘, 𝟙, and ℕ, denoting the empty type, one-element type, and natural numbers), **type formers** (+, Π, Σ, Id, denoting binary sum, product, sum, and the identity type), and an infinite collection of **universes** (types of types) and universe variables to denote them (for which we will use upper-case caligraphic letters like 𝓤, 𝓥, 𝓦, etc., typically from the latter half of the English alphabet).




### <a id="intended-audience">Intended audience</a>

This document describes [UALib][] in enough detail so that working mathematicians (and possibly some normal people, too) might be able to learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying new mathematics.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, [Bergman (2012)][] or [McKenzie, McNulty, Taylor (2018)], or category theory, as presented in, say, [Riehl (2017)][] or [categorytheory.gitlab.io][].

Some prior exposure to [type theory][] and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to one or more of the resources mentioned in the references section below to fill in gaps as needed.




### <a id="installation">Installation</a>

It is assumed that the reader of this documentation is actively experimenting with [Agda][] using [Emacs][] with the [agda2-mode][] extension installed.

If you don't have [Agda][] and [agda2-mode][] installed, follow the directions on [the main Agda website][], and/or consult [Martin Escardo's installation instructions](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/blob/master/INSTALL.md) or [our modified version of MHE's instructions](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/INSTALL_AGDA.md).

The main repository for the [UAlib][] is [gitlab.com/ualib/ualib.gitlab.io][]. There are more installation instructions in the [README.md](https://gitlab.com/ualib/ualib.gitlab.io/README.md) file of the [UALib repository](https://gitlab.com/ualib/ualib.gitlab.io), but a summary of what's required is

* [Emacs](https://www.gnu.org/software/emacs/)
* [Agda][] 2.6.1
* [agda2-mode][] (for emacs)
* A cloned copy of the [ualib/ualib.gitlab.io][] repository.

Instructions for installing each of these are available in the [README.md](https://gitlab.com/ualib/ualib.gitlab.io/README.md) file of the [UALib repository](https://gitlab.com/ualib/ualib.gitlab.io).

If you already have `git` installed, a cloned copy of [ualib/ualib.gitlab.io][] is obtained using **one** of the following alternative commands:

```shell
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
```

**or**, if you have a gitlab account with [ssh keys](https://docs.gitlab.com/ee/ssh/) configured, you could try

```shell
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
```




### <a id="about-this-document">About this documentation</a>

These pages are generated from a set of [literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) Agda (.lagda) files, written in markdown, with the formal, verified, mathematical development appearing within `\\begin{code}...\\end{code}` blocks, and some mathematical discussions outside those blocks. The html pages are generated automatically by Agda with the command

```
agda --html --html-highlight=code UALib.lagda
```

This generates a set of markdown files that are then converted to html by jekyll with the command

```shell
bundle exec jekyll build
```

In practice, we use the script `UALib/generate-md`, to process the lagda files and put the resulting markdown output in the right place, and then we use the script `jekyll-serve` to invoke the following commands.

```
cp UALib/html/UALib.md index.md
cp UALib/html/*.html UALib/html/*.md .
bundle install --path vendor
bundle exec jekyll serve --watch --incremental
```

This causes jekyll to serve the web pages locally so we can inspect them by pointing a browser to [127.0.0.1:4000](http://127.0.0.1:4000).

LaTeX source files may be generated with a combination of `agda --latex` and `pandoc` commands. This can only be done one module at a time, but the script `generate-tex` is set up to process all modules in the library.  Typically, after each update of the library, we run the following at the command line from within the UALib subdirectory:

```shell
./generate-tex; ./generate-md
```

This type-checks all the modules, and generates html and latex documentation (in the `UALib/html` and `UALib/latex` subdirectories).

**Warning!** Our `.lagda` source files make heavy use of unicode characters, both inside and outside code blocks. Therefore, the tex source files produced with the `agda --latex` command cannot be processed correctly with `pdflatex` (as far as we know). Instead, we use `xelatex` along with the `unixode` package. For examples, look in the subdirectories of the [_static/paper](https://gitlab.com/ualib/ualib.gitlab.io/-/tree/master/_static/paper) directory of the [ualib.gitlab.io](https://gitlab.com/ualib/ualib.gitlab.io`) repository.

**XeLaTeX and arXiv**. xelatex has the major advantage of correctly processing and formatting unicode characters, but it has the major disadvantage of not being compatible with arXiv, and it seems there are no plans to support `xelatex` in the near future.  However, one can email the arXiv administrators and explain that `xelatex` is required to process the manuscript and (in my experience, at least) this will prompt a reply with permission to submit a precompiled pdf without the accompanying tex source code.




### <a id="acknowledgments">Acknowledgments</a>

The author wishes to thank [Siva Somayyajula][], who contributed to this project during its first year and helped get it off the ground.

Thanks also to [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martin Escardo][], [Ralph Freese][], [Bill Lampe][], [Miklós Maróti][], [Peter Mayr][], [JB Nation][], and [Hyeyoung Shin][] for helpful discussions, instruction, advice, inspiration and encouragement.

#### <a id="attributions-and-citations">Attributions and citations</a>

Most of the mathematical results that formalized in the [UAlib][] are already well known.

Regarding the Agda source code in the [Agda UALib][], this is mainly due to the author with one major caveat: we benefited greatly from, and the library depends upon, the lecture notes on [Univalent Foundations and Homotopy Type Theory][] and the [Type Topology][] Agda Library by [Martin Hötzel Escardo][].  The author is indebted to Martin for making his library and notes available and for teaching a course on type theory in Agda at the [Midlands Graduate School in the Foundations of Computing Science][] in Birmingham in 2019.




### <a id="references">References</a>

The following Agda documentation and tutorials helped inform and improve the [UAlib][], especially the first one in the list.

* Escardo, [Introduction to Univalent Foundations of Mathematics with Agda][]
* Wadler, [Programming Language Foundations in Agda][]
* Altenkirk, [Computer Aided Formal Reasoning][]
* Bove and Dybjer, [Dependent Types at Work][]
* Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
* János, [Agda Tutorial][]
* Norell and Chapman, [Dependently Typed Programming in Agda][]

Finally, the official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the (open source) [Agda Standard Library][] source code are also quite useful.




### <a id="how-to-cite-the-agda-ualib">How to cite the Agda UALib</a>

If you use the Agda UALib or wish to refer to it or its documentation in a publication or on a web page, please use the following BibTeX data:

```bibtex
@article{DeMeo:2021,
 author        = {William DeMeo},
 title         = {The {A}gda {U}niversal {A}lgebra {L}ibrary and
                 {B}irkhoff's {T}heorem in {D}ependent {T}ype {T}heory},
 journal       = {CoRR},
 volume        = {abs/2101.10166},
 year          = {2021},
 eprint        = {2101.10166},
 archivePrefix = {arXiv},
 primaryClass  = {cs.LO},
 url           = {https://arxiv.org/abs/2101.10166},
 note          = {source code: \url{https://gitlab.com/ualib/ualib.gitlab.io}}
}
```

See also: [dblp record](https://dblp.uni-trier.de/rec/journals/corr/abs-2101-10166.html), [dblp BibTeX record](https://dblp.uni-trier.de/rec/journals/corr/abs-2101-10166.html?view=bibtex).


### <a id="contributions-welcomed">Contributions welcomed</a>
Readers and users are encouraged to suggest improvements to the Agda UALib and/or its documentation by submitting a [new issue][] or [merge request][] to [gitlab.com/ualib/ualib.gitlab.io/](https://gitlab.com/ualib/ualib.gitlab.io/).

* Submit a new [issue][] or [feature request][].
* Submit a new [merge request][].

------------------------------------------------

[↑ Agda UALib](UALib.html)
<span style="float:right;">[Prelude →](Prelude.html)</span>


{% include UALib.Links.md %}


