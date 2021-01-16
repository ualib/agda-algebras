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

<pre class="Agda">
<a id="341" class="Symbol">{-#</a> <a id="345" class="Keyword">OPTIONS</a> <a id="353" class="Pragma">--without-K</a> <a id="365" class="Pragma">--exact-split</a> <a id="379" class="Pragma">--safe</a> <a id="386" class="Symbol">#-}</a>
<a id="390" class="Keyword">module</a> <a id="397" href="UALib.Preface.html" class="Module">UALib.Preface</a> <a id="411" class="Keyword">where</a>
</pre>

To support formalization in type theory of research level mathematics in universal algebra and related fields, we present the [Agda Universal Algebra Library][] ([gitlab/ualib][] ), a library for the [Agda][] proof assistant which contains statements and proofs of many foundational definitions and results from universal algebra. In particular, the library includes formal statements and proofs the First (Noether) Isomorphism Theorem and the Birkhoff HSP Theorem asserting that every variety is an equational class.

[Agda][] is a programming language and proof assistant, or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful *proof tactics* for proving things about the objects that inhabit these types.

### <a id="vision-and-goals">Vision and Goals</a>

The idea for the [UALib][] project originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of type theory---in particular, [dependent types][] and [inductive types][]) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### <a id="primary-goals">Primary Goals</a>

The first goal of [UALib][] is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and possibly risky investment of time and resources.  However, we believe our subject is well served by a new, modern, [constructive](https://ncatlab.org/nlab/show/constructive+mathematics) presentation of its foundations.  Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

#### <a id="secondary-goals">Secondary Goals</a>

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our intermediate-term objectives include

+ developing domain specific "proof tactics" to express the idioms of universal algebra,
+ incorporating automated proof search for universal algebra, and
+ formalizing theorems emerging from our own mathematics research,
+ documenting the resulting software libraries so they are usable by other working mathematicians.

For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.

### <a id="intended-audience">Intended audience</a>

This document describes [UALib][] in enough detail so that working mathematicians (and possibly some normal people, too) might be able to learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying new mathematics.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, [Bergman (2012)][] or [McKenzie, McNulty, Taylor (1987)], and to a lesser extent category theory, as presented in [categorytheory.gitlab.io][] or [Riehl (2017)][].

Some prior exposure to [type theory][] and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to the appendix and glossary, while simultaneously consulting one or more of the references mentioned in the references section to fill in gaps as needed.

Finally, it is assumed that while reading these materials the reader is actively experimenting with Agda using [Emacs][] with its [agda2-mode][] extension installed. [Martin Escardo
Agda [2.6.0](https://agda.readthedocs.io/en/v2.6.0/getting-started/installation.html) is required. Consult Martin Escardo's [installation instructions](INSTALL.md) to help you set up Agda and Emacs.
nstructions for setting up Agda and emacs 

### <a id="installation">Installation</a>

The main repository for the [UAlib][] is [gitlab.com/ualib/ualib.gitlab.io][].

There are installation instructions in the main README.md file in that repository, but really all you need to do is have Agda (and [agda2-mode][] for Emacs) installed and then clone the [ualib/ualib.gitlab.io][] repository with, e.g.,

```shell
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
```

OR

```shell
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
```

If you don't have [Agda][] and [agda2-mode][] installed on your machine, follow the directions on [the main Agda website][] to install them.


<!--
### Unicode hints
At the end of each chapter of this documentation we show how to produce in Emacs agda2-mode_ some of the fancy unicode characters that we use in our code. For example, we might say "type ``\MCI`` to produce the symbol 𝓘".  We hope these occasional hints are convenient for the reader, but they are not meant to be comprehensive. Instead, information about unicode symbols is readily available in Emacs agda2-mode_; simply place the cursor on the character of interest and enter the command ``M-x describe-char``; alternatively, use the shortcut ``M-m h d c``. To see a full list of available characters, enter ``M-x describe-input-method`` (or ``C-h I``).
-->

### <a id="acknowledgments">Acknowledgments</a>

The author wishes to thank Siva Somayyajula, who contributed substantially to the launch of this project and helped get it off the ground.

Thanks also to Clifford Bergman, Venanzio Capretta, Andrej Bauer, Miklós Maróti, Peter Mayr and Ralph Freese, for helpful discussions, as well as instruction, advice, and encouragement that they continue to generously donate to the project, often without even knowing it.

#### <a id="attributions-and-citations">Attributions and citations</a>

William DeMeo is the primary developer of the [Agda Universal Algebra Library][].

Siva Somayyajula contributed to an early version of the library.

Regarding the mathematical results that are implemented in the [UAlib][], as well as the presentation and informal statements of these results in the documentation, the author of these web pages makes no claims to originality.

Regarding the Agda source code in the [UALib][], this is mainly due to the authors with one major caveat:

The [UALib][] has benefited enormously from the lecture notes on [Univalent Foundations and Homotopy Type Theory][] and the [Type Topology][] Agda Library, both by [Martin Hötzel Escardo][].  The first author is greatly indebted to Martin for teaching him about type theory in Agda at the [Midlands Graduate School in the Foundations of Computing Science][] in Birmingham in 2019.

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

----------------------------

### <a id="about-this-document">About this documentation</a>

These pages are generated from a set of [literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) Agda (.lagda) files, written in markdown, with the formal, verified, mathematical development appearing within `\\begin{code}...\\end{code}` blocks, and some mathematical discussions outside those blocks. The html pages are generated automatically by Agda with the command

`agda --html --html-highlight=code UALib.lagda`

This generates a set of markdown files that are then converted to html by jekyll with the command

`jekyll build`

[Issues][] or [merge requests][] contributing comments, bug fixes or other improvements are most welcomed.

* Submit a new [issue][] or [feature request][].
* Submit a new [merge request][].

-------------------------------------

[← Table of Contents](UALib.html)
<span style="float:right;">[UALib.Prelude →](UALib.Prelude.html)</span>


{% include UALib.Links.md %}
