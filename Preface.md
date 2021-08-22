---
layout: default
title : Preface (The Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

## Preface

<pre class="Agda">

<a id="172" class="Symbol">{-#</a> <a id="176" class="Keyword">OPTIONS</a> <a id="184" class="Pragma">--without-K</a> <a id="196" class="Pragma">--exact-split</a> <a id="210" class="Pragma">--safe</a> <a id="217" class="Symbol">#-}</a>

<a id="222" class="Keyword">module</a> <a id="229" href="Preface.html" class="Module">Preface</a> <a id="237" class="Keyword">where</a>

</pre>

To support formalization in type theory of research level mathematics in universal algebra and related fields, we present the [Agda Universal Algebra Library](https://github.com/ualib/agda-algebras) (or [agda-algebras](https://github.com/ualib/agda-algebras) for short), a library for the [Agda][] proof assistant which contains definitions, theorems and proofs from the foundations of universal algebra. In particular, the library formalizes the First (Noether) Isomorphism Theorem and the Birkhoff HSP Theorem asserting that every variety is an equational class.

### Vision and Goals

The idea for the [agda-algebras][] project originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of type theory---in particular, [dependent types][] and [inductive types][]) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### Primary Goals

The first goal of [agda-algebras][] is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and a possibly risky investment of time and energy.  However, we believe our subject is well served by a new, modern, [constructive](https://ncatlab.org/nlab/show/constructive+mathematics) presentation of its foundations.  Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

#### Secondary Goals

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our long-term objectives include

+ domain specific types to express the idioms of universal algebra,
+ automated proof search for universal algebra, and
+ formalization of theorems discovered in our own (informal) mathematics research,
+ documentation of the resulting Agda library so it is usable by others.

For our own mathematics research, we believe a proof assistant like Agda, equipped with a specialized library for universal algebra is an extremely useful research tool. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such technologies for discovering new mathematics.

### Logical foundations

The [Agda UniversalAlgebra][] library is based on a minimal version of [Martin-Löf dependent type theory][] (MLTT) as implemented in Agda. More details on this type theory can be read at [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory).


### Intended audience

The comments and source code in the library should provide enough detail so that people familiar with functional programming and proof assistants can learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying mathematical theorems and proofs.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, [Bergman (2012)][] or [McKenzie, McNulty, Taylor (2018)], or category theory, as presented in, say, [Riehl (2017)][].

Some prior exposure to [type theory][] and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to one or more of the resources mentioned in the references section below to fill in gaps as needed.




### The Agda Algebras Development Team

The [agda-algebras][] library is developed and maintained by the *Agda Algebras Development Team* led by [William DeMeo][] with major contributions by senior advisor [Jacques Carette][] (McMaster University).



### Acknowledgements and attributions

We thank [Andreas Abel][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration and encouragement.

Most of the mathematical results formalized in the [agda-algebras][] are well known. Regarding the source code in the [agda-algebras][] library, this is mainly due to the contributors listed above.


### References

The following Agda documentation and tutorials helped inform and improve the [agda-algebras][] library, especially the first one in the list.

* Escardo, [Introduction to Univalent Foundations of Mathematics with Agda][]
* Wadler, [Programming Language Foundations in Agda][]
* Bove and Dybjer, [Dependent Types at Work][]
* Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
* Norell and Chapman, [Dependently Typed Programming in Agda][]

Finally, the official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the (open source) [Agda Standard Library][] source code are also quite useful.




### How to cite the Agda UniversalAlgebra

If you use the Agda UniversalAlgebra or wish to refer to it or its documentation in a publication or on a web page, please use the following BibTeX data:

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
Readers and users are encouraged to suggest improvements to the Agda [agda-algebras][] library and/or its documentation by submitting a [new issue][] or [merge request][] to [github.com/ualib/agda-algebras/](https://github.com/ualib/agda-algebras).

* Submit a new [issue][] or [feature request][].
* Submit a new [merge request][].

------------------------------------------------

{% include UALib.Links.md %}

[agda-algebras]: https://github.com/ualib/agda-algebras

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

