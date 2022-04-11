---
layout: default
title : "Preface (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "the agda-algebras development team"
---

## <a id="preface">Preface</a>

<pre class="Agda">

<a id="198" class="Symbol">{-#</a> <a id="202" class="Keyword">OPTIONS</a> <a id="210" class="Pragma">--without-K</a> <a id="222" class="Pragma">--exact-split</a> <a id="236" class="Pragma">--safe</a> <a id="243" class="Symbol">#-}</a>

<a id="248" class="Keyword">module</a> <a id="255" href="Preface.html" class="Module">Preface</a> <a id="263" class="Keyword">where</a>

</pre>

To support formalization in type theory of research level mathematics in universal algebra and related fields, we present the [Agda Universal Algebra Library](https://github.com/ualib/agda-algebras) (or [agda-algebras](https://github.com/ualib/agda-algebras) for short), a library for the [Agda][] proof assistant which contains definitions, theorems and proofs from the foundations of universal algebra. In particular, the library formalizes the First (Noether) Isomorphism Theorem and the [Birkhoff HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) asserting that every variety is an equational class.

### <a id="vision-and-goals">Vision and goals</a>

The idea for the [agda-algebras](https://github.com/ualib/agda-algebras) project originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of type theory---in particular, [dependent types][] and [inductive types][]) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### <a id="primary-goals">Primary goals</a>

The first goal of [agda-algebras](https://github.com/ualib/agda-algebras) is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and a possibly risky investment of time and energy.  However, we believe our subject is well served by a new, modern, [constructive](https://ncatlab.org/nlab/show/constructive+mathematics) presentation of its foundations.  Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

#### <a id="secondary-goals">Secondary goals</a>

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our long-term objectives include

+ domain specific types to express the idioms of universal algebra,
+ automated proof search for universal algebra, and
+ formalization of theorems discovered in our own (informal) mathematics research,
+ documentation of the resulting Agda library so it is usable by others.

For our own mathematics research, we believe a proof assistant like Agda, equipped with a specialized library for universal algebra is an extremely useful research tool. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such technologies for discovering new mathematics.

### <a id="logical-foundations">Logical foundations</a>

The [Agda Universal Algebra Library][] is based on a minimal version of [Martin-Löf dependent type theory][] (MLTT) as implemented in Agda. More details on this type theory can be read at [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory).


### <a id="intended-audience">Intended audience</a>

The comments and source code in the library should provide enough detail so that people familiar with functional programming and proof assistants can learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying mathematical theorems and proofs.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, [Bergman (2012)][] or [McKenzie, McNulty, Taylor (2018)], or category theory, as presented in, say, [Riehl (2017)][].

Some prior exposure to [type theory][] and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to one or more of the resources mentioned in the references section below to fill in gaps as needed.


### <a id="attributions">Attributions</a>

#### <a id="the-agda-algebras-development-team">The agda-algebras development team</a>

The [agda-algebras](https://github.com/ualib/agda-algebras) library is developed and maintained by the *Agda Algebras Development Team* led by [William DeMeo][] with major contributions by senior advisor [Jacques Carette][] (McMaster University).

#### <a id="Acknowledgements">Acknowledgements</a>

We thank [Andreas Abel][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration and encouragement.

Most of the mathematical results formalized in the [agda-algebras](https://github.com/ualib/agda-algebras) are well known. Regarding the source code in the [agda-algebras](https://github.com/ualib/agda-algebras) library, this is mainly due to the contributors listed above.


#### <a id="references">References</a>

The following Agda documentation and tutorials helped inform and improve the [agda-algebras](https://github.com/ualib/agda-algebras) library, especially the first one in the list.

* Escardo, [Introduction to Univalent Foundations of Mathematics with Agda][]
* Wadler, [Programming Language Foundations in Agda][]
* Bove and Dybjer, [Dependent Types at Work][]
* Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
* Norell and Chapman, [Dependently Typed Programming in Agda][]

Finally, the official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the (open source) [Agda Standard Library][] source code are also quite useful.


#### <a id="citing-the-agda-algebras-library">Citing the agda-algebras library</a>

If you find the [agda-algebras](https://github.com/ualib/agda-algebras) library useful, please cite it using the following BibTeX entry:

```bibtex
@misc{ualib_v2.0.1,
  author       = {De{M}eo, William and Carette, Jacques},
  title        = {{T}he {A}gda {U}niversal {A}lgebra {L}ibrary (agda-algebras)},
  year         = 2021,
  note         = {{D}ocumentation available at https://ualib.org},
  version      = {2.0.1},
  doi          = {10.5281/zenodo.5765793},
  howpublished = {{G}it{H}ub.com},
  note         = {{V}er.~2.0.1; source code: \href{https://zenodo.org/record/5765793/files/ualib/agda-algebras-v.2.0.1.zip?download=1}{agda-algebras-v.2.0.1.zip}, {G}it{H}ub repo: \href{https://github.com/ualib/agda-algebras}{github.com/ualib/agda-algebras}},
}
```

#### <a id="citing-our-formalization-of-the-Birkhoff-theorem">Citing our formalization of the Birkhoff Theorem </a>

To cite the [formalization of Birkhoff's HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem), please use the following BibTeX entry:

```bibtex
@article{DeMeo:2021,
 author        = {De{M}eo, William and Carette, Jacques},
 title         = {A {M}achine-checked {P}roof of {B}irkhoff's {V}ariety {T}heorem
                  in {M}artin-{L}\"of {T}ype {T}heory}, 
 journal       = {CoRR},
 volume        = {abs/2101.10166},
 year          = {2021},
 eprint        = {2101.2101.10166},
 archivePrefix = {arXiv},
 primaryClass  = {cs.LO},
 url           = {https://arxiv.org/abs/2101.10166}
 note          = {Source code: \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}}
}
```

[![DOI](https://zenodo.org/badge/360493064.svg)](https://zenodo.org/badge/latestdoi/360493064)



#### <a id="contributions-welcomed">Contributions welcomed</a>

Readers and users are encouraged to suggest improvements to the Agda [agda-algebras](https://github.com/ualib/agda-algebras) library and/or its documentation by submitting a [new issue](https://github.com/ualib/agda-algebras/issues/new/choose) or [merge request](https://github.com/ualib/agda-algebras/compare) to [github.com/ualib/agda-algebras/](https://github.com/ualib/agda-algebras).


------------------------------------------------

<span style="float:left;">[↑ agda-algebras](agda-algebras.html)</span>
<span style="float:right;">[Base →](Base.html)</span>

{% include UALib.Links.md %}
