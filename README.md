# ualib.gitlab.io

(version 2.01 of {{ "now" | date: "%d %b %Y" }})

**Author**. [William DeMeo][]  
*Affiliation*. [Department of Algebra][], [Charles University in Prague][]

**PDF documentation**. [ualib-24Jan2021.pdf](ualib-24Jan2021.pdf)

**Abstract**. The [Agda Universal Algebra Library][] ([UALib][]) is a library of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in Martin-Löf type theory using the [Agda][] proof assistant language.

This is the main repository for the Agda UALib. Below are instructions for getting the UALib installed on your machine.  I hope that these steps work for you; they work on my Ubuntu 18.04 machine, but I haven't tested them on a fresh distro, or any other OS, so... 

...in any case, please [email me](mailto:williamdemeo@gmail.com) if you have trouble.

---------------------------

## Introduction

This repository contains the source code, as well as files that generate [documentation](https://ualib.gitlab.io/), for the [Agda Universal Algebra Library](https://gitlab.com/ualib/ualib.gitlab.io), aka [Agda UALib](https://gitlab.com/ualib/ualib.gitlab.io).

The docs are served at [ualib.org](https://ualib.gitlab.io/), and are automatically generated from the .lagda files using the script [generate-md](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/generate-md). See the section on [Generating the documentation](#generating-the-documentation) below.

-----------------------------

## Install Agda

Agda [2.6.1](https://agda.readthedocs.io/en/v2.6.1/getting-started/installation.html) is required. 

If you don't have Agda and agda2-mode installed, follow the [official installation instructions](https://agda.readthedocs.io/en/v2.6.0/getting-started/installation.html) or [Martin Escardo's installation instructions](INSTALL_AGDA.md) to help you set up Agda and Emacs.

-----------------------------

## Download the UALib

[Clone](https://docs.gitlab.com/ee/gitlab-basics/command-line-commands.html) the repository to your local machine using **ONE** of the following alternative commands:

``` sh
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
```

**OR**, if you have a gitlab account and have configured [ssh keys](https://docs.gitlab.com/ee/ssh/),


``` sh
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
```

This creates a directory on your local machine called `ualib.gitlab.io`. The UALib source code files reside in subdirectories of `ualib.gitlab.io/UALib` and have the `.lagda` extension.

Having installed Agda and cloned the `ualib.gitlab.io` repository, you should now be able to work with the source code contained in the .lagda files, such as UALib.lagda or any of it submodules. For example, you might start by loading the file [UALib/Prelude/Preliminaries.lagda](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/UALib/Prelude/Preliminaries.lagda) into Emacs and check that Agda can type-check that file using the command `C-c C-l`.

Other Emacs keybindings are described in the [emacs-mode.html#keybindings](https://agda.readthedocs.io/en/v2.6.1.1/tools/emacs-mode.html#keybindings) section of the [Agda docs](https://agda.readthedocs.io).

--------------------------------------------

## Generating the documentation

The html documentation pages are generated from the [literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) Agda (.lagda) files, written in markdown, with the formal, verified, mathematical development appearing within `\begin{code}...\end{code}` blocks, and some mathematical discussions outside those blocks.

The html pages are generated automatically by Agda with the command

```
agda --html --html-highlight=code UALib.lagda
```

This generates a set of markdown files that are then converted to html by jekyll with the command

```shell
bundle exec jekyll build
```

In practice, we use the script `generate-md`, to process the lagda files and put the resulting markdown output in the right place, and then using the script `jekyll-serve` to invoke the following commands

```
cp html/UALib.md index.md
cp html/*.html html/*.md .
bundle install --path vendor
bundle exec jekyll serve --watch --incremental
```

This causes jekyll to serve the web pages locally so we can inspect them by pointing a browser to [127.0.0.1:4000](http://127.0.0.1:4000).

--------------------------------


### Acknowledgements

A great source of information and inspiration for the Agda UALib is [Marin Escardo's lecture notes on HoTT/UF in Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html).

See also Martin's [HoTT/UF github repository](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes) and [Type Topology github repository](https://github.com/martinescardo/TypeTopology).

The author wishes to thank [Siva Somayyajula][], who contributed to this project during its first year and helped get it off the ground.

Thanks also to [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martin Escardo][], [Ralph Freese][], [Bill Lampe][], [Miklós Maróti][], [Peter Mayr][], [JB Nation][], and [Hyeyoung Shin][] for helpful discussions, instruction, advice, inspiration and encouragement.

#### <a id="attributions-and-citations">Attributions and citations</a>

Most of the mathematical results that formalized in the [UAlib][] are already well known.

Regarding the Agda source code in the [Agda UALib][], this is mainly due to the author with one major caveat: we benefited greatly from, and the library depends upon, the lecture notes on [Univalent Foundations and Homotopy Type Theory][] and the [Type Topology][] Agda Library by [Martin Hötzel Escardo][].  The author is indebted to Martin for making his library and notes available and for teaching a course on type theory in Agda at the [Midlands Graduate School in the Foundations of Computing Science][] in Birmingham in 2019.

-------------------------------

## Citing the UALib

If you use the Agda UALib or wish to refer to it or its documentation in a publication or on a web page, please use the following BibTeX data:

```bibtex
@article{DeMeo:2021,
 author        = {William DeMeo},
 title         = {The {A}gda {U}niversal {A}lgebra {L}ibrary and 
                  {B}irkhoff's {T}heorem in {M}artin-{L}\"of 
                  {D}ependent {T}ype {T}heory}, 
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
