---
layout: title-page
title : The Agda Universal Algebra Library
date : 2021-01-14
author: William DeMeo
---

[The Agda Universal Algebra Library](UniversalAlgebra.html)

LICENSE:

The software in this file is subject to the GNU General Public License v3.0.

See the LICENSE file at https://gitlhub.com/ualib/agda-universal-algebra/-/blob/master/LICENSE

The text other than software is copyright of the author. It can be
used for scholarly purposes subject to the usual academic conventions
of citation.

* The *.lagda files are not meant to be read by people, but rather to be
  type-checked by the Agda proof assistant and to automatically generate html files
  (which are meant to be read by people).

* This is done with the generatehtml file to generate markdown and html files from the
  literate Agda (.lagda) files, and then using jekyll to convert markdown into html.

-->

## <a id="ualib">The Agda Universal Algebra Library</a>

---------------------------------------------------------------------------------

(version 2.03 of {{ "now" | date: "%d %b %Y" }})

**Abstract**. The [Agda UniversalAlgebra][] library is a collection of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda][] proof assistant language.

In the latest version of the library we have defined many new types for representing the important constructs and theorems that comprise part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files, with the `.lagda` extension, and they are grouped into modules so that they may be easily imported into other Agda programs.

To give an idea of the current scope of the library, we note that it now includes a complete proof of the [Birkhoff HSP Theorem](Birkhoff.HSPTheorem.html) which asserts that every variety is an equational class.  That is, if 𝒦 is a class of algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then 𝒦 is the class of algebras satisfying some set of identities. To our knowledge, ours is the first formal, constructive, machine-checked proof of Birkhoff's Theorem.<sup>[1](UniversalAlgebra.html#fn1)</sup>

We hope the library will be useful to mathematicians and computer scientists who wish to formally develop their work in type theory and verify their results with a proof assistant. Indeed, the [Agda UniversalAlgebra][] library is (or wants to be when it grows up) an indispensable guide on our mathematical journey, helping us forge new paths to higher peaks, all the time verifying and authenticating what we think we found along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [https://gitlab.com/ualib/ualib.gitlab.io.git](https://gitlab.com/ualib/ualib.gitlab.io.git)

**PDF documentation**. [ualib-part1.pdf](ualib-part1.pdf), [ualib-part2.pdf](ualib-part2.pdf) (ualib-part3.pdf coming soon)

**Citing this work**. To learn [how to cite the Agda UALib](Preface.html#how-to-cite-the-agda-ualib) and its documentation, follow [this link](Preface.html#how-to-cite-the-agda-ualib).

**Contributors**. William DeMeo, Jacques Carette, Venanzio Capretta, Siva Somayyajula, Andreas Abel, Hyeyoung Shin.

--------------------------------

### <a id="brief-contents"></a> Brief Contents

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UniversalAlgebra where

-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Preface
open import Overture
open import Relations
open import Algebras
open import Homomorphisms
open import Terms
open import Subalgebras
open import Varieties

\end{code}

-------------------------------------------

### <a id="detailed-contents"></a> Detailed Contents

- [Preface][]

- [Overture](Overture.html)
  - [Preliminaries](Overture.Preliminaries.html)
  - [Inverses](Overture.Inverses.html)

- [Relation and Quotient Types](Relations.html)
  - [Discrete Relations](Relations.Discrete.html)
  - [Continuous Relations](Relations.Continuous.html)
  - [Quotients](Relations.Quotients.html)
  - [Truncation](Relations.Truncation.html)
  - [Relation Extensionality](Relations.Extensionality.html)

- [Algebra Types](Algebras.html)
  - [Basic Definitions](Algebras.Basic.html)
  - [Product Algebras](Algebras.Products.html)
  - [Congruence Relations](Algebras.Congruences.html)

- [Homomorphism Types](Homomorphisms.html)
  - [Basic Definitions](Homomorphisms.Basic.html)
  - [Homomorphism Theorems](Homomorphisms.Noether.html)
  - [Isomorphisms](Homomorphisms.Isomorphisms.html)
  - [Homomorphic Images](Homomorphisms.HomomorphicImages.html)

- [Types for Terms](Terms.html)
  - [Basic Definitions](Terms.Basic.html)
  - [Term Operations](Terms.Operations.html)

- [Subalgebra Types](Subalgebras.html)
  - [Subuniverses](Subalgebras.Subuniverses.html)
  - [Subalgebras](Subalgebras.Subalgebras)

- [Equations and Varieties](Varieties.html)
  - [Model Theory and Equational Logic](Varieties.EquationalLogic.html)
  - [The Inductive Types H, S, P, V](Varieties.Varieties.html)
  - [Equation Preservation Theorems](Varieties.Preservation.html)
  - [Free Algebras and Birkhoff's Theorem](Varieties.FreeAlgebras.html)

---------------------------------------

#### License and citations

<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
  <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="css/by-sa.svg" />
  <!-- <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png" /> -->
</a>
<span xmlns:dct="http://purl.org/dc/terms/" property="dct:title">
  The Agda Universal Algebra Library
</span> by
<a xmlns:cc="http://creativecommons.org/ns#" href="https://williamdemeo.gitlab.io/" property="cc:attributionName" rel="cc:attributionURL">
  William DeMeo
</a>
is licensed under a
<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
  Creative Commons Attribution-ShareAlike 4.0 International License.
</a>
<br />
<a href="https://ualib.gitlab.io/Preface.html#how-to-cite-the-agda-ualib">BibTeX citation information.</a>
<br />
<br />
<a href="https://stereotypeb.gitlab.io"><img alt="stereotypeb" style="border-width:0; float: left; padding:0px 5px 0px 0px;" width='70' src="css/stereotypeb-avatar.png" /></a>
Based on the work at
<a xmlns:dct="http://purl.org/dc/terms/" href="https://gitlab.com/ualib/ualib.gitlab.io" rel="dct:source">
  https://gitlab.com/ualib/ualib.gitlab.io.
</a>

<p></p>

---------------------------------

<span class="footnote" id="fn1"><sup>1</sup>[Contact the authors](mailto:williamdemeo@gmail.com) if you find any evidence that refutes this claim.</span>

<p></p>

<span style="float:right;">[Next Module (Preface) →](Preface.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}

