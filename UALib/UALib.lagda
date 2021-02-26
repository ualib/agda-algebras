---
layout: title-page
title : The Agda Universal Algebra Library (UAlib)
date : 2021-01-14
author: William DeMeo
---

<!--

FILE      : UALib.lagda
AUTHOR    : William DeMeo  <williamdemeo@gmail.com>
DATED     : 14 Jan 2021
UPDATED   : 15 Jan 2021
COPYRIGHT : (c) 2021 William DeMeo

[The Agda Universal Algebra Library](UALib.html)

LICENSE:

The software in this file is subject to the GNU General Public License v3.0.

See the LICENSE file at https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/LICENSE

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

**Author**. [William DeMeo][]  
**Affiliation**. [Department of Algebra][], [Charles University in Prague][]

**Abstract**. The [Agda Universal Algebra Library][] ([UALib][]) is a library of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda][] proof assistant language.

In the latest version of the library we have defined many new types for representing the important constructs and theorems that comprise part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files, with the `.lagda` extension, and they are grouped into modules so that they may be easily imported into other Agda programs.

To give an idea of the current scope of the library, we note that it now includes a complete proof of the [Birkhoff HSP Theorem](Birkhoff.HSPTheorem.html) which asserts that every variety is an equational class.  That is, if 𝒦 is a class of algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then 𝒦 is the class of algebras satisfying some set of identities. To our knowledge, ours is the first formal, constructive, machine-checked proof of Birkhoff's Theorem.<sup>[1](UALib.html#fn1)</sup>

We hope the library will be useful to mathematicians and computer scientists who wish to formally develop their work in type theory and verify their results with a proof assistant. Indeed, the [Agda UALib][] is (or wants to be when it grows up) an indispensable guide on our mathematical journey, helping us forge new paths to higher peaks, all the time verifying and authenticating what we think we found along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [https://gitlab.com/ualib/ualib.gitlab.io.git](https://gitlab.com/ualib/ualib.gitlab.io.git)

**PDF documentation**. [ualib-long.pdf](ualib-long.pdf), [ualib-short.pdf](ualib-short.pdf)

**Citing this work**. To learn [how to cite the Agda UALib](Preface.html#how-to-cite-the-agda-ualib) and its documentation, follow [this link](Preface.html#how-to-cite-the-agda-ualib).

--------------------------------

### <a id="brief-contents"></a> Brief Contents

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib where

open import Preface
open import Prelude
open import Relations
open import Algebras
open import Homomorphisms
open import Terms
open import Subalgebras
open import Varieties
open import Birkhoff

\end{code}

-------------------------------------------

### <a id="detailed-contents"></a> Detailed Contents

- [Preface](Preface.html)

- [Prelude](Prelude.html)
  - [Preliminaries](Prelude.Preliminaries.html)
  - [Equality](Prelude.Equality.html)
  - [Inverses](Prelude.Inverses.html)
  - [Extensionality](Prelude.Extensionality.html)
  - [Agda's Universe Hierarchy](Prelude.Lifts.html)

- [Relation and Quotient Types](Relations.html)
  - [Unary Relations](Relations.Unary.html)
  - [Binary Relations](Relations.Binary.html)
  - [Equivalence Relations and Quotients](Relations.Quotients.html)
  - [Truncation, Sets, and Propositions](Relations.Truncation.html)

- [Algebra Types](Algebras.html)
  - [Operations and Signatures](Algebras.Signatures.html)
  - [Algebras](Algebras.Algebras.html)
  - [Product Algebras](Algebras.Products.html)
  - [Congruence Relations](Algebras.Congruences.html)

- [Homomorphism Types](Homomorphisms.html)
  - [Basic definitions](Homomorphisms.Basic.html)
  - [Homomorphism Theorems](Homomorphisms.Noether.html)
  - [Isomorphisms](Homomorphisms.Isomorphisms.html)
  - [Homomorphic Images](Homomorphisms.HomomorphicImages.html)

- [Types for Terms](Terms.html)
  - [Basic Definitions](Terms.Basic.html)
  - [Term Operations](Terms.Operations.html)

- [Subalgebra Types](Subalgebras.html)
  - [Subuniverses](Subalgebras.Subuniverses.html)
  - [Subuniverse Generation](Subalgebras.Generation.html)
  - [Subalgebras](Subalgebras.Subalgebras)
  - [Univalent Subalgebras](Subalgebras.Univalent.html)

- [Types for Equations and Varieties](Varieties.html)
  - [Model Theory and Equational Logic](Varieties.EquationalLogic.html)
  - [The Inductive Types H, S, P, V](Varieties.Varieties.html)
  - [Equation Preservation Theorems](Varieties.Preservation.html)

- [The Free Algebra and Birkhoff's Theorem](Birkhoff.html)
  - [The Free Algebra](Birkhoff.FreeAlgebra.html)
  - [Birkhoff's Theorem](Birkhoff.HSPTheorem.html)

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

---------------------------------

<span class="footnote" id="fn1"><sup>1</sup>[Contact the author](mailto:williamdemeo@gmail.com) if you find any evidence that refutes this claim.</span>

<p></p>

<span style="float:right;">[Next Module (Preface) →](Preface.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}

