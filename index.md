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

(version 2.01 of {{ "now" | date: "%d %b %Y" }})

**Author**. [William DeMeo][]  
**Affiliation**. [Department of Algebra][], [Charles University in Prague][]

**Abstract**. The [Agda Universal Algebra Library][] ([UALib][]) is a library of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda][] proof assistant language.

In the latest version of the library we have defined many new types for representing the important constructs and theorems that comprise part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files, with the `.lagda` extension, and they are grouped into modules so that they may be easily imported into other Agda programs.

To give an idea of the current scope of the library, we note that it now includes a complete proof of the [Birkhoff HSP Theorem](UALib.Birkhoff.Theorem.html) which asserts that every variety is an equational class.  That is, if 𝒦 is a class of algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then 𝒦 is the class of algebras satisfying some set of identities. To our knowledge, ours is the first formal, constructive, machine-checked proof of Birkhoff's Theorem.<span class="footnote"><sup>1</sup></span>

We hope the library will be useful to mathematicians and computer scientists who wish to formally develop their work in type theory and verify their results with a proof assistant. Indeed, the [Agda UALib][] is (or wants to be when it grows up) an indispensable guide on our mathematical journey, helping us forge new paths to higher peaks, all the time verifying and authenticating what we think we found along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [https://gitlab.com/ualib/ualib.gitlab.io.git](https://gitlab.com/ualib/ualib.gitlab.io.git)

**PDF documentation**. [ualib-6Feb2021-arXiv.pdf](ualib-6Feb2021-arXiv.pdf), [ualib-short-6Feb2021.pdf](ualib-short-6Feb2021.pdf)

**Citing this work**. To learn [how to cite the Agda UALib]((UALib.Preface.html#how-to-cite-the-agda-ualib) and its documentation, follow [this link](UALib.Preface.html#how-to-cite-the-agda-ualib).

--------------------------------

### <a id="brief-contents"></a> Brief Contents

<pre class="Agda">

<a id="3663" class="Symbol">{-#</a> <a id="3667" class="Keyword">OPTIONS</a> <a id="3675" class="Pragma">--without-K</a> <a id="3687" class="Pragma">--exact-split</a> <a id="3701" class="Pragma">--safe</a> <a id="3708" class="Symbol">#-}</a>

<a id="3713" class="Keyword">module</a> <a id="3720" href="UALib.html" class="Module">UALib</a> <a id="3726" class="Keyword">where</a>

<a id="3733" class="Keyword">open</a> <a id="3738" class="Keyword">import</a> <a id="3745" href="UALib.Preface.html" class="Module">UALib.Preface</a>
<a id="3759" class="Keyword">open</a> <a id="3764" class="Keyword">import</a> <a id="3771" href="UALib.Prelude.html" class="Module">UALib.Prelude</a>
<a id="3785" class="Keyword">open</a> <a id="3790" class="Keyword">import</a> <a id="3797" href="UALib.Algebras.html" class="Module">UALib.Algebras</a>
<a id="3812" class="Keyword">open</a> <a id="3817" class="Keyword">import</a> <a id="3824" href="UALib.Relations.html" class="Module">UALib.Relations</a>
<a id="3840" class="Keyword">open</a> <a id="3845" class="Keyword">import</a> <a id="3852" href="UALib.Homomorphisms.html" class="Module">UALib.Homomorphisms</a>
<a id="3872" class="Keyword">open</a> <a id="3877" class="Keyword">import</a> <a id="3884" href="UALib.Terms.html" class="Module">UALib.Terms</a>
<a id="3896" class="Keyword">open</a> <a id="3901" class="Keyword">import</a> <a id="3908" href="UALib.Subalgebras.html" class="Module">UALib.Subalgebras</a>
<a id="3926" class="Keyword">open</a> <a id="3931" class="Keyword">import</a> <a id="3938" href="UALib.Varieties.html" class="Module">UALib.Varieties</a>
<a id="3954" class="Keyword">open</a> <a id="3959" class="Keyword">import</a> <a id="3966" href="UALib.Birkhoff.html" class="Module">UALib.Birkhoff</a>

</pre>

-------------------------------------------

### <a id="detailed-contents"></a> Detailed Contents

- [Preface](UALib.Preface.html)

- [Prelude](UALib.Prelude.html)
  - [Preliminaries](UALib.Prelude.Preliminaries.html)
  - [Equality](UALib.Prelude.Equality.html)
  - [Inverses](UALib.Prelude.Inverses.html)
  - [Extensionality](UALib.Prelude.Extensionality.html)

- [Algebras](UALib.Algebras.html)
  - [Operation and Signature Types](UALib.Algebras.Signatures.html)
  - [Algebra Types](UALib.Algebras.Algebras.html)
  - [Product Algebra Types](UALib.Algebras.Products.html)
  - [Agda's Universe Hierarchy](UALib.Algebras.Lifts.html)

- [Relations](UALib.Relations.html)
  - [Unary Relation Types](UALib.Relations.Unary.html)
  - [Binary Relation and Kernel Types](UALib.Relations.Binary.html)
  - [Equivalence Relation Types](UALib.Relations.Equivalences.html)
  - [Quotient Types](UALib.Relations.Quotients.html)
  - [Congruence Relation Types](UALib.Relations.Congruences.html)

- [Homomorphisms](UALib.Homomorphisms.html)
  - [Basic definitions](UALib.Homomorphisms.Basic.html)
  - [Kernels of Homomorphisms](UALib.Homomorphisms.Kernels.html)
  - [Homomorphism Theorems](UALib.Homomorphisms.Noether.html)
  - [Homomorphisms and Products](UALib.Homomorphisms.Products.html)
  - [Isomorphism Type](UALib.Homomorphisms.Isomorphisms.html)
  - [Homomorphic Image Types](UALib.Homomorphisms.HomomorphicImages.html)

- [Terms and Free Algebras](UALib.Terms.html)
  - [Basic Definitions](UALib.Terms.Basic.html)
  - [The Term Algebra](UALib.Terms.Free.html)
  - [Term Operation Types](UALib.Terms.Operations.html)
  - [Term Compatibility Theorems](UALib.Terms.Compatibility.html)

- [Subalgebras](UALib.Subalgebras.html)
  - [Subuniverse Types](UALib.Subalgebras.Subuniverses.html)
  - [Inductive Types for Subuniverse Generation](UALib.Subalgebras.Generation.html)
  - [Subuniverse Lemmas](UALib.Subalgebras.Properties.html)
  - [Subuniverses and Homomorphisms](UALib.Subalgebras.Homomorphisms.html)
  - [Subalgebra Types](UALib.Subalgebras.Subalgebras)
  - [WWMD](UALib.Subalgebras.WWMD.html)

- [Equations and Varieties](UALib.Varieties.html)
  - [Types for Theories and Models](UALib.Varieties.ModelTheory.html)
  - [Equational Logic Types](UALib.Varieties.EquationalLogic.html)
  - [Inductive Types H, S, P, V](UALib.Varieties.Varieties.html)
  - [Equation Preservation Theorems](UALib.Varieties.Preservation.html)

- [Birkhoff's Theorem](UALib.Birkhoff.html)
  - [The Relatively Free Algebra](UALib.Birkhoff.FreeAlgebra.html)
  - [HSP Lemmata](UALib.Birkhoff.Lemmata.html)
  - [HSP Theorem](UALib.Birkhoff.Theorem.html)

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
<br />
<img alt="stereotypeb" style="border-width:0; float: left; padding:0px 5px 0px 0px;" width='70' src="css/stereotypeb-avatar.png" />
Based on a work at
<a xmlns:dct="http://purl.org/dc/terms/" href="https://gitlab.com/ualib/ualib.gitlab.io" rel="dct:source">
  https://gitlab.com/ualib/ualib.gitlab.io
</a>.
<br />
<a href="https://ualib.gitlab.io/UALib.Preface.html#how-to-cite-the-agda-ualib">BibTeX citation information.</a>

---------------------------------

<span class="footnote"><sup>1</sup>[Contact the author](mailto:williamdemeo@gmail.com) if you find any evidence that refutes this claim.</span>

<p></p>

<span style="float:right;">[Next Module (UALib.Preface) →](UALib.Preface.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}

