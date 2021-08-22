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

## The Agda Universal Algebra Library

---------------------------------------------------------------------------------

(version 0.01 of {{ "now" | date: "%d %b %Y" }})

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

### Brief Contents

<pre class="Agda">

<a id="3455" class="Symbol">{-#</a> <a id="3459" class="Keyword">OPTIONS</a> <a id="3467" class="Pragma">--without-K</a> <a id="3479" class="Pragma">--exact-split</a> <a id="3493" class="Pragma">--safe</a> <a id="3500" class="Symbol">#-}</a>

<a id="3505" class="Keyword">module</a> <a id="3512" href="agda-algebras.html" class="Module">agda-algebras</a> <a id="3526" class="Keyword">where</a>

<a id="3533" class="Comment">-- Imports from Agda (builtin/primitive) and the Agda Standard Library</a>
<a id="3604" class="Keyword">open</a> <a id="3609" class="Keyword">import</a> <a id="3616" href="Preface.html" class="Module">Preface</a>
<a id="3624" class="Keyword">open</a> <a id="3629" class="Keyword">import</a> <a id="3636" href="Overture.html" class="Module">Overture</a>
<a id="3645" class="Keyword">open</a> <a id="3650" class="Keyword">import</a> <a id="3657" href="Relations.html" class="Module">Relations</a>
<a id="3667" class="Keyword">open</a> <a id="3672" class="Keyword">import</a> <a id="3679" href="Foundations.html" class="Module">Foundations</a>
<a id="3691" class="Keyword">open</a> <a id="3696" class="Keyword">import</a> <a id="3703" href="GaloisConnections.html" class="Module">GaloisConnections</a>
<a id="3721" class="Keyword">open</a> <a id="3726" class="Keyword">import</a> <a id="3733" href="ClosureSystems.html" class="Module">ClosureSystems</a>
<a id="3748" class="Keyword">open</a> <a id="3753" class="Keyword">import</a> <a id="3760" href="Algebras.html" class="Module">Algebras</a>
<a id="3769" class="Keyword">open</a> <a id="3774" class="Keyword">import</a> <a id="3781" href="Homomorphisms.html" class="Module">Homomorphisms</a>
<a id="3795" class="Keyword">open</a> <a id="3800" class="Keyword">import</a> <a id="3807" href="Terms.html" class="Module">Terms</a>
<a id="3813" class="Keyword">open</a> <a id="3818" class="Keyword">import</a> <a id="3825" href="Subalgebras.html" class="Module">Subalgebras</a>
<a id="3837" class="Keyword">open</a> <a id="3842" class="Keyword">import</a> <a id="3849" href="Varieties.html" class="Module">Varieties</a>
<a id="3859" class="Keyword">open</a> <a id="3864" class="Keyword">import</a> <a id="3871" href="Structures.html" class="Module">Structures</a>
<a id="3882" class="Keyword">open</a> <a id="3887" class="Keyword">import</a> <a id="3894" href="Complexity.html" class="Module">Complexity</a>

</pre>


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

