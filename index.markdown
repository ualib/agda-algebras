---
layout: title-page
title : The Agda Universal Algebra Library
date : 2021-01-14
author: William DeMeo
---

<!--

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

(Version 2.01 of {{ "now" | date: "%d %b %Y" }})

**Abstract**. The [Agda UniversalAlgebra][] library is a collection of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda][] proof assistant language.

In the latest version of the library we have defined many new types for representing the important constructs and theorems that comprise part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files, with the `.lagda` extension, and they are grouped into modules so that they may be easily imported into other Agda programs.

To give an idea of the current scope of the library, we note that it now includes a complete proof of the [Birkhoff HSP Theorem](Birkhoff.HSPTheorem.html) which asserts that every variety is an equational class.  That is, if 𝒦 is a class of algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then 𝒦 is the class of algebras satisfying some set of identities. To our knowledge, ours is the first formal, constructive, machine-checked proof of Birkhoff's Theorem.<sup>[1](UniversalAlgebra.html#fn1)</sup>

We hope the library will be useful to mathematicians and computer scientists who wish to formally develop their work in type theory and verify their results with a proof assistant. Indeed, the [Agda UniversalAlgebra][] library is (or wants to be when it grows up) an indispensable guide on our mathematical journey, helping us forge new paths to higher peaks, all the time verifying and authenticating what we think we found along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [https://github.com/ualib/agda-algebras](https://gitub.com/ualib/agda-algebras)

**Citing this work**. To learn [how to cite the Agda UALib](Preface.html#how-to-cite-the-agda-ualib) and its documentation, follow [this link](Preface.html#how-to-cite-the-agda-ualib).

**Contributors**. William DeMeo, Jacques Carette, Siva Somayyajula, Andreas Abel, Hyeyoung Shin.

--------------------------------

### Brief Contents

<pre class="Agda">

<a id="3243" class="Symbol">{-#</a> <a id="3247" class="Keyword">OPTIONS</a> <a id="3255" class="Pragma">--without-K</a> <a id="3267" class="Pragma">--exact-split</a> <a id="3281" class="Pragma">--safe</a> <a id="3288" class="Symbol">#-}</a>

<a id="3293" class="Keyword">module</a> <a id="3300" href="agda-algebras.html" class="Module">agda-algebras</a> <a id="3314" class="Keyword">where</a>

<a id="3321" class="Comment">-- Imports from Agda (builtin/primitive) and the Agda Standard Library</a>
<a id="3392" class="Keyword">open</a> <a id="3397" class="Keyword">import</a> <a id="3404" href="Preface.html" class="Module">Preface</a>
<a id="3412" class="Keyword">open</a> <a id="3417" class="Keyword">import</a> <a id="3424" href="Overture.html" class="Module">Overture</a>
<a id="3433" class="Keyword">open</a> <a id="3438" class="Keyword">import</a> <a id="3445" href="Relations.html" class="Module">Relations</a>
<a id="3455" class="Keyword">open</a> <a id="3460" class="Keyword">import</a> <a id="3467" href="Foundations.html" class="Module">Foundations</a>
<a id="3479" class="Keyword">open</a> <a id="3484" class="Keyword">import</a> <a id="3491" href="GaloisConnections.html" class="Module">GaloisConnections</a>
<a id="3509" class="Keyword">open</a> <a id="3514" class="Keyword">import</a> <a id="3521" href="ClosureSystems.html" class="Module">ClosureSystems</a>
<a id="3536" class="Keyword">open</a> <a id="3541" class="Keyword">import</a> <a id="3548" href="Algebras.html" class="Module">Algebras</a>
<a id="3557" class="Keyword">open</a> <a id="3562" class="Keyword">import</a> <a id="3569" href="Homomorphisms.html" class="Module">Homomorphisms</a>
<a id="3583" class="Keyword">open</a> <a id="3588" class="Keyword">import</a> <a id="3595" href="Terms.html" class="Module">Terms</a>
<a id="3601" class="Keyword">open</a> <a id="3606" class="Keyword">import</a> <a id="3613" href="Subalgebras.html" class="Module">Subalgebras</a>
<a id="3625" class="Keyword">open</a> <a id="3630" class="Keyword">import</a> <a id="3637" href="Varieties.html" class="Module">Varieties</a>
<a id="3647" class="Keyword">open</a> <a id="3652" class="Keyword">import</a> <a id="3659" href="Structures.html" class="Module">Structures</a>
<a id="3670" class="Keyword">open</a> <a id="3675" class="Keyword">import</a> <a id="3682" href="Complexity.html" class="Module">Complexity</a>

</pre>


#### <a id="license">License</a>

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

