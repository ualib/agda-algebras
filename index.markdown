---
layout: title-page
title : agda-algebras.lagda (The Agda Universal Algebra Library)
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

* This is done with the generate-html file to generate markdown and html files from the
  literate Agda (.lagda) files, and then using jekyll to convert markdown into html.

-->

# The Agda Universal Algebra Library

---------------------------------------------------------------------------------

(Version 2.01 of {{ "now" | date: "%d %b %Y" }})

**Abstract**. The [Agda Universal Algebra Library](https://ualib.github.io/agda-algebras) is a collection of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) proof assistant language.

The library contains definitions of many new types for representing important constructs and theorems comprising a substantial part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files (with the `.lagda` extension), and they are grouped into modules which can be easily imported and integrated into other Agda developments.

To get an idea of the current scope of the library, note that it now includes a formal proof of Birkhoff's [HSP Theorem](https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem), which asserts that every *variety* is an *equational class*.  That is, if 𝒦 is a class of algebras which is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then 𝒦 is the class of all algebras satisfying some set of identities. To our knowledge, ours is the first formal, machine-checked proof of Birkhoff's Theorem. (If you believe you there is evidence refuting this claim, we would love to hear about it; please [email us](mailto:williamdemeo@gmail.com)!)

We hope the library is useful to mathematicians and computer scientists who wish to formalize their work in dependent type theory and verify their results with a proof assistant. Indeed, the [agda-algebras library](https://github.com/ualib/agda-algebras) aims to become an indispensable companion on our mathematical journeys, helping us authenticate the discoveries we make along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [github.com/ualib/agda-algebras](https://gitub.com/ualib/agda-algebras)

**Citing this work**. See the instructions at [ualib.github.io/agda-algebras/Preface.html](https://ualib.github.io/agda-algebras/Preface.html#how-to-cite-the-agda-ualib).

**Primary Contributors**. [William DeMeo](https://williamdemeo.gitlab.io) and [Jacques Carette](http://www.cas.mcmaster.ca/~carette/)

--------------------------------

## Brief Contents

<pre class="Agda">

<a id="3458" class="Symbol">{-#</a> <a id="3462" class="Keyword">OPTIONS</a> <a id="3470" class="Pragma">--without-K</a> <a id="3482" class="Pragma">--exact-split</a> <a id="3496" class="Pragma">--safe</a> <a id="3503" class="Symbol">#-}</a>

<a id="3508" class="Keyword">module</a> <a id="3515" href="agda-algebras.html" class="Module">agda-algebras</a> <a id="3529" class="Keyword">where</a>

<a id="3536" class="Keyword">open</a> <a id="3541" class="Keyword">import</a> <a id="3548" href="Preface.html" class="Module">Preface</a>
<a id="3556" class="Keyword">open</a> <a id="3561" class="Keyword">import</a> <a id="3568" href="Overture.html" class="Module">Overture</a>
<a id="3577" class="Keyword">open</a> <a id="3582" class="Keyword">import</a> <a id="3589" href="Relations.html" class="Module">Relations</a>
<a id="3599" class="Keyword">open</a> <a id="3604" class="Keyword">import</a> <a id="3611" href="Foundations.html" class="Module">Foundations</a>
<a id="3623" class="Keyword">open</a> <a id="3628" class="Keyword">import</a> <a id="3635" href="Residuation.html" class="Module">Residuation</a>
<a id="3647" class="Keyword">open</a> <a id="3652" class="Keyword">import</a> <a id="3659" href="GaloisConnections.html" class="Module">GaloisConnections</a>
<a id="3677" class="Keyword">open</a> <a id="3682" class="Keyword">import</a> <a id="3689" href="ClosureSystems.html" class="Module">ClosureSystems</a>
<a id="3704" class="Keyword">open</a> <a id="3709" class="Keyword">import</a> <a id="3716" href="Algebras.html" class="Module">Algebras</a>
<a id="3725" class="Keyword">open</a> <a id="3730" class="Keyword">import</a> <a id="3737" href="Homomorphisms.html" class="Module">Homomorphisms</a>
<a id="3751" class="Keyword">open</a> <a id="3756" class="Keyword">import</a> <a id="3763" href="Terms.html" class="Module">Terms</a>
<a id="3769" class="Keyword">open</a> <a id="3774" class="Keyword">import</a> <a id="3781" href="Subalgebras.html" class="Module">Subalgebras</a>
<a id="3793" class="Keyword">open</a> <a id="3798" class="Keyword">import</a> <a id="3805" href="Varieties.html" class="Module">Varieties</a>
<a id="3815" class="Keyword">open</a> <a id="3820" class="Keyword">import</a> <a id="3827" href="Structures.html" class="Module">Structures</a>
<a id="3838" class="Keyword">open</a> <a id="3843" class="Keyword">import</a> <a id="3850" href="Complexity.html" class="Module">Complexity</a>

</pre>


## <a id="license">License</a>

<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
  <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="css/by-sa.svg" />
  <!-- <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png" /> -->
</a>
<span xmlns:dct="http://purl.org/dc/terms/" property="dct:title">
  The agda-algebras library and its documentation,
</span> by
<a xmlns:cc="http://creativecommons.org/ns#" href="https://williamdemeo.gitlab.io/" property="cc:attributionName" rel="cc:attributionURL">
  William DeMeo
  </a> and the <a href="https://github.com/ualib/agda-algebras/Preface.html#the-agda-algebras-development-team">agda algebras team</a>,
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

<span style="float:right;">[Next Module (Preface) →](Preface.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}

