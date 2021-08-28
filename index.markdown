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

We hope the library is useful to mathematicians and computer scientists who wish to formalize their work in dependent type theory and verify their results with a proof assistant. Indeed, the [Agda Universal Algebra Library]((https://ualib.github.io/agda-algebras) aims to become an indispensable companion on our mathematical journeys, helping us authenticate the discoveries we make along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [github.com/ualib/agda-algebras](https://gitub.com/ualib/agda-algebras)

**Citing this work**. See the instructions at [ualib.github.io/agda-algebras/Preface.html](https://ualib.github.io/agda-algebras/Preface.html#how-to-cite-the-agda-ualib).

**Primary Contributors**. [William DeMeo](https://williamdemeo.gitlab.io) and [Jacques Carette](http://www.cas.mcmaster.ca/~carette/)

--------------------------------

## Brief Contents

<pre class="Agda">

<a id="3467" class="Symbol">{-#</a> <a id="3471" class="Keyword">OPTIONS</a> <a id="3479" class="Pragma">--without-K</a> <a id="3491" class="Pragma">--exact-split</a> <a id="3505" class="Pragma">--safe</a> <a id="3512" class="Symbol">#-}</a>

<a id="3517" class="Keyword">module</a> <a id="3524" href="agda-algebras.html" class="Module">agda-algebras</a> <a id="3538" class="Keyword">where</a>

<a id="3545" class="Keyword">open</a> <a id="3550" class="Keyword">import</a> <a id="3557" href="Preface.html" class="Module">Preface</a>
<a id="3565" class="Keyword">open</a> <a id="3570" class="Keyword">import</a> <a id="3577" href="Overture.html" class="Module">Overture</a>
<a id="3586" class="Keyword">open</a> <a id="3591" class="Keyword">import</a> <a id="3598" href="Relations.html" class="Module">Relations</a>
<a id="3608" class="Keyword">open</a> <a id="3613" class="Keyword">import</a> <a id="3620" href="Foundations.html" class="Module">Foundations</a>
<a id="3632" class="Keyword">open</a> <a id="3637" class="Keyword">import</a> <a id="3644" href="Residuation.html" class="Module">Residuation</a>
<a id="3656" class="Keyword">open</a> <a id="3661" class="Keyword">import</a> <a id="3668" href="GaloisConnections.html" class="Module">GaloisConnections</a>
<a id="3686" class="Keyword">open</a> <a id="3691" class="Keyword">import</a> <a id="3698" href="ClosureSystems.html" class="Module">ClosureSystems</a>
<a id="3713" class="Keyword">open</a> <a id="3718" class="Keyword">import</a> <a id="3725" href="Algebras.html" class="Module">Algebras</a>
<a id="3734" class="Keyword">open</a> <a id="3739" class="Keyword">import</a> <a id="3746" href="Homomorphisms.html" class="Module">Homomorphisms</a>
<a id="3760" class="Keyword">open</a> <a id="3765" class="Keyword">import</a> <a id="3772" href="Terms.html" class="Module">Terms</a>
<a id="3778" class="Keyword">open</a> <a id="3783" class="Keyword">import</a> <a id="3790" href="Subalgebras.html" class="Module">Subalgebras</a>
<a id="3802" class="Keyword">open</a> <a id="3807" class="Keyword">import</a> <a id="3814" href="Varieties.html" class="Module">Varieties</a>
<a id="3824" class="Keyword">open</a> <a id="3829" class="Keyword">import</a> <a id="3836" href="Structures.html" class="Module">Structures</a>
<a id="3847" class="Keyword">open</a> <a id="3852" class="Keyword">import</a> <a id="3859" href="Complexity.html" class="Module">Complexity</a>

</pre>


## <a id="license">License</a>

<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
  <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="css/by-sa.svg" />
  <!-- <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png" /> -->
</a>
<span xmlns:dct="http://purl.org/dc/terms/" property="dct:title">
  The Agda Universal Algebra Library
</span> by
<a xmlns:cc="http://creativecommons.org/ns#" href="https://williamdemeo.gitlab.io/" property="cc:attributionName" rel="cc:attributionURL">
  William DeMeo
</a> and the <a href="
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

