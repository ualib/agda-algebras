---
layout: title-page
title : "agda-algebras.lagda (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "[agda-algebras development team][]"
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

## The Agda Universal Algebra Library

---------------------------------------------------------------------------------

(Version 2.01 of {{ "now" | date: "%d %b %Y" }})

**Abstract**. The [Agda Universal Algebra Library](https://ualib.github.io/agda-algebras) is a collection of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) proof assistant language.

The library contains definitions of many new types for representing important constructs and theorems comprising a substantial part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files (with the `.lagda` extension), and they are grouped into modules which can be easily imported and integrated into other Agda developments.

To get an idea of the current scope of the library, note that it now includes a formal proof of Birkhoff's [HSP Theorem](https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem), which asserts that every *variety* is an *equational class*.  That is, if 𝒦 is a class of algebras which is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then 𝒦 is the class of all algebras satisfying some set of identities. To our knowledge, ours is the first formal, machine-checked proof of Birkhoff's Theorem. (If you have evidence refuting this claim, we would love to hear about it; please [email us](mailto:williamdemeo@gmail.com)!)

We hope the library is useful to mathematicians and computer scientists who wish to formalize their work in dependent type theory and verify their results with a proof assistant. Indeed, the [agda-algebras library](https://github.com/ualib/agda-algebras) aims to become an indispensable companion on our mathematical journeys, helping us authenticate the discoveries we make along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [github.com/ualib/agda-algebras](https://gitub.com/ualib/agda-algebras)

**Citing this work**. See the instructions at [agda-algebras/Preface.html](https://ualib.github.io/agda-algebras/Preface.html#how-to-cite-the-agda-algebras-library).

**Primary Contributors**. [William DeMeo](https://williamdemeo.gitlab.io) and [Jacques Carette](http://www.cas.mcmaster.ca/~carette/)

--------------------------------

### Brief Contents

The following list of modules imported by the current module, [agda-algebras](https://ualib.github.io/agda-algebras/agda-algebras.html), serves as a brief table of contents.

<pre class="Agda">
<a id="3646" class="Symbol">{-#</a> <a id="3650" class="Keyword">OPTIONS</a> <a id="3658" class="Pragma">--without-K</a> <a id="3670" class="Pragma">--exact-split</a> <a id="3684" class="Pragma">--safe</a> <a id="3691" class="Symbol">#-}</a>
</pre>
<pre class="Agda">
<a id="3719" class="Keyword">module</a> <a id="3726" href="agda-algebras.html" class="Module">agda-algebras</a> <a id="3740" class="Keyword">where</a>

<a id="3747" class="Keyword">open</a> <a id="3752" class="Keyword">import</a> <a id="3759" href="Preface.html" class="Module">Preface</a>
<a id="3767" class="Keyword">open</a> <a id="3772" class="Keyword">import</a> <a id="3779" href="Overture.html" class="Module">Overture</a>
<a id="3788" class="Keyword">open</a> <a id="3793" class="Keyword">import</a> <a id="3800" href="Relations.html" class="Module">Relations</a>
<a id="3810" class="Keyword">open</a> <a id="3815" class="Keyword">import</a> <a id="3822" href="Equality.html" class="Module">Equality</a>
<a id="3831" class="Keyword">open</a> <a id="3836" class="Keyword">import</a> <a id="3843" href="Residuation.html" class="Module">Residuation</a>
<a id="3855" class="Keyword">open</a> <a id="3860" class="Keyword">import</a> <a id="3867" href="GaloisConnections.html" class="Module">GaloisConnections</a>
<a id="3885" class="Keyword">open</a> <a id="3890" class="Keyword">import</a> <a id="3897" href="ClosureSystems.html" class="Module">ClosureSystems</a>
<a id="3912" class="Keyword">open</a> <a id="3917" class="Keyword">import</a> <a id="3924" href="Algebras.html" class="Module">Algebras</a>
<a id="3933" class="Keyword">open</a> <a id="3938" class="Keyword">import</a> <a id="3945" href="Homomorphisms.html" class="Module">Homomorphisms</a>
<a id="3959" class="Keyword">open</a> <a id="3964" class="Keyword">import</a> <a id="3971" href="Terms.html" class="Module">Terms</a>
<a id="3977" class="Keyword">open</a> <a id="3982" class="Keyword">import</a> <a id="3989" href="Subalgebras.html" class="Module">Subalgebras</a>
<a id="4001" class="Keyword">open</a> <a id="4006" class="Keyword">import</a> <a id="4013" href="Varieties.html" class="Module">Varieties</a>
<a id="4023" class="Keyword">open</a> <a id="4028" class="Keyword">import</a> <a id="4035" href="Structures.html" class="Module">Structures</a>
<a id="4046" class="Keyword">open</a> <a id="4051" class="Keyword">import</a> <a id="4058" href="Complexity.html" class="Module">Complexity</a>

</pre>

------------------------------

##### <a id="license">License</a>

<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
  <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="css/by-sa.svg" />
  <!-- <img alt="Creative Commons License" style="border-width:0; float: left; padding:5px 5px 0px 0px" height='40' src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png" /> -->
</a>
<span xmlns:dct="http://purl.org/dc/terms/" property="dct:title">
  The agda-algebras library and its documentation,
</span> by
<a xmlns:cc="http://creativecommons.org/ns#" href="https://williamdemeo.gitlab.io/" property="cc:attributionName" rel="cc:attributionURL">
  William DeMeo
  </a> and the <a href="https://ualib.github.io/agda-algebras/Preface.html#the-agda-algebras-development-team">agda algebras team</a>,
is licensed under a
<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">
  Creative Commons Attribution-ShareAlike 4.0 International License.
</a>
<br />
<a href="https://ualib.github.io/agda-algebras/Preface.html#how-to-cite-the-agda-algebras-library">BibTeX citation information.</a>
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

