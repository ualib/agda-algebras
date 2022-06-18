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

# The Agda Universal Algebra Library

---------------------------------------------------------------------------------

(Version 2.04 of {{ "now" | date: "%d %b %Y" }})

**Abstract**. The [Agda Universal Algebra Library][] is a collection of types and
programs (theorems and proofs) that formalizes the foundations of universal
algebra in dependent type theory using the [Agda][] proof assistant language.

The library contains definitions of many new types for representing important
constructs and theorems comprising a substantial part of the foundations of
general (universal) algebra and equational logic. These types are implemented in
so called "literate" Agda files (with the `.lagda` extension), and they are
grouped into modules which can be easily imported and integrated into other Agda
developments.

To get an idea of the current scope of the library, note that it now includes a
formal proof of Birkhoff's [HSP
Theorem](https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem),
which asserts that every *variety* is an *equational class*.  That is, if 𝒦 is a
class of algebras which is closed under the taking of homomorphic images,
subalgebras, and arbitrary products, then 𝒦 is the class of all algebras
satisfying some set of identities. To our knowledge, ours is the first formal,
machine-checked proof of Birkhoff's Theorem. (If you have evidence refuting this
claim, we would love to hear about it; please [email
us](mailto:williamdemeo@gmail.com)!)

We hope the library is useful to mathematicians and computer scientists who wish
to formalize their work in dependent type theory and verify their results with a
proof assistant. Indeed, the [agda-algebras][] library aims to become an indispensable
companion on our mathematical journeys, helping us authenticate the discoveries we
make along the way.

**Keywords and phrases**. Universal algebra, Equational logic, Martin-Löf Type
  Theory, Birkhoff’s HSP Theorem, Formalization of mathematics, Agda

**Software Repository**. [github.com/ualib/agda-algebras](https://github.com/ualib/agda-algebras)

**Citing this work**. See the instructions at [agda-algebras/Preface.html](https://ualib.github.io/agda-algebras/Preface.html#citing-the-agda-algebras-library).

**Primary Contributors**. [William DeMeo](https://williamdemeo.gitlab.io) and [Jacques Carette](http://www.cas.mcmaster.ca/~carette/)

--------------------------------

## Organization

We have organized the library into two main modules, called [Base](Base.html) and
[Setoid](Setoid.html), which are imported below (after the [Preface][] module,
which contains no Agda code).  These two modules are mostly independent of one
another.  The [Base](Base.html) module contains submodules that comprise the first
version of the library.  The [Setoid](Setoid.html) contains an alternative version
of the library that is based on setoids.  Finally, we have begun work on a third
alternative version of the library, called `cubical-agda-algebras`, based on
Cubical Agda.


<pre class="Agda">
<a id="3923" class="Symbol">{-#</a> <a id="3927" class="Keyword">OPTIONS</a> <a id="3935" class="Pragma">--without-K</a> <a id="3947" class="Pragma">--exact-split</a> <a id="3961" class="Pragma">--safe</a> <a id="3968" class="Symbol">#-}</a>
</pre>
<pre class="Agda">
<a id="3996" class="Keyword">module</a> <a id="4003" href="agda-algebras.html" class="Module">agda-algebras</a> <a id="4017" class="Keyword">where</a>

<a id="4024" class="Keyword">open</a> <a id="4029" class="Keyword">import</a> <a id="4036" href="Overture.html" class="Module">Overture</a>  <a id="4046" class="Comment">-- preliminaries</a>
<a id="4063" class="Keyword">open</a> <a id="4068" class="Keyword">import</a> <a id="4075" href="Base.html" class="Module">Base</a>      <a id="4085" class="Comment">-- version 1 of the library (based on standard dependent types)</a>
<a id="4149" class="Keyword">open</a> <a id="4154" class="Keyword">import</a> <a id="4161" href="Setoid.html" class="Module">Setoid</a>    <a id="4171" class="Comment">-- version 2 of the library (based on setoids)</a>
<a id="4218" class="Keyword">open</a> <a id="4223" class="Keyword">import</a> <a id="4230" href="Demos.html" class="Module">Demos</a>     <a id="4240" class="Comment">-- demonstrations (e.g., proof of the HSP Theorem in a single module)</a>
<a id="4310" class="Keyword">open</a> <a id="4315" class="Keyword">import</a> <a id="4322" href="Examples.html" class="Module">Examples</a>

</pre>


## The formalization of Brkhoff's Theorem

The [Demos.HSP][] module presents a fairly self-contained formal proof of
Birkhoff's HSP Theorem in a single module.

An earlier version of the proof is described in the [Birkhoff HSP Theorem
Section](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) of
the documentation; specifically, see [Setoid.Varieties.HSP][].

The source code containing the complete formal proof of Birkhoff's Theorem is
available in the [agda-algebras][] GitHub repository; see [Demos/HSP.lagda][] or
[Setoid/Varieties/HSP.lagda][].

------------------------------

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

<span style="float:right;">[Next Module (Overture) →](Overture.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}

