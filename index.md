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
*Affiliation*. [Department of Algebra][], [Charles University in Prague][]

**PDF documentation**. [ualib-and-birkhoff-24Jan2021.pdf](ualib-and-birkhoff-24Jan2021.pdf)

**Abstract**. The [Agda Universal Algebra Library][] ([UALib][]) is a library of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in Martin-Löf type theory using the [Agda][] proof assistant language.

In the latest version of the library we have defined many new types for representing the important constructs and theorems that comprise part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files, with the `.lagda` extension, and they are grouped into modules so that they may be easily imported into other Agda programs.

To give an idea of the current scope of the library, we note that it now includes a complete proof of the [Birkhoff HSP Theorem](UALib.Birkhoff.Theorem.html) which asserts that every variety is an equational class.  That is, if K is a class of algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then K is the class of algebras satisfying some set of identities. To our knowledge, ours is the first formal, constructive, machine-checked proof of Birkhoff's Theorem.<span class="footnote"><sup>1</sup></span>

We hope the library will be useful to research mathematicians and computer scientists who wish to verify their work by formalizing and type-checking the theorems they prove. Indeed, the [Agda UALib][] is (or wants to be when it grows up) an indispensable guide on our mathematical journey, helping us forge new paths to ever higher peaks, all the time verifying and authenticating what we think we found along the way.

--------------------------------

### <a id="brief-contents"></a> Brief Contents

<pre class="Agda">

<a id="3065" class="Symbol">{-#</a> <a id="3069" class="Keyword">OPTIONS</a> <a id="3077" class="Pragma">--without-K</a> <a id="3089" class="Pragma">--exact-split</a> <a id="3103" class="Pragma">--safe</a> <a id="3110" class="Symbol">#-}</a>

<a id="3115" class="Keyword">module</a> <a id="3122" href="UALib.html" class="Module">UALib</a> <a id="3128" class="Keyword">where</a>

<a id="3135" class="Keyword">open</a> <a id="3140" class="Keyword">import</a> <a id="3147" href="UALib.Preface.html" class="Module">UALib.Preface</a>
<a id="3161" class="Keyword">open</a> <a id="3166" class="Keyword">import</a> <a id="3173" href="UALib.Prelude.html" class="Module">UALib.Prelude</a>
<a id="3187" class="Keyword">open</a> <a id="3192" class="Keyword">import</a> <a id="3199" href="UALib.Algebras.html" class="Module">UALib.Algebras</a>
<a id="3214" class="Keyword">open</a> <a id="3219" class="Keyword">import</a> <a id="3226" href="UALib.Relations.html" class="Module">UALib.Relations</a>
<a id="3242" class="Keyword">open</a> <a id="3247" class="Keyword">import</a> <a id="3254" href="UALib.Homomorphisms.html" class="Module">UALib.Homomorphisms</a>
<a id="3274" class="Keyword">open</a> <a id="3279" class="Keyword">import</a> <a id="3286" href="UALib.Terms.html" class="Module">UALib.Terms</a>
<a id="3298" class="Keyword">open</a> <a id="3303" class="Keyword">import</a> <a id="3310" href="UALib.Subalgebras.html" class="Module">UALib.Subalgebras</a>
<a id="3328" class="Keyword">open</a> <a id="3333" class="Keyword">import</a> <a id="3340" href="UALib.Varieties.html" class="Module">UALib.Varieties</a>
<a id="3356" class="Keyword">open</a> <a id="3361" class="Keyword">import</a> <a id="3368" href="UALib.Birkhoff.html" class="Module">UALib.Birkhoff</a>

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
  - [Relatively Free Algebra Types](UALib.Birkhoff.FreeAlgebra.html)
  - [HSP Lemmata](UALib.Birkhoff.Lemmata.html)
  - [HSP Theorem](UALib.Birkhoff.Theorem.html)

---------------------------------------

<span class="footnote"><sup>1</sup>[Contact the author](mailto:williamdemeo@gmail.com) if you find any evidence that refutes this claim.</span>

<p></p>

<span style="float:right;">[Next Module (UALib.Preface) →](UALib.Preface.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}

