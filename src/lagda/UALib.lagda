---
layout: default
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

# <a id="ualib">Agda UALib</a>

The Agda Universal Algebra Library

14 Jan 2021 (version of {{ "now" | date: "%d %b %Y, %H:%M" }})

**Author**. [William DeMeo][]  
*Affiliation*. [Department of Algebra][], [Charles University in Prague][]

**Abstract**. The [Agda Universal Algebra Library][] is a library of types and programs (or theorems and proofs) that formalizes, in Martin-Löf type theory, the foundations of universal algebra using the [Agda][] proof assistant language.

The goal is a library that is usable by research mathematicians who wish to formally verify their work by implementing and type-checking existing ("known") results, and to aid in the discovery of new mathematics.

The latest version of the library contains statements and proofs of many results from the foundations of general algebra and equational logic, and it is easily imported and used by others to support their own Agda projects.

To get an idea of the current scope of the library, note that it now includes a complete proof of the [Birkhoff HSP Theorem](UALib.Birkhoff.Theorem.html), which asserts that every variety is an equational class. To our knowledge, this is the first constructive, machine-checked proof of Birkhoff's Theorem.<sup>1</sup>

--------------------------------

## <a id="brief-contents"></a> Brief Contents

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib where

open import UALib.Preface
open import UALib.Prelude
open import UALib.Algebras
open import UALib.Relations
open import UALib.Homomorphisms
open import UALib.Terms
open import UALib.Subalgebras
open import UALib.Varieties
open import UALib.Birkhoff

\end{code}

-------------------------------------------

## <a id="contents"></a> Detailed Contents

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
  - [Types for Equational Logic](UALib.Varieties.EquationalLogic.html)
  - [Inductively Defined Closure Operators](UALib.Varieties.Varieties.html)
  - [Equation Preservation Theorems](UALib.Varieties.Preservation.html)

- [Birkhoff's Theorem](UALib.Birkhoff.html)
  - [Relatively Free Algebra Types](UALib.Birkhoff.FreeAlgebra.html)
  - [HSP Lemmata](UALib.Birkhoff.Lemmata.html)
  - [HSP Theorem](UALib.Birkhoff.Theorem.html)

---------------------------------------

Suggest improvements by submitting a [new issue][] or [merge request][] to [gitlab.com/ualib/ualib.gitlab.io/](https://gitlab.com/ualib/ualib.gitlab.io/).

<sup>1</sup> Please [notify me](mailto:williamdemeo@gmail.com) if you find any evidence that refutes this claim.

<p><span style="float:right;"><i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i></span></p>

{% include UALib.Links.md %}









<!--
- [Prelude](UALib.Prelude.html)
  - [Prelude.Preliminaries](UALib.Prelude.Preliminaries.html)
  - [Prelude.Equality](UALib.Prelude.Equality.html)
  - [Prelude.Inverses](UALib.Prelude.Inverses.html)
  - [Prelude.Extensionality](UALib.Prelude.Extensionality.html)

- [Algebras in Agda](UALib.Algebras.html)
  - [Algebras.Signatures](UALib.Algebras.Signatures.html)
  - [Algebras.Algebras](UALib.Algebras.Algebras.html)
  - [Algebras.Products](UALib.Algebras.Products.html)
  - [Algebras.Lifts](UALib.Algebras.Lifts.html)

- [Relations in Agda](UALib.Relations.html)
  - [Relations.Unary](UALib.Relations.Unary.html)
  - [Relations.Binary](UALib.Relations.Binary.html)
  - [Relations.Equivalences](UALib.Relations.Equivalences.html)
  - [Relations.Quotients](UALib.Relations.Quotients.html)
  - [Relations.Congruences](UALib.Relations.Congruences.html)

- [Homomorphisms in Agda](UALib.Homomorphisms.html)
  - [Basic definitions](UALib.Homomorphisms.Basic.html)
  - [Homomorphisms.Kernels](UALib.Homomorphisms.Kernels.html)
  - [Homomorphisms.Noether](UALib.Homomorphisms.Noether.html)
  - [Homomorphisms.Products](UALib.Homomorphisms.Products.html)
  - [Homomorphisms.Isomorphisms](UALib.Homomorphisms.Isomorphisms.html)
  - [Homomorphisms.HomomorphicImages](UALib.Homomorphisms.HomomorphicImages.html)

- [Terms and Free Algebras in Agda](UALib.Terms.html)
  - [Terms.Basic](UALib.Terms.Basic.html)
  - [Terms.Free](UALib.Terms.Free.html)
  - [Terms.Operations](UALib.Terms.Operations.html)
  - [Terms.Compatibility](UALib.Terms.Compatibility.html)

- [Subalgebras in Agda](UALib.Subalgebras.html)
  - [Subalgebras.Subuniverses](UALib.Subalgebras.Subuniverses.html)
  - [Subalgebras.Generation](UALib.Subalgebras.Generation.html)
  - [Subalgebras.Properties](UALib.Subalgebras.Properties.html)
  - [Subalgebras.Homomorphisms](UALib.Subalgebras.Homomorphisms.html)
  - [Subalgebras.Subalgebras](UALib.Subalgebras.Subalgebras)
  - [Subalgebras.WWMD](UALib.Subalgebras.WWMD.html)

- [Equations and Varieties in Agda](UALib.Varieties.html)
  - [Varieties.ModelTheory](UALib.Varieties.ModelTheory.html)
  - [Varieties.EquationalLogic](UALib.Varieties.EquationalLogic.html)
  - [Varieties.Varieties](UALib.Varieties.Varieties.html)
  - [Varieties.Preservation](UALib.Varieties.Preservation.html)

- [The Birkhoff HSP Theorem in Agda](UALib.Birkhoff.html)
  - [Birkhoff.FreeAlgebra](UALib.Birkhoff.FreeAlgebra.html)
  - [Birkhoff.Lemmata](UALib.Birkhoff.Lemmata.html)
  - [Birkhoff.Theorem](UALib.Birkhoff.Theorem.html)
-->
