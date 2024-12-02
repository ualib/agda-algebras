{-

The Agda Universal Algebra Library

(Version 2.04 of 2024.11.29)

------------------------------------------

LICENSE:

The software in this file is subject to the GNU General Public License v3.0.

The [LICENSE file](https://github.com/ualib/agda-algebras/raw/master/LICENSE)
is available at
[github.com/ualib/agda-algebras](https://github.com/ualib/agda-algebras/blob/master/LICENSE).

The text other than software is copyright of the author. It can be
used for scholarly purposes subject to the usual academic conventions
of citation.

* The *.lagda files are not meant to be read by people, but rather to be
  type-checked by the Agda proof assistant and to automatically generate html files
  (which are meant to be read by people).

* This is done with the generate-html file to generate markdown and html files from the
  literate Agda (.lagda) files, and then using jekyll to convert markdown into html.

----------------------------------------

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

**Software Repository**.

[github.com/ualib/agda-algebras](https://github.com/ualib/agda-algebras)

**Citing this work**. See the instructions at

[agda-algebras/Preface.html](https://ualib.github.io/agda-algebras/Preface.html#citing-the-agda-algebras-library).

**Primary Contributors**.

[William DeMeo](https://williamdemeo.gitlab.io) and
[Jacques Carette](http://www.cas.mcmaster.ca/~carette/)

--------------------------------------------

## Organization

We have organized the library into two main modules, called [Base](Base.html) and
[Setoid](Setoid.html), which are imported below (after the [Preface][] module,
which contains no Agda code).  These two modules are mostly independent of one
another.  The [Base](Base.html) module contains submodules that comprise the first
version of the library.  The [Setoid](Setoid.html) contains an alternative version
of the library that is based on setoids.  Finally, we have begun work on a third
alternative version of the library, called `cubical-agda-algebras`, based on
Cubical Agda.

--------------------------------------------
-}


{-# OPTIONS --without-K --exact-split --safe #-}

module agda-algebras where

open import Overture  -- preliminaries
open import Base      -- version 1 of the library (based on standard dependent types)
open import Setoid    -- version 2 of the library (based on setoids)
open import Demos     -- demonstrations (e.g., proof of the HSP Theorem in a single module)
open import Examples

{-
--------------------------------------------

## The formalization of Birkhoff's Theorem

The [Demos.HSP][] module presents a fairly self-contained formal proof of
Birkhoff's HSP Theorem in a single module.

An earlier version of the proof is described in the [Birkhoff HSP Theorem
Section](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) of
the documentation; specifically, see [Setoid.Varieties.HSP][].

The source code containing the complete formal proof of Birkhoff's Theorem is
available in the [agda-algebras][] GitHub repository; see [Demos/HSP.lagda][] or
[Setoid/Varieties/HSP.lagda][].

--------------------------------------------
-}
