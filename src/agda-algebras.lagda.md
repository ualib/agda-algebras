---
layout: title-page
title : "agda-algebras (The Agda Universal Algebra Library)"
date : "2026-05-02"
author: "[agda-algebras development team][]"
---

# The Agda Universal Algebra Library

The [Agda Universal Algebra Library][agda-algebras] is a formalization of
universal algebra in Martin-Löf type theory using the [Agda][] proof
assistant.  The library defines algebras, homomorphisms, subalgebras,
congruences, terms, varieties, and the equational logic that underlies them;
the centrepiece is a fully constructive proof of [Birkhoff's HSP
theorem][HSP-wiki], which characterizes equational classes of algebras.  The
library is being developed simultaneously as a working substrate for research
in universal algebra and as a high-quality training corpus of Agda proofs for
machine learning on formal mathematics.

For installation, build, and contribution instructions, see the project
[`README.md`][README] and [`INSTALL.md`][INSTALL] on GitHub.  For the milestone
roadmap of the in-progress 3.0 reconstruction, see
[`docs/GITHUB_PROJECT.md`][ROADMAP]; for the architectural decisions that
shape it, see [`docs/adr/`][ADR-dir].

**Software repository**.  [github.com/ualib/agda-algebras][agda-algebras]

**Citing**.  See the citation guidance in the project [`README.md`][README].

**Primary contributors**.  [William DeMeo][] and [Jacques Carette][].

----

## Library structure

The 3.0 reconstruction organizes the source tree around a canonical
foundation — `Setoid/` — with optional layers built on top of it.  The
top-level aggregator below imports each layer in turn.

+  [`Overture/`][Overture] — the small set of definitions shared across
   `Setoid/`, `Classical/`, and (eventually) `Cubical/`.
+  [`Setoid/`][Setoid] — **the canonical development tree** for 3.0.
   Algebras carry an explicit equivalence relation (a setoid structure) and
   their operations and homomorphisms are required to respect that
   equivalence.  Definitions are phrased in terms of the algebra's
   equivalence rather than propositional equality, which makes the eventual
   port to Cubical Agda largely mechanical.  See [ADR-001][ADR-001] for
   the rationale.
+  [`Legacy.Base/`][Legacy.Base] — the **frozen pre-3.0** development.  The
   bare-types development that was the original `Base/` tree, retained for
   two reasons (see [`DEPRECATED.md`][DEPRECATED]): (i) so v2.x downstream
   users have a mechanical migration path during the 3.0 transition; and
   (ii) because some modules — most prominently
   [`Legacy.Base.Relations.Continuous`][Continuous] and the
   [`Legacy.Base.Complexity`][Complexity] subtree, both central to milestone
   M9 (algebraic complexity / CSP) — have no `Setoid/` analog yet and are
   scheduled for migration in later milestones.  New work does not land in
   `Legacy.Base`.
+  `Classical/` *(planned, M3)* — specific algebraic theories (semigroups,
   monoids, groups, lattices, rings) built on the universal-algebra
   foundation.  Σ-typed core with parallel record-typed bundle views in
   `Classical/Bundles/` for stdlib interop.  ADR-002 (forthcoming) will
   record the design.
+  `Cubical/` *(planned, M5; canonical for 4.0)* — cubical-Agda counterparts
   of the `Setoid/` and `Classical/` developments, using the structure
   identity principle in place of setoid equivalence.
+  [`Demos/`][Demos] — self-contained pedagogical presentations of marquee
   results.  [`Demos.HSP`][Demos.HSP] is a single-file rendition of
   Birkhoff's theorem suitable for teaching; the canonical proof of record
   lives in [`Setoid.Varieties.HSP`][Setoid.HSP], factored across the
   broader `Setoid.Varieties.*` development.
+  [`Examples/`][Examples] — worked examples of the library in use.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
```
-->

```agda
module agda-algebras where

-- Shared foundations used across Setoid/, Classical/, and (eventually) Cubical/.
open import Overture

-- Setoid/ is the canonical 3.0 development tree.  All new universal-algebra
-- content lands here.  See docs/adr/001-setoid-as-canonical.md for rationale.
open import Setoid

-- Legacy.Base is the frozen pre-3.0 development.  It is retained both for
-- v2.x downstream-user continuity and because some modules have no Setoid/
-- analog yet (tracked per-orphan in src/Legacy/Base/DEPRECATED.md).
-- New work does not land in Legacy.Base.
open import Legacy.Base

-- Self-contained pedagogical presentations of marquee results.
open import Demos

-- Worked examples built against the canonical tree.
open import Examples
```

----

## Birkhoff's HSP theorem

The [`Demos.HSP`][Demos.HSP] module presents a fairly self-contained formal
proof of Birkhoff's theorem in a single Agda module — the version most
often discussed in the project's expository writing.  The canonical proof
of record lives in [`Setoid.Varieties.HSP`][Setoid.HSP], factored across the
broader `Setoid.Varieties.*` development.  The theorem itself asserts that a
class 𝒦 of algebras of fixed signature is closed under homomorphic images,
subalgebras, and arbitrary products if and only if it is the class of all
algebras satisfying some set of identities.

----

## License

agda-algebras is dual-licensed: the source code under `src/` is released
under the [Apache License 2.0][LICENSE], and the documentation under `docs/`
(together with the prose embedded in literate Agda files) is released under
[Creative Commons Attribution 4.0 International][LICENSE-docs].  See the
project [`README.md`][README] for further detail and citation information.

[agda-algebras]: https://github.com/ualib/agda-algebras
[agda-algebras development team]: https://github.com/ualib/agda-algebras#credits
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[ADR-001]: https://github.com/ualib/agda-algebras/blob/master/docs/adr/001-setoid-as-canonical.md
[ADR-dir]: https://github.com/ualib/agda-algebras/tree/master/docs/adr
[Complexity]: Legacy.Base.Complexity.html
[Continuous]: Legacy.Base.Relations.Continuous.html
[Demos]: Demos.html
[Demos.HSP]: Demos.HSP.html
[DEPRECATED]: https://github.com/ualib/agda-algebras/blob/master/src/Legacy/Base/DEPRECATED.md
[Examples]: Examples.html
[HSP-wiki]: https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem
[INSTALL]: https://github.com/ualib/agda-algebras/blob/master/INSTALL.md
[Jacques Carette]: http://www.cas.mcmaster.ca/~carette/
[Legacy.Base]: Legacy.Base.html
[LICENSE]: https://github.com/ualib/agda-algebras/blob/master/LICENSE
[LICENSE-docs]: https://github.com/ualib/agda-algebras/blob/master/LICENSE-docs
[Overture]: Overture.html
[README]: https://github.com/ualib/agda-algebras/blob/master/README.md
[ROADMAP]: https://github.com/ualib/agda-algebras/blob/master/docs/GITHUB_PROJECT.md
[Setoid]: Setoid.html
[Setoid.HSP]: Setoid.Varieties.HSP.html
[William DeMeo]: https://williamdemeo.github.io/

----

<span style="float:right;">[Next Module (Overture) →](Overture.html)</span>

{% include UALib.Links.md %}
