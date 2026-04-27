---
layout: default
title : "Overture.Preface module (The Agda Universal Algebra Library)"
file: docs/lagda/Overture/Preface.lagda
date : "2026-04-20"
author: "the agda-algebras development team"
---

### <a id="preface">Preface</a>

This is the [Overture.Preface][] module of the [Agda Universal Algebra Library][].


<!--
```agda

{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Overture.Preface where
```
-->


The [Agda Universal Algebra Library][] ([agda-algebras][], for short) is a formalization in [Agda][] of the foundations of general algebra in the sense of Birkhoff, Grätzer, McKenzie–McNulty–Taylor, and Bergman: sets equipped with arbitrary-arity operations, the homomorphisms between them, the congruences on them, the term algebras they generate, the varieties they fall into, and the equational logic that organizes all of the above.  The library's current centrepiece is a fully constructive, machine-checked proof of Birkhoff's HSP theorem — every variety is an equational class — in a setoid-based reformulation that avoids function extensionality.

This Preface explains why a mathematician working in universal algebra or an adjacent area might care about this library, why it is written in Agda specifically, what the 3.0 reconstruction has changed, and where to go next.

#### <a id="why-univ-alg-in-type-theory">Why formalize universal algebra in type theory?</a>

Universal algebra has a native affinity for type theory that is stronger than first appearances suggest.  Signatures are indexed families of operation symbols; algebras are sets together with a family of operations indexed by the signature; terms are the initial algebra over a set of variables; subalgebras, homomorphic images, and products are each captured by a small collection of definitions each a few lines long.  These are exactly the constructions Martin-Löf type theory was designed to support — inductive types for terms and trees, Π- and Σ-types for universal and existential parameters, dependent records for structured objects — and the transcription between informal mathematical practice and formal type-theoretic statement turns out to be short.

The dividend is not only aesthetic.  A formalization in type theory is *computable by construction*: a closed proof that every variety is an equational class does not merely assert the theorem, it can be evaluated on inputs.  It is also *compositional*: the free algebra of a variety is not only named, it is built, and its universal property is a dependent function one can apply.  When the formalization is done constructively, as agda-algebras is, the resulting proof terms are objects one can inspect, slice, export, and share — a feature whose importance has grown sharply with the rise of machine learning on formal mathematics.

#### <a id="why-agda">Why Agda?</a>

The proof-assistant landscape of 2026 offers several mature choices — Lean 4, Coq / Rocq, Isabelle — each with excellent universal-algebra formalizations at various stages of development.  The case for Agda here rests on three pillars.

**Proof terms as first-class training and retrieval data**.  Agda's proofs are terms in a pure functional language, constructed by the programmer in direct correspondence with the mathematical content.  Tactic languages, reflection-based automation, and decision procedures have their virtues, but they produce proofs whose surface form is not the proof: a chain of `rfl`, `simp`, `omega`, `aesop` operates on an internal state that the reader cannot see.  An Agda proof is *what it looks like*.  This matters for two present-day concerns.  First, for the library as pedagogy: a graduate student reading agda-algebras encounters the mathematics at full resolution, not a sequence of tactic invocations whose outcomes depend on implementation details of a search procedure.  Second, for the library as training corpus: a (theorem, proof) pair extracted from agda-algebras is a pair a language model can directly learn to generate, not a tactic script whose semantics are opaque without running the assistant.  Milestone 8 of the 3.0 roadmap builds explicitly on this property.

**A clear path to cubical type theory**.  Agda has a mature cubical mode with computational univalence and the structure identity principle.  The 3.0 canonical development uses setoids rather than cubical paths, partly because the cubical ecosystem is still stabilizing and partly because setoids are a lingua franca that readers from many traditions can approach without a tutorial.  But the development is written *with cubical portability in mind*: definitions are stated in terms of the algebra's own equivalence relation (`Algebra.Domain`) rather than propositional equality, so that when v4.0 swaps setoids for paths the substitution is substantively mechanical.  The appeal for a universal algebraist is direct: in the cubical mode, isomorphism *is* equality, which is what the informal practice has always pretended.  The structure identity principle turns that pretence into computation.

**A constructive substrate well-matched to universal algebra**.  Universal algebra has historically been set-theoretic, but its core constructions are constructive by nature.  Free algebras are inductive; subalgebra closures are least fixed points of monotone operators, which are computable when the operators are; homomorphic images, quotient algebras, and subdirect products are concretely describable without invoking ambient set-theoretic machinery.  Agda under `--safe --cubical-compatible --exact-split` is a setting where one cannot cheat without the checker noticing, and where the resulting developments are guaranteed consistent with a constructive universe.  Much of classical universal algebra does not need classical logic; the subset that does — ultrafilter-based compactness arguments, Birkhoff-style completeness relying on Zorn — can be isolated, made explicit, and if need be postulated cleanly at the boundary rather than absorbed invisibly into the ambient logic.

These three reasons are not independent: the constructive substrate makes the proof terms meaningful, and the cubical trajectory keeps the constructive substrate future-proof against the eventual migration of foundations to path-based equality.

#### <a id="the-3-0-reconstruction">The 3.0 reconstruction</a>

The first public release, v2.0.1 ([archived on Zenodo](https://doi.org/10.5281/zenodo.5765793), December 2021), accompanied the TYPES 2021 proof of Birkhoff's HSP theorem.  It succeeded narrowly — the proof type-checks, as does everything it depends on — but bequeathed a codebase with two parallel developments (a standard-dependent-types `Base/` tree and a setoid-based `Setoid/` tree), uneven naming, a handful of synonyms for each central concept, and a documentation layer split across LaTeX-literate Agda, Markdown, and Jekyll templating in ways no one could reproduce from first principles.

The 3.0 reconstruction is a long-overdue consolidation, organized into nine milestones detailed in [`docs/GITHUB_PROJECT.md`](https://github.com/ualib/agda-algebras/blob/master/docs/GITHUB_PROJECT.md).  The decisions most visible to a reader:

+  `Setoid/` is canonical.  `Base/` is being frozen as `Legacy/Base/` and no new work lands there.
+  `Classical/` is a new tree (under construction) for specific algebraic theories — semigroups, monoids, groups, lattices, rings — built on the universal-algebra foundation.  Core structures are Σ-typed for mathematical elegance, with parallel record-typed bundle views in `Classical/Bundles/` for compatibility with the Agda standard library's `Algebra.Bundles` idiom.
+  `Cubical/` is the long-term canonical target for v4.0, where the setoid equivalence is replaced by path equality and the structure identity principle takes its proper place.
+  A project-wide style guide ([`docs/STYLE_GUIDE.md`](https://github.com/ualib/agda-algebras/blob/master/docs/STYLE_GUIDE.md)) and a Setoid-to-Cubical portability discipline govern new contributions.

The documentation conventions have also tightened: public definitions are paired with prose that explains what the definition means and when a mathematician would reach for it, rather than restating the type signature in English.  This is in service of the library's dual role as reference and training corpus, a role the 2021 version acknowledged in passing but did not systematically enforce.

#### <a id="mathematical-horizon">Mathematical horizon</a>

The library is a working substrate for active mathematical research, not only a reference for settled material.  The 3.0 roadmap sketches several tracks.

**Foundations that unlock many research questions**.  Beyond Birkhoff, the universal-algebra prerequisites shared by many active areas include the congruence lattice `Con 𝑨` as a complete lattice, subalgebra lattices, subdirectly irreducible algebras and subdirect decomposition, and the basic Maltsev conditions — congruence permutability, distributivity, modularity, the near-unanimity conditions, and cube terms.  Milestone 6 (M6) targets this material.  A reader who cares about any of tame congruence theory, commutator theory, clone theory, equational completeness, or the structural side of CSP complexity will find these foundations are their common prerequisite, and having them in one consistent formalization is worth something independently of any specific research horizon.

**The Finite Lattice Representation Problem as a long-term anchor**.  A motivating problem for the maintainers is the Finite Lattice Representation Problem (FLRP): is every finite lattice the congruence lattice of some finite algebra?  The problem has been open since Grätzer–Schmidt (1963), where the corresponding statement for algebraic lattices was resolved affirmatively — no restriction on cardinality — while the finite case has resisted every subsequent attempt.  The 3.0 library does not attempt the FLRP directly, but the M6 foundational material is precisely what an attempt would need; M6 is explicit about this framing.  The FLRP is not the only horizon and not the primary marketing point, but it is the reason the library exists in its present form, and keeping it in view disciplines the design decisions.

**Algebraic complexity and constraint satisfaction**.  Milestone 7 (M7) extends the small `Base.Complexity/CSP` stub into a proper development of finite-template algebraic CSP.  The central objects are polymorphism clones `Pol(A, Γ)` as first-class types, the Jeavons Galois connection between invariant relations and polymorphism clones, worked examples from classical tractability (Horn-SAT, 2-SAT, linear systems over finite fields), and a formal statement — not necessarily a proof, at this stage — of the Bulatov–Zhuk algebraic dichotomy.  Infinite-template extensions in the spirit of the Bodirsky–Pinsker program (polymorphism clones of ω-categorical structures, canonical functions in the sense of Pinsker's recent work, topological Birkhoff analogues for polymorphism clones with a topological structure) are mapped out as a natural application of the continuous-relation API in M9-2.

**Applications of continuous relations**.  The library's `Base.Relations.Continuous` formalization generalizes classical finite-arity relations by allowing the arity to be an arbitrary type, with compatibility with operations stated pointwise over that arity.  That generalization is not ad hoc: it is exactly the shape needed for Scott-continuous relations on directed-complete partial orders (M9-1), and for the infinitary constraints of ω-categorical templates (M9-2).  The former connects agda-algebras to domain theory in the Scott sense — with applications in denotational semantics of typed lambda calculi, topologically enriched model theory, and Escardó's characterization of searchable sets via topological continuity.  The latter connects it to the topological-dynamics approach to infinite-template CSP complexity.  An exploratory track (M9-3) asks whether the same abstraction has novel applications to bisimulation of non-finitary coalgebras — a question at the intersection of coalgebraic methods and Birkhoff-style universal algebra that appears to be less developed than one might expect, and that the maintainers intend to scope rather than speculate about.  These tracks share a foundation and a proof-assistant substrate; keeping them under one roof is one of the library's quiet advantages.

**Library as corpus**.  Milestone 8 (M8) treats the library itself as a deliverable: a published (theorem, proof) corpus, regenerated on each release, distributed on Hugging Face for retrieval and training.  The maintainers' parallel work on agda-native-air — an AI-assisted formal-proof workflow — is a natural downstream consumer, and the design of the corpus is informed by that use case.  The broader goal is to contribute a high-quality source of constructive, human-authored Agda proofs to the growing ecosystem of datasets for machine learning on formal mathematics.  This is not a side project relative to the pure mathematics: the library's design decisions — many small focused lemmas, named helper functions, rich prose comments paired with formal statements, explicit type signatures on every public definition — were tuned for this dual role from the start of the reconstruction.

#### <a id="where-to-go-next">Where to go next</a>

Readers approaching the library for the first time will typically want one of a few entry points.

+  For the headline result, see the [Proof of the HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) in [Setoid.Varieties.HSP][], or the single-file [Demos.HSP][] rendition written to accompany the TYPES 2021 paper.
+  For the core definitions, see [Setoid.Algebras.Basic][], [Setoid.Homomorphisms][], [Setoid.Subalgebras][], and [Setoid.Varieties][].
+  For the library's layered structure, the milestone plan, and the roadmap, see [`docs/GITHUB_PROJECT.md`](https://github.com/ualib/agda-algebras/blob/master/docs/GITHUB_PROJECT.md).
+  For the style guide and contribution conventions, see [`docs/STYLE_GUIDE.md`](https://github.com/ualib/agda-algebras/blob/master/docs/STYLE_GUIDE.md) and [`CONTRIBUTING.md`](https://github.com/ualib/agda-algebras/blob/master/CONTRIBUTING.md).

The remainder of the `Overture` chapter introduces the library's conventions and notation.  Readers familiar with both Agda and universal algebra can skim it; others may want to read it carefully before moving into the substantive material.

#### <a id="attributions">Attributions</a>

The [agda-algebras][] library is developed and maintained by the *agda-algebras development team*, led by [William DeMeo][] with senior-advisor contributions from [Jacques Carette][] (McMaster University).

##### <a id="acknowledgements">Acknowledgements</a>

We thank [Andreas Abel][], [Jeremy Avigad][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration, and encouragement over the life of the project.  Most of the mathematical content formalized in agda-algebras is well known; the novelty lies in the formalization itself, which is due to the contributors and acknowledgees listed above.

#### <a id="references">References</a>

The following Agda documentation and tutorials informed the development of agda-algebras, and we recommend them to readers new to the language.

+  Escardó, [Introduction to Univalent Foundations of Mathematics with Agda][]
+  Wadler, Kokke, and Siek, [Programming Language Foundations in Agda][]
+  Bove and Dybjer, [Dependent Types at Work][]
+  Gunther, Gadea, and Pagano, [Formalization of Universal Algebra in Agda][]
+  Norell and Chapman, [Dependently Typed Programming in Agda][]

The official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the open-source [Agda Standard Library][] source code are also indispensable.

#### <a id="citing">Citing</a>

Citation information — both the v2.0.1 Zenodo archival entry and the BibTeX for the Birkhoff formalization paper — is maintained in the [README's Citing section](https://github.com/ualib/agda-algebras#citing).  While the 3.0 reconstruction is in development, please cite the GitHub repository and pin a commit hash for reproducibility; a new Zenodo DOI will be minted at the v3.0 release.

#### <a id="contributions-welcomed">Contributions welcomed</a>

Improvements to `agda-algebras` — bug reports, design discussions, pull requests, documentation fixes — are welcome.  See [`CONTRIBUTING.md`](https://github.com/ualib/agda-algebras/blob/master/CONTRIBUTING.md) for the development workflow and the [GitHub issue tracker](https://github.com/ualib/agda-algebras/issues/new/choose) to report problems or propose changes.

------------------------------------------------

<span style="float:left;">[↑ Overture](Overture.html)</span>
<span style="float:right;">[Overture.Basic →](Overture.Basic.html)</span>

{% include UALib.Links.md %}
