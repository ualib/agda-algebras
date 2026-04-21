<!-- File: README.md -->
# agda-algebras

[![CI](https://github.com/ualib/agda-algebras/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/ualib/agda-algebras/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](./LICENSE)
[![Docs License: CC BY 4.0](https://img.shields.io/badge/Docs-CC_BY_4.0-lightgrey.svg)](./LICENSE-docs)
[![Agda 2.8.0](https://img.shields.io/badge/Agda-2.8.0-purple.svg)](https://github.com/agda/agda/releases/tag/v2.8.0)
[![stdlib 2.3](https://img.shields.io/badge/stdlib-2.3-orange.svg)](https://github.com/agda/agda-stdlib/releases/tag/v2.3)

A formalization of universal algebra in [Agda][], built on the [Agda standard library][].  The library defines algebras, homomorphisms, congruences, terms, varieties, and the equational logic that underlies them, with a fully constructive proof of [Birkhoff's HSP theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) at the centre.  It is being developed both as a working substrate for research in universal algebra and as a high-quality training corpus of Agda proofs for machine learning on formal mathematics.

> **Status.** Version 3.0 is under active reconstruction on `master`.  The library currently targets Agda 2.8.0 and standard-library 2.3.  Expect breaking changes until 3.0 is released; see [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md) for the milestone plan and [`CHANGELOG.md`](CHANGELOG.md) for what has landed so far.

The **previous** version (called `UALib`, built against [TypeTopology](https://github.com/martinescardo/TypeTopology)) is no longer maintained but remains available:

+  Source: [https://gitlab.com/ualib/ualib.gitlab.io](https://gitlab.com/ualib/ualib.gitlab.io)
+  Docs: [https://ualib.gitlab.io](https://ualib.gitlab.io)

---

## Quickstart

From a clean checkout to a green build, assuming [Nix][] with flakes enabled (see [`INSTALL.md`](INSTALL.md) for installation and flake-activation instructions):

```bash
git clone https://github.com/ualib/agda-algebras.git
cd agda-algebras
nix develop          # pins Agda 2.8.0 + standard-library 2.3 automatically
make check           # type-check the entire library
make html            # (optional) build clickable HTML under ./html/
```

The first `nix develop` downloads and builds the pinned Agda and standard library; subsequent entries into the shell are essentially instantaneous.  Non-Nix installation paths (Agda's PyPI package, prebuilt binaries, `cabal` from source) are documented in [`INSTALL.md`](INSTALL.md).

---

## Documentation

+  Rendered clickable HTML of the library: [https://ualib.org](https://ualib.org).
+  Installation guide: [`INSTALL.md`](INSTALL.md).
+  Contributor's guide: [`CONTRIBUTING.md`](CONTRIBUTING.md).
+  Style guide: [`docs/STYLE_GUIDE.md`](docs/STYLE_GUIDE.md).
+  Roadmap and milestone plan: [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md).
+  Changelog: [`CHANGELOG.md`](CHANGELOG.md).
+  Architecture decision records: [`docs/adr/`](docs/adr/) (scaffolding tracked in M1-6).
+  Code of conduct: [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md).

---

## Library structure

The 3.0 reconstruction organizes the source tree around a canonical foundation with optional layers built on top of it.

+  **`src/Setoid/`** is the **canonical** development tree for 3.0.  Algebras are sets-with-equivalence (setoids) carrying a signature interpretation that respects the equivalence; homomorphisms preserve both the operations and the equivalence.  Definitions are stated in terms of the `Algebra.Domain` equivalence rather than propositional equality, which makes the eventual port to Cubical Agda largely mechanical.
+  **`src/Classical/`** *(planned, M3)* builds specific algebraic theories — semigroups, monoids, groups, lattices, rings — on the universal-algebra foundation.  Core structures are Σ-typed for mathematical elegance, with parallel record-typed *bundle views* in `Classical/Bundles/` for stdlib interop.
+  **`src/Cubical/`** *(planned, v4.0, tracked in M5)* is the long-term canonical target: cubical-Agda counterparts of the `Setoid/` and `Classical/` developments, using the structure identity principle in place of setoid equivalence.
+  **`src/Base/`** holds the pre-reconstruction development and shared foundations still in use during the 3.0 transition.  M2-1 will move the frozen portions to `src/Legacy/Base/`; new contributions do not land in `Base/` (or later in `Legacy/Base/`).
+  **`src/Overture/`** holds the small set of definitions shared across `Setoid/`, `Classical/`, and (eventually) `Cubical/`.
+  **`src/Demos/`** holds self-contained pedagogical presentations of marquee results.  [`src/Demos/HSP`](src/Demos) is a single-file rendition of Birkhoff's variety theorem suitable for teaching; the canonical proof lives in [`src/Setoid/Varieties/HSP.agda`](src/Setoid/Varieties/HSP.agda) (canonicality to be formalized in M2-4).

The contributor's guide gives more detail on which tree a new piece of work belongs in; when in doubt, please open an issue with the `design-discussion` label.

---

## Installation

The recommended development environment is [Nix][] (Option 1 in [`INSTALL.md`](INSTALL.md)):

```bash
nix develop
```

inside a clone of the repository.  This pins Agda 2.8.0 and standard-library 2.3 automatically, writes a project-local Agda library configuration under `.agda/`, and bypasses any Agda or standard-library versions registered elsewhere on the host machine.

For contributors who cannot or prefer not to use Nix, [`INSTALL.md`](INSTALL.md) walks through three alternative paths: Agda's official Python installer (`pipx install agda==2.8.0`), a prebuilt binary from the Agda 2.8.0 release page, and a `cabal` build from source.  All three require manually installing standard-library 2.3 and registering it in `~/.config/agda/libraries`.

### Requirements

+  [Agda](https://agda.readthedocs.io) 2.8.0 (released 2025-07)
+  [standard-library](https://github.com/agda/agda-stdlib) 2.3 (released 2025-08)
+  GNU Make

Older versions of either component are **not** supported on the `master` branch.  To work against the v2.0.1 archival release (which targets Agda 2.6.2 / stdlib 1.7), check out the [`v2.0.1` tag](https://github.com/ualib/agda-algebras/releases/tag/v2.0.1).

---

## Contributing

Contributions are welcome — bug reports, design discussions, pull requests, and documentation improvements alike.  Before contributing code, please read

+  [`CONTRIBUTING.md`](CONTRIBUTING.md) — development workflow, branching, and review expectations;
+  [`docs/STYLE_GUIDE.md`](docs/STYLE_GUIDE.md) — file format, naming, notation, proof style, and the *library-as-training-corpus* considerations that shape how we write proofs;
+  [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md) — the 3.0 milestone roadmap (check whether your contribution fits an existing track before opening a fresh issue);
+  [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) — community standards.

For questions about mathematical content or larger design changes, please open a GitHub issue with the `design-discussion` label before writing code.

---

## Licensing

agda-algebras is dual-licensed to match the dual nature of the project.

+  **Source code** (under `src/`) is licensed under the [Apache License 2.0](./LICENSE), a permissive industry-standard software license compatible with essentially all other open-source licenses and with commercial use.
+  **Documentation, papers, and tutorials** (under `docs/`) are licensed under the [Creative Commons Attribution 4.0 International License](./LICENSE-docs), the standard license for academic-style written material; it permits sharing and adaptation with attribution.

If you are redistributing or building on agda-algebras, please respect both licenses for their respective parts of the repository.

---

## Citing

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.5765793.svg)](https://doi.org/10.5281/zenodo.5765793)

The archival reference is the v2.0.1 Zenodo deposit, made for the TYPES 2021 submission:

```bibtex
@misc{ualib_v2.0.1,
  author       = {De{M}eo, William and Carette, Jacques},
  title        = {{T}he {A}gda {U}niversal {A}lgebra {L}ibrary (agda-algebras)},
  year         = 2021,
  note         = {{D}ocumentation available at https://ualib.org},
  version      = {2.0.1},
  doi          = {10.5281/zenodo.5765793},
  howpublished = {{G}it{H}ub.com},
  note         = {{V}er.~2.0.1; source code: \href{https://zenodo.org/record/5765793/files/ualib/agda-algebras-v.2.0.1.zip?download=1}{agda-algebras-v.2.0.1.zip}, {G}it{H}ub repo: \href{https://github.com/ualib/agda-algebras}{github.com/ualib/agda-algebras}},
}
```

While the 3.0 reconstruction is in development, please cite the GitHub repository directly and pin a commit hash for reproducibility.  A new Zenodo DOI will be minted at the v3.0 release.

To cite the [formalization of Birkhoff's HSP theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem):

```bibtex
@article{DeMeo:2021,
  author        = {De{M}eo, William and Carette, Jacques},
  title         = {A {M}achine-checked {P}roof of {B}irkhoff's {V}ariety {T}heorem
                   in {M}artin-{L}\"of {T}ype {T}heory},
  journal       = {CoRR},
  volume        = {abs/2101.10166},
  year          = {2021},
  eprint        = {2101.10166},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LO},
  url           = {https://arxiv.org/abs/2101.10166},
  note          = {Source code: \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}}
}
```

The current canonical setoid-based formalization of Birkhoff's theorem is in the [Setoid.Varieties.HSP][] module, with the proof anchor in the rendered HTML at [https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem).

---

## Credits

The `agda-algebras` library is developed and maintained by the *agda-algebras development team*:

+  [Jacques Carette][]
+  [William DeMeo][]

### Acknowledgements

We thank [Andreas Abel][], [Jeremy Avigad][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration, and encouragement.  Most of the mathematical results formalized in agda-algebras are well known; the novelty is in the formalization itself, which is mainly due to the contributors and acknowledgees listed above.

### References

The following Agda documentation and tutorials informed the development of agda-algebras:

+  Escardó, [Introduction to Univalent Foundations of Mathematics with Agda][]
+  Wadler, [Programming Languages Foundations in Agda][]
+  Bove and Dybjer, [Dependent Types at Work][]
+  Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
+  Norell and Chapman, [Dependently Typed Programming in Agda][]

The official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the open-source [Agda Standard Library][] source code are also indispensable.

---

<!-- Link definitions — kept at the bottom for readability above. -->

[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Agda Language Reference]: https://agda.readthedocs.io/en/latest/language/
[Agda standard library]: https://github.com/agda/agda-stdlib
[Agda Standard Library]: https://github.com/agda/agda-stdlib
[Agda User's Manual]: https://agda.readthedocs.io/en/latest/
[Agda Wiki]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Andreas Abel]: http://www.cse.chalmers.se/~abela/
[Andrej Bauer]: http://www.andrej.com/
[Clifford Bergman]: https://orion.math.iastate.edu/cbergman/
[Dependent Types at Work]: https://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf
[Dependently Typed Programming in Agda]: https://link.springer.com/chapter/10.1007/978-3-642-04652-0_5
[Formalization of Universal Algebra in Agda]: https://www.sciencedirect.com/science/article/pii/S1571066118300768
[Hyeyoung Shin]: https://hyeyoungshin.github.io/
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
[Jacques Carette]: https://www.cas.mcmaster.ca/~carette/
[Jeremy Avigad]: https://www.andrew.cmu.edu/user/avigad/
[Martín Escardó]: https://www.cs.bham.ac.uk/~mhe/
[Nix]: https://nixos.org/download.html
[Programming Languages Foundations in Agda]: https://plfa.github.io/
[Ralph Freese]: https://math.hawaii.edu/~ralph/
[Setoid.Varieties.HSP]: src/Setoid/Varieties/HSP.agda
[Siva Somayyajula]: https://cs.stanford.edu/~siva/
[Venanzio Capretta]: https://www.cs.nott.ac.uk/~pszvc/
[William DeMeo]: https://williamdemeo.github.io/
