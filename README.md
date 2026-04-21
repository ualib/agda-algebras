# agda-algebras

[![CI](https://github.com/ualib/agda-algebras/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/ualib/agda-algebras/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](./LICENSE)
[![Docs License: CC BY 4.0](https://img.shields.io/badge/Docs-CC_BY_4.0-lightgrey.svg)](./LICENSE-docs)
[![Agda 2.8.0](https://img.shields.io/badge/Agda-2.8.0-purple.svg)](https://github.com/agda/agda/releases/tag/v2.8.0)
[![stdlib 2.3](https://img.shields.io/badge/stdlib-2.3-orange.svg)](https://github.com/agda/agda-stdlib/releases/tag/v2.3)

A formalization of universal algebra in [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php), built on the [Agda standard library](https://github.com/agda/agda-stdlib).

**Status.** Version 3.0 is under active development on `master`. The library currently targets Agda 2.8.0 and standard-library 2.3. Expect breaking changes until 3.0 is released; see [docs/GITHUB_PROJECT.md](docs/GITHUB_PROJECT.md) for the milestone plan.

The **previous** version (called `UALib`, built against [TypeTopology](https://github.com/martinescardo/TypeTopology)) is no longer maintained but remains available:

+  Source: [https://gitlab.com/ualib/ualib.gitlab.io](https://gitlab.com/ualib/ualib.gitlab.io)
+  Docs: [https://ualib.gitlab.io](https://ualib.gitlab.io)

---

## Documentation

HTML documentation for the current line is served at [https://ualib.org](https://ualib.org).

The library's structure, design decisions, and roadmap are documented in [docs/GITHUB_PROJECT.md](docs/GITHUB_PROJECT.md).

---

## Installation

The recommended development environment is [Nix](https://nixos.org/download.html).

Inside the main directory of a clone of the `agda-algebras` repository, enter

```bash
nix develop
```

This pins Agda 2.8.0 and standard-library 2.3 automatically, writes a project-local Agda library configuration, and bypasses any Agda or standard-library versions you may have installed elsewhere on the machine.

Once in the Nix shell, enter

```bash
make check   # type-check the library
make html    # build clickable HTML to ./html/
```

Contributors who prefer not to use Nix should install Agda 2.8.0 and standard-library 2.3 by other means (see [docs/INSTALL.md](docs/INSTALL.md) for options) and register them in `~/.config/agda/libraries` before running `make check`.

---

## Requirements

+  [Agda](https://agda.readthedocs.io) 2.8.0 (released 2025-07)
+  [standard-library](https://github.com/agda/agda-stdlib) 2.3 (released 2025-08)
+  GNU Make

Older versions of either component are **not** supported on the `master` branch.

---

## Contributing

Contributions are welcome.  See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the development workflow and conventions, and [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) for community standards.  The style guide ([`docs/STYLE_GUIDE.md`](docs/STYLE_GUIDE.md)) is being drafted as part of Milestone 1; see [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md) for the full roadmap.

For questions about mathematical content or large design changes, open a GitHub issue
labeled `design-discussion` before writing code.

---

## Licensing

agda-algebras is dual-licensed to match the dual nature of the project:

+  **Source code** (under `src/`) is licensed under the [Apache License, Version 2.0](./LICENSE).  This is a permissive, industry-standard software license compatible with essentially all other open-source licenses and commercial use.

+  **Documentation, papers, and tutorials** (under `docs/`) are licensed under the [Creative Commons Attribution 4.0 International License](./LICENSE-docs).  CC BY 4.0 is the standard license for academic-style written material; it permits sharing and adaptation with attribution.

If you are redistributing or building on agda-algebras, please respect both licenses for their respective parts of the repository.

---

## Credits

The `agda-algebras` library is developed and maintained by the *agda-algebras development team*:

+  [Jacques Carette][]
+  [William DeMeo][]

### Acknowledgements

We thank [Andreas Abel][], [Jeremy Avigad][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration, and encouragement.

Most of the mathematical results formalized in agda-algebras are well known. The novelty is in the Agda formalization itself, which is mainly due to the contributors listed above.

### References

The following Agda documentation and tutorials informed the development of agda-algebras:

+  Escardó, [Introduction to Univalent Foundations of Mathematics with Agda][]
+  Wadler, [Programming Languages Foundations in Agda][]
+  Bove and Dybjer, [Dependent Types at Work][]
+  Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
+  Norell and Chapman, [Dependently Typed Programming in Agda][]

The official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the open-source [Agda Standard Library][] source code are also indispensable.

---

## Citing

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.5765793.svg)](https://doi.org/10.5281/zenodo.5765793)

To cite the [agda-algebras][] software library in a publication or on a web page, please use the following BibTeX entry:

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

To cite the [formalization of Birkhoff's HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem), please use the following BibTeX entry:

```bibtex
@article{DeMeo:2021,
 author        = {De{M}eo, William and Carette, Jacques},
 title         = {A {M}achine-checked {P}roof of {B}irkhoff's {V}ariety {T}heorem
                  in {M}artin-{L}\"of {T}ype {T}heory}, 
 journal       = {CoRR},
 volume        = {abs/2101.10166},
 year          = {2021},
 eprint        = {2101.2101.10166},
 archivePrefix = {arXiv},
 primaryClass  = {cs.LO},
 url           = {https://arxiv.org/abs/2101.10166},
 note          = {Source code: \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}}
}
```

If you're looking for the latest (setoid-based) formalization of Birkhoff's Theorem, see the [Proof of the HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) in the html documentation, or the source code of the [Setoid.Varieties.HSP][] module.

---

<!-- Link definitions — keep at bottom for readability above -->
[agda-algebras]: https://github.com/ualib/agda-algebras
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Agda Language Reference]: https://agda.readthedocs.io/en/latest/language/
[Agda Standard Library]: https://github.com/agda/agda-stdlib
[Agda Tools]: https://agda.readthedocs.io/en/latest/tools/
[Agda Tutorial]: https://people.inf.elte.hu/pgj/agda/tutorial/Index.html
[Agda User's Manual]: https://agda.readthedocs.io/en/latest/
[Agda Wiki]: https://wiki.portal.chalmers.se/agda/pmwiki.php

[Andreas Abel]: http://www.cse.chalmers.se/~abela/
[Andrej Bauer]: http://www.andrej.com/
[Clifford Bergman]: https://orion.math.iastate.edu/cbergman/
[Hyeyoung Shin]: https://hyeyoungshin.github.io/
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
[Jacques Carette]: https://www.cas.mcmaster.ca/~carette/
[Jeremy Avigad]: https://www.andrew.cmu.edu/user/avigad/
[Martín Escardó]: https://www.cs.bham.ac.uk/~mhe/
[Ralph Freese]: https://math.hawaii.edu/~ralph/
[Siva Somayyajula]: https://cs.stanford.edu/~siva/
[Venanzio Capretta]: https://www.cs.nott.ac.uk/~pszvc/
[William DeMeo]: https://williamdemeo.github.io/

[Dependent Types at Work]: https://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf
[Dependently Typed Programming in Agda]: https://link.springer.com/chapter/10.1007/978-3-642-04652-0_5
[Formalization of Universal Algebra in Agda]: https://www.sciencedirect.com/science/article/pii/S1571066118300768
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
[Programming Languages Foundations in Agda]: https://plfa.github.io/
[Setoid.Varieties.HSP]: src/Setoid/Varieties/HSP.agda

