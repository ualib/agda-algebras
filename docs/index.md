---
title: The Agda Universal Algebra Library
hide:
  - navigation
  - toc
---

<div class="ualib-hero" markdown>

# The Agda Universal Algebra Library

<p class="ualib-tagline" markdown>
A constructive formalization of **universal algebra** in dependent type theory —
from signatures, algebras, and homomorphisms to a fully machine-checked proof of
**Birkhoff's variety theorem** — written in literate [Agda][] and type-checked on
every commit.
</p>

<div class="ualib-formula">𝖵(𝒦) = 𝖧𝖲𝖯(𝒦)</div>

<div class="ualib-cta" markdown>
[Get started](install.md){ .md-button .md-button--primary }
[Browse the library](/Setoid/){ .md-button }
[:simple-github: GitHub](https://github.com/ualib/agda-algebras){ .md-button }
</div>

</div>

<div class="grid cards" markdown>

-   :material-rocket-launch-outline:{ .lg .middle } &nbsp; **Quickstart**

    ---

    From a clean checkout to a green build in three commands with the pinned
    [Nix][] toolchain — Agda 2.8.0 and standard-library 2.3, reproducibly.

    [:octicons-arrow-right-24: Installation](install.md)

-   :material-cube-outline:{ .lg .middle } &nbsp; **The canonical library**

    ---

    `Setoid/`{.AgdaModule} is the canonical development tree: algebras as
    setoids, with every definition stated up to the carrier's equivalence so
    the eventual Cubical port is mechanical.

    [:octicons-arrow-right-24: Setoid tree](/Setoid/)

-   :material-check-decagram-outline:{ .lg .middle } &nbsp; **Birkhoff's HSP theorem**

    ---

    A class of algebras is a [variety][HSP Theorem] exactly when it is closed
    under homomorphic images, subalgebras, and products — proved constructively,
    in full.

    [:octicons-arrow-right-24: The HSP theorem](/Setoid/Varieties/HSP/)

-   :material-school-outline:{ .lg .middle } &nbsp; **A guided proof**

    ---

    [`Demos.HSP`][Demos.HSP] is a single self-contained module that walks
    through the variety theorem end to end — the companion to the TYPES 2021
    paper, ideal for teaching.

    [:octicons-arrow-right-24: Read the demo](/Demos/HSP/)

-   :material-map-outline:{ .lg .middle } &nbsp; **Where it's going**

    ---

    The 3.0 reconstruction is organized into milestones M1–M10 — the classical
    structures layer, the Cubical track, complexity extensions, and corpus
    artifacts for machine learning.

    [:octicons-arrow-right-24: Roadmap](GITHUB_PROJECT.md)

-   :material-heart-outline:{ .lg .middle } &nbsp; **Get involved**

    ---

    Bug reports, design discussions, and pull requests are welcome.  The
    contributor's guide explains which tree new work belongs in and the
    house style.

    [:octicons-arrow-right-24: Contributing](contributing.md)

</div>

## What is this?

`agda-algebras`{.AgdaModule} is a library of universal algebra developed in
[Agda][], a dependently typed programming language and proof assistant.  It
defines the core objects of the subject — [signatures][Overture.Signatures],
[algebras][Setoid.Algebras.Basic], [homomorphisms][Setoid.Homomorphisms],
[terms][Setoid.Terms], [subalgebras][Setoid.Subalgebras], and
[varieties][Setoid.Varieties] — together with the equational logic that
underlies them, and it carries each construction all the way to a fully
constructive, machine-checked proof of [Birkhoff's HSP theorem][Setoid.Varieties.HSP].

It is developed with two audiences in mind: as a working substrate for research
in universal algebra, and as a high-quality, vetted training corpus of Agda
proofs for machine learning on formal mathematics.  Every page you see here is
rendered directly from a literate `.lagda.md`{.AgdaModule} source that the
type-checker reads — prose and proof live in one file, and the proof you read
is the proof that compiles.

!!! note "Reading the code"

    Inline names are colour-coded by their Agda role — a
    `function`{.AgdaFunction}, a `Record`{.AgdaRecord}, a
    `constructor`{.AgdaInductiveConstructor}, a `Datatype`{.AgdaDatatype}, a
    bound `variable`{.AgdaBound}.  Use the search box (press <kbd>/</kbd>) to
    jump to any module, and the **edit** pencil on any page to view its source
    on GitHub.
