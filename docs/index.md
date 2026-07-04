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
from signatures, algebras, and homomorphisms to a machine-checked proof of
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

<div class="ualib-stats">
  <div class="ualib-stat"><span class="ualib-stat__num">283</span><span class="ualib-stat__label">literate modules</span></div>
  <div class="ualib-stat"><span class="ualib-stat__num">38k</span><span class="ualib-stat__label">lines of Agda</span></div>
  <div class="ualib-stat"><span class="ualib-stat__num">100%</span><span class="ualib-stat__label">machine-checked</span></div>
  <div class="ualib-stat"><span class="ualib-stat__num">2.8.0</span><span class="ualib-stat__label">Agda · stdlib 2.3</span></div>
</div>

## Featured results

Landmark theorems of universal algebra, each formalized and type-checked here —
follow a face to the proof.

<div class="ualib-carousel" data-autoplay="4000" aria-roledescription="carousel" aria-label="Featured results">
<div class="ualib-carousel__viewport">
<div class="ualib-carousel__track">

  <a class="ualib-figure" href="/Setoid/Congruences/Lattice/">
    <span class="ualib-portrait">
    <img src="/assets/portraits/Dedekind.jpeg" alt="Richard Dedekind"></span>
    <span class="ualib-figure__body">
      <span class="ualib-figure__result">Congruence lattices</span>
      <span class="ualib-figure__who">Richard Dedekind · 1831–1916</span>
    </span>
  </a>

  <a class="ualib-figure" href="/Setoid/Homomorphisms/Noether/">
    <span class="ualib-portrait">
    <img src="/assets/portraits/Noether.jpeg" alt="Emmy Noether"></span>
    <span class="ualib-figure__body">
      <span class="ualib-figure__result">Homomorphism theorems</span>
      <span class="ualib-figure__who">Emmy Noether · 1882–1935</span>
    </span>
  </a>

  <a class="ualib-figure" href="/Setoid/Subalgebras/Subdirect/Irreducible/">
    <span class="ualib-portrait">
    <img src="/assets/portraits/Birkhoff_alt.jpeg" alt="Garrett Birkhoff"></span>
    <span class="ualib-figure__body">
      <span class="ualib-figure__result">Subdirect representation</span>
      <span class="ualib-figure__who">Garrett Birkhoff · 1911–1996</span>
    </span>
  </a>

  <a class="ualib-figure" href="/Setoid/Varieties/Maltsev/">
    <span class="ualib-portrait">
    <img src="/assets/portraits/Malcev.jpeg" alt="Anatoly Maltsev"></span>
    <span class="ualib-figure__body">
      <span class="ualib-figure__result">Maltsev conditions</span>
      <span class="ualib-figure__who">Anatoly Maltsev · 1909–1967</span>
    </span>
  </a>

  <a class="ualib-figure" href="/Setoid/Varieties/HSP/">
    <span class="ualib-portrait">
    <img src="/assets/portraits/Birkhoff_alt.jpeg" alt="Garrett Birkhoff"></span>
    <span class="ualib-figure__body">
      <span class="ualib-figure__result">Birkhoff's HSP theorem</span>
      <span class="ualib-figure__who">Garrett Birkhoff · 1911–1996</span>
    </span>
  </a>

</div>
</div>
<div class="ualib-carousel__dots"></div>
</div>


## What's formalized

The classical-structures layer builds the algebraic hierarchy on the
universal-algebra core.  Each row is a structure (follow it to its module); each
column an equational axiom it satisfies.

<div class="ualib-matrix-wrap" markdown>

<table class="ualib-matrix">
<thead>
<tr>
  <th>Structure</th><th>Assoc.</th><th>Comm.</th><th>Identity</th>
  <th>Inverse</th><th>Idemp.</th><th>Absorp.</th><th>Distrib.</th>
</tr>
</thead>
<tbody>
<tr><th><a href="/Classical/Structures/Magma/">Magma</a></th><td></td><td></td><td></td><td></td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/Semigroup/">Semigroup</a></th><td class="yes">✓</td><td></td><td></td><td></td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/CommutativeSemigroup/">Comm. semigroup</a></th><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/Monoid/">Monoid</a></th><td class="yes">✓</td><td></td><td class="yes">✓</td><td></td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/CommutativeMonoid/">Comm. monoid</a></th><td class="yes">✓</td><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/Group/">Group</a></th><td class="yes">✓</td><td></td><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/AbelianGroup/">Abelian group</a></th><td class="yes">✓</td><td class="yes">✓</td><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/Semilattice/">Semilattice</a></th><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td class="yes">✓</td><td></td><td></td></tr>
<tr><th><a href="/Classical/Structures/Lattice/">Lattice</a></th><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td></td><td class="yes">✓</td><td></td></tr>
<tr><th><a href="/Classical/Structures/DistributiveLattice/">Distrib. lattice</a></th><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td></td><td class="yes">✓</td><td class="yes">✓</td></tr>
<tr><th><a href="/Classical/Structures/Ring/">Ring</a></th><td class="yes">✓</td><td class="yes-2">✓</td><td class="yes">✓</td><td class="yes-2">✓</td><td></td><td></td><td class="yes">✓</td></tr>
<tr><th><a href="/Classical/Structures/CommutativeRing/">Comm. ring</a></th><td class="yes">✓</td><td class="yes">✓</td><td class="yes">✓</td><td class="yes">✓</td><td></td><td></td><td class="yes">✓</td></tr>
</tbody>
</table>

</div>

<small>Rings carry two operations; <span style="color:var(--chalk-coral)">coral ✓</span> marks an axiom of the additive group, plain ✓ the shared/multiplicative axioms.</small>

## Explore

<div class="grid cards" markdown>

-   :material-rocket-launch-outline:{ .lg .middle } &nbsp; **Quickstart**

    ---

    Clean checkout to green build in three commands with the pinned [Nix][] toolchain.

    [:octicons-arrow-right-24: Installation](install.md)

-   :material-cube-outline:{ .lg .middle } &nbsp; **The canonical library**

    ---

    `Setoid/`{.AgdaModule} — algebras as setoids, every definition stated up to the carrier's equivalence.

    [:octicons-arrow-right-24: Setoid tree](/Setoid/)

-   :material-code-tags:{ .lg .middle } &nbsp; **Classic Agda HTML**

    ---

    Prefer the bare agda-html view?  The clickable, fully-highlighted source with `Everything` as index.

    [:octicons-arrow-right-24: Browse the source](/classic/Everything.html)

-   :material-map-outline:{ .lg .middle } &nbsp; **Where it's going**

    ---

    The 3.0 reconstruction in milestones M1–M10 — classical structures, the Cubical track, corpus artifacts.

    [:octicons-arrow-right-24: Roadmap](GITHUB_PROJECT.md)

</div>

## What is this?

`agda-algebras`{.AgdaModule} is a library of universal algebra developed in
[Agda][], a dependently typed programming language and proof assistant.  It
defines the core objects of the subject — [signatures][Overture.Signatures],
[algebras][Setoid.Algebras.Basic], [homomorphisms][Setoid.Homomorphisms],
[terms][Setoid.Terms], [subalgebras][Setoid.Subalgebras], and
[varieties][Setoid.Varieties] — together with the equational logic that
underlies them, and carries each construction all the way to a fully
constructive, machine-checked proof of [Birkhoff's HSP theorem][Setoid.Varieties.HSP].

It is developed with two audiences in mind: as a working substrate for research
in universal algebra, and as a high-quality, vetted training corpus of Agda
proofs for machine learning on formal mathematics.  Every page is rendered
directly from a literate `.lagda.md`{.AgdaModule} source the type-checker reads —
the proof you read is the proof that compiles.

!!! note "Reading the code"

    In code blocks, every Agda token is coloured by its role and **links to its
    definition** — click a `function`{.AgdaFunction}, a `Record`{.AgdaRecord}, a
    `constructor`{.AgdaInductiveConstructor} to jump to where it is defined.
    Press <kbd>/</kbd> to search any module; use the **edit** pencil to view a
    page's source on GitHub.
