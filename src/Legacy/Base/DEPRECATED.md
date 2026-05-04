---
layout: default
title : "Legacy.Base — Deprecation notice"
date : "2026-05-02"
author: "the agda-algebras development team"
---

# `Legacy.Base` — Deprecation Notice

The `Legacy.Base.*` modules in this directory descend from `src/Base/`, the
original "bare-types" development of universal algebra in agda-algebras.  As of
version 3.0, `Setoid/` is the **canonical** development tree (see
[`docs/adr/001-setoid-as-canonical.md`](../../../docs/adr/001-setoid-as-canonical.md)
for the full rationale).

`Base/` was moved here rather than deleted because three distinct categories of
modules live within it.  Each is described below; the distinction matters because
it tells users whether a given import is **discouraged**, **provisional**, or
**without planned replacement**.

## Three categories of legacy module

### Category A — Deprecated; a `Setoid/` analog already exists

These modules duplicate, in a non-fully-constructive setting, content that is
already formalized canonically in `Setoid/`.  **Do not** start new work against
these modules; **do** migrate existing imports to their `Setoid/` counterparts.
The bare-types style in these modules typically depends on postulates of
function extensionality and propositional extensionality that `Setoid/` retires
by construction.

Note on aggregator rows: `Legacy.Base.Relations`, `Legacy.Base.Functions`, and
`Legacy.Base.Varieties` are aggregator modules whose contents straddle Categories
A and B.  The "canonical replacement" column points at the corresponding canonical
aggregator, which covers most but not all of the legacy aggregator's submodules.
Users importing aggregators should consult the per-submodule rows in this table
and the Category-B table below to confirm coverage of specific submodules.

For users of these modules, the migration is mechanical when the concrete
setting works up to propositional equality: replace `Legacy.Base.X` with
`Setoid.X` and pass `Relation.Binary.PropositionalEquality.setoid A` (or the
appropriate setoid for your carrier) where a setoid argument is now expected.
This recovers the bare-types reading without committing the library to a
parallel abstract foundation.

| Legacy module                                 | Canonical replacement                    |
|-----------------------------------------------|------------------------------------------|
| `Legacy.Base.Algebras`                        | `Setoid.Algebras`                        |
| `Legacy.Base.Algebras.Basic`                  | `Setoid.Algebras.Basic`                  |
| `Legacy.Base.Algebras.Congruences`            | `Setoid.Algebras.Congruences`            |
| `Legacy.Base.Algebras.Products`               | `Setoid.Algebras.Products`               |
| `Legacy.Base.Functions`                       | `Setoid.Functions`                       |
| `Legacy.Base.Functions.Injective`             | `Setoid.Functions.Injective`             |
| `Legacy.Base.Functions.Inverses`              | `Setoid.Functions.Inverses`              |
| `Legacy.Base.Functions.Surjective`            | `Setoid.Functions.Surjective`            |
| `Legacy.Base.Homomorphisms`                   | `Setoid.Homomorphisms`                   |
| `Legacy.Base.Homomorphisms.Basic`             | `Setoid.Homomorphisms.Basic`             |
| `Legacy.Base.Homomorphisms.Factor`            | `Setoid.Homomorphisms.Factor`            |
| `Legacy.Base.Homomorphisms.HomomorphicImages` | `Setoid.Homomorphisms.HomomorphicImages` |
| `Legacy.Base.Homomorphisms.Isomorphisms`      | `Setoid.Homomorphisms.Isomorphisms`      |
| `Legacy.Base.Homomorphisms.Kernels`           | `Setoid.Homomorphisms.Kernels`           |
| `Legacy.Base.Homomorphisms.Noether`           | `Setoid.Homomorphisms.Noether`           |
| `Legacy.Base.Homomorphisms.Products`          | `Setoid.Homomorphisms.Products`          |
| `Legacy.Base.Homomorphisms.Properties`        | `Setoid.Homomorphisms.Properties`        |
| `Legacy.Base.Relations`                       | `Setoid.Relations` (partial — see note above; `Continuous` and `Properties` are tracked under Category B) |
| `Legacy.Base.Relations.Discrete`              | `Setoid.Relations.Discrete`              |
| `Legacy.Base.Relations.Quotients`             | `Setoid.Relations.Quotients`             |
| `Legacy.Base.Subalgebras`                     | `Setoid.Subalgebras`                     |
| `Legacy.Base.Subalgebras.Properties`          | `Setoid.Subalgebras.Properties`          |
| `Legacy.Base.Subalgebras.Subalgebras`         | `Setoid.Subalgebras.Subalgebras`         |
| `Legacy.Base.Subalgebras.Subuniverses`        | `Setoid.Subalgebras.Subuniverses`        |
| `Legacy.Base.Terms`                           | `Setoid.Terms`                           |
| `Legacy.Base.Terms.Basic`                     | `Setoid.Terms.Basic`                     |
| `Legacy.Base.Terms.Operations`                | `Setoid.Terms.Operations`                |
| `Legacy.Base.Terms.Properties`                | `Setoid.Terms.Properties`                |
| `Legacy.Base.Varieties`                       | `Setoid.Varieties`                       |
| `Legacy.Base.Varieties.Closure`               | `Setoid.Varieties.Closure`               |
| `Legacy.Base.Varieties.EquationalLogic`       | `Setoid.Varieties.EquationalLogic`       |
| `Legacy.Base.Varieties.FreeAlgebras`          | `Setoid.Varieties.FreeAlgebras`          |
| `Legacy.Base.Varieties.Preservation`          | `Setoid.Varieties.Preservation`          |
| `Legacy.Base.Varieties.Properties`            | `Setoid.Varieties.Properties`            |

### Category B — Pending port; no `Setoid/` analog yet

These modules contain mathematical content with **no canonical replacement at
the time of the M2-1 freeze**, but with a planned port scheduled in a later
milestone.  Importing from `Legacy.Base.*` is the **supported,
non-deprecated** way to use this content until the corresponding canonical
module exists.

When a Category-B module is ported, the row migrates to Category A in the same
PR that lands the port, and the legacy file gains a `{-# WARNING_ON_USAGE #-}`
pragma pointing to the new home.  The legacy module is removed in the
*following* minor release, never in the same release that introduces the
replacement; this gives downstream users one full minor cycle to migrate.

| Legacy module                              | Planned destination                              | Target milestone | Tracking issue |
|--------------------------------------------|--------------------------------------------------|------------------|----------------|
| `Legacy.Base.Adjunction`                   | TBD (`Setoid/`, `Classical/`, or `Overture/`)    | M2               | #305           |
| `Legacy.Base.Adjunction.Closure`           | as parent                                        | M2               | #305           |
| `Legacy.Base.Adjunction.Galois`            | as parent                                        | M2               | #305           |
| `Legacy.Base.Adjunction.Residuation`       | as parent                                        | M2               | #305           |
| `Legacy.Base.Categories`                   | TBD (decision part of #306)                      | M2               | #306           |
| `Legacy.Base.Categories.Functors`          | as parent                                        | M2               | #306           |
| `Legacy.Base.Complexity`                   | `Setoid.Complexity`                              | M9               | #307           |
| `Legacy.Base.Complexity.Basic`             | `Setoid.Complexity.Basic`                        | M9               | #307           |
| `Legacy.Base.Complexity.CSP`               | `Setoid.Complexity.CSP`                          | M9               | #307           |
| `Legacy.Base.Functions.Transformers`       | stdlib redirect or `Setoid.Functions.Transformers` (decision part of #310) | TBD | #310 |
| `Legacy.Base.Relations.Continuous`         | `Setoid.Relations.Continuous`                    | M9               | #308           |
| `Legacy.Base.Relations.Properties`         | `Setoid.Relations.Properties`                    | M2 follow-up     | #309           |
| `Legacy.Base.Structures`                   | `Classical/` (entire subtree superseded)         | M3               | #260           |
| `Legacy.Base.Structures.Basic`             | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Congruences`       | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.EquationalLogic`   | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Graphs`            | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Graphs0`           | (slated for removal; see M2-3)                   | M2-3             | #258           |
| `Legacy.Base.Structures.Homs`              | `Classical/`                                     | M3               | #260           |
| `Legacy.Base.Structures.Isos`              | `Classical/`                                     | M3               | #260           |
| `Legacy.Base.Structures.Products`          | `Classical/`                                     | M3               | #260           |
| `Legacy.Base.Structures.Sigma`             | `Classical/` (subsumed by Σ-typed core)          | M3               | #260           |
| `Legacy.Base.Structures.Sigma.Basic`       | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Sigma.Congruences` | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Sigma.Homs`        | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Sigma.Isos`        | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Sigma.Products`    | as above                                         | M3               | #260           |
| `Legacy.Base.Structures.Substructures`     | `Classical/`                                     | M3               | #260           |
| `Legacy.Base.Structures.Terms`             | `Classical/`                                     | M3               | #260           |
| `Legacy.Base.Varieties.Invariants`         | `Setoid.Varieties.Invariants`                    | TBD              | #311           |

### Category C — No replacement planned

These modules encode auxiliary infrastructure that the canonical `Setoid/`
foundation **retires by construction**.  In `Setoid/` the equivalence relation
is bundled into the algebra and operations are required to respect it; the
extensionality postulates and well-definedness lemmas these modules provide
are simply not needed.

For users with active dependencies on these modules, the migration is to
restate the surrounding development in `Setoid/` and let the equivalence
machinery do the work that extensionality was previously doing.  Where
propositional truncation (h-props, h-sets) is genuinely needed, prefer
stdlib's `Relation.Nullary.Reflects` and
`Relation.Binary.PropositionalEquality.Properties`, or pull the relevant
pieces into `Overture/` as that scope expands.

| Legacy module                          | Status                                                  |
|----------------------------------------|---------------------------------------------------------|
| `Legacy.Base.Equality`                 | No replacement planned; subsumed by `Setoid/`           |
| `Legacy.Base.Equality.Extensionality`  | No replacement planned; postulates retired by `Setoid/` |
| `Legacy.Base.Equality.Welldefined`     | No replacement planned; built into `Setoid/` algebra signatures |
| `Legacy.Base.Equality.Truncation`      | Possibly migrated to `Overture/` or replaced by stdlib equivalents; tracked separately |

## What you should do

+  **New code**.  Do not import from `Legacy.Base.*` for any module that has a
   canonical replacement (Category A) or whose replacement is being designed
   in another milestone (most of Category B).  For modules without one yet
   (Category B with an open tracking issue), importing from `Legacy.Base.*` is
   supported in the interim, but please subscribe to the corresponding
   tracking issue so you are notified when the port lands.
+  **Existing code**.  Begin migrating Category-A imports now.  The migration
   is typically mechanical: replace `Legacy.Base.X` with `Setoid.X` and pass
   `Relation.Binary.PropositionalEquality.setoid A` where a setoid is now
   expected.  See the migration recipe in the 3.0 `CHANGELOG.md` for examples.
+  **Contributors**.  New contributions to `Legacy.Base/*` are accepted only
   when they support the port-out workflow (e.g., extracting a lemma to make
   the canonical port cleaner).  For day-to-day development, work in
   `Setoid/`, `Classical/` (when it lands), or eventually `Cubical/`.

## Why preserve `Legacy.Base/` at all?

Three reasons:

1.  **Continuity for downstream users**.  v2.x users have imports from `Base.*`
    throughout their developments.  Renaming the module path to `Legacy.Base.*`
    is a breaking change, but a small one: a single sed across imports.
    Deleting these modules outright would force a full migration to `Setoid/`
    in lockstep with the v3.0 upgrade, which is a much larger undertaking than
    v3.0 itself should impose.
2.  **Reference and provenance**.  `Base/` contains the original ≡-based
    formulations of definitions and lemmas that were subsequently re-developed
    in `Setoid/`.  Keeping the legacy versions visible in the repository
    preserves a useful historical record and supports cross-comparison during
    review of `Setoid/`-side changes.
3.  **Provisional content**.  Categories B and C above.  Until each orphan is
    ported (or formally retired with a stdlib redirect), deleting
    `Legacy.Base/` would actively remove formalized mathematics from the
    library.  The freeze-but-retain policy is what lets M2-1 ship without
    blocking on milestones M3, M9, and beyond.

## Further reading

+  ADR-001 — [`docs/adr/001-setoid-as-canonical.md`](../../../docs/adr/001-setoid-as-canonical.md)
+  Migration guide — [`CHANGELOG.md`](../../../CHANGELOG.md) (3.0 entry)
+  Roadmap — [`docs/GITHUB_PROJECT.md`](../../../docs/GITHUB_PROJECT.md)


