<!-- File: scripts/gap/flrp/README.md -->

# FLRP GAP engine — subgroup-interval search (issue #487)

The group-theory engine of the FLRP computational campaign (tracker #483, roadmap § 5.A.1).  These GAP scripts hunt for a target finite lattice as an *upper interval* `[H, G]` in the subgroup lattice of a finite group, using A. Hulpke's intermediate-subgroup routine `IntermediateSubgroups(G, H)`, across the GAP group libraries (SmallGroups first, then the transitive- and primitive-groups libraries).

This tree is the group-side mirror of the WP-6 emitter tree `scripts/python/flrp/`.  The two families divide labour cleanly:

+  **GAP is the untrusted group engine.**  It computes intervals, cosets, and versions, and emits *deterministic JSON artifacts* — nothing more.  Its raw logs stay in a scratchpad, out of `src/` and out of git (roadmap § 6).
+  **Python owns the lattice bookkeeping.**  A thin bridge reuses the one canonical implementation already in `scripts/python/flrp/` — `eqsearch.tables_from_leq` for meet/join tables, `lattice.py` for the isomorphism test, `emit_agda.py` for certificate emission — rather than re-deriving any of it in GAP.
+  **Agda re-checks everything.**  A found interval enters the library only as an Agda-checked `Representableᵈ` witness: for indices within the renderer's literal cap, by dumping the coset action into a claim file for `emit_agda.py` (the direct-certificate route); for larger indices, through the WP-3 bridge `FLRP.Bridge` (issue #454, merged).

## The environment

GAP is not in the default flake shell; it lives in a dedicated devshell so the heavier group libraries never burden `make check`.  Enter it and run the smoke test:

```sh
nix develop .#gap
make gap-smoke          # SmallGroup(216,153) and TransitiveGroup(8,1) load; provenance prints
```

`nix develop .#gap` provides GAP with `packageSet = "standard"`, which bundles the libraries this issue needs — `smallgrp` (SmallGroups), `transgrp` (transitive groups), `primgrp` (primitive groups) — as required packages.  Every emitted artifact records the GAP and library versions (`lib/provenance.g`), so `make check` and `make flrp-test` never depend on GAP's presence and results are reproducible.

Scripts are run **from the repo root** (like the Python tools), so their `Read("scripts/gap/flrp/…")` paths resolve.

## Layout

```
scripts/gap/flrp/
  lib/json.g          # deterministic JSON writer (no external package dependency)
  lib/provenance.g    # GAP + smallgrp/transgrp/primgrp version stamp
  bin/smoke.g         # deliverable 1: the shell smoke test
  out/                # committed JSON artifacts only (raw logs never land here)
```

Forthcoming on this branch (issue #487): `lib/interval.g` (interval poset via `IntermediateSubgroups`, core-free normalization), `lib/search.g` (the slice-driven search), `lib/cosets.g` (coset-action tables for the direct route), `bin/pentagon216.g` (deliverable 3), `bin/search.g` (deliverables 2/5), `bin/scan_transitive.g` (deliverable 4), and the Python bridge `scripts/python/flrp/gap_interval.py`.

## Artifact schema

Two deterministic, version-stamped JSON formats, echoing the `flrp-eqsearch v1` / `flrp-cert v1` conventions of the Python tree.

`flrp-gap-interval v1` — one found interval `[H, G]`:

```jsonc
{
  "format": "flrp-gap-interval v1",
  "date": "2026-07-24",
  "engine": { "gap": "4.15.1",
              "libraries": { "smallgrp": "…", "transgrp": "…", "primgrp": "…" } },
  "group":    { "source": "SmallGroup", "id": [216, 153], "order": 216,
                "structureDescription": "(C3 x C3) : SL(2,3)" },   // annotation; id is canonical
  "subgroup": { "order": 6, "index": 36, "coreFree": true, "coreOrder": 1,
                "generators": "…" },                 // H
  "interval": { "size": 5,                            // |[H, G]|, endpoints included
                "covers": [[0,1],[0,2],[1,3],[2,4],[3,4]],   // Hulpke, 0 = H … top = G
                "meet": [[…]], "join": [[…]] },       // canonical, via tables_from_leq
  "match":    { "target": "N5", "isomorphic": true, "witness": [0,1,2,3,4] },
  "cosetAction": {                                    // present when computed
    "points": 36, "directCertifiable": false,         // directCertifiable = index ≤ 31
    "generators": [ { "name": "a", "table": [ … ] }, … ] }   // unary maps on the cosets
}
```

`flrp-gap-search v1` — one search run: the same `engine` stamp, the `config` (slice + target), a `scanned` count, a `hits` list of `flrp-gap-interval v1` records, and a `verdict`.  This is the deliverable-4 negative report and the deliverable-2/5 census wrapper.
