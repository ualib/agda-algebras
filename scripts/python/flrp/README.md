<!-- File: scripts/python/flrp/README.md -->

# FLRP certificate emitters (WP-6)

The engine side of the WP-6 certificate pipeline (issue #457; design fixed in `docs/notes/flrp-wp6-freese-certificates.md`).  These scripts compute congruence lattices of finite algebras with R. Freese's `cg2` worklist algorithm, record the **Freese traces** that justify every block merge, and emit a literate Agda module whose type-checking re-verifies everything through the search-free checkers of `Setoid.Congruences.Certificates` and the `Representableᵈ` assembly of `FLRP.Certificates`.  Nothing computed here is trusted: the scripts are untrusted engines, and the emitted module is certificate data plus checker invocations.

+  `cg2.py` — the instrumented `cg2` worklist (arity-general): union-find, justified merges, normal-form parent vectors.
+  `lattice.py` — whole lattices: principal congruences for every carrier pair, closure under joins, meet and join tables, and the (bounded, engine-side) isomorphism match against the claimed target lattice.
+  `emit_agda.py` — the CLI: claim file in, `.lagda.md` module and audit JSON out.
+  `eqsearch.py` — the search side (issue #486), converse in direction to the emitters: given a target lattice, find its sublattice copies in `Eq(n)` with bounds at the diagonal and the total relation, classify them up to relabeling, and run the Snow closure test on each class; a closed class yields the witness algebra `⟨X, M⟩` and a ready-made claim file for the emitter.
+  `eqfast.py` — the optional numpy backend for the search side (`--fast`): identical semantics and byte-identical reports, vectorized kernels; what makes `Eq(8)` a minutes-scale sweep.
+  `slr_catalog.py` — the transcription stage of issue #485: parse the SmallLatticeReps manuscript's § 6 catalog (`docs/papers/fin-lat-rep/SmallLatticeReps.tex`) — Hasse diagrams from the tikz coordinates and edges, value tables from the array blocks — into claim files, audits, and certificate modules; see § SmallLatticeReps below.
+  `inputs/` — claim files (`inputs/slr/` for the catalog); `out/` — audit copies of emitted certificates (`out/slr/` likewise) and citable sweep reports.

## Usage

```sh
python3 scripts/python/flrp/emit_agda.py scripts/python/flrp/inputs/v4_regular_m3.json
```

This writes `src/<module path>/<name>.lagda.md` — the claim file's dotted `module` prefix decides the placement, `FLRP.Certificates.Pilot` by default — (the only file placement needed — the generated `Everything` aggregator picks it up, so `make check` verifies it with no manual editing) and `scripts/python/flrp/out/<name>.cert.json` (the raw certificate, kept outside `src/` per roadmap § 6).  Output is a deterministic function of the input; pin the input's `date` field for byte-stable re-emission.

## The claim file (`flrp-cert-input v1`)

```json
{
  "format": "flrp-cert-input v1",
  "name": "V4RegularM3",              // Agda-name; module <module>.<name>
  "date": "2026-07-22",               // optional; defaults to today (breaks byte-stability)
  "module": "FLRP.Certificates.Pilot",// optional namespace prefix (this is the default)
  "provenance": "…",                  // optional Markdown paragraph for the module header
  "algebra": {
    "name": "human-readable provenance",
    "card": 4,                        // carrier is range(card)
    "operations": [                   // value tables, nested lists of depth arity
      { "name": "a", "arity": 1, "table": [1, 0, 3, 2] }
    ]
  },
  "lattice": {                        // the claimed congruence lattice, by tables
    "name": "M3",
    "size": 5,
    "meet": [[0, 0, "..."]],          // size × size, meet[k][l] = k ∧ l
    "join": [[0, 1, "..."]]
  }
}
```

The claim file *is* the human-auditable statement: "the congruence lattice of this algebra is isomorphic to this lattice".  The emitter fails with a `CertificateError` if the claim is false (wrong congruence count, or no table-respecting bijection).

## The certificate (`flrp-cert v1`, the audit JSON)

The tool-interchange format any future emitter (instrumented UACalc, GAP, SAT decoders) should produce; `emit_agda.py`'s rendering half can then be reused as is.  All indices are 0-based.

+  `parts` — the congruence list as parent vectors in **Freese normal form** (every index points directly at the least element of its block), indexed by the target lattice's carrier, so `meet`/`join` are literally the target's tables.
+  `bot` — the position of the diagonal congruence.
+  `prin`, `prinTraces` — for every carrier pair `(i, j)`, the position of `Cg(i, j)` and the Freese trace of its `cg2` run (seed list: the one pair).
+  `meet`, `join`, `joinTraces` — the tables; each join entry's trace comes from a `cg2` run seeded with both arguments' forest edges (each non-root index ascending, paired with its root — this must match the Agda-side `forestEdges` order).
+  A trace entry is `{"lhs": u, "rhs": v, "seed": s}` (position `s` of the seed list) or `{"lhs": u, "rhs": v, "op": f, "coord": c, "frozen": [...], "ref": r}` — the pair is the image of trace entry `r` (an **absolute** 0-based position; the Agda renderer converts to the schema's backward offsets) under operation `f` with coordinate `c` moving and the remaining coordinates frozen (`frozen` has full arity length; the entry at `coord` is dead data, written as 0).

## The search side (`eqsearch.py`)

```sh
python3 scripts/python/flrp/eqsearch.py TARGET.json N [--json REPORT.json]
python3 scripts/python/flrp/eqsearch.py scripts/python/flrp/inputs/l7_lattice.json 6
```

`TARGET.json` is either a bare lattice stanza (`name`/`size`/`meet`/`join`, exactly the `lattice` field of a claim file) or a full claim file, and `N` is the ground-set size; `inputs/l7_lattice.json` ships the `L7` tables, so the second line reproduces the `Eq(6)` census of `docs/notes/flrp-l7-eq6.md` directly.  The tool prints, and optionally writes as deterministic JSON (`flrp-eqsearch v1`), the census of sublattice copies of the target in `Eq(N)` with bounds pinned at the diagonal and the total relation — the only copies that can be congruence lattices — classified up to relabeling of the points, each class with its Snow closure verdict: the order of the preserving group, the size of the full preserving monoid `M`, and `|Inv(M)|`.  A class is **closed** when `Inv(M)` is exactly the copy; the congruence lattice of an arbitrary algebra is determined by its unary polynomials, so a closed class means the unary algebra `⟨X, M⟩` has the target as its congruence lattice — `closed_class_algebra` and `claim_input` package that witness as a claim file, closing the loop *lattice ⇒ search ⇒ algebra ⇒ certificate*.  Conversely, if no class on `n` points is closed, no algebra on `n` points represents the target.

Provenance: this generalizes the 2026-07-22 `L7` session (issue #484) — minimal sublattice representation of `L7` in `Eq(6)`, two classes up to relabeling, and closure failing on 6, 7, and 8 points, so any representation of `L7` as a congruence lattice needs at least 9 points.  Those numbers are pinned as regression tests, and the full `Eq(8)` result (4,112,640 copies, 108 classes, none closed — `docs/notes/flrp-l7-eq6.md` § 5) is committed as the citable report `out/l7_eq8_report.json`.

**The fast backend**.  `--fast` routes the survey through `eqfast.py`: numpy-vectorized meet/join table construction, mask-arithmetic candidate filtering over the same assignment plan as the pure search, and per-class vectorized orbit generation, with closure verdicts delegated to the pure implementation so the backends cannot drift where it matters.  The reports are byte-identical to the pure engine's (pinned by `test_eqfast.py`).  numpy is deliberately not a dependency of the pure tools and is not in the nix dev shell; install it any convenient way (for instance `python3 -m venv .venv && .venv/bin/pip install numpy`) to use `--fast`.  Measured scale on one core: `Eq(6)` in ~2 s and `Eq(7)` in ~30 s (versus about five minutes for `Eq(7)` with the pure engine), while the committed `Eq(8)` run took about three hours: the generic height-ordered assignment plan defers join constraints, so intermediate prefix counts balloon at eight points.  A constraint-density-guided assignment order (place an element as soon as it is the meet or join of placed ones) is the known fix — a schedule-specific engine with exactly that order ran `Eq(8)` in minutes — and is follow-up work on #486, as is the blocked-table build that `Eq(9)` (`Bell(9) = 21,147`, ~1.8 GB of tables at `int16`) needs.

## The SmallLatticeReps catalog (`slr_catalog.py`, issue #485)

```sh
make flrp-slr           # regenerate inputs/slr/, out/slr/, and the SLR modules
python3 scripts/python/flrp/slr_catalog.py --check        # committed copies re-derive?
python3 scripts/python/flrp/slr_catalog.py --dictionary   # naming table (docs/notes/flrp-slr-naming.md)
python3 scripts/python/flrp/slr_catalog.py --census       # status table (docs/notes/flrp-slr-census.md)
python3 scripts/python/flrp/slr_catalog.py --diagnose 28  # the erratum log's reproducible core
```

The catalog tool derives every artifact mechanically from the manuscript's LaTeX source: Hasse diagrams from the tikz node coordinates and drawn edges (oriented upward by y-coordinate, rejected unless they are exactly the covers of a bounded lattice order), value tables from the array blocks, meets and joins via `eqsearch.tables_from_leq`.  Every entry whose printed claim survives the engine audit becomes a certificate module under `src/FLRP/Certificates/SmallLatticeReps/` (`SLRnn`, manuscript numbering) with its audit JSON committed alongside; entries without printed algebras become bare lattice stanzas (`slrNN_lattice.json`, ready-made `eqsearch.py` targets).  A printed claim the engine *refutes* is recorded in `ERRATA` and the census note's erratum log — never "fixed" to pass; `B28` is the standing example.  The naming dictionary (including the manuscript-`L10`-is-library-`L7` clash) is `docs/notes/flrp-slr-naming.md`; the per-entry status is `docs/notes/flrp-slr-census.md`.

## Testing

```sh
make flrp-test          # from the repo root
```

`test_flrp.py` runs three layers of tests: engine unit tests (worklist, normal forms, lattice construction, target matching, renderer guard rails), a Python **mirror of the Agda checker's obligations** (C1 trace soundness, C2 replay coverage, C3 seed containment) over every trace of the pilot certificate — an engine-side regression tripwire only, never a substitute for the checker — and **golden round-trip tests**: re-emitting the committed pilot input must reproduce the committed `.lagda.md` module and audit JSON byte for byte.  Negative tests confirm that a false claim (wrong lattice, corrupted join table) raises a `CertificateError` and that the renderer rejects out-of-scope inputs.

`test_eqsearch.py` covers the search side: the partition kernel cross-validated against brute force (the backtracking monoid enumeration versus a full `n^n` scan), the `M3`-on-4-points census with its closed matchings class flowing all the way to a checked certificate, and the pinned `L7` session results.  The `Eq(7)` sweep (about five minutes) runs only with `FLRP_EQSEARCH_SLOW=1`.

`test_slr_catalog.py` guards the catalog transcription: shape and carrier pins for all 35 entries, the naming identifications (`L1 = N5` by hand-pinned tables, `L2` equal to the pilot's `M3`, `L10` equal to library `L7` under exactly one relabeling), the `B28` erratum with cg2-independent congruence verification, parser guard rails on synthetic inputs, and a golden sweep re-deriving every committed catalog artifact byte for byte.

`test_eqfast.py` pins the fast backend to the pure one — equal tables, byte-identical survey reports on `M3`/`Eq(4)` and `L7`/`Eq(6)`, the `Eq(7)` census in seconds — and, behind `FLRP_EQSEARCH_SLOW=1`, re-runs the `Eq(8)` sweep and checks its output against the committed `out/l7_eq8_report.json` byte for byte.  All of it skips cleanly when numpy is absent.

The Agda side needs no separate harness: the emitted pilot module is part of the library, so `make check` — the repository's single test gate, exactly what CI runs — *is* the end-to-end verification of the certificate.  To see the falsification story in action, flip any table entry or trace index in the emitted module and re-run `agda src/FLRP/Certificates/Pilot/V4RegularM3.lagda.md`: the corresponding `from-yes` decision computes to `no` and compilation fails.

## Scope notes

+  The `cg2` engine is arity-general; the Agda renderer targets **unary signatures** (`Sig-Unary`, i.e. G-sets and their kin — the Pálfy–Pudlák frontier).  `Fin` literals come from `Data.Fin.Patterns` up to `9F` and from emitted module-local pattern synonyms (`pattern 10F = suc 9F`, …) beyond, capped at `LITERAL_LIMIT` (32, comfortably past the catalog's carrier 19; type-checking cost grows with the carrier — see the census note § 5 — so raising the cap is a deliberate act).  Both limits are checked and produce clear errors.
+  The bijection search in `lattice.py` is bounded brute force (≤ 8! with a guard); it is engine-side only — the Agda checker re-verifies the match definitionally — so cleverness there buys nothing but speed.
