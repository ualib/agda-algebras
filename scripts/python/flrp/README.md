<!-- File: scripts/python/flrp/README.md -->

# FLRP certificate emitters (WP-6)

The engine side of the WP-6 certificate pipeline (issue #457; design fixed in `docs/notes/flrp-wp6-freese-certificates.md`).  These scripts compute congruence lattices of finite algebras with R. Freese's `cg2` worklist algorithm, record the **Freese traces** that justify every block merge, and emit a literate Agda module whose type-checking re-verifies everything through the search-free checkers of `Setoid.Congruences.Certificates` and the `Representableᵈ` assembly of `FLRP.Certificates`.  Nothing computed here is trusted: the scripts are untrusted engines, and the emitted module is certificate data plus checker invocations.

+  `cg2.py` — the instrumented `cg2` worklist (arity-general): union-find, justified merges, normal-form parent vectors.
+  `lattice.py` — whole lattices: principal congruences for every carrier pair, closure under joins, meet and join tables, and the (bounded, engine-side) isomorphism match against the claimed target lattice.
+  `emit_agda.py` — the CLI: claim file in, `.lagda.md` module and audit JSON out.
+  `eqsearch.py` — the search side (issue #486), converse in direction to the emitters: given a target lattice, find its sublattice copies in `Eq(n)` with bounds at the diagonal and the total relation, classify them up to relabeling, and run the Snow closure test on each class; a closed class yields the witness algebra `⟨X, M⟩` and a ready-made claim file for the emitter.
+  `inputs/` — claim files; `out/` — audit copies of emitted certificates.

## Usage

```sh
python3 scripts/python/flrp/emit_agda.py scripts/python/flrp/inputs/v4_regular_m3.json
```

This writes `src/FLRP/Certificates/Pilot/<name>.lagda.md` (the only file placement needed — the generated `Everything` aggregator picks it up, so `make check` verifies it with no manual editing) and `scripts/python/flrp/out/<name>.cert.json` (the raw certificate, kept outside `src/` per roadmap § 6).  Output is a deterministic function of the input; pin the input's `date` field for byte-stable re-emission.

## The claim file (`flrp-cert-input v1`)

```json
{
  "format": "flrp-cert-input v1",
  "name": "V4RegularM3",              // Agda-name; module FLRP.Certificates.Pilot.<name>
  "date": "2026-07-22",               // optional; defaults to today (breaks byte-stability)
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

Provenance: this generalizes the 2026-07-22 `L7` session (issue #484) — minimal sublattice representation of `L7` in `Eq(6)`, two classes up to relabeling, and closure failing on 6 and on 7 points, so any representation of `L7` as a congruence lattice needs at least 8 points.  Those numbers are pinned as regression tests.

## Testing

```sh
make flrp-test          # from the repo root
```

`test_flrp.py` runs three layers of tests: engine unit tests (worklist, normal forms, lattice construction, target matching, renderer guard rails), a Python **mirror of the Agda checker's obligations** (C1 trace soundness, C2 replay coverage, C3 seed containment) over every trace of the pilot certificate — an engine-side regression tripwire only, never a substitute for the checker — and **golden round-trip tests**: re-emitting the committed pilot input must reproduce the committed `.lagda.md` module and audit JSON byte for byte.  Negative tests confirm that a false claim (wrong lattice, corrupted join table) raises a `CertificateError` and that the renderer rejects out-of-scope inputs.

`test_eqsearch.py` covers the search side: the partition kernel cross-validated against brute force (the backtracking monoid enumeration versus a full `n^n` scan), the `M3`-on-4-points census with its closed matchings class flowing all the way to a checked certificate, and the pinned `L7` session results.  The `Eq(7)` sweep (about five minutes) runs only with `FLRP_EQSEARCH_SLOW=1`.

The Agda side needs no separate harness: the emitted pilot module is part of the library, so `make check` — the repository's single test gate, exactly what CI runs — *is* the end-to-end verification of the certificate.  To see the falsification story in action, flip any table entry or trace index in the emitted module and re-run `agda src/FLRP/Certificates/Pilot/V4RegularM3.lagda.md`: the corresponding `from-yes` decision computes to `no` and compilation fails.

## Scope notes

+  The `cg2` engine is arity-general; the v1 Agda renderer targets **unary signatures** (`Sig-Unary`, i.e. G-sets and their kin — the Pálfy–Pudlák frontier) and `Fin` literals `0F`–`9F` (carriers, symbol counts, and lattices of size ≤ 10).  Both limits are checked and produce clear errors; lifting them is renderer work only.
+  The bijection search in `lattice.py` is bounded brute force (≤ 8! with a guard); it is engine-side only — the Agda checker re-verifies the match definitionally — so cleverness there buys nothing but speed.
