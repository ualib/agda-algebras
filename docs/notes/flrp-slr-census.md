<!-- File: docs/notes/flrp-slr-census.md -->

# FLRP census: certificate status of the SmallLatticeReps catalog

This note records, for every entry of the DeMeo–Freese–Jipsen § 6 catalog (`docs/papers/fin-lat-rep/SmallLatticeReps.tex`, 2016-06-10 draft), whether an Agda-checked certificate of representability exists in this library and by which route — the acceptance criterion of issue #485 (part of the #483 campaign).  All numbering below is the **manuscript's**; the dictionary to this library's names, including the `L10`-versus-library-`L7` clash, is `docs/notes/flrp-slr-naming.md`.

## 1. How this census is produced, and how to reproduce it

Every artifact is a deterministic function of the manuscript source, via `scripts/python/flrp/slr_catalog.py` (the transcription stage) and `scripts/python/flrp/emit_agda.py` (the WP-6 renderer):

+  `make flrp-slr` regenerates the claim files (`scripts/python/flrp/inputs/slr/`), the audit JSONs (`scripts/python/flrp/out/slr/`), and the certificate modules (`src/FLRP/Certificates/SmallLatticeReps/`); `python3 scripts/python/flrp/slr_catalog.py --check` verifies the committed copies re-derive byte for byte, and `make flrp-test` runs that check among its suites.
+  The status table below is `python3 scripts/python/flrp/slr_catalog.py --census`; regenerate it there rather than editing it here.
+  A **certified** entry means the emitted module type-checks under `make check`, i.e. the search-free checkers of `Setoid.Congruences.Certificates` re-verified the engine's Freese traces and the `FLRP.Certificates` assembly produced a `Representableᵈ` witness for the target lattice.  Nothing is believed on the engine's authority.
+  An **engine-audited** entry means `lattice.build_certificate` verified the claim engine-side and the audit JSON is committed, but the certificate module awaits the renderer extension past the `0F`–`9F` `Fin` literals (#485 batch 2: `B5`, `B9`, `B13`, `B17`, `B27`, `B33`, carriers 12–19); the engine is size-agnostic, so batch 2 is renderer work only.

## 2. The census

| manuscript | size | status |
|---|---|---|
| `L1` | 5 | certified — `FLRP.Certificates.SmallLatticeReps.SLR01` |
| `L2` | 5 | certified — `FLRP.Certificates.SmallLatticeReps.SLR02` |
| `L3` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR03` |
| `L4` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR04` |
| `L5` | 6 | engine-audited (audit JSON committed); certificate module pending the renderer extension (#485 batch 2) |
| `L6` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR06` |
| `L7` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR07` |
| `L8` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR08` |
| `L9` | 7 | engine-audited (audit JSON committed); certificate module pending the renderer extension (#485 batch 2) |
| `L10` | 7 | open — this library's `L7`, the subject of #484 |
| `L11` | 7 | group representation (108-element coset algebra in SmallGroup(216,153)); pending the WP-3 bridge #454 with data from #487 |
| `L12` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR12` |
| `L13` | 7 | engine-audited (audit JSON committed); certificate module pending the renderer extension (#485 batch 2) |
| `L14` | 7 | group representation (upper interval in Sub(A6), 90 points); pending #454/#487 |
| `L15` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR15` |
| `L16` | 7 | group representation (Sub(C2.A6), 180 points); pending #454/#487 |
| `L17` | 7 | engine-audited (audit JSON committed); certificate module pending the renderer extension (#485 batch 2) |
| `L18` | 7 | dual of L19; assumption-conditional via Kurzweil–Netter duality (#456) |
| `L19` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR19` |
| `L20` | 7 | group representation (filter-ideal in SmallGroup(216,153)); pending #454/#487 |
| `L21` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR21` |
| `L22` | 7 | dual of L23; assumption-conditional via Kurzweil–Netter duality (#456) |
| `L23` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR23` |
| `L24` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR24` |
| `L25` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR25` |
| `L26` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR26` |
| `L27` | 7 | engine-audited (audit JSON committed); certificate module pending the renderer extension (#485 batch 2) |
| `L28` | 7 | candidate manuscript erratum — Con(B28) as printed has 8 congruences — a 7-chain plus one doubly irreducible element — not the 7 elements of L28 (erratum log below); no verified representation in hand |
| `L29` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR29` |
| `L30` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR30` |
| `L31` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR31` |
| `L32` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR32` |
| `L33` | 7 | engine-audited (audit JSON committed); certificate module pending the renderer extension (#485 batch 2) |
| `L34` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR34` |
| `L35` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR35` |

Tally: **21 certified**, **6 engine-audited awaiting the batch-2 renderer**, **4 parked on the group route** (#454/#487), **2 assumption-conditional duals** (#456), **1 open** (#484), **1 candidate erratum**.

## 3. The parked entries, in detail

+  **`L10`** — this library's `L7`; the manuscript's lone open case, and the subject of the dedicated hunt #484 (minimal `Eq(6)` sublattice representation formalized in `FLRP.L7EqSix`; closure obstructions machine-checked through eight points; see `docs/notes/flrp-l7-eq6.md`).
+  **`L11`, `L14`, `L16`, `L20`** — the manuscript's representations are group-theoretic (subgroup-lattice intervals and a filter-ideal construction, carriers 90–216).  Route per #485: the WP-3 bridge (#454) once #487 supplies the concrete group data, or direct big-carrier certificates if type-checking cost permits; nothing is emitted for them in this batch.
+  **`L18`, `L22`** — duals of `L19` and `L23`, with no explicit small algebras in the manuscript.  Both duals' partners are now **certified** (`SLR19`, `SLR23`), so once WP-5 (#456) registers Kurzweil–Netter duality as a named assumption, `L18` and `L22` become assumption-conditional corollaries; explicit algebras may also be found by the #486 search tooling (their lattice stanzas `slr18_lattice.json`, `slr22_lattice.json` are committed as ready-made `eqsearch.py` targets).

## 4. Erratum log

Per the #485 discipline, a claim that fails the engine is first rechecked against the source; only if the transcription survives is it recorded here.  The manuscript's own data is never altered to make an entry pass.  Findings should be reported upstream to https://github.com/UniversalAlgebra/fin-lat-rep.

### E1 (2026-07-22): `Con(B28) ≠ L28` as printed — one congruence too many

+  **The claim**.  § 6 prints `B28` (16 elements, operations `f`, `g`, `h`, `k`, `l`, `m`, method "overalgebras") as a representation of `L28`, the seven-element lattice `0 ⋖ 1 ⋖ 2 ⋖ 3 ⋖ 5 ⋖ 6` with one doubly irreducible element `4` (a six-element chain plus one).
+  **The refutation**.  `Con(B28)` as printed has **eight** congruences: in bar notation (blocks by least member, reproducible with `python3 scripts/python/flrp/slr_catalog.py --diagnose 28`),

  ```text
  θ0  |0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|
  θ1  |0,1,2,6,7,11,12|3,4,5|8,9,10|13,14,15|
  θ2  |0,3,8|1,4|2,5,15|6,9|7,10|11,13|12,14|
  θ3  |0,...,15| (the total congruence)
  θ4  |0|1,2,12|3,4|5|6,7|8,9|10|11|13,14|15|
  θ5  |0|1,2,12|3,4,5|6,7|8,9,10|11|13,14,15|
  θ6  |0|1,2,12|3,4|5|6,7|8,9,10|11|13,14,15|
  θ7  |0,1,2,6,7,11,12|3,4,5|8,9,10,13,14,15|
  ```

  with covers `θ0 ⋖ θ2`, `θ0 ⋖ θ4 ⋖ θ6 ⋖ θ5 ⋖ θ1 ⋖ θ7 ⋖ θ3`, `θ2 ⋖ θ3` — a **seven**-element chain plus the doubly irreducible `θ2`, i.e. exactly the `L28` shape with the long chain one element too long (the printed diagram wants the chain `θ4 ⋖ θ6 ⋖ θ5` two steps shorter than the algebra delivers).
+  **Why the refutation is airtight**.  Each of the eight partitions is verified to respect all six printed operation tables by a direct double loop independent of the `cg2` machinery (`respects_operations` in `slr_catalog.py`, exercised by `test_slr_catalog.py`); eight pairwise distinct congruences refute `|Con(B28)| = 7` regardless of any enumeration's completeness.
+  **The transcription was rechecked** character by character against the `.tex` source before recording this: the diagram parse (`0 ⋖ 1; 0 ⋖ 4; 1 ⋖ 2; 2 ⋖ 3; 3 ⋖ 5; 4 ⋖ 6; 5 ⋖ 6`) and all six value rows match the printed entry exactly.
+  **Circumstantial diagnosis** (for the upstream report, not acted on here): `B27` — the same overalgebra construction, sharing its `f`, `l`, `m` rows with `B28` verbatim — passes and is engine-audited, which points at a typo in one of `B28`'s `g`/`h`/`k` rows; `B28`'s `h` and `k` rows restricted to `{0,…,5}` are exactly `B7`'s `f` and `g`, consistent with `B28` being built as an overalgebra of `B7`.
+  **Consequence for the census**: `L28` currently has no verified representation in this library; its lattice stanza (`slr28_lattice.json`) is committed as an `eqsearch.py` target, and a small representation may well be recoverable by the #486 search once the upstream table is corrected.

## 5. Costs observed in batch 1

Type-checking any single emitted module costs about 4.5 s of interface loading plus 0–2.5 s for the certificate decisions themselves at these sizes (carriers ≤ 9, lattices ≤ 7); the largest, `SLR12` and `SLR21` (carrier 9), stay under 7 s wall-clock per module.  Engine time is negligible throughout (the full 27-entry audit plus emission runs in under two seconds).  Batch 2's carriers (12–19) will test the quadratic-in-carrier trace tables; timings are to be reported with that PR per #485.
