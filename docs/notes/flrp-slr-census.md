<!-- File: docs/notes/flrp-slr-census.md -->

# FLRP census: certificate status of the SmallLatticeReps catalog

This note records, for every entry of the DeMeo–Freese–Jipsen § 6 catalog (`docs/papers/fin-lat-rep/SmallLatticeReps.tex`, 2016-06-10 draft), whether an Agda-checked certificate of representability exists in this library and by which route — the acceptance criterion of issue #485 (part of the #483 campaign).  All numbering below is the **manuscript's**; the dictionary to this library's names, including the `L10`-versus-library-`L7` clash, is `docs/notes/flrp-slr-naming.md`.

## 1. How this census is produced, and how to reproduce it

Every artifact is a deterministic function of the manuscript source, via `scripts/python/flrp/slr_catalog.py` (the transcription stage) and `scripts/python/flrp/emit_agda.py` (the WP-6 renderer):

+  `make flrp-slr` regenerates the claim files (`scripts/python/flrp/inputs/slr/`), the audit JSONs (`scripts/python/flrp/out/slr/`), and the certificate modules (`src/FLRP/Certificates/SmallLatticeReps/`); `python3 scripts/python/flrp/slr_catalog.py --check` verifies the committed copies re-derive byte for byte, and `make flrp-test` runs that check among its suites.
+  The status table below is `python3 scripts/python/flrp/slr_catalog.py --census`; regenerate it there rather than editing it here.
+  A **certified** entry means the emitted module type-checks under `make check`, i.e. the search-free checkers of `Setoid.Congruences.Certificates` re-verified the engine's Freese traces and the `FLRP.Certificates` assembly produced a `Representableᵈ` witness for the target lattice.  Nothing is believed on the engine's authority.
+  An **engine-audited** entry means `lattice.build_certificate` verified the claim engine-side and the audit JSON is committed but no certificate module exists yet.  Batch 1 left `B5`, `B9`, `B13`, `B17`, `B27`, `B33` (carriers 12–19) in that state; the batch-2 renderer extension (module-local pattern synonyms past `Data.Fin.Patterns`' `0F`–`9F`) has since landed and all six are certified, so no entry currently holds this status.

## 2. The census

| manuscript | size | status |
|---|---|---|
| `L1` | 5 | certified — `FLRP.Certificates.SmallLatticeReps.SLR01` |
| `L2` | 5 | certified — `FLRP.Certificates.SmallLatticeReps.SLR02` |
| `L3` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR03` |
| `L4` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR04` |
| `L5` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR05` |
| `L6` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR06` |
| `L7` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR07` |
| `L8` | 6 | certified — `FLRP.Certificates.SmallLatticeReps.SLR08` |
| `L9` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR09` |
| `L10` | 7 | open — this library's `L7`, the subject of #484 |
| `L11` | 7 | group representation (108-element coset algebra in SmallGroup(216,153)); pending the WP-3 bridge #454 with data from #487 |
| `L12` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR12` |
| `L13` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR13` |
| `L14` | 7 | group representation (upper interval in Sub(A6), 90 points); pending #454/#487 |
| `L15` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR15` |
| `L16` | 7 | group representation (Sub(C2.A6), 180 points); pending #454/#487 |
| `L17` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR17` |
| `L18` | 7 | dual of L19; assumption-conditional via Kurzweil–Netter duality (#456) |
| `L19` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR19` |
| `L20` | 7 | group representation (filter-ideal in SmallGroup(216,153)); pending #454/#487 |
| `L21` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR21` |
| `L22` | 7 | dual of L23; assumption-conditional via Kurzweil–Netter duality (#456) |
| `L23` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR23` |
| `L24` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR24` |
| `L25` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR25` |
| `L26` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR26` |
| `L27` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR27` |
| `L28` | 7 | candidate manuscript erratum — Con(B28) as printed has 8 congruences — a 7-chain plus one doubly irreducible element — not the 7 elements of L28 (erratum log below); no verified representation in hand |
| `L29` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR29` |
| `L30` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR30` |
| `L31` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR31` |
| `L32` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR32` |
| `L33` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR33` |
| `L34` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR34` |
| `L35` | 7 | certified — `FLRP.Certificates.SmallLatticeReps.SLR35` |

Tally: **27 certified** (21 in batch 1, 6 more once the batch-2 renderer landed), **4 parked on the group route** (#454/#487), **2 assumption-conditional duals** (#456), **1 open** (#484), **1 candidate erratum**.

## 3. The parked entries, in detail

+  **`L10`** — this library's `L7`; the manuscript's lone open case, and the subject of the dedicated hunt #484 (minimal `Eq(6)` sublattice representation formalized in `FLRP.L7EqSix`; closure obstructions machine-checked through eight points; see `docs/notes/flrp-l7-eq6.md`).
+  **`L11`, `L14`, `L16`, `L20`** — the manuscript's representations are group-theoretic (carriers 90–216).  The #487 GAP engine has now supplied the concrete group data (committed under `scripts/gap/flrp/out/`); certification remains the WP-3 bridge (#454) at big carrier, driven from #485.
   +  **`L14`** — reproduced: the core-free index-90 subgroup of `A6` whose upper interval is `≅ L14` (`l14_a6.search.json`, verdict positive), with its 90-point coset action bundled for the bridge.
   +  **`L11`** — the manuscript's filter-ideal construction reproduced in `SmallGroup(216,153)` (`bin/filter_ideal_216.g`): the pentagon filter `[H, G] ≅ N5` together with the order-3 minimal subgroup `K` (index 72, below β but neither α nor γ), `l11_filter_ideal_216_153.json`.
   +  **`L16`** — **not reproduced as printed**: the manuscript's "upper interval in `Sub(C2.A6)`, index 180" does not appear in `C2.A6 = 2.A6 = SL(2,9)`; recorded as candidate erratum E2 below.
   +  **`L20`** — filter-ideal in `SmallGroup(216,153)`; the 2016-06-10 draft states the method but prints no explicit construction, so only the group is pinned, with the pentagon/subgroup data of `L11` in hand for a fuller reproduction.
+  **`L18`, `L22`** — duals of `L19` and `L23`, with no explicit small algebras in the manuscript.  Both duals' partners are now **certified** (`SLR19`, `SLR23`), so once WP-5 (#456) registers Kurzweil–Netter duality as a named assumption, `L18` and `L22` become assumption-conditional corollaries; explicit algebras may also be found by the #486 search tooling (their lattice stanzas `slr18_lattice.json`, `slr22_lattice.json` are committed as ready-made `eqsearch.py` targets).

## 4. Erratum log

Per the #485 discipline, a claim that fails the engine is first rechecked against the source; only if the transcription survives is it recorded here.  The manuscript's own data is never altered to make an entry pass.  Findings should be reported upstream to https://github.com/UniversalAlgebra/fin-lat-rep.

### E1 (2026-07-22): `Con(B28) ≠ L28` as printed — one congruence too many

+  **The claim**.  § 6 prints `B28` (16 elements, operations `f`, `g`, `h`, `k`, `l`, `m`, method "overalgebras") as a representation of `L28`, the seven-element lattice `0 ≺ 1 ≺ 2 ≺ 3 ≺ 5 ≺ 6` with one doubly irreducible element `4` (a six-element chain plus one).
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

  with covers `θ0 ≺ θ2`, `θ0 ≺ θ4 ≺ θ6 ≺ θ5 ≺ θ1 ≺ θ7 ≺ θ3`, `θ2 ≺ θ3` — a **seven**-element chain plus the doubly irreducible `θ2`, i.e. exactly the `L28` shape with the long chain one element too long (the printed diagram wants the chain `θ4 ≺ θ6 ≺ θ5` two steps shorter than the algebra delivers).
+  **Why the refutation is airtight**.  Each of the eight partitions is verified to respect all six printed operation tables by a direct double loop independent of the `cg2` machinery (`respects_operations` in `slr_catalog.py`, exercised by `test_slr_catalog.py`); eight pairwise distinct congruences refute `|Con(B28)| = 7` regardless of any enumeration's completeness.
+  **The transcription was rechecked** character by character against the `.tex` source before recording this: the diagram parse (`0 ≺ 1; 0 ≺ 4; 1 ≺ 2; 2 ≺ 3; 3 ≺ 5; 4 ≺ 6; 5 ≺ 6`) and all six value rows match the printed entry exactly.
+  **Circumstantial diagnosis** (for the upstream report, not acted on here): `B27` — the same overalgebra construction, sharing its `f`, `l`, `m` rows with `B28` verbatim — passes and is engine-audited, which points at a typo in one of `B28`'s `g`/`h`/`k` rows; `B28`'s `h` and `k` rows restricted to `{0,…,5}` are exactly `B7`'s `f` and `g`, consistent with `B28` being built as an overalgebra of `B7`.
+  **Consequence for the census**: `L28` currently has no verified representation in this library; its lattice stanza (`slr28_lattice.json`) is committed as an `eqsearch.py` target, and a small representation may well be recoverable by the #486 search once the upstream table is corrected.

### E2 (2026-07-24): `L16` as an upper interval in `Sub(C2.A6)` does not reproduce

+  **The claim**.  § 6 lists `L16` (seven elements, covers `0 ≺ 1, 2`; `1 ≺ 3, 4, 5`; `2, 3, 4, 5 ≺ 6`) as an upper interval in `Sub(C2.A6)` with algebra of size 180 — that is, an index-180, hence order-4, subgroup `H` of `C2.A6` (order 720) with `[H, C2.A6] ≅ L16`.
+  **The finding**.  Read as the double cover `C2.A6 = 2.A6 = SL(2,9)`, the claim fails: the #487 engine finds `SL(2,9)` has a single conjugacy class of order-4 (index-180) subgroups, whose upper interval has **38** elements, not seven.  The only size-7 upper interval of `SL(2,9)` (over subgroups of order ≥ 3) is `≅ L14`, at index 90 (`|H| = 8`).  Scanning the other order-720 relatives of `A6` — `S6`, `PGL(2,9)`, `M10` — turns up `L14` (index 90) and two further seven-element lattices (indices 40 and 144), but never `L16`.  Reproduce with `bin/find_interval.g` on `SL(2,9)` at `FLRP_INDEX := 180`.
+  **Caveat and status**.  The lattice transcription (`slr16_lattice.json`) matches the printed diagram, and `C2.A6` is standard ATLAS notation for `2.A6`; either the group name or the index is off in the 2016-06-10 draft.  Recorded as a candidate erratum pending clarification of the intended group; `L16` has no verified group representation in hand, and `slr16_lattice.json` remains a search target.  Reported upstream alongside E1.

## 5. Costs observed

Type-checking a single emitted module costs about 4.5 s of interface loading plus the certificate decisions themselves, which grow with the carrier as the trace tables do (`n²` principal traces of length ≤ `n − 1`): 0–2.5 s at batch-1 sizes (carriers 3–9; the largest, `SLR12` and `SLR21`, stay under 7 s wall-clock), then 8.6–9.6 s at carrier 12 (`SLR05`, `SLR17`), 15.9–18.0 s at carrier 16 (`SLR33`, `SLR09`, and `SLR27` with six operations), and 27.9 s at carrier 19 (`SLR13`) — comfortable throughout, with headroom before the renderer's literal cap (31) becomes the binding constraint.  Engine time is negligible (the full 27-entry audit plus emission runs in about two seconds).
