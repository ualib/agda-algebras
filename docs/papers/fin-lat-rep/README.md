<!-- File: docs/papers/fin-lat-rep/README.md -->

# Pinned source data: the SmallLatticeReps manuscript

`SmallLatticeReps.tex` is a **frozen snapshot** of `article/SmallLatticeReps.tex` from the manuscript's permanent home, https://github.com/UniversalAlgebra/fin-lat-rep, taken at upstream commit `8ff0afb3e601ac3ab9a4fda90f60b6cc54759e66` (the 2016-06-10 draft).  It is committed here as *source data*, not as a maintained copy: the transcription stage of issue #485 (`scripts/python/flrp/slr_catalog.py`) parses its § 6 catalog — Hasse diagrams from the tikz coordinates, value tables from the array blocks — and every committed claim file, audit JSON, and certificate module under `src/FLRP/Certificates/SmallLatticeReps/` re-derives from this file byte for byte (`make flrp-test` enforces it, and `slr_catalog.py --check` reports it entry by entry).

+  **Never edit this file.**  A printed claim the engines refute is a candidate erratum to report upstream (see the erratum log in `docs/notes/flrp-slr-census.md`), never a local fix; the `ERRATA` mechanism in `slr_catalog.py` enforces that discipline.
+  **To track a newer draft**, replace the file wholesale from upstream, record the new commit hash here, and rerun `make flrp-slr`; the diff over the regenerated artifacts is the review surface for exactly what the revision changed.
+  Only the main `.tex` is pinned: the § 6 catalog the pipeline reads is inline in this file, so the upstream repository's class file, bibliography, figure sources, and rendered PDFs are deliberately not vendored — consult them upstream.
