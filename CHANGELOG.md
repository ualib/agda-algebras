# CHANGELOG

All notable changes to agda-algebras are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and this project aspires to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased] — 3.0 development

The 3.0 release is a major reconstruction of agda-algebras building on the Setoid-based redevelopment that shipped in v2.0.1 (December 2021).  Work is organized into milestones tracked in [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md).

### Added

+  **Setoid-canonical tree.**  `src/Setoid/` is the canonical development tree for 3.0.
+  **Nix flake** at the repo root pinning Agda 2.8.0 and standard-library 2.3, so `nix develop` provides a reproducible development environment.
+  **`INSTALL.md`** as the canonical installation guide.
+  **GitHub Actions CI** (`.github/workflows/ci.yml`) that type-checks the library on every push and pull request.
+  **Community-health files**: `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, issue templates, pull-request template.
+  **Dual license**: Apache 2.0 for source code under `src/`, CC BY 4.0 for documentation under `docs/`.

### Changed

+  **Agda target**: 2.6.2 → 2.8.0.
+  **Standard library target**: 1.7 → 2.3.
+  **Pragma**: `--without-K` → `--cubical-compatible` across the tree.  See `src/Overture/Basic.lagda.md` for the reasoning.
+  **Literate-Agda format** (**breaking** for external links into `docs/lagda/`).  The historical dual-tree split — minimal `src/X/Y/Z.agda` skeletons paired with LaTeX-literate `docs/lagda/X/Y/Z.lagda` content — is consolidated into unified Markdown-literate `src/X/Y/Z.lagda.md` files.  127 module pairs were collapsed; the `docs/lagda/` tree was deleted.  Rationale and migration policy are recorded in [ADR-004](docs/adr/004-lagda-md-canonical.md).  External bookmarks pointing at specific `docs/lagda/X/Y/Z.lagda` paths will not resolve; the rendered documentation site at [https://ualib.org](https://ualib.org) is unaffected because it serves `X.Y.Z.html` paths under the same scheme as before.
+  **Documentation directory**: `doc/` → `docs/` following modern conventions.
+  **README**: rewritten for the 3.0 line.

### Deprecated

+  **`docs/INSTALL_AGDA.md`** superseded by `INSTALL.md`.  Retained with a deprecation banner; will be removed in a future release.

### Removed

+  **`docs/lagda/` tree** (127 LaTeX-literate `.lagda` files).  Content migrated to `src/X/Y/Z.lagda.md`; see "Literate-Agda format" above.
+  **`src/X/Y/Z.agda` skeleton companions** (127 files) that were mechanically derived from the LaTeX-literate sources by `admin/illiterator/`.  The illiterator program itself is slated for deletion in the rendering-pipeline-modernization follow-up.

### Fixed

Nothing to report.  3.0 is a forward-looking reconstruction rather than a bug-fix release.

---

## [2.0.1] — 2021-12-07

Archival release coinciding with the TYPES 2021 submission.  This version was the first to use the Setoid-based formulation, reconstructed from the earlier UALib project.  Archived on Zenodo: [DOI 10.5281/zenodo.5765793](https://doi.org/10.5281/zenodo.5765793).

Targets Agda 2.6.2 and standard-library 1.7.

---

## [1.x and earlier]

The earlier UALib library (GitLab-hosted) and the pre-v2.0.1 agda-algebras work.  No per-version changelog was maintained; see the git log and the related papers for details.
