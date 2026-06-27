<!-- File: docs/adr/007-mkdocs-rendering-pipeline.md -->

# ADR-007: MkDocs (Material) as the documentation rendering pipeline

## Status

Accepted — 2026-06-27 (M10-1, #295).

> **Numbering note.**  Issue #295 proposed this ADR as `005-mkdocs-rendering-pipeline.md`.  By the time it was written, `005` (universe-level variable scope) and `006` (signature-morphism category) had already been merged, so it takes the next free number, `007`.  Numbers are assigned in merge order (see [the ADR README](README.md)); the renumber is purely mechanical.

## Context

[ADR-004](004-lagda-md-canonical.md) made single-file `.lagda.md` the canonical literate format and that migration has landed: every module is one literate-Markdown file that the type-checker reads directly.  The rendering pipeline did not follow.  The site at [ualib.org](https://ualib.org) is still produced by the pre-3.0 machinery — `admin/generate-html` and `admin/generate-tex` driving a Jekyll build, with `admin/illiterator` and `_config.yml` in support — which was designed for the old dual-tree layout (`.agda` skeletons paired with LaTeX-literate `docs/lagda/*.lagda`).  That machinery is now dead weight: it post-processes a tree shape that no longer exists, ages the deferred CHANGELOG entries, and blocks the M8 `make corpus` walker that wants the same `.lagda.md` traversal a static-site generator would exercise.

Once the sources are Markdown-literate, a static-site generator that reads Markdown directly is the natural fit, and the Agda ecosystem's de-facto choice for that role is [MkDocs](https://www.mkdocs.org/) with the [Material](https://squidfunk.github.io/mkdocs-material/) theme.  The forces to settle before building it:

+  **Domain.**  Whether to keep `ualib.org` or move.
+  **`agda --html` integration.**  Whether to keep a token-highlighting preprocess step or render the `.lagda.md` sources directly.
+  **URL scheme.**  The legacy site serves flat `Module.Submodule.html`; a Markdown SSG with directory URLs serves `/Module/Submodule/`.  These differ, and external links point at the old form.
+  **Shared link includes.**  Every module ended in a Jekyll `{% include UALib.Links.md %}` that pulled in a large reference-link file so that `[Setoid.Algebras.Basic][]`-style links resolved.  Jekyll's `{% include %}` does not exist under MkDocs; the convention needs a replacement.
+  **Reproducibility.**  The toolchain must be pinned the way Agda and the standard library already are, so that `make site` reproduces CI's build.

## Decision

**Render ualib.org with MkDocs + Material, consumed directly from the `.lagda.md` sources, pinned in the Nix flake.**  Concretely:

1.  **Keep `ualib.org`.**  It is the established public URL; preserving it avoids breaking every external reference to the library.  Alternative domains (`formalverification.org`, `agda-algebras.org`) are explicitly out of scope.

2.  **Render the `.lagda.md` sources directly — no `agda --html` step (issue #295 architecture (b)).**  Inline Agda terms are written as kramdown attribute spans (`` `Algebra`{.AgdaRecord} ``), which python-markdown's `attr_list` extension turns into class-tagged inline `<code>` elements; `docs/stylesheets/custom.css` colours the eleven-plus Agda classes in light and dark, mirroring Agda's HTML palette as 1Lab and formal-ledger-specifications do.  Fenced ```` ```agda ```` blocks render as plain, well-set monospace.  The trade-off is deliberate: whole-token, click-through highlighting of code blocks (what `agda --html` produces) is given up in exchange for eliminating a build-time dependency on a full type-check and matching what the migrator already emits.  In practice the class-tagged inline references are what readers follow in prose, and the code blocks remain perfectly legible.

3.  **Serve directory URLs rooted at the module hierarchy: `/Module/Submodule/`.**  `src/Setoid/Algebras/Basic.lagda.md` is served at `/Setoid/Algebras/Basic/` — the same components as the legacy `Setoid.Algebras.Basic.html`, `/`-separated.  `mkdocs-redirects` is wired into the config (with an initially empty map) so the legacy flat URLs can be redirected at the cutover; populating that map is a cutover task, not a blocker for the build.

4.  **Mount the library with `mkdocs-gen-files` + `mkdocs-literate-nav` + `mkdocs-section-index`.**  This is the one place the plugin set goes beyond issue #295's baseline (`material`, `search`, `macros`, `redirects`), and it is what makes architecture (b) realisable cleanly.  `scripts/python/mkdocs_gen_library.py` walks `src/**/*.lagda.md` and, for each module, writes a *virtual* page at its hierarchical path with the `.lagda` infix stripped (so URLs are `/Setoid/Algebras/Basic/`, not `…/Basic.lagda/`), drops the Jekyll front matter, and prepends a clean `# Dotted.Module` title (the corpus leads with `####` sub-headings, so pages would otherwise render untitled).  It also emits `SUMMARY.md`, the literate-nav file that becomes the whole navigation; each barrel module is the clickable section-index page for its subtree.  The sources themselves are never modified — only the rendered copy is shaped — and `mkdocs serve` regenerates on edit, which a copy-into-place build step would not.

5.  **Replace the Jekyll link include with `pymdownx.snippets` `auto_append` (issue #295's "reference-link include scheme").**  The shared link library moves to `docs/_links.md` and is appended to every page automatically; the per-module `{% include UALib.Links.md %}` directive is removed from every source.  Internal targets are *root-relative* (`/Setoid/Algebras/Basic/`) so cross-references resolve identically under `mkdocs serve` and at `ualib.org`.  The module half of `docs/_links.md` is generated from the tree by `scripts/python/gen_links.py` (it had fallen ~130 entries behind by hand).  `mkdocs-macros-plugin` is still configured — per the issue's plugin set — but it is *not* used for the link include; appending one file to every page is exactly `auto_append`'s job and carries no templating risk.  Because Agda's `{{ }}`, `{ }`, `{% %}`, and `{# %}` occur throughout the corpus, macros is given collision-free Jinja2 delimiters — doubled-square-bracket variants, configured in `mkdocs.yml`, that occur nowhere in `src/` — and reserved for site variables.

6.  **Rewrite repo-relative prose links with a build hook.**  Prose links written for GitHub viewing (`](src/X.lagda.md)`, `](docs/adr/…)`, `](CONTRIBUTING.md)`) are rewritten to site URLs by `scripts/python/mkdocs_hooks.py` (`on_page_markdown`), which is careful to skip fenced code so Agda is never touched.

7.  **Pin the toolchain in the flake; drive it from the Makefile; deploy from CI.**  `flake.nix` gains a Python environment with `mkdocs-material` and the plugins, so `nix develop --command make site` reproduces CI exactly, the same way `make check` reproduces the type-check.  `make site` builds to `./site`; `make serve` previews locally.  `.github/workflows/docs.yml` builds and deploys to the `gh-pages` branch on every push to `master`.

## Consequences

+  **The Jekyll machinery is retired.**  `admin/generate-html`, `admin/generate-tex`, `admin/illiterator/`, and `_config.yml` are deleted, and `make html` becomes `make site`.  The new path is built and verified green *before* the old one is removed.
+  **One pinned command builds the site.**  `nix develop --command make site` produces the whole library under `./site` with no Agda invocation, in well under a minute.  CI and a contributor run the identical command.
+  **Cross-references resolve everywhere.**  Reference-style links resolve site-wide via the auto-appended `docs/_links.md`; repo-relative inline links are rewritten by the hook.  A handful of pre-existing prose references to modules that do not exist (typos predating this work) remain unresolved and are left for a content-cleanup pass — fixing them is a prose correction, not a rendering concern.
+  **Token-by-token code highlighting is gone.**  Accepted under architecture (b); inline class-tagged references carry the semantic colour and code blocks stay legible.  Should full highlighting ever be wanted back, a preprocess step (architecture (a)) can be layered on without changing the URL scheme or the link scheme.
+  **The URL scheme changes shape.**  `/Module/Submodule/` replaces `Module.Submodule.html`.  `mkdocs-redirects` absorbs the legacy URLs at the cutover; until then the live site is untouched.
+  **The cutover is a documented manual step.**  Pointing GitHub Pages at `gh-pages`, attaching the `ualib.org` custom domain, and the registrar DNS change are deferred to the maintainer and listed as a checklist on the migration PR.  Nothing in this ADR disturbs the currently-live site.
+  **Authoring is unchanged.**  Contributors keep writing `.lagda.md`; the front matter and the `{% include %}` footer they used to copy are no longer needed (the include is gone; the title and nav are generated).

## Alternatives considered

+  **Architecture (a): preprocess with `agda --html --html-highlight=code`, point MkDocs at the generated Markdown.**  Rejected as the default because it reintroduces a full type-check into the docs build and a generated intermediate tree, for highlighting that inline class spans already provide where readers use it.  It remains a clean future addition if full code highlighting is wanted.
+  **A non-MkDocs generator (Hugo, Zola, Quarto).**  Rejected; MkDocs + Material is the Agda ecosystem's convention (1Lab, formal-ledger-specifications, agda-stdlib tooling), and tracking the ecosystem lowers contributor friction.  Re-litigating the SSG choice is a non-goal of #295.
+  **Keep the `.lagda` infix in URLs (`/Setoid/Algebras/Basic.lagda/`).**  Rejected; it is ugly and drifts further from the legacy `Setoid.Algebras.Basic.html` than `/Setoid/Algebras/Basic/` does.  Stripping it is one line in the gen-files mount.
+  **Use `mkdocs-macros` `{% include %}` for the link library.**  Rejected; it would keep a per-page directive and run a Jinja2 pass over Agda-dense pages whose `{{ }}`/`{ }` collide with the default delimiters.  `pymdownx.snippets` `auto_append` appends the file with no per-page directive and no templating pass.
+  **Hand-author the navigation in `mkdocs.yml`.**  Rejected for ~280 modules; literate-nav driven by a generated `SUMMARY.md` keeps the nav in lock-step with the tree and is the standard mkdocstrings-style mechanism.

## References

+  Issue #295 — [M10-1] doc rendering-pipeline modernization (mkdocs).
+  [ADR-004](004-lagda-md-canonical.md) — Markdown-literate Agda as the canonical literate format (the migration this pipeline completes).
+  [1Lab](https://1lab.dev) and [formal-ledger-specifications](https://omelkonian.github.io/formal-ledger/) — the kramdown-attribute-span + custom-CSS precedents.
+  [Material for MkDocs](https://squidfunk.github.io/mkdocs-material/), [mkdocs-gen-files](https://oprypin.github.io/mkdocs-gen-files/), [mkdocs-literate-nav](https://oprypin.github.io/mkdocs-literate-nav/), [pymdownx.snippets](https://facelessuser.github.io/pymdown-extensions/extensions/snippets/).
