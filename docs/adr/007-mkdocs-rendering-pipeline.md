<!-- File: docs/adr/007-mkdocs-rendering-pipeline.md -->

# ADR-007: MkDocs (Material) as the documentation rendering pipeline

## Status

Accepted — 2026-06-27 (M10-1, #295).

Amended — 2026-06-30 (M10-4, #430): the hosting decision changed.  The new
MkDocs site is **relocated** to `agda-algebras.universalalgebra.org`, and the
legacy site is **parked** at `ualib.org`; see the revised Decision 1 and 7.

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

**Render the documentation site with MkDocs + Material, consumed directly from the `.lagda.md` sources, pinned in the Nix flake.**  Concretely:

1.  **Park the legacy site at `ualib.org`; serve the new site at `agda-algebras.universalalgebra.org`.**  *(Amended for #430; the original decision was simply "keep `ualib.org`".)*  The established `ualib.org` URL is preserved **as an archive of the pre-3.0 site** — so every external `Module.Submodule.html` link keeps resolving — while the new MkDocs site is published to a subdomain of the existing `universalalgebra.org`.  A **subdomain** (rather than a `universalalgebra.org/agda-algebras` subdirectory) is required: the rendered pages use root-absolute internal links (`/Setoid/…`, `/classic/…`, `/assets/…`) that a subdirectory base path would break, whereas a subdomain serves at the host root and needs only a one-line `site_url` plus a DNS `CNAME`.

2.  **Highlight code blocks with `agda --html` for the published site; keep a no-agda fast path for iteration.**  Two complementary mechanisms run over the *same* `.lagda.md` sources:

    +  **Inline prose terms** are kramdown attribute spans (`` `Algebra`{.AgdaRecord} ``), which `attr_list` turns into class-tagged `<code>`; `docs/stylesheets/custom.css` colours them in light and dark (the 1Lab / formal-ledger-specifications precedent).  This needs no Agda and is always on.
    +  **Code blocks** are highlighted by `agda --html --html-highlight=code` (`make agda-md`), which emits, per module, a Markdown file whose code blocks are `<pre class="Agda">` with every token semantically classed and **hyperlinked to its definition** — essential for navigating a large development.  `gen-files` embeds those (rewriting Agda's `Module.Sub.html#id` hrefs to `/Module/Sub/#id` for library modules and `/classic/…` for the standard library), and `md_in_html` preserves the multi-line blocks intact.  When the `agda --html` output is absent, `gen-files` falls back to the raw `.lagda.md` with plain monospace code blocks — so `make site` stays instant for prose/theme work while `make site-full` (what CI publishes) carries the full highlighting.

    The earlier intent (issue #295 architecture (b): *no* `agda --html` at all) is thus relaxed on maintainer review: token-level highlighting and per-token hyperlinks are too valuable to give up, the cost is a type-check the project already runs, and a `.agdai`-cached rerun is cheap.  Architecture (b) survives as the fast fallback, not the only mode.

2b.  **Also publish the classic clickable-HTML site at `/classic/` (issue #295's keep-`make html` request).**  The same type-check, run as plain `agda --html` (`make html`), produces the agda-categories-style standalone site — `Everything.html` as the index, library + standard library, self-contained — which `gen-files` mounts at `/classic/` (working under both build and serve) and which doubles as the stdlib link target for the embedded code above.  `make html` is restored as a first-class target.

3.  **Serve directory URLs rooted at the module hierarchy: `/Module/Submodule/`.**  `src/Setoid/Algebras/Basic.lagda.md` is served at `/Setoid/Algebras/Basic/` — the same components as the legacy `Setoid.Algebras.Basic.html`, `/`-separated.  `mkdocs-redirects` is wired into the config (with an initially empty map) so the legacy flat URLs can be redirected at the cutover; populating that map is a cutover task, not a blocker for the build.

4.  **Mount the library with `mkdocs-gen-files` + `mkdocs-literate-nav` + `mkdocs-section-index`.**  This is the one place the plugin set goes beyond issue #295's baseline (`material`, `search`, `macros`, `redirects`), and it is what makes architecture (b) realisable cleanly.  `scripts/python/mkdocs_gen_library.py` walks `src/**/*.lagda.md` and, for each module, writes a *virtual* page at its hierarchical path with the `.lagda` infix stripped (so URLs are `/Setoid/Algebras/Basic/`, not `…/Basic.lagda/`), drops the Jekyll front matter, and prepends a clean `# Dotted.Module` title (the corpus leads with `####` sub-headings, so pages would otherwise render untitled).  It also emits `SUMMARY.md`, the literate-nav file that becomes the whole navigation; each barrel module is the clickable section-index page for its subtree.  The sources themselves are never modified — only the rendered copy is shaped — and `mkdocs serve` regenerates on edit, which a copy-into-place build step would not.

5.  **Replace the Jekyll link include with `pymdownx.snippets` `auto_append` (issue #295's "reference-link include scheme").**  The shared link library moves to `docs/_links.md` and is appended to every page automatically; the per-module `{% include UALib.Links.md %}` directive is removed from every source.  Internal targets are *root-relative* (`/Setoid/Algebras/Basic/`) so cross-references resolve identically under `mkdocs serve` and at the deployed host (this is why the new site is served at a host *root*, not a `…/agda-algebras` subdirectory — Decision 1).  The module half of `docs/_links.md` is generated from the tree by `scripts/python/gen_links.py` (it had fallen ~130 entries behind by hand).  `mkdocs-macros-plugin` is still configured — per the issue's plugin set — but it is *not* used for the link include; appending one file to every page is exactly `auto_append`'s job and carries no templating risk.  Because Agda's `{{ }}`, `{ }`, `{% %}`, and `{# %}` occur throughout the corpus, macros is given collision-free Jinja2 delimiters — doubled-square-bracket variants, configured in `mkdocs.yml`, that occur nowhere in `src/` — and reserved for site variables.

6.  **Rewrite repo-relative prose links with a build hook.**  Prose links written for GitHub viewing (`](src/X.lagda.md)`, `](docs/adr/…)`, `](CONTRIBUTING.md)`) are rewritten to site URLs by `scripts/python/mkdocs_hooks.py` (`on_page_markdown`), which is careful to skip fenced code so Agda is never touched.

7.  **Pin the toolchain in the flake; drive it from the Makefile; deploy from CI.**  `flake.nix` gains a Python environment with `mkdocs-material` and the plugins, so a contributor reproduces CI exactly, the same way `make check` reproduces the type-check.  `make site` is the fast preview build (to `./site`); `make serve` previews locally; `make site-full` (`make html` + `make agda-md` + `make site`) is the fully-featured build CI publishes.  `.github/workflows/docs.yml` runs `make site-full` and **cross-deploys** the built `./site` to the `gh-pages` branch of the new-home repository in the `universalalgebra` org (via `peaceiris/actions-gh-pages` with `external_repository` + a deploy key, `cname: agda-algebras.universalalgebra.org`) on every push to `master`.  `ualib/agda-algebras` stays the single canonical source; its *own* `gh-pages` branch holds the parked legacy site and is no longer a deploy target.  *(Amended for #430; the original deployed to this repository's own `gh-pages`.)*

## Consequences

+  **The Jekyll machinery is retired.**  `admin/generate-html`, `admin/generate-tex`, `admin/illiterator/`, and `_config.yml` are deleted; `make html` is repurposed to build the classic `agda --html` site (Decision 2b).  The new path is built and verified green *before* the old one is removed.
+  **Two pinned builds, one toolchain.**  `make site` produces the whole library under `./site` with no Agda invocation in well under a minute (fast iteration); `make site-full` adds the `agda --html` passes (a `.agdai`-cached type-check) for the published, fully-highlighted site.  CI runs the latter.
+  **Cross-references resolve everywhere.**  Reference-style links resolve site-wide via the auto-appended `docs/_links.md`; repo-relative inline links are rewritten by the hook; and in the published site every code-block token links to its definition (library → the rendered page, stdlib → `/classic/`).  A handful of pre-existing prose references to modules that do not exist (typos predating this work) remain unresolved and are left for a content-cleanup pass.
+  **Full token highlighting in the published site.**  `agda --html` gives whole-token semantic colour and per-token hyperlinks in code blocks, alongside the inline prose spans.  The cost is a type-check the project already runs; the fast no-agda path keeps prose/theme iteration instant.  (Type-on-hover tooltips, 1Lab-style, are a tracked follow-up that builds on this same output.)
+  **The URL scheme changes shape.**  `/Module/Submodule/` replaces `Module.Submodule.html`.  `mkdocs-redirects` absorbs the legacy URLs at the cutover; until then the live site is untouched.
+  **The cutover is a documented manual step (tracked in #430).**  Standing up the new home — the `universalalgebra`-org repo, the cross-repo deploy key, and the `agda-algebras.universalalgebra.org` DNS `CNAME` + custom-domain — and parking the legacy site at `ualib.org` (restoring its pre-merge `gh-pages` content + CNAME) are deferred to the maintainer and tracked in **#430**, along with populating `mkdocs-redirects`.
+  **Authoring is unchanged.**  Contributors keep writing `.lagda.md`; the front matter and the `{% include %}` footer they used to copy are no longer needed (the include is gone; the title and nav are generated).

## Alternatives considered

+  **Architecture (b) *only* — no `agda --html` at all.**  The issue's original recommendation, and our first cut.  Superseded on maintainer review (Decision 2): it gives up token-level highlighting and the per-token hyperlinks that make a large Agda development navigable, to save a type-check the project runs anyway.  We keep it as the fast fallback rather than the sole mode.
+  **A non-MkDocs generator (Hugo, Zola, Quarto).**  Rejected; MkDocs + Material is the Agda ecosystem's convention (1Lab, formal-ledger-specifications, agda-stdlib tooling), and tracking the ecosystem lowers contributor friction.  Re-litigating the SSG choice is a non-goal of #295.
+  **Keep the `.lagda` infix in URLs (`/Setoid/Algebras/Basic.lagda/`).**  Rejected; it is ugly and drifts further from the legacy `Setoid.Algebras.Basic.html` than `/Setoid/Algebras/Basic/` does.  Stripping it is one line in the gen-files mount.
+  **Use `mkdocs-macros` `{% include %}` for the link library.**  Rejected; it would keep a per-page directive and run a Jinja2 pass over Agda-dense pages whose `{{ }}`/`{ }` collide with the default delimiters.  `pymdownx.snippets` `auto_append` appends the file with no per-page directive and no templating pass.
+  **Hand-author the navigation in `mkdocs.yml`.**  Rejected for ~280 modules; literate-nav driven by a generated `SUMMARY.md` keeps the nav in lock-step with the tree and is the standard mkdocstrings-style mechanism.

## References

+  Issue #295 — [M10-1] doc rendering-pipeline modernization (mkdocs).
+  Issue #430 — [M10-4] retire/park the legacy `ualib.org` site; relocate the new site to `agda-algebras.universalalgebra.org`.
+  [ADR-004](004-lagda-md-canonical.md) — Markdown-literate Agda as the canonical literate format (the migration this pipeline completes).
+  [1Lab](https://1lab.dev) and [formal-ledger-specifications](https://omelkonian.github.io/formal-ledger/) — the kramdown-attribute-span + custom-CSS precedents.
+  [Material for MkDocs](https://squidfunk.github.io/mkdocs-material/), [mkdocs-gen-files](https://oprypin.github.io/mkdocs-gen-files/), [mkdocs-literate-nav](https://oprypin.github.io/mkdocs-literate-nav/), [pymdownx.snippets](https://facelessuser.github.io/pymdown-extensions/extensions/snippets/).
