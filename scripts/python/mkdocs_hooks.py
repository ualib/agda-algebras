"""MkDocs build hooks for the agda-algebras site (ADR-007).

`on_page_markdown` rewrites the *repo-relative* links that the prose uses for
GitHub viewing into the site's URL scheme, so cross-references resolve both in
`mkdocs serve` and at the deployed site:

    ](src/Setoid/Varieties/HSP.lagda.md#…)  ->  ](/Setoid/Varieties/HSP/#…)
    ](docs/adr/001-setoid-as-canonical.md)  ->  ](/adr/001-setoid-as-canonical/)
    ](CONTRIBUTING.md)                       ->  ](/contributing/)
    ](LICENSE)                               ->  ](https://github.com/…/LICENSE)

Only link/image targets OUTSIDE fenced code blocks are touched, so Agda source
is never altered.  External (http/mailto), root-relative (/…), and pure-anchor
(#…) targets pass through unchanged.
"""
from __future__ import annotations

import hashlib
import logging
import re
from pathlib import Path

log = logging.getLogger("mkdocs.plugins.ualib.render")

REPO_BLOB = "https://github.com/ualib/agda-algebras/blob/master/"

# Render-progress state (#2): the markdown→HTML loop is otherwise silent, so we
# emit a line per page as MkDocs works through them.
_total = 0
_done = 0

# Root-level repo files that have an on-site page …
ON_SITE = {
    "INSTALL.md": "/install/",
    "CONTRIBUTING.md": "/contributing/",
    "CHANGELOG.md": "/changelog/",
}
# … and ones that do not (link out to GitHub instead of 404ing on-site).
TO_BLOB = {"README.md", "LICENSE", "LICENSE-docs", "CODE_OF_CONDUCT.md", "NOTICE"}

LINK = re.compile(r"(\]\()([^)\s]+)(\))")
FENCE = re.compile(r"^\s*```")


def _retarget(target: str) -> str:
    base, sep, frag = target.partition("#")
    anchor = (sep + frag) if sep else ""

    if base == "" or re.match(r"^(?:https?:|mailto:|/)", base):
        return target  # external, root-relative, or pure anchor

    # Prose links are repo-relative and written from varying directory depths
    # (./docs/…, ../../docs/…); strip the leading dot-segments so we can match
    # on the repo path regardless of where the source module sits.
    base = re.sub(r"^(?:\.{1,2}/)+", "", base)

    # The frozen-tree inventory lives at src/Legacy/Base/DEPRECATED.md and is
    # linked from many depths; it is not a `.lagda.md` page, so point it at the
    # source on GitHub.
    if base.rsplit("/", 1)[-1] == "DEPRECATED.md":
        return f"{REPO_BLOB}src/Legacy/Base/DEPRECATED.md{anchor}"

    m = re.match(r"^src/(.+)\.lagda\.md$", base)
    if m:
        return f"/{m.group(1)}/{anchor}"
    m = re.match(r"^docs/adr/(.+)\.md$", base)
    if m:
        return f"/adr/{m.group(1)}/{anchor}"
    if base in ON_SITE:
        return ON_SITE[base] + anchor
    if base in TO_BLOB:
        return f"{REPO_BLOB}{base}{anchor}"
    m = re.match(r"^docs/(.+)\.md$", base)   # STYLE_GUIDE, GITHUB_PROJECT, …
    if m:
        return f"/{m.group(1)}/{anchor}"
    # Any other repo-relative path to a non-page file (mkdocs.yml, a script,
    # a stylesheet, a workflow) → view it on GitHub rather than 404 on-site.
    if re.search(r"\.[A-Za-z0-9]+$", base) and not base.endswith(".md"):
        return f"{REPO_BLOB}{base}{anchor}"
    return target


def _cache_bust(entry, docs_dir: Path):
    """Append a short content hash to a local asset reference so a changed file
    gets a fresh URL.  ``entry`` is a ``str`` (extra_css) or an
    ``ExtraScriptValue`` carrying a ``.path`` (extra_javascript).  Absolute URLs
    (CDN links) and already-queried refs pass through untouched.
    """
    has_path = hasattr(entry, "path")
    ref = entry.path if has_path else entry
    if "://" in ref or "?" in ref:
        return entry
    try:
        digest = hashlib.md5((docs_dir / ref).read_bytes()).hexdigest()[:8]
    except OSError:
        return entry                       # not a local file we can hash
    busted = f"{ref}?h={digest}"
    if has_path:
        entry.path = busted
        return entry
    return busted


def on_config(config):
    """Cache-bust the site's own CSS/JS (#429).

    The deployed assets carry a multi-hour ``max-age``, so when custom.css or a
    ``docs/assets/js/*.js`` file changes, a returning visitor can render a stale
    mix — e.g. an updated script against a cached older stylesheet — until the
    cache expires.  Appending an 8-char content hash to each local extra_css /
    extra_javascript URL gives a changed file a fresh URL, which the short-lived
    HTML (``max-age`` 600) picks up within minutes, so the CSS/JS a page loads
    always match the page.  The copied file keeps its plain name; the query
    string is ignored by the server.
    """
    docs_dir = Path(config["docs_dir"])
    config["extra_css"] = [_cache_bust(e, docs_dir) for e in config["extra_css"]]
    config["extra_javascript"] = [_cache_bust(e, docs_dir) for e in config["extra_javascript"]]
    n = sum(1 for e in config["extra_css"] + config["extra_javascript"]
            if "?h=" in (getattr(e, "path", None) or str(e)))
    log.info(f"🔖  cache-busted {n} local asset URL(s)")
    return config


def on_files(files, config):
    """Count the documentation pages so the per-page log can show progress."""
    global _total, _done
    _total = sum(1 for f in files if getattr(f, "is_documentation_page", lambda: False)())
    _done = 0
    return files


def on_page_markdown(markdown: str, *, page=None, config=None, files=None) -> str:
    global _done
    _done += 1
    where = f"[{_done}/{_total}]" if _total else f"[{_done}]"

    out: list[str] = []
    in_code = False
    rewrites = 0
    for line in markdown.split("\n"):
        if FENCE.match(line):
            in_code = not in_code
        elif not in_code:
            new = LINK.sub(lambda m: m.group(1) + _retarget(m.group(2)) + m.group(3), line)
            if new != line:
                rewrites += 1
            line = new
        out.append(line)

    src = getattr(getattr(page, "file", None), "src_uri", None) or getattr(page, "title", "?")
    note = f"  🔗 {rewrites} link(s) retargeted" if rewrites else ""
    log.info(f"  🖋  {where} rendering {src} … ✅{note}")
    return "\n".join(out)

