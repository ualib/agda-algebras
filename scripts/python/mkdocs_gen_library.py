"""Mount the agda-algebras library into the MkDocs site (ADR-007).

Run by ``mkdocs-gen-files`` during ``mkdocs build`` / ``mkdocs serve``.  It

  1.  walks ``src/**/*.lagda.md`` and, for each module, writes a *virtual* site
      page at the module's hierarchical path with the ``.lagda`` infix stripped
      (``/Setoid/Algebras/Basic/``).  Two rendering modes (#3a):

        + **highlighted** — if ``.agda-html/md/<Dotted>.md`` exists (produced by
          ``make agda-md``, i.e. ``agda --html --html-highlight=code``), mount
          that: its code blocks are ``<pre class="Agda">`` with every token
          semantically classed and hyperlinked to its definition.  Agda's
          ``Module.Sub.html#id`` hrefs are rewritten to the site scheme
          (``/Module/Sub/#id`` for library modules, ``/classic/…`` for stdlib);
        + **plain** — otherwise mount the raw ``.lagda.md`` (fast path, used by
          ``make site`` for quick prose/theme iteration);

  2.  copies the classic ``agda --html`` site from ``html/`` to ``/classic/``
      (#1) — ``Everything.html`` as the index — so it works under both build and
      serve, and serves as the stdlib link target for the highlighted code; and

  3.  emits ``SUMMARY.md``, the literate-nav file that becomes the navigation.

In every mode the Jekyll front matter is dropped and a ``# Dotted.Module`` title
is prepended.  The real sources are never modified.
"""

from __future__ import annotations

import json
import logging
import re
from pathlib import Path
from typing import Optional

import mkdocs_gen_files

log = logging.getLogger("mkdocs.plugins.ualib.gen")

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

SRC_DIR = Path("src")
DOCS_DIR = Path("docs")
ADR_DIR = DOCS_DIR / "adr"
AGDA_MD_DIR = Path(".agda-html/md")     # agda --html --html-highlight=code output
CLASSIC_DIR = Path("html")              # agda --html (classic full-page) output

TOP_LEVEL_ORDER: list[str] = [
    "Overture", "Setoid", "Classical", "Order",
    "Examples", "Exercises", "Demos", "Legacy",
]
EVERYTHING_MODULE = "agda-algebras"

FRONT_MATTER_RE = re.compile(r"\A---\r?\n.*?\r?\n---\r?\n", re.DOTALL)
LIQUID_LINE_RE = re.compile(r"^[ \t]*\{%.*?%\}[ \t]*\r?\n?", re.MULTILINE)
FIRST_H1_RE = re.compile(r"^# \S", re.MULTILINE)
# An agda --html hyperlink: href="Module.Dotted.html" with an optional #offset.
AGDA_HREF_RE = re.compile(r'href="([A-Za-z0-9._]+)\.html(#\d+)?"')


# --------------------------------------------------------------------------
# Per-page source → site transformation
# --------------------------------------------------------------------------

def dotted_name(parts: tuple[str, ...]) -> str:
    return ".".join(parts)


def rewrite_agda_hrefs(html: str, library: set[str]) -> str:
    """Rewrite agda --html token links into the MkDocs URL scheme.

    Library modules → the rendered page (``/Setoid/Algebras/Basic/#id``); every
    other target (the standard library) → the self-contained classic site at
    ``/classic/Module.html#id``, whose char-offset anchors match exactly.
    """
    def repl(m: "re.Match[str]") -> str:
        mod, anchor = m.group(1), m.group(2) or ""
        if mod in library:
            return f'href="/{mod.replace(".", "/")}/{anchor}"'
        return f'href="/classic/{mod}.html{anchor}"'
    return AGDA_HREF_RE.sub(repl, html)


def normalise(source: str, title: str) -> str:
    """Drop the Jekyll front matter / Liquid tags and ensure a ``# Title`` H1."""
    body = FRONT_MATTER_RE.sub("", source, count=1)
    body = LIQUID_LINE_RE.sub("", body)
    body = body.lstrip("\n")
    if not FIRST_H1_RE.search(body):
        body = f"# {title}\n\n{body}"
    return body


# --------------------------------------------------------------------------
# Navigation tree
# --------------------------------------------------------------------------

class Node:
    def __init__(self, name: str) -> None:
        self.name = name
        self.page: Optional[str] = None
        self.children: dict[str, "Node"] = {}

    def child(self, name: str) -> "Node":
        return self.children.setdefault(name, Node(name))


def emit_node(node: Node, lines: list[str], depth: int) -> None:
    indent = "    " * depth
    for name in sorted(node.children):
        kid = node.children[name]
        if kid.page and kid.children:
            lines.append(f"{indent}- [{name}]({kid.page})")
            emit_node(kid, lines, depth + 1)
        elif kid.page:
            lines.append(f"{indent}- [{name}]({kid.page})")
        else:
            lines.append(f"{indent}- {name}")
            emit_node(kid, lines, depth + 1)


def adr_entries() -> list[str]:
    lines: list[str] = []
    for path in sorted(ADR_DIR.glob("*.md")):
        if path.name == "README.md":
            continue
        label = path.stem
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                label = line[2:].strip()
                break
        lines.append(f"        - [{label}](adr/{path.name})")
    return lines


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

modules = sorted(SRC_DIR.rglob("*.lagda.md"))
library = {dotted_name(p.relative_to(SRC_DIR).with_suffix("").with_suffix("").parts)
           for p in modules}
highlight = AGDA_MD_DIR.is_dir()

mode = "highlighted (agda --html)" if highlight else "plain (no agda --html — run `make agda-md` for highlighting)"
log.info(f"📚  Mounting {len(modules)} library modules — {mode}")

root = Node("")
everything_page: Optional[str] = None
n_high = n_plain = 0

for src_path in modules:
    parts = src_path.relative_to(SRC_DIR).with_suffix("").with_suffix("").parts
    dotted = dotted_name(parts)
    dest = Path(*parts).with_suffix(".md").as_posix()

    agda_md = AGDA_MD_DIR / f"{dotted}.md"
    if highlight and agda_md.is_file():
        body = normalise(rewrite_agda_hrefs(agda_md.read_text(encoding="utf-8"), library), dotted)
        n_high += 1
        mark = "✨ highlighted"
    else:
        body = normalise(src_path.read_text(encoding="utf-8"), dotted)
        n_plain += 1
        mark = "◻ plain"

    with mkdocs_gen_files.open(dest, "w") as fh:
        fh.write(body)
    mkdocs_gen_files.set_edit_path(dest, src_path.as_posix())
    log.info(f"  🛠  {dotted}  {mark}")

    if dotted == EVERYTHING_MODULE:
        everything_page = dest
        continue
    node = root
    for part in parts:
        node = node.child(part)
    node.page = dest

log.info(f"✅  Mounted {len(modules)} modules ({n_high} highlighted, {n_plain} plain)")

# ---- Classic agda --html site at /classic/ (#1) ---------------------------
n_classic = 0
if CLASSIC_DIR.is_dir():
    for f in sorted(CLASSIC_DIR.iterdir()):
        if f.suffix in (".html", ".css"):
            with mkdocs_gen_files.open(f"classic/{f.name}", "wb") as fh:
                fh.write(f.read_bytes())
            n_classic += 1
    log.info(f"📦  /classic/: published {n_classic} agda --html pages (index: Everything.html)")
else:
    log.info("📦  /classic/: skipped (run `make html` to build the classic site)")

# ---- Repo-root meta pages -------------------------------------------------
META_PAGES = {
    "install.md": (Path("INSTALL.md"), "Installation"),
    "contributing.md": (Path("CONTRIBUTING.md"), "Contributing"),
    "changelog.md": (Path("CHANGELOG.md"), "Changelog"),
}
for dest, (src_path, title) in META_PAGES.items():
    if src_path.exists():
        with mkdocs_gen_files.open(dest, "w") as fh:
            fh.write(normalise(src_path.read_text(encoding="utf-8"), title))
        mkdocs_gen_files.set_edit_path(dest, src_path.as_posix())

# ---- Module-dependency constellation data (#6) ----------------------------
# A force-graph of the library's internal import structure: one node per module
# (grouped by top-level tree, sized by how many modules import it), one edge per
# internal import.  docs/assets/js/constellation.js renders it with d3.
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z][A-Za-z0-9.]*)")
indeg = {m: 0 for m in library}
links: list[dict] = []
for src_path in modules:
    me = dotted_name(src_path.relative_to(SRC_DIR).with_suffix("").with_suffix("").parts)
    in_code, seen = False, set()
    for line in src_path.read_text(encoding="utf-8").split("\n"):
        if line.lstrip().startswith("```"):
            in_code = not in_code
            continue
        if not in_code:
            continue
        m = IMPORT_RE.match(line)
        if m and m.group(1) in library and m.group(1) != me and m.group(1) not in seen:
            seen.add(m.group(1))
            links.append({"source": me, "target": m.group(1)})
            indeg[m.group(1)] += 1
nodes = [{"id": m, "group": m.split(".")[0], "deg": indeg[m],
          "url": "/" + m.replace(".", "/") + "/"} for m in sorted(library)]
with mkdocs_gen_files.open("assets/constellation.json", "w") as fh:
    fh.write(json.dumps({"nodes": nodes, "links": links}))
log.info(f"🌌  constellation: {len(nodes)} nodes, {len(links)} edges")


# ---- Assemble SUMMARY.md --------------------------------------------------
nav: list[str] = ["- [Home](index.md)", "- The Library"]
ordered_tops = [t for t in TOP_LEVEL_ORDER if t in root.children]
ordered_tops += [t for t in sorted(root.children) if t not in TOP_LEVEL_ORDER]
for top in ordered_tops:
    group = Node("")
    group.children[top] = root.children[top]
    emit_node(group, nav, 1)
if everything_page is not None:
    nav.append(f"    - [Everything (module index)]({everything_page})")
if CLASSIC_DIR.is_dir():
    nav.append("    - [Classic Agda HTML ↗](classic/Everything.html)")
nav.append("- [Constellation](constellation.md)")

nav += [
    "- Project",
    "    - [Roadmap](GITHUB_PROJECT.md)",
    "    - [Maintaining the site](site-guide.md)",
    "    - [Style Guide](STYLE_GUIDE.md)",
    "    - Architecture Decisions",
    "        - [Overview](adr/README.md)",
    *adr_entries(),
    "    - [Installation](install.md)",
    "    - [Contributing](contributing.md)",
    "    - [Changelog](changelog.md)",
]
with mkdocs_gen_files.open("SUMMARY.md", "w") as fh:
    fh.write("\n".join(nav) + "\n")

log.info("🧹  gen-files complete — handing off to the renderer")
