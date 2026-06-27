"""Mount the agda-algebras library into the MkDocs site (ADR-007).

Run by ``mkdocs-gen-files`` during ``mkdocs build`` / ``mkdocs serve``.  It

  1.  walks ``src/**/*.lagda.md`` and, for each module, writes a *virtual*
      site page at the module's hierarchical path with the ``.lagda`` infix
      stripped — so ``src/Setoid/Algebras/Basic.lagda.md`` is served at
      ``/Setoid/Algebras/Basic/`` rather than ``…/Basic.lagda/`` — after
      lightly normalising the source (drop the Jekyll front matter, drop any
      stray ``{% … %}`` Liquid tags, and prepend a clean ``# Dotted.Module``
      title so every page has a real heading); and

  2.  emits ``SUMMARY.md``, the literate-nav file that becomes the whole site
      navigation: a hand-curated top matter (Home, Project docs) wrapped
      around the auto-generated library tree, with each barrel module acting
      as the clickable section-index page for its subtree.

The script never touches the real sources; it only shapes the rendered copy.
Inline Agda highlighting comes from the kramdown attribute spans already in
the prose (``Algebra``{.AgdaRecord}) plus ``docs/stylesheets/custom.css`` —
there is no ``agda --html`` step (architecture (b) of issue #295).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional

import mkdocs_gen_files

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

SRC_DIR = Path("src")
DOCS_DIR = Path("docs")
ADR_DIR = DOCS_DIR / "adr"

# Conceptual reading order of the top-level groups; anything not listed is
# appended alphabetically so a newly-added top-level tree still shows up.
TOP_LEVEL_ORDER: list[str] = [
    "Overture",    # foundations
    "Setoid",      # the canonical 3.0 development tree
    "Classical",   # classical-structures layer over the UA foundation
    "Order",       # order-theoretic support
    "Examples",    # worked examples
    "Exercises",   # exercises
    "Demos",       # self-contained demonstrations (e.g. the HSP theorem)
    "Legacy",      # frozen Base/ tree (read-only; see ADR-001)
]

# The everything-barrel: rendered (so its URL exists) but parked at the end
# of the library nav rather than promoted as a top-level group.
EVERYTHING_MODULE = "agda-algebras"

FRONT_MATTER_RE = re.compile(r"\A---\r?\n.*?\r?\n---\r?\n", re.DOTALL)
LIQUID_LINE_RE = re.compile(r"^[ \t]*\{%.*?%\}[ \t]*\r?\n?", re.MULTILINE)
FIRST_H1_RE = re.compile(r"^# \S", re.MULTILINE)


# --------------------------------------------------------------------------
# Per-page source → site transformation
# --------------------------------------------------------------------------

def dotted_name(parts: tuple[str, ...]) -> str:
    """``("Setoid", "Algebras", "Basic")`` → ``"Setoid.Algebras.Basic"``."""
    return ".".join(parts)


def normalise(source: str, title: str) -> str:
    """Shape a raw ``.lagda.md`` source into a clean MkDocs page.

    Drops the Jekyll front matter and any leftover Liquid include tags, then
    guarantees a top-level ``# Dotted.Module`` heading (the corpus leads with
    ``####`` sub-headings, so without this the page would render titleless).
    """
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
    """A node in the module tree: an optional page plus ordered children."""

    def __init__(self, name: str) -> None:
        self.name = name
        self.page: Optional[str] = None            # site path, e.g. "Setoid/Algebras/Basic.md"
        self.children: dict[str, "Node"] = {}

    def child(self, name: str) -> "Node":
        return self.children.setdefault(name, Node(name))


def emit_node(node: Node, lines: list[str], depth: int) -> None:
    """Render ``node``'s children as an indented Markdown nav list.

    A child that has both a page and descendants becomes a clickable
    section-index (a link that also carries nested items); a child with only a
    page is a leaf link; a child with only descendants is a bare section.
    """
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
    """Nav lines for the Architecture Decision Records, ordered by number."""
    lines: list[str] = []
    for path in sorted(ADR_DIR.glob("*.md")):
        if path.name == "README.md":
            continue
        # Prefer the document's own ``# ADR-NNN: …`` title for the nav label.
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

root = Node("")
everything_page: Optional[str] = None

for src_path in sorted(SRC_DIR.rglob("*.lagda.md")):
    parts = src_path.relative_to(SRC_DIR).with_suffix("").with_suffix("").parts
    dotted = dotted_name(parts)
    dest = Path(*parts).with_suffix(".md").as_posix()

    with mkdocs_gen_files.open(dest, "w") as fh:
        fh.write(normalise(src_path.read_text(encoding="utf-8"), dotted))
    mkdocs_gen_files.set_edit_path(dest, src_path.as_posix())

    if dotted == EVERYTHING_MODULE:
        everything_page = dest
        continue

    node = root
    for part in parts:
        node = node.child(part)
    node.page = dest

# ---- Mount repo-root meta files as polished on-site pages -----------------
# These live at the repo root (outside docs/), so they are mounted here; the
# build hook rewrites their repo-relative links into site URLs.
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


# ---- Assemble SUMMARY.md (the entire site navigation) --------------------

nav: list[str] = ["- [Home](index.md)", "- The Library"]

ordered_tops = [t for t in TOP_LEVEL_ORDER if t in root.children]
ordered_tops += [t for t in sorted(root.children) if t not in TOP_LEVEL_ORDER]

for top in ordered_tops:
    group = Node("")
    group.children[top] = root.children[top]
    emit_node(group, nav, 1)

if everything_page is not None:
    nav.append(f"    - [Everything (module index)]({everything_page})")

nav += [
    "- Project",
    "    - [Roadmap](GITHUB_PROJECT.md)",
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
