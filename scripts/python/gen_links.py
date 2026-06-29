#!/usr/bin/env python3
"""Regenerate docs/_links.md, the site-wide reference-link library (ADR-007).

`pymdownx.snippets` auto-appends docs/_links.md to every page, so any module
can write reference-style links — `[Setoid.Algebras.Basic][]`,
`[Agda Universal Algebra Library][]` — and have them resolve.  Keeping the
module half of that file in sync with the tree by hand is error-prone (it had
fallen ~130 entries behind), so this tool regenerates it:

  + one `[Dotted.Module]: /Slashed/Module/` per module under src/ (root-relative
    so cross-references work under `mkdocs serve` and at ualib.org alike);
  + one `[Slashed/Module.lagda]: <github>/src/Slashed/Module.lagda.md` per module
    for the "view the source" links some prose uses;
  + the external links (and a few fixed library-name / concept links) carried
    over verbatim from the existing file.

Run from the repo root (idempotent):  python3 scripts/python/gen_links.py
"""
from __future__ import annotations

import re
from pathlib import Path

SRC = Path("src")
LINKS = Path("docs/_links.md")
GH = "https://github.com/ualib/agda-algebras/blob/master/src/"

# Conceptual ordering of the top-level groups; others sort after, alphabetically.
TOP_ORDER = ["Overture", "Setoid", "Classical", "Order",
             "Examples", "Exercises", "Demos", "Legacy", "agda-algebras"]

HEADER = """\
<!-- File: docs/_links.md -->
<!-- agda-algebras shared reference-link library (ADR-007). -->
<!-- pymdownx.snippets auto-appends this file to every page so reference-style -->
<!-- links resolve site-wide without a per-page include directive.  Internal -->
<!-- targets are ROOT-RELATIVE so cross-references work under `mkdocs serve` -->
<!-- and at https://ualib.org/ alike.  The module sections are GENERATED from -->
<!-- the src/ tree by scripts/python/gen_links.py; re-run it rather than -->
<!-- editing those entries by hand. -->
"""

# Library-name and concept links the old file targeted at the retired
# GitHub-Pages URL or never defined at all.
EXTRA = [
    "[Agda Universal Algebra Library]: /",
    "[Agda UniversalAlgebra]: /",
    "[agda-algebras-everything]: /agda-algebras/",
    "[UALib]: /",
    "[agda-categories]: https://github.com/agda/agda-categories",
    "[Nix]: https://nixos.org/",
    "[UIP]: https://ncatlab.org/nlab/show/uniqueness+of+identity+proofs",
    "[Containers]: https://ncatlab.org/nlab/show/container",
    "[#308]: https://github.com/ualib/agda-algebras/issues/308",
    "[ADR-007]: /adr/007-mkdocs-rendering-pipeline/",
]


def modules() -> list[tuple[str, str]]:
    mods = []
    for p in sorted(SRC.rglob("*.lagda.md")):
        parts = p.relative_to(SRC).with_suffix("").with_suffix("").parts
        mods.append((".".join(parts), "/".join(parts)))
    mods.sort(key=lambda m: (
        TOP_ORDER.index(m[1].split("/")[0]) if m[1].split("/")[0] in TOP_ORDER
        else len(TOP_ORDER), m[1]))
    return mods


def carried_over_links(mods: list[tuple[str, str]]) -> list[str]:
    """External + non-module-internal link definitions from the current file."""
    module_labels = {d.lower() for d, _ in mods} | {f"{s}.lagda".lower() for _, s in mods}
    out, seen = [], set()
    existing = LINKS.read_text(encoding="utf-8").splitlines() if LINKS.exists() else []
    for line in existing + EXTRA:
        m = re.match(r"^\[([^\]]+)\]:\s*(\S+)", line)
        if not m:
            continue
        label, target = m.group(1), m.group(2)
        external = target.startswith("http") and "/blob/master/src/" not in target
        nonmodule_internal = target.startswith("/") and label.lower() not in module_labels
        if (external or nonmodule_internal) and label.lower() not in seen:
            seen.add(label.lower())
            out.append(f"[{label}]: {target}")
    return out


def main() -> None:
    mods = modules()
    page_defs, src_defs, top = [], [], None
    for dotted, slashed in mods:
        if slashed.split("/")[0] != top:
            page_defs.append("")
            src_defs.append("")
            top = slashed.split("/")[0]
        page_defs.append(f"[{dotted}]: /{slashed}/")
        src_defs.append(f"[{slashed}.lagda]: {GH}{slashed}.lagda.md")

    body = (
        HEADER
        + "\n<!-- ===== Rendered module pages ===== -->\n"
        + "\n".join(page_defs).strip("\n")
        + "\n\n<!-- ===== Module sources on GitHub ===== -->\n"
        + "\n".join(src_defs).strip("\n")
        + "\n\n<!-- ===== External links ===== -->\n"
        + "\n".join(carried_over_links(mods))
        + "\n"
    )
    LINKS.write_text(body, encoding="utf-8")
    print(f"wrote {LINKS}: {len(mods)} modules, {len(body.splitlines())} lines")


if __name__ == "__main__":
    main()
