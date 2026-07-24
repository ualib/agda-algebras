#!/usr/bin/env python3
"""Regenerate docs/_links.md, the site-wide reference-link library (ADR-007).

`pymdownx.snippets` auto-appends docs/_links.md to every page, so any module
can write reference-style links — `[Setoid.Algebras.Basic][]`, `[ADR-008][]`,
`[Agda Universal Algebra Library][]` — and have them resolve.  Keeping that file
in sync with the tree by hand is error-prone (it had fallen ~130 entries behind,
and every new ADR was a fresh broken `[ADR-NNN][]`), so this tool regenerates the
GENERATED sections from the filesystem:

  + one `[Dotted.Module]: /Slashed/Module/` per module under src/ (root-relative
    so cross-references work under `mkdocs serve` and at the deployed site alike);
  + one `[Slashed/Module.lagda]: <github>/src/Slashed/Module.lagda.md` per module
    for the "view the source" links some prose uses;
  + one `[ADR-NNN]: /adr/NNN-slug/` per Architecture Decision Record under
    docs/adr/ (root-relative — the ADRs render on-site, see mkdocs_gen_library.py);
  + the external links (and a few fixed library-name / concept links) carried
    over verbatim from the existing file.

Run from the repo root (idempotent):  python3 scripts/python/gen_links.py

Pass --check to verify the committed file is exactly what this tool produces and
exit non-zero (printing a diff) if it has drifted — this is what CI runs so a new
module or ADR can never silently ship a broken reference-style link again.
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

SRC = Path("src")
ADR = Path("docs/adr")
LINKS = Path("docs/_links.md")
GH = "https://github.com/ualib/agda-algebras/blob/master/src/"

# Conceptual ordering of the top-level groups; others sort after, alphabetically.
TOP_ORDER = ["Overture", "Setoid", "Classical", "Order",
             "Examples", "Exercises", "Legacy", "agda-algebras"]

HEADER = """\
<!-- File: docs/_links.md -->
<!-- agda-algebras shared reference-link library (ADR-007). -->
<!-- pymdownx.snippets auto-appends this file to every page so reference-style -->
<!-- links resolve site-wide without a per-page include directive.  Internal -->
<!-- targets are ROOT-RELATIVE so cross-references work under `mkdocs serve` -->
<!-- and at the deployed site alike.  The module and ADR sections are GENERATED -->
<!-- from the src/ and docs/adr/ trees by scripts/python/gen_links.py; re-run it -->
<!-- rather than editing those entries by hand (CI runs it with --check).  New -->
<!-- external links may be added by hand to the External-links section. -->
"""

# Library-name and concept links the old file targeted at the retired
# GitHub-Pages URL or never defined at all.  (ADR labels are NOT listed here:
# they are generated from docs/adr/ so a new ADR is picked up automatically.)
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


def adrs() -> list[tuple[str, str]]:
    """(label, target) per numbered ADR, e.g.
    ('ADR-008', '/adr/008-two-layer-congruence-discipline/').  The ADRs render
    as on-site pages (mkdocs_gen_library.adr_entries), so the target is the
    root-relative site URL, matching the [ADR-007] precedent."""
    out = []
    for p in sorted(ADR.glob("*.md")):
        m = re.match(r"^(\d+)-", p.name)
        if m:
            out.append((f"ADR-{m.group(1)}", f"/adr/{p.stem}/"))
    return out


def carried_over_links(skip: set[str]) -> list[str]:
    """External + non-generated link definitions from the current file, in file
    order, minus any label that is (re)generated here (``skip``)."""
    out, seen = [], set()
    existing = LINKS.read_text(encoding="utf-8").splitlines() if LINKS.exists() else []
    for line in existing + EXTRA:
        m = re.match(r"^\[([^\]]+)\]:\s*(\S+)", line)
        if not m:
            continue
        label, target = m.group(1), m.group(2)
        key = label.lower()
        if key in skip or key in seen:
            continue
        external = target.startswith("http") and "/blob/master/src/" not in target
        internal = target.startswith("/")
        if external or internal:
            seen.add(key)
            out.append(f"[{label}]: {target}")
    return out


def render() -> str:
    mods = modules()
    adr = adrs()
    page_defs, src_defs, top = [], [], None
    for dotted, slashed in mods:
        if slashed.split("/")[0] != top:
            page_defs.append("")
            src_defs.append("")
            top = slashed.split("/")[0]
        page_defs.append(f"[{dotted}]: /{slashed}/")
        src_defs.append(f"[{slashed}.lagda]: {GH}{slashed}.lagda.md")

    # Labels this tool owns, so carry-over never re-emits a stale copy of them.
    skip = {d.lower() for d, _ in mods} | {f"{s}.lagda".lower() for _, s in mods}
    skip |= {label.lower() for label, _ in adr}

    return (
        HEADER
        + "\n<!-- ===== Rendered module pages ===== -->\n"
        + "\n".join(page_defs).strip("\n")
        + "\n\n<!-- ===== Module sources on GitHub ===== -->\n"
        + "\n".join(src_defs).strip("\n")
        + "\n\n<!-- ===== Architecture Decision Records ===== -->\n"
        + "\n".join(f"[{label}]: {target}" for label, target in adr)
        + "\n\n<!-- ===== External links ===== -->\n"
        + "\n".join(carried_over_links(skip))
        + "\n"
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="fail (with a diff) if docs/_links.md is out of sync")
    args = ap.parse_args()

    body = render()
    n_mods = len(modules())
    n_adr = len(adrs())

    if args.check:
        current = LINKS.read_text(encoding="utf-8") if LINKS.exists() else ""
        if current != body:
            diff = difflib.unified_diff(
                current.splitlines(keepends=True), body.splitlines(keepends=True),
                fromfile=f"{LINKS} (committed)", tofile=f"{LINKS} (regenerated)")
            sys.stderr.write("".join(diff))
            sys.stderr.write(
                f"\n{LINKS} is out of sync with the src/ + docs/adr/ trees.\n"
                "Run:  python3 scripts/python/gen_links.py\n")
            return 1
        print(f"{LINKS} is up to date ({n_mods} modules, {n_adr} ADRs).")
        return 0

    LINKS.write_text(body, encoding="utf-8")
    print(f"wrote {LINKS}: {n_mods} modules, {n_adr} ADRs, {len(body.splitlines())} lines")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
