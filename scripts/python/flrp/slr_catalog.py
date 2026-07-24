"""Transcribe the SmallLatticeReps § 6 catalog into WP-6 pipeline artifacts.

File: scripts/python/flrp/slr_catalog.py

Description:

  The transcription stage of issue #485: read the DeMeo–Freese–Jipsen
  manuscript (``docs/papers/fin-lat-rep/SmallLatticeReps.tex``, 2016-06-10
  draft), whose § 6 catalogs the 35 nondistributive, non-ordinal-sum lattices
  ``L1``–``L35`` of size ≤ 7 together with minimal unary algebras
  ``B1``–``B35`` for most of them, and derive every catalog entry
  mechanically from the manuscript's own LaTeX source:

  + each Hasse diagram is parsed from its tikz code — nodes with coordinates,
    edges oriented upward by y-coordinate — validated for Hasse discipline
    (the drawn edges must be exactly the cover relation of a bounded order),
    closed to the order relation, and tabulated into meet and join tables
    with ``eqsearch.tables_from_leq``;
  + each value table is parsed from its ``array`` block exactly as printed
    (transcription fidelity is the point: parsing the source the paper is
    typeset from *is* exact transcription, and it is re-runnable);
  + a printed claim the engine refutes is a candidate manuscript erratum: it
    is recorded in ``ERRATA`` and the census note's erratum log, and the
    manuscript's data is never altered to make an entry pass (``B28`` is the
    standing example).

  Nothing parsed here is trusted: the emitted modules re-verify every table
  and trace in Agda during ``make check``, and the committed artifacts must
  re-derive from the manuscript byte for byte (``--check``, run by
  ``make flrp-test``).

Usage:

  python3 scripts/python/flrp/slr_catalog.py --write-inputs --emit
  python3 scripts/python/flrp/slr_catalog.py --check
  python3 scripts/python/flrp/slr_catalog.py --dictionary
  python3 scripts/python/flrp/slr_catalog.py --census
  python3 scripts/python/flrp/slr_catalog.py --diagnose 28

  Flags:

  +  ``--census`` prints the per-entry status rows (markdown) of the census
     table in ``docs/notes/flrp-slr-census.md``: certified when the entry's
     certificate module exists, otherwise the parked route (group
     representation, dual, open case) or the erratum verdict.

  +  ``--check`` re-derives every committed artifact from the manuscript —
     claim files and lattice stanzas under ``inputs/slr/``, audit JSONs under
     ``out/slr/``, certificate modules under
     ``src/FLRP/Certificates/SmallLatticeReps/`` — and compares byte for
     byte, printing one ✅/❌ line per catalog entry; any missing or stale
     file fails the run.  ``make flrp-test`` runs this as its golden sweep.

  +  ``--diagnose N`` prints ``Con(B_N)`` of entry ``N``'s printed algebra:
     every congruence in bar notation, re-verified against the value tables
     independently of the cg2 machinery, plus the covers of the inclusion
     order — the reproducible core of the census note's erratum log.

  +  ``--dictionary`` prints the naming-dictionary rows (markdown) of the
     table in ``docs/notes/flrp-slr-naming.md``: per entry, the lattice size,
     the cover relation in the manuscript's own element labels, any standard
     alias (``N5``, ``M3``, the hexagon, …), and the printed algebra's shape.

  +  ``--emit`` audits every unrefuted claim through
     ``lattice.build_certificate`` — which fails loudly on any false claim,
     so a misread diagram or table cannot survive silently — writes the audit
     JSON to ``out/slr/``, and renders the certificate module for every entry
     within the renderer's literal range (since the batch-2 pattern-synonym
     extension, that is all of them).

  +  ``--write-inputs`` writes the transcription itself to ``inputs/slr/``: a
     claim file (``flrp-cert-input v1``, date pinned for byte-stable
     re-emission) for each entry with an unrefuted printed algebra, and a
     bare lattice stanza (a ready-made ``eqsearch.py`` target) for each entry
     without one — the parked entries and the ``B28`` erratum.

  ``make flrp-slr`` is ``--write-inputs --emit``.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import emit_agda
from cg2 import Algebra, CertificateError, Operation, Pair, validate_algebra
from eqsearch import tables_from_leq, validate_target
from lattice import TargetLattice, build_certificate, congruence_lattice

REPO_ROOT = Path(__file__).resolve().parents[3]
TEX_PATH = REPO_ROOT / "docs" / "papers" / "fin-lat-rep" / "SmallLatticeReps.tex"
INPUT_DIR = REPO_ROOT / "scripts" / "python" / "flrp" / "inputs" / "slr"
OUT_DIR = REPO_ROOT / "scripts" / "python" / "flrp" / "out" / "slr"
MODULE_PREFIX = "FLRP.Certificates.SmallLatticeReps"
MODULE_DIR = REPO_ROOT.joinpath("src", *MODULE_PREFIX.split("."))
NAMING_NOTE = "docs/notes/flrp-slr-naming.md"

# Pinned so that re-emission is byte-stable (the claim date is the date the
# catalog was transcribed, not the date the tool happens to run).
DATE = "2026-07-22"

# An entry is renderable iff every index — carrier, operation symbol,
# lattice element — stays within the renderer's literal range (Data.Fin
# .Patterns 0F–9F plus the emitted pattern synonyms of #485 batch 2).
RENDER_LIMIT = emit_agda.LITERAL_LIMIT

# Names this library (or the general literature) already has for some catalog
# lattices; the full dictionary is docs/notes/flrp-slr-naming.md.
AKA: Dict[int, str] = {
    1: "N5",
    2: "M3",
    6: "the hexagon",
    8: "M4",
    10: "library L7",
    33: "M5",
}

# Entries the manuscript ships without an explicit small algebra, with the
# route recorded in the census note (docs/notes/flrp-slr-census.md).
PARKED: Dict[int, str] = {
    10: "open — this library's `L7`, the subject of #484",
    11: "group representation (108-element coset algebra in SmallGroup(216,153)); pending the WP-3 bridge #454 with data from #487",
    14: "group representation (upper interval in Sub(A6), 90 points); pending #454/#487",
    16: "group representation (Sub(C2.A6), 180 points); pending #454/#487",
    18: "dual of L19; assumption-conditional via Kurzweil–Netter duality (#456)",
    20: "group representation (filter-ideal in SmallGroup(216,153)); pending #454/#487",
    22: "dual of L23; assumption-conditional via Kurzweil–Netter duality (#456)",
}

# Candidate manuscript errata: printed claims the engine refutes.  Per the
# #485 discipline the manuscript's data is transcribed exactly and never
# "fixed" to make an entry pass; a refuted entry keeps its lattice stanza
# but gets no claim file or certificate, and the census note's erratum log
# carries the diagnosis (reproducible with --diagnose).
ERRATA: Dict[int, str] = {
    28: "Con(B28) as printed has 8 congruences — a 7-chain plus one doubly "
        "irreducible element — not the 7 elements of L28",
}


# ---------------------------------------------------------------------------
# Parsing the manuscript

ENTRY_RE = re.compile(r"\$\\bL_(?:(\d+)|\{(\d+)\})\$")
NODE_RE = re.compile(r"\\node\((\d+)\)\s*at\s*\(\s*(-?[\d.]+)\s*,\s*(-?[\d.]+)\s*\)")
EDGE_RE = re.compile(r"\\draw\((\d+)\)--\((\d+)\);")
ARRAY_RE = re.compile(r"\\begin\{array\}\{[^}]*\}(.*?)\\end\{array\}", re.DOTALL)
HEADER_RE = re.compile(r"\\bB_(?:(\d+)|\{(\d+)\})")
OP_NAME_RE = re.compile(r"([A-Za-z]+)\(x\)")


@dataclass(frozen=True)
class HasseDiagram:
    """One catalog diagram: element coordinates (indexed by the manuscript's
    own node labels 0..m−1) and the cover relation, each pair (lower, upper)."""

    number: int
    coords: Tuple[Tuple[float, float], ...]
    covers: Tuple[Pair, ...]


@dataclass(frozen=True)
class CatalogEntry:
    """One catalog entry: the diagram, its derived lattice tables, and the
    printed algebra when the manuscript gives one."""

    number: int
    diagram: HasseDiagram
    lattice: TargetLattice
    algebra: Optional[Algebra]


def strip_comments(tex: str) -> str:
    """Drop TeX comments (`%` to end of line); the catalog keeps an obsolete
    B2 table and some annotations only in comments."""
    return re.sub(r"(?<!\\)%[^\n]*", "", tex)


def catalog_source() -> str:
    """The § 6.2 catalog slice of the manuscript, comments stripped."""
    tex = TEX_PATH.read_text()
    start = tex.index("\\subsection{Lattices of size at most 7}")
    end = tex.index("\\bibliographystyle")
    return strip_comments(tex[start:end])


def parse_diagram(number: int, chunk: str) -> HasseDiagram:
    """The tikz picture of one entry, as labeled coordinates plus cover
    pairs oriented upward by y-coordinate (a Hasse diagram's only implicit
    datum is that orientation)."""
    seen: Dict[int, Tuple[float, float]] = {}
    for m in NODE_RE.finditer(chunk):
        label = int(m.group(1))
        if label in seen:
            raise CertificateError(f"L{number}: node {label} defined twice")
        seen[label] = (float(m.group(2)), float(m.group(3)))
    size = len(seen)
    if size == 0 or sorted(seen) != list(range(size)):
        raise CertificateError(f"L{number}: node labels are not 0..{size - 1}")
    coords = tuple(seen[i] for i in range(size))

    covers: List[Pair] = []
    for m in EDGE_RE.finditer(chunk):
        a, b = int(m.group(1)), int(m.group(2))
        if a not in seen or b not in seen:
            raise CertificateError(f"L{number}: edge ({a}, {b}) uses an unknown node")
        ya, yb = seen[a][1], seen[b][1]
        if ya == yb:
            raise CertificateError(
                f"L{number}: edge ({a}, {b}) joins nodes at equal height — "
                "cannot orient a cover")
        covers.append((a, b) if ya < yb else (b, a))
    if len(set(covers)) != len(covers):
        raise CertificateError(f"L{number}: duplicate cover edge")
    return HasseDiagram(number=number, coords=coords, covers=tuple(covers))


def order_closure(diagram: HasseDiagram) -> Tuple[Tuple[bool, ...], ...]:
    """The reflexive-transitive closure of the cover relation, after checking
    Hasse discipline: the drawn edges are exactly the covers of a bounded
    order (no drawn edge is implied by the others, one bottom, one top)."""
    size = len(diagram.coords)
    above: List[List[int]] = [[] for _ in range(size)]
    for lo, hi in diagram.covers:
        above[lo].append(hi)

    def up_set(start: int) -> Tuple[bool, ...]:
        reach = [False] * size
        stack = [start]
        while stack:
            x = stack.pop()
            if not reach[x]:
                reach[x] = True
                stack.extend(above[x])
        return tuple(reach)

    leq = tuple(up_set(i) for i in range(size))

    for lo, hi in diagram.covers:
        if any(z not in (lo, hi) and leq[lo][z] and leq[z][hi] for z in range(size)):
            raise CertificateError(
                f"L{diagram.number}: drawn edge ({lo}, {hi}) is not a cover")
    bottoms = [x for x in range(size) if all(leq[x][y] for y in range(size))]
    tops = [x for x in range(size) if all(leq[y][x] for y in range(size))]
    if len(bottoms) != 1 or len(tops) != 1:
        raise CertificateError(f"L{diagram.number}: order is not bounded")
    return leq


def lattice_name(number: int) -> str:
    alias = f" ({AKA[number]})" if number in AKA else ""
    return f"manuscript L{number}{alias}"


def parse_algebra(number: int, chunk: str) -> Optional[Algebra]:
    """The printed value table of one entry, exactly as typeset: the header
    row pins the carrier 0..n−1, and each following row is one unary
    operation.  Entries without a table (the parked ones) return None."""
    arrays = ARRAY_RE.findall(chunk)
    if not arrays:
        return None
    if len(arrays) > 1:
        raise CertificateError(f"L{number}: more than one value table")

    rows = [row.strip() for row in re.split(r"\\\\", arrays[0].replace("\\hline", ""))]
    rows = [row for row in rows if row]
    header = [cell.strip() for cell in rows[0].split("&")]
    matched = HEADER_RE.fullmatch(header[0])
    if not matched or int(matched.group(1) or matched.group(2)) != number:
        raise CertificateError(f"L{number}: table header names the wrong algebra")
    card = len(header) - 1
    if [int(cell) for cell in header[1:]] != list(range(card)):
        raise CertificateError(f"B{number}: header row is not 0..{card - 1}")

    operations: List[Operation] = []
    for row in rows[1:]:
        cells = [cell.strip() for cell in row.split("&")]
        named = OP_NAME_RE.fullmatch(cells[0])
        if not named:
            raise CertificateError(f"B{number}: malformed operation row {cells[0]!r}")
        table = [int(cell) for cell in cells[1:]]
        if len(table) != card:
            raise CertificateError(
                f"B{number}: operation {named.group(1)} has {len(table)} values, "
                f"expected {card}")
        operations.append(Operation(name=named.group(1), arity=1, table=table))
    if not operations:
        raise CertificateError(f"B{number}: table has no operation rows")

    algebra = Algebra(name=f"B{number}", card=card, operations=tuple(operations))
    validate_algebra(algebra)
    return algebra


def parse_entry(number: int, chunk: str) -> CatalogEntry:
    diagram = parse_diagram(number, chunk)
    lattice = tables_from_leq(lattice_name(number), order_closure(diagram))
    validate_target(lattice)
    return CatalogEntry(number=number, diagram=diagram, lattice=lattice,
                        algebra=parse_algebra(number, chunk))


def parse_catalog() -> Tuple[CatalogEntry, ...]:
    """All 35 entries, in manuscript order."""
    src = catalog_source()
    marks = list(ENTRY_RE.finditer(src))
    numbers = [int(m.group(1) or m.group(2)) for m in marks]
    if numbers != list(range(1, 36)):
        raise CertificateError(f"catalog: expected L1–L35 in order, found {numbers}")
    ends = [m.start() for m in marks[1:]] + [len(src)]
    return tuple(parse_entry(n, src[mark.end():stop])
                 for n, mark, stop in zip(numbers, marks, ends))


# ---------------------------------------------------------------------------
# Rendering the committed artifacts

def provenance(number: int) -> str:
    return (f"`B{number}`/`L{number}` in the numbering of the DeMeo–Freese–Jipsen "
            "manuscript *Representing Finite Lattices as Congruence Lattices of "
            "Finite Algebras* (§ 6 of the 2016-06-10 draft, "
            "`docs/papers/fin-lat-rep/SmallLatticeReps.tex`).  The dictionary "
            "between the manuscript's lattice numbering and this library's names "
            f"is `{NAMING_NOTE}`.")


def lattice_stanza_lines(lattice: TargetLattice, indent: str) -> List[str]:
    """The name/size/meet/join fields, one table row per line (the layout of
    the hand-written pilot claim file)."""

    def table(label: str, rows: Sequence[Sequence[int]], last: bool) -> List[str]:
        body = [json.dumps(list(row)) for row in rows]
        closing = f"{indent}]" + ("" if last else ",")
        return ([f'{indent}"{label}": ['] +
                [f"{indent}  {row}," for row in body[:-1]] +
                [f"{indent}  {body[-1]}", closing])

    return ([f'{indent}"name": {json.dumps(lattice.name, ensure_ascii=False)},',
             f'{indent}"size": {lattice.size},'] +
            table("meet", lattice.meet, last=False) +
            table("join", lattice.join, last=True))


def claim_text(entry: CatalogEntry) -> str:
    """The flrp-cert-input v1 claim file for an entry with an algebra."""
    algebra = entry.algebra
    if algebra is None:
        raise CertificateError(f"L{entry.number}: no algebra to claim")
    lines = [
        "{",
        '  "format": "flrp-cert-input v1",',
        f'  "name": "SLR{entry.number:02d}",',
        f'  "date": "{DATE}",',
        f'  "module": "{MODULE_PREFIX}",',
        f'  "provenance": {json.dumps(provenance(entry.number), ensure_ascii=False)},',
        '  "algebra": {',
        f'    "name": {json.dumps(algebra.name)},',
        f'    "card": {algebra.card},',
        '    "operations": [',
    ]
    for position, op in enumerate(algebra.operations):
        comma = "," if position + 1 < len(algebra.operations) else ""
        lines.append(f'      {{ "name": "{op.name}", "arity": 1, '
                     f'"table": {json.dumps(op.table)} }}{comma}')
    lines += ['    ]', '  },', '  "lattice": {']
    lines += lattice_stanza_lines(entry.lattice, indent="    ")
    lines += ['  }', '}']
    return "\n".join(lines) + "\n"


def stanza_text(entry: CatalogEntry) -> str:
    """A bare lattice stanza (an eqsearch.py target) for a parked entry."""
    return "\n".join(["{"] + lattice_stanza_lines(entry.lattice, indent="  ") +
                     ["}"]) + "\n"


def certifiable(entry: CatalogEntry) -> bool:
    """Has a printed algebra whose claim the engine has not refuted."""
    return entry.algebra is not None and entry.number not in ERRATA


def input_path(entry: CatalogEntry) -> Path:
    suffix = "" if certifiable(entry) else "_lattice"
    return INPUT_DIR / f"slr{entry.number:02d}{suffix}.json"


def input_text(entry: CatalogEntry) -> str:
    return claim_text(entry) if certifiable(entry) else stanza_text(entry)


def audit_path(entry: CatalogEntry) -> Path:
    return OUT_DIR / f"SLR{entry.number:02d}.cert.json"


def module_path(entry: CatalogEntry) -> Path:
    return MODULE_DIR / f"SLR{entry.number:02d}.lagda.md"


def renderable(entry: CatalogEntry) -> bool:
    """Within the v1 renderer's 0F–9F literal range?"""
    assert entry.algebra is not None
    return max(entry.algebra.card, len(entry.algebra.operations),
               entry.lattice.size) <= RENDER_LIMIT


def write_inputs(entries: Sequence[CatalogEntry]) -> None:
    INPUT_DIR.mkdir(parents=True, exist_ok=True)
    for entry in entries:
        path = input_path(entry)
        path.write_text(input_text(entry))
        print(f"wrote    {path.relative_to(REPO_ROOT)}")


def emit_all(entries: Sequence[CatalogEntry]) -> None:
    """Audit every claim through build_certificate and render the modules
    within renderer range; the audits of the out-of-range entries are still
    computed and committed (a false claim must not wait for batch 2)."""
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    for entry in entries:
        if not certifiable(entry):
            continue
        claim_file, audit_file = input_path(entry), audit_path(entry)
        if renderable(entry):
            emit_agda.main([str(claim_file), "--cert-json", str(audit_file)])
        else:
            claim = emit_agda.parse_input(claim_file)
            cert = build_certificate(claim.algebra, claim.lattice)
            audit_file.write_text(
                emit_agda.certificate_json(claim.name, claim.algebra,
                                           claim.lattice, cert))
            print(f"audited  {audit_file.relative_to(REPO_ROOT)} "
                  "(module deferred: carrier past the 0F–9F renderer, #485 batch 2)")


def entry_problems(entry: CatalogEntry) -> List[str]:
    """One entry's missing or stale committed artifacts; [] means current."""
    problems: List[str] = []

    def compare(path: Path, expected: str) -> None:
        rel = path.relative_to(REPO_ROOT).as_posix()
        if not path.exists():
            problems.append(f"missing: {rel}")
        elif path.read_text() != expected:
            problems.append(f"stale: {rel}")

    compare(input_path(entry), input_text(entry))
    if not certifiable(entry) or not input_path(entry).exists():
        return problems
    claim = emit_agda.parse_input(input_path(entry))
    cert = build_certificate(claim.algebra, claim.lattice)
    compare(audit_path(entry),
            emit_agda.certificate_json(claim.name, claim.algebra,
                                       claim.lattice, cert))
    if renderable(entry):
        rel = input_path(entry).relative_to(REPO_ROOT).as_posix()
        compare(module_path(entry), emit_agda.emitted_module(claim, cert, rel))
    return problems


def entry_verified(entry: CatalogEntry) -> str:
    """The verified-artifacts clause of an entry's ✅ line."""
    if not certifiable(entry):
        return "lattice stanza re-derives byte for byte"
    if renderable(entry):
        return "claim file, audit JSON, and module re-derive byte for byte"
    return "claim file and audit JSON re-derive byte for byte (module past the literal cap)"


def check_committed(entries: Sequence[CatalogEntry],
                    verbose: bool = False) -> List[str]:
    """Re-derive every committed artifact from the manuscript and report any
    file that is missing or stale; [] means everything is current.  With
    ``verbose``, print one ✅/❌ line per catalog entry as it is checked
    (the style of the repository's test runners)."""
    all_problems: List[str] = []
    for entry in entries:
        problems = entry_problems(entry)
        all_problems.extend(problems)
        if verbose:
            label = f"L{entry.number}".ljust(4)
            if problems:
                print(f"❌ {label} " + "; ".join(problems))
            else:
                print(f"✅ {label} {entry_verified(entry)}")
    return all_problems


# ---------------------------------------------------------------------------
# Diagnosis of a refuted entry (the erratum log's reproducible core)

def partition_bar(parent: Sequence[int]) -> str:
    """A parent vector in bar notation, blocks and members ascending."""
    blocks: Dict[int, List[int]] = {}
    for i, root in enumerate(parent):
        blocks.setdefault(root, []).append(i)
    return "|" + "|".join(",".join(map(str, blocks[r])) for r in sorted(blocks)) + "|"


def respects_operations(parent: Sequence[int], algebra: Algebra) -> bool:
    """Independent congruence check (no cg2 machinery): the partition is
    compatible with every unary operation table."""
    n = algebra.card
    return all(parent[op.table[i]] == parent[op.table[j]]  # type: ignore[index]
               for op in algebra.operations
               for i in range(n) for j in range(n)
               if parent[i] == parent[j])


def diagnose(entry: CatalogEntry) -> List[str]:
    """The congruences of the entry's printed algebra, each re-verified
    independently of cg2, with the inclusion order's covers — enough to
    refute (or confirm) the printed claim by inspection."""
    if entry.algebra is None:
        return [f"L{entry.number}: no printed algebra to diagnose"]
    parts, _, _ = congruence_lattice(entry.algebra)
    lines = [f"Con(B{entry.number}) has {len(parts)} congruences "
             f"(the printed L{entry.number} has {entry.lattice.size} elements):"]
    for position, parent in enumerate(parts):
        verified = respects_operations(parent, entry.algebra)
        lines.append(f"  θ{position}  {partition_bar(parent)}"
                     f"{'' if verified else '   NOT A CONGRUENCE'}")

    def finer(p: Sequence[int], q: Sequence[int]) -> bool:
        return all(q[i] == q[p[i]] for i in range(len(p)))

    total = len(parts)
    leq = [[finer(parts[a], parts[b]) for b in range(total)] for a in range(total)]
    covers = sorted((a, b) for a in range(total) for b in range(total)
                    if a != b and leq[a][b]
                    and not any(z not in (a, b) and leq[a][z] and leq[z][b]
                                for z in range(total)))
    lines.append("  covers: " + "; ".join(f"θ{a} ≺ θ{b}" for a, b in covers))
    return lines


# ---------------------------------------------------------------------------
# The naming dictionary and census tables (markdown, for the docs notes)

def covers_text(diagram: HasseDiagram) -> str:
    return "; ".join(f"{lo} ≺ {hi}" for lo, hi in sorted(diagram.covers))


def status(entry: CatalogEntry) -> str:
    if entry.number in ERRATA:
        return (f"candidate manuscript erratum — {ERRATA[entry.number]} "
                "(erratum log below); no verified representation in hand")
    if entry.algebra is None:
        return PARKED[entry.number]
    if module_path(entry).exists():
        return f"certified — `{MODULE_PREFIX}.SLR{entry.number:02d}`"
    if not renderable(entry):
        return ("engine-audited (audit JSON committed); certificate module "
                "pending the renderer extension (#485 batch 2)")
    return "claim file ready; module not yet emitted"


def dictionary_rows(entries: Sequence[CatalogEntry]) -> List[str]:
    lines = ["| manuscript | size | covers (manuscript element labels) | also known as | algebra |",
             "|---|---|---|---|---|"]
    for entry in entries:
        aka = AKA.get(entry.number, "—")
        ops = len(entry.algebra.operations) if entry.algebra else 0
        algebra = (f"`B{entry.number}` on {entry.algebra.card} elements, "
                   f"{ops} operation{'s' if ops != 1 else ''}"
                   if entry.algebra else "none printed")
        if entry.number in ERRATA:
            algebra += " — engine-refuted as printed (candidate erratum)"
        lines.append(f"| `L{entry.number}` | {entry.lattice.size} | "
                     f"{covers_text(entry.diagram)} | {aka} | {algebra} |")
    return lines


def census_rows(entries: Sequence[CatalogEntry]) -> List[str]:
    lines = ["| manuscript | size | status |",
             "|---|---|---|"]
    for entry in entries:
        lines.append(f"| `L{entry.number}` | {entry.lattice.size} | {status(entry)} |")
    return lines


# ---------------------------------------------------------------------------
# CLI

def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write-inputs", action="store_true",
                        help="write the claim files and lattice stanzas under inputs/slr/")
    parser.add_argument("--emit", action="store_true",
                        help="audit every claim and render the in-range certificate modules")
    parser.add_argument("--check", action="store_true",
                        help="verify every committed artifact re-derives byte for byte, "
                             "one ✅/❌ line per entry")
    parser.add_argument("--dictionary", action="store_true",
                        help="print the naming-dictionary table rows (markdown)")
    parser.add_argument("--census", action="store_true",
                        help="print the census table rows (markdown)")
    parser.add_argument("--diagnose", type=int, metavar="N", default=None,
                        help="print Con(B<N>) with independent verification (erratum log)")
    args = parser.parse_args(argv)
    if not any((args.write_inputs, args.emit, args.check, args.dictionary,
                args.census, args.diagnose is not None)):
        parser.error("choose at least one action")

    entries = parse_catalog()
    if args.write_inputs:
        write_inputs(entries)
    if args.emit:
        emit_all(entries)
    if args.check:
        problems = check_committed(entries, verbose=True)
        if problems:
            print(f"{len(problems)} committed artifact(s) missing or stale")
            return 1
        print(f"all {len(entries)} catalog entries re-derive byte for byte")
    if args.dictionary:
        print("\n".join(dictionary_rows(entries)))
    if args.census:
        print("\n".join(census_rows(entries)))
    if args.diagnose is not None:
        by_number = {entry.number: entry for entry in entries}
        if args.diagnose not in by_number:
            parser.error(f"no catalog entry L{args.diagnose}")
        print("\n".join(diagnose(by_number[args.diagnose])))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
