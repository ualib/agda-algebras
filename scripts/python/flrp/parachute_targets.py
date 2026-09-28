"""
File: scripts/python/flrp/parachute_targets.py

Description: Target lattice stanzas for the RP-3 parachute realizability sweep.

  The RP-3 hunt (docs/notes/flrp-rp3-hunt.md) uses the smallest parachutes
  with two big canopies as GAP interval-search targets: a core-free group
  representation of such a parachute is a positive instance of the note's
  statement (C) for the corresponding family of cf-IE classes, and its
  absence over a bounded slice of the group libraries is a recorded lower
  bound (never a non-representability claim).  This module is the
  deterministic generator of the target stanzas under
  scripts/gap/flrp/inputs/, in the shared stanza format of
  eqsearch.parse_target; the meet/join tables come from the one canonical
  implementation, eqsearch.tables_from_leq, never re-derived by hand.

  The M6-27 pass (docs/notes/flrp-m6-27-paths.md) adds two targets that are
  not seven-element parachutes: P(2x2, 2x2), the smallest coatomistic
  parachute with two big canopies, which is the least lattice the parachute
  analog of Aschbacher's Theorem 3 reaches; and the fourteen-element
  DDelta(3,3), the smallest lattice of Shareshian's Conjecture D, which is not
  a parachute at all (its two components have no least element).  The
  generator is indifferent to the shape: a target is any bounded lattice
  given by its Hasse diagram.

  Regenerate with `python3 scripts/python/flrp/parachute_targets.py`; verify
  that the committed copies re-derive byte for byte with `--check` (run by
  test_parachute_targets.py, part of make flrp-test).
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence, Tuple

from cg2 import CertificateError
from eqsearch import tables_from_leq, validate_target

STANZA_DIR = Path("scripts/gap/flrp/inputs")

Cover = Tuple[int, int]


@dataclass(frozen=True)
class TargetSpec:
    """One parachute target: a stanza filename stem, a display name, and the
    Hasse diagram (0-based covers; 0 is the bottom, size - 1 the top)."""
    stem: str
    name: str
    size: int
    covers: Tuple[Cover, ...]


# The four smallest parachutes with two canopies of more than two elements,
# element order: bottom, then each canopy's proper elements atom-upward, then
# the shared top.  These are exactly the least lattices to which the note's
# Lemma 3.7 and statement (C) apply, which is what makes their group
# realizability worth recording.
TARGETS: Tuple[TargetSpec, ...] = (
    TargetSpec(
        stem="p33",
        name="P(3,3): parachute of two three-chains",
        size=6,
        covers=((0, 1), (1, 2), (2, 5), (0, 3), (3, 4), (4, 5))),
    TargetSpec(
        stem="p332",
        name="P(3,3,2): parachute of two three-chains and a two-chain",
        size=7,
        covers=((0, 1), (1, 2), (2, 6), (0, 3), (3, 4), (4, 6), (0, 5), (5, 6))),
    TargetSpec(
        stem="p34",
        name="P(3,4): parachute of a three-chain and a four-chain",
        size=7,
        covers=((0, 1), (1, 2), (2, 6), (0, 3), (3, 4), (4, 5), (5, 6))),
    TargetSpec(
        stem="p3m2",
        name="P(3,2x2): parachute of a three-chain and the four-element Boolean lattice",
        size=7,
        covers=((0, 1), (1, 2), (2, 6), (0, 3), (3, 4), (3, 5), (4, 6), (5, 6))),
    # M6-27: the smallest coatomistic parachute with two big canopies.  Element
    # order: bottom; canopy 1 (atom 1, coatoms 2 and 3); canopy 2 (atom 4,
    # coatoms 5 and 6); top.
    TargetSpec(
        stem="pm2m2",
        name="P(2x2,2x2): parachute of two four-element Boolean lattices",
        size=8,
        covers=((0, 1), (1, 2), (1, 3), (2, 7), (3, 7),
                (0, 4), (4, 5), (4, 6), (5, 7), (6, 7))),
    # M6-27: the dual of P(2x2,2x2), scanned as well since Kurzweil-Netter
    # duality makes the two representability questions one.  Element order:
    # bottom; the two dual coatoms of canopy 1 (1, 2) below the dual atom 5;
    # those of canopy 2 (3, 4) below the dual atom 6; top.
    TargetSpec(
        stem="pm2m2d",
        name="dual of P(2x2,2x2): two four-element Boolean lattices hanging from the top",
        size=8,
        covers=((0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 5), (3, 6), (4, 6),
                (5, 7), (6, 7))),
    # M6-27: DDelta(3,3), the smallest lattice of Shareshian's Conjecture D.
    # Element order: bottom; component 1 (atoms 1, 2, 3, coatoms 4 = {1,2},
    # 5 = {1,3}, 6 = {2,3}); component 2 (atoms 7, 8, 9, coatoms 10, 11, 12
    # likewise); top.  Not a parachute: neither component has a least element.
    TargetSpec(
        stem="dd33",
        name="DDelta(3,3): two copies of the proper part of the rank-3 Boolean lattice",
        size=14,
        covers=((0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 4), (2, 6), (3, 5), (3, 6),
                (4, 13), (5, 13), (6, 13),
                (0, 7), (0, 8), (0, 9), (7, 10), (7, 11), (8, 10), (8, 12), (9, 11), (9, 12),
                (10, 13), (11, 13), (12, 13))),
)


def leq_from_covers(spec: TargetSpec) -> Tuple[Tuple[bool, ...], ...]:
    """The reflexive-transitive closure of the cover relation, with Hasse
    discipline checked: every drawn edge really is a cover, and the order is
    bounded with bottom 0 and top size - 1."""
    size = spec.size
    if any(not (0 <= lo < size and 0 <= hi < size) for lo, hi in spec.covers):
        raise CertificateError(f"{spec.stem}: cover index out of range")

    def up_set(start: int) -> Tuple[bool, ...]:
        reach = [False] * size
        stack = [start]
        while stack:
            x = stack.pop()
            if not reach[x]:
                reach[x] = True
                stack.extend(hi for lo, hi in spec.covers if lo == x)
        return tuple(reach)

    leq = tuple(up_set(i) for i in range(size))
    for lo, hi in spec.covers:
        if any(z not in (lo, hi) and leq[lo][z] and leq[z][hi] for z in range(size)):
            raise CertificateError(f"{spec.stem}: edge ({lo}, {hi}) is not a cover")
    if not all(leq[0][y] for y in range(size)):
        raise CertificateError(f"{spec.stem}: 0 is not the bottom")
    if not all(leq[y][size - 1] for y in range(size)):
        raise CertificateError(f"{spec.stem}: {size - 1} is not the top")
    return leq


def stanza(spec: TargetSpec) -> str:
    """The stanza JSON text for one target, via the canonical table builder;
    validation guarantees the poset really is a bounded lattice.  Rendered
    with one table row per line, matching the committed two_by_two.json."""
    lat = tables_from_leq(spec.name, leq_from_covers(spec))
    validate_target(lat)

    def table(rows: Sequence[Sequence[int]]) -> str:
        body = ",\n    ".join(json.dumps(list(row)) for row in rows)
        return "[\n    " + body + "\n  ]"

    return ("{\n"
            f"  \"name\": {json.dumps(lat.name)},\n"
            f"  \"size\": {lat.size},\n"
            f"  \"meet\": {table(lat.meet)},\n"
            f"  \"join\": {table(lat.join)}\n"
            "}\n")


def stanza_path(spec: TargetSpec) -> Path:
    return STANZA_DIR / f"{spec.stem}.json"


def write_stanzas() -> Sequence[Path]:
    """Write every target stanza; returns the paths written."""
    STANZA_DIR.mkdir(parents=True, exist_ok=True)
    for spec in TARGETS:
        stanza_path(spec).write_text(stanza(spec))
    return [stanza_path(spec) for spec in TARGETS]


def check_stanzas() -> Sequence[str]:
    """Compare the committed stanzas against regeneration; returns the list
    of mismatch descriptions (empty means everything re-derives byte for
    byte)."""
    def mismatch(spec: TargetSpec) -> Sequence[str]:
        path = stanza_path(spec)
        if not path.exists():
            return [f"{path}: missing (run parachute_targets.py)"]
        if path.read_text() != stanza(spec):
            return [f"{path}: committed copy does not re-derive"]
        return []

    return [msg for spec in TARGETS for msg in mismatch(spec)]


def main(argv: Sequence[str]) -> int:
    if "--check" in argv:
        problems = check_stanzas()
        for msg in problems:
            print(msg, file=sys.stderr)
        print(f"parachute targets: {len(TARGETS)} stanzas, "
              f"{'OK' if not problems else f'{len(problems)} problem(s)'}")
        return 0 if not problems else 1
    for path in write_stanzas():
        print(f"wrote {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
