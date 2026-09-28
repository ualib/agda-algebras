"""Summarize a tables-of-marks scan (`make gap-tomscan`).

File: scripts/python/flrp/tomscan_summary.py

Description:

  `scripts/gap/flrp/bin/tomscan.g` hunts a target lattice as an upper interval
  `[H, G]` across GAP's library of tables of marks and prints one line per
  event: `HIT` (a marks-exact interval isomorphic to the target), `AMBIGUOUS`
  (a size match the marks cannot decide), `EXPLICIT` (an ambiguous case
  recomputed through IntermediateSubgroups, with its verdict), `UNRESOLVED` (an
  ambiguous case above the resolution bound), and a final `scanned` tally.
  GAP wraps long lines, so a record can span several physical lines.

  This module unwraps that log and writes the canonical `flrp-tomscan v1`
  record: the tally, every hit with its interval orders, every explicit
  resolution with its verdict, every unresolved table, and the ambiguous
  cases.  Nothing is trusted or re-derived here; the record is a faithful,
  deterministic transcription of the engine's output, kept so that the survey
  notes' aggregate claims ("sixteen hits in 414 tables", "smallest carrier")
  re-derive from a committed file.  Timings are dropped so that a rerun
  reproduces the record byte for byte.

  `--upsets STANZA.json` prints the GAP up-set list of a committed target
  stanza (`k <= j` iff `meet[k][j] == k`, 1-based), so that the Makefile passes
  targets from the stanzas under scripts/gap/flrp/inputs/ rather than by hand.

Usage:

  python3 scripts/python/flrp/tomscan_summary.py --upsets scripts/gap/flrp/inputs/p33.json
  python3 scripts/python/flrp/tomscan_summary.py RUN.log \\
      --target scripts/gap/flrp/inputs/p33.json \\
      --out scripts/gap/flrp/out/tomscan_p33.json --date 2026-09-28
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

FORMAT = "flrp-tomscan v1"

RECORD_HEADS = ("HIT", "AMBIGUOUS", "EXPLICIT", "UNRESOLVED", "scanned")


@dataclass(frozen=True)
class Hit:
    """A marks-exact upper interval isomorphic to the target."""
    table: str
    order: int
    cls: int
    subgroupOrder: int
    index: int
    intervalOrders: Tuple[int, ...]


@dataclass(frozen=True)
class Ambiguous:
    """A size match whose poset the marks do not determine."""
    table: str
    order: int
    cls: int
    subgroupOrder: int
    index: int


@dataclass(frozen=True)
class Explicit:
    """An ambiguous case recomputed explicitly, with its verdict."""
    table: str
    cls: int
    order: int
    subgroupOrder: int
    structure: str
    index: int
    coreFree: bool
    intervalSize: int
    intervalOrders: Tuple[int, ...]
    target: bool


@dataclass(frozen=True)
class Unresolved:
    """An ambiguous case above the explicit-resolution bound."""
    table: str
    cls: int
    order: int


@dataclass(frozen=True)
class Tally:
    """The scan's closing line."""
    tables: int
    targetSize: int
    intervals: int
    hits: int
    ambiguous: int


@dataclass(frozen=True)
class Summary:
    tally: Optional[Tally]
    hits: Tuple[Hit, ...]
    ambiguous: Tuple[Ambiguous, ...]
    explicit: Tuple[Explicit, ...]
    unresolved: Tuple[Unresolved, ...]
    unparsed: Tuple[str, ...]
    gapVersion: Optional[str]
    tomlibVersion: Optional[str]


# --- unwrapping -------------------------------------------------------------

def unwrap(lines: Sequence[str]) -> List[str]:
    """Join GAP's wrapped output back into one string per record.

    A record starts at a line beginning with one of RECORD_HEADS; every
    following line that does not start a record continues it.  Lines before
    the first record (the shell banner) are dropped.  Whitespace runs collapse
    to one space."""
    records: List[str] = []
    for raw in lines:
        line = raw.rstrip("\n")
        if line.startswith(RECORD_HEADS):
            records.append(line.strip())
        elif records and line.strip():
            records[-1] = records[-1] + " " + line.strip()
    return [re.sub(r"\s+", " ", r) for r in records]


_ENGINE = re.compile(r"^engine GAP (\S+) tomlib (\S+)")


def engine_versions(lines: Sequence[str]) -> Tuple[Optional[str], Optional[str]]:
    """The GAP and tomlib versions the scan script announces on its own
    `engine` line (the shell banner is not relied on: it appears only when
    GAP runs through the `nix develop` wrapper)."""
    for line in lines:
        m = _ENGINE.match(line.strip())
        if m:
            return m.group(1), m.group(2)
    return None, None


# --- one record --------------------------------------------------------------

_INTS = r"\[\s*([0-9,\s]*)\]"


def _ints(text: str) -> Tuple[int, ...]:
    return tuple(int(x) for x in re.findall(r"\d+", text))


_HIT = re.compile(
    r"^HIT (\S+) \|G\|=(\d+) class (\d+) \|H\|=(\d+) index (\d+) interval orders " + _INTS)
_AMBIGUOUS = re.compile(
    r"^AMBIGUOUS (\S+) \|G\|=(\d+) class (\d+) \|H\|=(\d+) index (\d+) multiplicities")
_EXPLICIT = re.compile(
    r"^EXPLICIT (\S+) class (\d+): \|G\| = (\d+) \|H\| = (\d+) \((.*)\) index (\d+) "
    r"core-free (true|false); interval size (\d+) orders " + _INTS +
    r" covers .*; target: (true|false)")
_UNRESOLVED = re.compile(
    r"^UNRESOLVED \(\|G\| = (\d+) above FLRP_RESOLVE_BOUND\) (\S+) class (\d+)")
_SCANNED = re.compile(
    r"^scanned (\d+) tables; size-(\d+) upper intervals: (\d+); "
    r"marks-exact hits: (\d+); ambiguous survivors: (\d+)")


def parse_record(record: str) -> Tuple[str, object]:
    """Classify one unwrapped record.  Returns (kind, value); kind is
    'unparsed' when the line matches no known shape."""
    m = _HIT.match(record)
    if m:
        return "hit", Hit(m.group(1), int(m.group(2)), int(m.group(3)),
                          int(m.group(4)), int(m.group(5)), _ints(m.group(6)))
    m = _AMBIGUOUS.match(record)
    if m:
        return "ambiguous", Ambiguous(m.group(1), int(m.group(2)), int(m.group(3)),
                                      int(m.group(4)), int(m.group(5)))
    m = _EXPLICIT.match(record)
    if m:
        return "explicit", Explicit(
            m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)),
            m.group(5), int(m.group(6)), m.group(7) == "true", int(m.group(8)),
            _ints(m.group(9)), m.group(10) == "true")
    m = _UNRESOLVED.match(record)
    if m:
        return "unresolved", Unresolved(m.group(2), int(m.group(3)), int(m.group(1)))
    m = _SCANNED.match(record)
    if m:
        return "tally", Tally(*(int(g) for g in m.groups()))
    return "unparsed", record


def summarize(lines: Sequence[str]) -> Summary:
    """The summary of a whole log."""
    parsed = [parse_record(r) for r in unwrap(lines)]
    pick = lambda kind: tuple(v for k, v in parsed if k == kind)  # noqa: E731
    tallies = pick("tally")
    gap, tomlib = engine_versions(lines)
    return Summary(
        tally=tallies[-1] if tallies else None,
        hits=pick("hit"),
        ambiguous=pick("ambiguous"),
        explicit=pick("explicit"),
        unresolved=pick("unresolved"),
        unparsed=pick("unparsed"),
        gapVersion=gap,
        tomlibVersion=tomlib)


# --- the committed record ---------------------------------------------------

def target_header(stanza: Optional[Path]) -> Dict[str, object]:
    if stanza is None:
        return {}
    data = json.loads(stanza.read_text())
    return {"stem": stanza.stem, "name": data.get("name"), "size": data.get("size")}


def record(summary: Summary, stanza: Optional[Path], date: Optional[str],
           config: Dict[str, object]) -> Dict[str, object]:
    """The `flrp-tomscan v1` record as a JSON-ready dictionary."""
    return {
        "format": FORMAT,
        "date": date,
        "engine": {"gap": summary.gapVersion, "tomlib": summary.tomlibVersion,
                   "script": "scripts/gap/flrp/bin/tomscan.g"},
        "config": config,
        "target": target_header(stanza),
        "scanned": None if summary.tally is None else asdict(summary.tally),
        "hits": [asdict(h) for h in summary.hits],
        "explicit": [asdict(e) for e in summary.explicit],
        "unresolved": [asdict(u) for u in summary.unresolved],
        "ambiguous": [asdict(a) for a in summary.ambiguous],
        "unparsed": list(summary.unparsed),
    }


def render(rec: Dict[str, object]) -> str:
    return json.dumps(rec, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


# --- targets from stanzas ---------------------------------------------------

def upsets(stanza: Path) -> List[List[int]]:
    """The GAP up-set list of a stanza: element k's up-set is every j with
    meet[k][j] == k, 1-based, in the stanza's own element order."""
    data = json.loads(stanza.read_text())
    meet = data["meet"]
    n = data["size"]
    return [[j + 1 for j in range(n) if meet[k][j] == k] for k in range(n)]


def gap_list(rows: Sequence[Sequence[int]]) -> str:
    return "[" + ",".join("[" + ",".join(str(x) for x in row) + "]" for row in rows) + "]"


# --- command line -----------------------------------------------------------

def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("log", nargs="?", type=Path, help="a tomscan.g run's output")
    parser.add_argument("--target", type=Path, help="the target stanza (for the header)")
    parser.add_argument("--out", type=Path, help="write the record here (default: stdout)")
    parser.add_argument("--date", help="date field (pin for byte-stability)")
    parser.add_argument("--tables", help="the FLRP_TABLES restriction the run used, if any")
    parser.add_argument("--bound", help="the FLRP_RESOLVE_BOUND the run used, if not the default")
    parser.add_argument("--upsets", type=Path, metavar="STANZA",
                        help="print the GAP up-set list of this stanza and exit")
    args = parser.parse_args(argv)

    if args.upsets is not None:
        sys.stdout.write(gap_list(upsets(args.upsets)) + "\n")
        return 0
    if args.log is None:
        parser.error("a log file is required unless --upsets is given")

    lines = args.log.read_text(errors="replace").splitlines()
    config: Dict[str, object] = {
        "tables": args.tables.split(",") if args.tables else "all",
        "resolveBound": args.bound if args.bound else "default",
    }
    text = render(record(summarize(lines), args.target, args.date, config))
    if args.out is None:
        sys.stdout.write(text)
    else:
        args.out.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
