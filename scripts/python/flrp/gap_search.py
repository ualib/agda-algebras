"""GAP search report → confirmed lattice-representation census.

File: scripts/python/flrp/gap_search.py

Description:

  The Python confirmation stage of a #487 search run.  A GAP scan
  (`scripts/gap/flrp/bin/scan_transitive.g`, `...`/search over SmallGroups)
  emits a raw report: the groups scanned, a histogram of interval sizes, and
  the raw interval records of every candidate whose interval has the target's
  element count.  This tool re-derives each candidate's meet/join tables with
  the canonical `tables_from_leq`, tests each against the target lattice, and
  writes the committed `flrp-gap-search v1` report with an explicit verdict.

  A negative verdict is the point for the degree-8 L7 scan (deliverable 4): it
  must agree with the committed Eq(8) closure sweep, which already excludes
  every 8-point algebra.  Agreement cross-validates both engines; a positive
  hit would be a discovery (or a bug) — never trusted here, always re-checked
  in Agda through the certificate pipeline.

Usage:

  python3 scripts/python/flrp/gap_search.py REPORT.raw.json \\
      --target scripts/python/flrp/inputs/l7_lattice.json \\
      --out scripts/gap/flrp/out/l7_transitive_deg8.search.json --date 2026-07-24
"""

from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

from cg2 import CertificateError
from eqsearch import parse_target
from gap_interval import canonical_artifact, interval_lattice, lattice_iso
from lattice import TargetLattice

SEARCH_RAW_FORMAT = "flrp-gap-search-raw v1"
SEARCH_FORMAT = "flrp-gap-search v1"


def load_search_raw(path: Path) -> dict:
    """Read and shape-check a raw GAP search report."""
    data = json.loads(path.read_text())
    if data.get("format") != SEARCH_RAW_FORMAT:
        raise CertificateError(
            f"{path}: expected format {SEARCH_RAW_FORMAT!r}, got {data.get('format')!r}")
    for key in ("engine", "config", "scanned", "candidates"):
        if key not in data:
            raise CertificateError(f"{path}: missing required field {key!r}")
    return data


def confirm(raw: dict, target: TargetLattice, date: str) -> Tuple[List[dict], str]:
    """Confirm each candidate against `target`; return the isomorphic hits (as
    canonical `flrp-gap-interval v1` records) and the verdict string."""
    hits: List[dict] = []
    for cand in raw["candidates"]:
        lat = interval_lattice(cand)
        witness = lattice_iso(lat, target)
        if witness is not None:
            hits.append(canonical_artifact(cand, lat, target, witness, date))
    return hits, ("positive" if hits else "negative")


def search_report(raw: dict, target: TargetLattice, hits: List[dict],
                  verdict: str, date: str) -> dict:
    """Assemble the committed `flrp-gap-search v1` report."""
    return {
        "format": SEARCH_FORMAT,
        "date": date,
        "engine": raw["engine"],
        "config": raw["config"],
        "target": {"name": target.name, "size": target.size},
        "scanned": raw["scanned"],
        "sizeHistogram": raw.get("sizeHistogram", {}),
        "candidates": len(raw["candidates"]),
        "verdict": verdict,
        "hits": hits,
    }


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("raw", type=Path, help="raw GAP search report (flrp-gap-search-raw v1)")
    parser.add_argument("--target", type=Path, required=True,
                        help="target lattice JSON (bare stanza or claim file)")
    parser.add_argument("--out", type=Path, default=None,
                        help="write the confirmed flrp-gap-search v1 report here")
    parser.add_argument("--date", default=datetime.date.today().isoformat(),
                        help="date field for the emitted report (pin for byte-stability)")
    args = parser.parse_args(argv)

    raw = load_search_raw(args.raw)
    target = parse_target(args.target)
    hits, verdict = confirm(raw, target, args.date)

    cfg = raw["config"]
    print(f"{cfg.get('mode', 'search')} (degree {cfg.get('degree', '?')}): "
          f"scanned {raw['scanned'].get('groups', '?')} groups, "
          f"{len(raw['candidates'])} size-{target.size} candidates")
    print(f"  interval-size histogram: {raw.get('sizeHistogram', {})}")
    print(f"  vs target {target.name!r}: VERDICT = {verdict.upper()} "
          f"({len(hits)} isomorphic)")

    if args.out is not None:
        write_json(args.out, search_report(raw, target, hits, verdict, args.date))
        print(f"  wrote report: {args.out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
