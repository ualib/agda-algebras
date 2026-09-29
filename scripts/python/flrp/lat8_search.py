"""
File: scripts/python/flrp/lat8_search.py

Description: One record for the searches over the 61 eight-element lattices.

  The census of lattices8.py leaves 61 eight-element lattices with no formal
  reason for representability (docs/notes/flrp-lattices8-census.md).  Three
  instruments of the RP-3 sweeps were run over them; this module folds their
  outputs into a single committed record, scripts/python/flrp/out/
  lat8_search_summary.json (format flrp-lat8-search v1), one entry per
  lattice:

  + the SmallGroups sweep (hunt_parachutes.g with the size-8 gate opened,
    FLRP_S8_ATOMS := [1 .. 7]; the raw report lat8_s8.raw.json is confirmed
    here against every target with gap_search.confirm, exactly as the
    per-target search.json records are);
  + the closure search in Eq(n) (eqsearch.py --fast, one flrp-eqsearch v1
    report per lattice and n, read from a directory);
  + the tables-of-marks scan (tomscan.g, one tomscan JSON per lattice, read
    from a directory).

  Usage:
    python3 scripts/python/flrp/lat8_search.py --raw scripts/gap/flrp/out/lat8_s8.raw.json \
        [--eq-reports DIR] [--tomscan DIR] --out scripts/python/flrp/out/lat8_search_summary.json \
        --date 2026-09-28
  Only the summary is committed; the per-run reports live where the run put
  them and are re-derivable from the stanzas under inputs/lat8/.
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional

from eqsearch import parse_target
from gap_search import confirm, load_search_raw

STANZA_DIR = Path("scripts/python/flrp/inputs/lat8")
FORMAT = "flrp-lat8-search v1"


def stanza_index(path: Path) -> int:
    m = re.fullmatch(r"l8_(\d+)\.json", path.name)
    if m is None:
        raise ValueError(f"not a lat8 stanza: {path}")
    return int(m.group(1))


def eq_summary(directory: Optional[Path], k: int) -> Dict[str, dict]:
    """Per n: copies, classes, closed classes, from the flrp-eqsearch reports
    l8_<k>_eq<n>.json found in `directory`."""
    out: Dict[str, dict] = {}
    if directory is None:
        return out
    for rep in sorted(directory.glob(f"l8_{k}_eq*.json")):
        n = int(re.fullmatch(rf"l8_{k}_eq(\d+)\.json", rep.name).group(1))
        data = json.loads(rep.read_text())
        classes = data.get("classes", [])
        out[str(n)] = {
            "copies": data.get("copies"),
            "classes": len(classes),
            "closed": sum(1 for c in classes if c.get("closed")),
        }
    return out


def tomscan_summary(directory: Optional[Path], k: int) -> Optional[dict]:
    if directory is None:
        return None
    path = directory / f"tomscan_l8_{k}.json"
    if not path.exists():
        return None
    data = json.loads(path.read_text())
    explicit = data.get("explicit", [])
    confirmed = [e for e in explicit if e.get("target") is True]
    hits = data.get("hits", [])
    return {
        "verdict": "positive" if (hits or confirmed) else "negative",
        "scanned": data.get("scanned", {}),
        "hits": hits,
        "explicitConfirmed": confirmed,
        "explicitNegative": sum(1 for e in explicit if e.get("target") is False),
        "unresolved": data.get("unresolved", []),
    }


def build(raw_path: Path, eq_dir: Optional[Path], tom_dir: Optional[Path],
          date: str) -> dict:
    raw = load_search_raw(raw_path)
    entries: List[dict] = []
    for path in sorted(STANZA_DIR.glob("l8_*.json"), key=stanza_index):
        k = stanza_index(path)
        target = parse_target(path)
        hits, verdict = confirm(raw, target, date)
        entries.append({
            "index": k,
            "name": target.name,
            "smallGroups": {"verdict": verdict, "hits": hits},
            "eq": eq_summary(eq_dir, k),
            "tomscan": tomscan_summary(tom_dir, k),
        })
    return {
        "format": FORMAT,
        "date": date,
        "smallGroups": {
            "raw": str(raw_path),
            "engine": raw["engine"],
            "config": raw["config"],
            "scanned": raw["scanned"],
            "sizeHistogram": raw.get("sizeHistogram", {}),
            "candidates": len(raw["candidates"]),
        },
        "summary": {
            "targets": len(entries),
            "smallGroupsPositive": [e["index"] for e in entries
                                    if e["smallGroups"]["verdict"] == "positive"],
            "eqClosed": [e["index"] for e in entries
                         if any(v["closed"] for v in e["eq"].values())],
            "tomscanPositive": [e["index"] for e in entries
                                if e["tomscan"] and e["tomscan"].get("verdict") == "positive"],
        },
        "targets": entries,
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--eq-reports", type=Path, default=None)
    parser.add_argument("--tomscan", type=Path, default=None)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--date", default=datetime.date.today().isoformat())
    args = parser.parse_args(argv)
    record = build(args.raw, args.eq_reports, args.tomscan, args.date)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2) + "\n")
    s = record["summary"]
    print(f"{s['targets']} targets; SmallGroups positive: {s['smallGroupsPositive']}; "
          f"Eq closed: {s['eqClosed']}; tomscan positive: {s['tomscanPositive']}")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
