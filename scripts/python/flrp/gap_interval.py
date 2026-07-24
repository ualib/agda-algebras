"""GAP interval → lattice bridge and certificate-input emitter.

File: scripts/python/flrp/gap_interval.py

Description:

  The Python half of the #487 subgroup-interval search.  GAP (an untrusted
  engine, `scripts/gap/flrp/`) emits a raw interval artifact — the poset
  `[H, G]` as covers plus a reflexive order matrix, together with the coset
  action of G on G/H as unary value tables.  This bridge turns that poset into
  canonical meet/join tables with the one implementation the repository already
  trusts (`eqsearch.tables_from_leq`), optionally tests the interval for
  isomorphism against a target lattice, and writes:

    + the canonical `flrp-gap-interval v1` artifact (raw fields + meet/join +
      the isomorphism verdict), the committed record of a found interval; and
    + on request, a `flrp-cert-input v1` claim file for `emit_agda.py`, when the
      coset index is within the renderer's Fin-literal cap — the direct
      group→certificate route (deliverable 6).  Larger indices are certified
      through the WP-3 bridge `FLRP.Bridge` (issue #454) instead.

  No group theory happens here and nothing is trusted: the lattice tables are
  mechanical, the isomorphism search is bounded brute force (the checker
  re-verifies any emitted certificate definitionally), and every artifact
  carries GAP's engine/version stamp verbatim.

Usage:

  python3 scripts/python/flrp/gap_interval.py RAW.json \\
      --target scripts/python/flrp/inputs/slr/slr01.json \\
      --out scripts/gap/flrp/out/pentagon_216_153.interval.json
"""

from __future__ import annotations

import argparse
import datetime
import json
from itertools import permutations
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from cg2 import CertificateError
from eqsearch import parse_target, tables_from_leq
from lattice import TargetLattice

RAW_FORMAT = "flrp-gap-interval-raw v1"
ARTIFACT_FORMAT = "flrp-gap-interval v1"


def load_raw(path: Path) -> dict:
    """Read and shape-check a raw GAP interval artifact."""
    data = json.loads(path.read_text())
    if data.get("format") != RAW_FORMAT:
        raise CertificateError(
            f"{path}: expected format {RAW_FORMAT!r}, got {data.get('format')!r}")
    for key in ("engine", "group", "subgroup", "interval"):
        if key not in data:
            raise CertificateError(f"{path}: missing required field {key!r}")
    return data


def interval_lattice(raw: dict) -> TargetLattice:
    """The found interval [H, G] as a bounded lattice, built from its reflexive
    order matrix by the canonical `tables_from_leq`.  Raises if the poset is
    somehow not a lattice (it always is, being an interval of Sub(G))."""
    interval = raw["interval"]
    leq = [[bool(x) for x in row] for row in interval["leq"]]
    name = f"[{raw['group']['source']}{raw['group']['id']}]-interval"
    return tables_from_leq(name, leq)


def lattice_iso(a: TargetLattice, b: TargetLattice) -> Optional[Tuple[int, ...]]:
    """A bijection `sigma` from `a`'s indices to `b`'s indices respecting both
    the meet and the join tables, or `None` if the two lattices are not
    isomorphic.  Bounded brute force over `a.size!` bijections, mirroring
    `lattice.match_target`; adequate for the small-lattice frontier and, for
    any emitted certificate, re-checked in Agda regardless."""
    if a.size != b.size:
        return None
    n = a.size
    if n > 8:
        raise CertificateError(
            f"refusing a brute-force search over {n}! bijections; "
            "add pruning to lattice_iso first")
    for sigma in permutations(range(n)):
        if all(sigma[a.meet[k][l]] == b.meet[sigma[k]][sigma[l]]
               and sigma[a.join[k][l]] == b.join[sigma[k]][sigma[l]]
               for k in range(n) for l in range(n)):
            return sigma
    return None


def canonical_artifact(raw: dict, lat: TargetLattice,
                       target: Optional[TargetLattice],
                       witness: Optional[Sequence[int]],
                       date: str) -> dict:
    """Assemble the committed `flrp-gap-interval v1` record: the raw fields,
    the interval's meet/join tables, and (when a target was given) the
    isomorphism verdict."""
    interval = dict(raw["interval"])
    interval["meet"] = [list(row) for row in lat.meet]
    interval["join"] = [list(row) for row in lat.join]
    art: Dict[str, object] = {
        "format": ARTIFACT_FORMAT,
        "date": date,
        "engine": raw["engine"],
        "group": raw["group"],
        "subgroup": raw["subgroup"],
        "interval": interval,
    }
    if target is not None:
        art["match"] = {
            "target": target.name,
            "isomorphic": witness is not None,
            "witness": list(witness) if witness is not None else None,
        }
    if "cosetAction" in raw:
        art["cosetAction"] = raw["cosetAction"]
    if "selection" in raw:
        art["selection"] = raw["selection"]
    return art


def claim_from_coset(raw: dict, lat: TargetLattice, name: str, module: str,
                     date: str, provenance: str) -> dict:
    """A `flrp-cert-input v1` claim asserting that the coset algebra's
    congruence lattice is the interval lattice — ready for `emit_agda.py`.
    Requires the coset index to fit the emitter's Fin-literal cap."""
    coset = raw.get("cosetAction")
    if coset is None:
        raise CertificateError("raw artifact has no cosetAction to emit a claim from")
    if not coset.get("directCertifiable"):
        raise CertificateError(
            f"coset index {coset['points']} exceeds the emitter's Fin-literal cap; "
            "certify through the WP-3 bridge (FLRP.Bridge) instead")
    grp = raw["group"]
    algebra_name = (f"coset action of {grp['source']}{grp['id']} on "
                    f"{coset['points']} cosets of H (order {raw['subgroup']['order']})")
    return {
        "format": "flrp-cert-input v1",
        "name": name,
        "date": date,
        "module": module,
        "provenance": provenance,
        "algebra": {
            "name": algebra_name,
            "card": coset["points"],
            "operations": [
                {"name": op["name"], "arity": op["arity"], "table": op["table"]}
                for op in coset["generators"]],
        },
        "lattice": {
            "name": lat.name,
            "size": lat.size,
            "meet": [list(row) for row in lat.meet],
            "join": [list(row) for row in lat.join],
        },
    }


def write_json(path: Path, payload: dict) -> None:
    """Write `payload` as deterministic pretty JSON with a trailing newline."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("raw", type=Path, help="raw GAP interval artifact (flrp-gap-interval-raw v1)")
    parser.add_argument("--target", type=Path, default=None,
                        help="target lattice JSON (bare stanza or claim file) to test isomorphism against")
    parser.add_argument("--out", type=Path, default=None,
                        help="write the canonical flrp-gap-interval v1 artifact here")
    parser.add_argument("--emit-claim", type=Path, default=None,
                        help="write a flrp-cert-input v1 claim (direct-certificate route) here")
    parser.add_argument("--name", default=None, help="Agda name for the emitted claim")
    parser.add_argument("--module", default="FLRP.Certificates.Group",
                        help="module prefix for the emitted claim")
    parser.add_argument("--provenance", default="", help="Markdown provenance for the emitted claim")
    parser.add_argument("--date", default=datetime.date.today().isoformat(),
                        help="date field for the emitted artifact/claim (pin for byte-stability)")
    args = parser.parse_args(argv)

    raw = load_raw(args.raw)
    lat = interval_lattice(raw)

    target: Optional[TargetLattice] = None
    witness: Optional[Tuple[int, ...]] = None
    if args.target is not None:
        target = parse_target(args.target)
        witness = lattice_iso(lat, target)

    grp, sub = raw["group"], raw["subgroup"]
    print(f"interval [H, G] in {grp['source']}{grp['id']}: "
          f"{lat.size} elements, [G:H] = {sub['index']}, "
          f"core-free = {sub['coreFree']}")
    if target is not None:
        verdict = "ISOMORPHIC" if witness is not None else "NOT isomorphic"
        print(f"  vs target {target.name!r}: {verdict}"
              + (f"  (witness {list(witness)})" if witness is not None else ""))

    if args.out is not None:
        write_json(args.out, canonical_artifact(raw, lat, target, witness, args.date))
        print(f"  wrote artifact: {args.out}")

    if args.emit_claim is not None:
        name = args.name or "".join(ch for ch in f"Interval{grp['id']}" if ch.isalnum())
        # Prefer the target's canonical tables and name for the certificate when
        # the interval was confirmed isomorphic to it; the coset algebra's Con
        # is re-checked against them definitionally by emit_agda regardless.
        claim_lat = target if (target is not None and witness is not None) else lat
        claim = claim_from_coset(raw, claim_lat, name, args.module, args.date,
                                 args.provenance)
        write_json(args.emit_claim, claim)
        print(f"  wrote claim:    {args.emit_claim}  (feed to emit_agda.py)")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
