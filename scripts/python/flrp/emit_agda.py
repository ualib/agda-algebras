"""Render a whole-lattice certificate as a literate Agda module.

File: scripts/python/flrp/emit_agda.py

Description:

  The final stage of the WP-6 pipeline (issue #457): read a claim file (the
  input JSON documented in README.md), run the cg2 engine (``cg2.py``,
  ``lattice.py``), and emit

  + a ``.lagda.md`` module whose type-checking *is* the verification — placed
    under ``src/<module>/`` for the claim file's dotted ``module`` namespace
    prefix (default ``FLRP.Certificates.Pilot``); the emitted literals feed the
    search-free checkers of ``Setoid.Congruences.Certificates`` and the
    ``Representableᵈ`` assembly of ``FLRP.Certificates``, so a wrong table or
    trace fails to compile; and
  + an audit copy of the raw certificate as JSON (kept outside ``src/``, per
    roadmap § 6).

  The v1 renderer targets **unary signatures** (G-sets and their kin — the
  Pálfy–Pudlák frontier); the cg2 engine itself is arity-general.  Emitted
  files are deterministic functions of the input (pin the input's ``date``
  field for byte-stable output) and are never edited by hand: rerun the
  emitter instead.

Usage:

   python3 scripts/python/flrp/emit_agda.py INPUT.json [--out PATH] [--cert-json PATH]
"""

from __future__ import annotations

import argparse
import datetime
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from cg2 import (Algebra, CertificateError, Merge, Operation, SeedJust,
                 TranslateJust, validate_algebra)
from lattice import (TargetLattice, WholeLatticeCertificate, build_certificate,
                     validate_lattice)

REPO_ROOT = Path(__file__).resolve().parents[3]


# ---------------------------------------------------------------------------
# Input parsing

@dataclass(frozen=True)
class Claim:
    """A parsed claim file: module placement, provenance, and the claim
    proper — "the congruence lattice of this algebra is this lattice"."""

    name: str
    date: str
    module: str
    provenance: str
    algebra: Algebra
    lattice: TargetLattice


def parse_input(path: Path) -> Claim:
    """Read a claim file into a ``Claim``."""
    data = json.loads(path.read_text())
    if data.get("format") != "flrp-cert-input v1":
        raise CertificateError(f"{path}: expected format 'flrp-cert-input v1'")

    name = data["name"]
    if not (name and name[0].isalpha() and name.isalnum()):
        raise CertificateError(f"{path}: 'name' must be a plain alphanumeric Agda name")
    date = data.get("date", datetime.date.today().isoformat())

    module = data.get("module", "FLRP.Certificates.Pilot")
    if not all(seg and seg[0].isalpha() and seg.isalnum()
               for seg in module.split(".")):
        raise CertificateError(
            f"{path}: 'module' must be a dotted prefix of plain alphanumeric Agda names")

    provenance = data.get("provenance", "")
    if not isinstance(provenance, str):
        raise CertificateError(f"{path}: 'provenance' must be a Markdown string")

    a = data["algebra"]
    algebra = Algebra(
        name=a.get("name", name),
        card=a["card"],
        operations=tuple(
            Operation(name=op["name"], arity=op["arity"], table=op["table"])
            for op in a["operations"]))
    validate_algebra(algebra)

    lat = data["lattice"]
    target = TargetLattice(
        name=lat.get("name", "target"),
        size=lat["size"],
        meet=tuple(tuple(row) for row in lat["meet"]),
        join=tuple(tuple(row) for row in lat["join"]))
    validate_lattice(target)

    return Claim(name=name, date=date, module=module, provenance=provenance,
                 algebra=algebra, lattice=target)


# ---------------------------------------------------------------------------
# Agda literal rendering

def fin(i: int) -> str:
    """A Fin literal via Data.Fin.Patterns (0F–9F only, by design: the
    small-lattice frontier fits, and larger carriers deserve a smarter
    renderer, not longer lines)."""
    if not 0 <= i <= 9:
        raise CertificateError(
            "index ≥ 10: the v1 renderer only emits Data.Fin.Patterns literals 0F–9F")
    return f"{i}F"


def fin_row(xs: Sequence[int]) -> str:
    return "(" + " ∷ ".join(fin(x) for x in xs) + " ∷ [])"


def merge_str(position: int, m: Merge) -> str:
    """One trace entry.  Translate references are emitted as backward
    offsets into the already-processed merges (0 = the previous one), per
    the schema's reference conventions; the engine records absolute trace
    positions, so the offset is `position - 1 - ref`."""
    if isinstance(m.why, SeedJust):
        return f"mkMerge {fin(m.lhs)} {fin(m.rhs)} (seed {m.why.seed})"
    relative = position - 1 - m.why.ref
    if relative < 0:
        raise CertificateError("translate justification references a later merge")
    frozen = "(" + " ∷ ".join(fin(x) for x in m.why.frozen) + " ∷ [])"
    return (f"mkMerge {fin(m.lhs)} {fin(m.rhs)} "
            f"(translate {fin(m.why.op)} {fin(m.why.coord)} {frozen} {relative})")


Block = List[str]


def trace_block(trace: Sequence[Merge]) -> Block:
    """A Trace literal, one merge per line when there are several."""
    entries = [merge_str(pos, m) for pos, m in enumerate(trace)]
    if not entries:
        return ["[]"]
    if len(entries) == 1:
        return [f"({entries[0]} ∷ [])"]
    return [f"( {entries[0]}"] + [f"∷ {e}" for e in entries[1:]] + ["∷ [] )"]


def vec_block(items: Sequence[Block]) -> Block:
    """A parenthesized Vec literal of (possibly multi-line) item blocks."""
    if not items:
        return ["[]"]
    out: Block = []
    for pos, block in enumerate(items):
        lead = "( " if pos == 0 else "∷ "
        out.append(lead + block[0])
        out.extend("  " + line for line in block[1:])
    out.append("∷ [] )")
    return out


def glue_vec(prefix: str, items: Sequence[Block]) -> Block:
    """`prefix item₀ ∷ item₁ ∷ … ∷ []` with the ∷ aligned under the '='
    of the prefix (the repository's Cayley-table layout)."""
    if not items:
        return [prefix + "[]"]
    pad = " " * (len(prefix) - 2)
    out: Block = []
    for pos, block in enumerate(items):
        lead = prefix if pos == 0 else pad + "∷ "
        out.append(lead + block[0])
        out.extend(" " * len(lead) + line for line in block[1:])
    out.append(pad + "∷ []")
    return out


def fin_table(prefix: str, table: Sequence[Sequence[int]]) -> Block:
    return glue_vec(prefix, [[fin_row(row)] for row in table])


# ---------------------------------------------------------------------------
# The module template

def emitted_module(claim: Claim, cert: WholeLatticeCertificate,
                   input_rel: str) -> str:
    name, date, alg, target = claim.name, claim.date, claim.algebra, claim.lattice
    qualified = f"{claim.module}.{name}"
    module_path = claim.module.replace(".", "/")
    prov_block = f"\n{claim.provenance}\n" if claim.provenance else ""
    n, k, m = alg.card, len(alg.operations), target.size
    if any(op.arity != 1 for op in alg.operations):
        raise CertificateError(
            "the v1 Agda renderer supports unary signatures only "
            "(the cg2 engine itself is arity-general)")
    max_fin = max(n, k, m) - 1
    fin_patterns = " ; ".join(f"{i}F" for i in range(max_fin + 1))

    op_rows: Block = glue_vec(
        "opTables = ", [[fin_row(list(op.table))] for op in alg.operations])  # type: ignore[arg-type]
    meet_rows = fin_table("∧-table = ", target.meet)
    join_rows = fin_table("∨-table = ", target.join)

    parts_rows = glue_vec("  partsᵛ = ", [[fin_row(pv)] for pv in cert.parts])
    prin_rows = glue_vec("  prinᵛ = ", [[fin_row(row)] for row in cert.prin])
    prin_tr = glue_vec(
        "  prinTrᵛ = ",
        [vec_block([trace_block(t) for t in row]) for row in cert.prin_traces])
    join_tr = glue_vec(
        "  joinTrᵛ = ",
        [vec_block([trace_block(t) for t in row]) for row in cert.join_traces])

    def lines(block: Block) -> str:
        return "\n".join(block)

    op_names = ", ".join(f"`{op.name}`" for op in alg.operations)

    return f'''---
layout: default
file: "src/{module_path}/{name}.lagda.md"
title: "{qualified} module (The Agda Universal Algebra Library)"
date: "{date}"
author: "the agda-algebras development team (emitted by scripts/python/flrp)"
---

### A machine-checked representation: Con({alg.name}) ≅ {target.name}

This is the [{qualified}][] module of the [Agda Universal Algebra Library][].

**This module was emitted by `scripts/python/flrp/emit_agda.py` from
`{input_rel}`.  Do not edit it by hand; rerun the emitter instead.**
{prov_block}
It re-verifies, end-to-end through the WP-6 certificate pipeline (#457), the
claim that the congruence lattice of the algebra "{alg.name}" — carrier size
{n}, unary operations {op_names} — is isomorphic to the lattice
"{target.name}" ({m} elements).  The engine's output below (normal-form
parent vectors, Freese traces, and pointer tables) is certificate data only:
the search-free checkers of [Setoid.Congruences.Certificates][] re-verify all
of it during type-checking, and the [FLRP.Certificates][] assembly turns the
checked certificate into the headline theorems — a
`Representableᵈ`{{.AgdaRecord}} witness for the target lattice and a
`FiniteCongruencesᵈ`{{.AgdaRecord}} instance for the algebra.  Nothing is
believed on the engine's authority: a wrong table or trace would make a
decidable check compute to `no`{{.AgdaInductiveConstructor}} and break
compilation.

<!--
```agda
{{-# OPTIONS --cubical-compatible --exact-split --safe #-}}

module {qualified} where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Fin.Base       using ( Fin )
open import Data.Fin.Patterns   using ( {fin_patterns} )
open import Data.List.Base      using ( [] ; _∷_ )
open import Data.Vec.Base       using ( Vec ; [] ; _∷_ )
open import Level               using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Unary   using ( Sig-Unary )
open import Classical.Structures.Unary   using ( tablesToUnaryAlgebra
                                               ; tablesToUnaryAlgebra-FiniteAlgebra
                                               ; Sig-Unary-Fin-FiniteSignature )
open import FLRP.Certificates            using ( MeetMatches ; meetMatches?
                                               ; certRepresentableᵈ )
open import FLRP.Problem                 using ( FiniteLattice ; toLattice )
open import FLRP.Representable           using ( Representableᵈ )
open import Overture.Cayley              using ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties
                                         using ( Associative? ; Commutative?
                                               ; Idempotent? ; Absorbsˡ? ; Absorbsʳ? )
open import Setoid.Algebras.Basic        using ( Algebra )
open import Setoid.Algebras.Finite       using ( FiniteAlgebra )
open import Setoid.Congruences.Certificates.Schema
                                         using ( ParentVec ; Trace ; LatticeCert
                                               ; mkLatticeCert ; mkMerge
                                               ; seed ; translate )
open import Setoid.Congruences.Certificates.Congruence
                                         using ( module CertCheck )
open import Setoid.Congruences.Certificates.Lattice
                                         using ( module LatticeCheck )
open import Setoid.Congruences.Finite.Decidable
                                         using ( FiniteCongruencesᵈ )
open import Setoid.Signatures.Finite     using ( FiniteSignature )
```
-->

#### The algebra, from its operation tables

Row `f` of `opTables`{{.AgdaFunction}} is the value table of the `f`-th unary
operation; [Classical.Structures.Unary][] turns the table into the algebra
and its finiteness witnesses.

```agda
opTables : Vec (Vec (Fin {n}) {n}) {k}
{lines(op_rows)}

𝑨 : Algebra {{𝑆 = Sig-Unary (Fin {k})}} 0ℓ 0ℓ
𝑨 = tablesToUnaryAlgebra {n} {k} opTables

𝑭 : FiniteAlgebra 𝑨
𝑭 = tablesToUnaryAlgebra-FiniteAlgebra {n} {k} opTables

𝑺 : FiniteSignature (Sig-Unary (Fin {k}))
𝑺 = Sig-Unary-Fin-FiniteSignature {k}
```

#### The target lattice, from its Cayley tables

The claimed congruence lattice "{target.name}", presented exactly as the
worked lattice examples are ([Examples.Classical.Lattices.L7][]): meet and
join tables, every law discharged by decision over the finite carrier.

```agda
∧-table ∨-table : Table {m}
{lines(meet_rows)}

{lines(join_rows)}

open FiniteLattice

𝑳 : FiniteLattice
𝑳 .size     = {m - 1}
𝑳 ._∧_      = ⟦ ∧-table ⟧
𝑳 ._∨_      = ⟦ ∨-table ⟧
𝑳 .∧-assoc  = from-yes (Associative? ⟦ ∧-table ⟧)
𝑳 .∧-comm   = from-yes (Commutative? ⟦ ∧-table ⟧)
𝑳 .∧-idem   = from-yes (Idempotent? ⟦ ∧-table ⟧)
𝑳 .∨-assoc  = from-yes (Associative? ⟦ ∨-table ⟧)
𝑳 .∨-comm   = from-yes (Commutative? ⟦ ∨-table ⟧)
𝑳 .∨-idem   = from-yes (Idempotent? ⟦ ∨-table ⟧)
𝑳 .absorbˡ  = from-yes (Absorbsˡ? ⟦ ∧-table ⟧ ⟦ ∨-table ⟧)
𝑳 .absorbʳ  = from-yes (Absorbsʳ? ⟦ ∧-table ⟧ ⟦ ∨-table ⟧)
```

#### The certificate

The engine's whole-lattice certificate (design note § 4): the congruence
list as normal-form parent vectors, indexed by the lattice's carrier; the
principal-congruence pointer table with one Freese trace per carrier pair;
and the join traces, seeded by forest edges.  The meet and join tables are
the target's own tables, which is what `MeetMatches`{{.AgdaFunction}} pins.

```agda
open CertCheck 𝑭 𝑺 using ( arOf )

cert : LatticeCert {n} {k} arOf {m}
cert = mkLatticeCert partsᵛ {fin(cert.bot)} prinᵛ prinTrᵛ ∧-table ∨-table joinTrᵛ
  where
  partsᵛ : Vec (ParentVec {n}) {m}
{lines(parts_rows)}

  prinᵛ : Vec (Vec (Fin {m}) {n}) {n}
{lines(prin_rows)}

  prinTrᵛ : Vec (Vec (Trace {n} {k} arOf) {n}) {n}
{lines(prin_tr)}

  joinTrᵛ : Vec (Vec (Trace {n} {k} arOf) {m}) {m}
{lines(join_tr)}
```

#### The verification

One decision for the whole certificate, one for the meet-table match; both
compute to `yes`{{.AgdaInductiveConstructor}} — that computation *is* the
re-verification of every engine claim above.

```agda
open LatticeCheck 𝑭 𝑺

certOK : LatticeCertOK cert
certOK = from-yes (latticeCertOK? cert)

certMeet : MeetMatches 𝑭 𝑺 𝑳 cert
certMeet = from-yes (meetMatches? 𝑭 𝑺 𝑳 cert)
```

#### The headline theorems

The target lattice is decidably representable, witnessed by this algebra;
and the certificate's congruence list is a complete Layer-D enumeration of
the algebra's decidable congruences.

```agda
{name}-Representableᵈ : Representableᵈ (toLattice 𝑳)
{name}-Representableᵈ = certRepresentableᵈ 𝑭 𝑺 𝑳 cert certOK certMeet

{name}-FiniteCongruencesᵈ : FiniteCongruencesᵈ 𝑨
{name}-FiniteCongruencesᵈ = certFiniteCongruencesᵈ cert certOK
```

--------------------------------------
'''


# ---------------------------------------------------------------------------
# Audit JSON

def certificate_json(name: str, alg: Algebra, target: TargetLattice,
                     cert: WholeLatticeCertificate) -> str:
    """The raw certificate as tool-interchange JSON (absolute trace refs)."""

    def merge_json(m: Merge) -> Dict[str, object]:
        base: Dict[str, object] = {"lhs": m.lhs, "rhs": m.rhs}
        if isinstance(m.why, SeedJust):
            base["seed"] = m.why.seed
        else:
            base.update(op=m.why.op, coord=m.why.coord,
                        frozen=list(m.why.frozen), ref=m.why.ref)
        return base

    def traces_json(rows: Sequence[Sequence[Sequence[Merge]]]) -> List[List[List[Dict[str, object]]]]:
        return [[[merge_json(m) for m in t] for t in row] for row in rows]

    return json.dumps({
        "format": "flrp-cert v1",
        "name": name,
        "algebra": {"name": alg.name, "card": alg.card,
                    "operations": [asdict(op) for op in alg.operations]},
        "lattice": {"name": target.name, "size": target.size,
                    "meet": [list(r) for r in target.meet],
                    "join": [list(r) for r in target.join]},
        "certificate": {
            "parts": [list(p) for p in cert.parts],
            "bot": cert.bot,
            "prin": [list(r) for r in cert.prin],
            "prinTraces": traces_json(cert.prin_traces),
            "meet": [list(r) for r in cert.meet],
            "join": [list(r) for r in cert.join],
            "joinTraces": traces_json(cert.join_traces),
        },
    }, indent=2, ensure_ascii=False) + "\n"


# ---------------------------------------------------------------------------
# CLI

def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("input", type=Path, help="claim file (flrp-cert-input v1 JSON)")
    parser.add_argument("--out", type=Path, default=None,
                        help="output .lagda.md (default: src/<module path>/<name>.lagda.md)")
    parser.add_argument("--cert-json", type=Path, default=None,
                        help="audit certificate JSON (default: scripts/python/flrp/out/<name>.cert.json)")
    args = parser.parse_args(argv)

    claim = parse_input(args.input)
    cert = build_certificate(claim.algebra, claim.lattice)

    out = args.out or REPO_ROOT.joinpath(
        "src", *claim.module.split("."), f"{claim.name}.lagda.md")
    cert_json = args.cert_json or \
        REPO_ROOT / "scripts" / "python" / "flrp" / "out" / f"{claim.name}.cert.json"

    input_rel = args.input.resolve().relative_to(REPO_ROOT).as_posix() \
        if args.input.resolve().is_relative_to(REPO_ROOT) else str(args.input)

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(emitted_module(claim, cert, input_rel))
    cert_json.parent.mkdir(parents=True, exist_ok=True)
    cert_json.write_text(certificate_json(claim.name, claim.algebra, claim.lattice, cert))

    print(f"emitted  {out.relative_to(REPO_ROOT) if out.is_relative_to(REPO_ROOT) else out}")
    print(f"audit    {cert_json.relative_to(REPO_ROOT) if cert_json.is_relative_to(REPO_ROOT) else cert_json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
