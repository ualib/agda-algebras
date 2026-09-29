"""
File: scripts/python/flrp/lattices8.py

Description: The eight-element lattices, classified by formal representability.

  Kjos-Hanssen's September 2026 note on the eight-element congruence lattices
  sorts the 222 lattices with eight elements into those representable "for
  formal reasons" (distributive; adjoined ordinal sums, an element other
  than the bounds comparable with everything; parallel sums, a disconnected
  comparability graph on the proper part) and the 54 that are none of these,
  for which it reports one representation each or none.  The parallel-sum
  closure it invokes is Snow's Lemma 3.10 (Algebra Universalis 43, 2000), but
  Snow's parallel sum L ∓ N adjoins a NEW top and a NEW bottom to the disjoint
  union of two lattices; the glued operation the note describes, identifying
  the tops and the bottoms, is not a theorem: closure under it would make
  every Mₙ (the glued sum of n three-element chains) a congruence lattice,
  and M₁₆ is open.  Nor does Snow's lemma cover the flat sum of three or more
  lattices (Mₙ again, the flat sum of n trivial lattices).

  This module enumerates the 222 lattices, reproduces the note's counts (15
  distributive, 96 adjoined ordinal sums, 69 with a disconnected proper part,
  54 of no kind, matching Table 1 of the note lattice for lattice), and then
  splits the 69 into the ones Snow's lemma covers (exactly two components,
  each an interval, so each a lattice) and the ones it does not; the latter
  are the lattices whose representability the note's argument leaves open.
  For each lattice the census also records whether it is simple as a lattice
  (the Pálfy–Pudlák–McKenzie theorem then makes representability a
  group-interval question), and its dual.

  Usage:
    python3 scripts/python/flrp/lattices8.py                 # summary table
    python3 scripts/python/flrp/lattices8.py --json OUT.json # the census record
    python3 scripts/python/flrp/lattices8.py --stanzas DIR   # eqsearch targets
                                                             # for the open ones
  The committed record is scripts/python/flrp/out/lattices8_census.json and
  the stanzas live under scripts/python/flrp/inputs/lat8/; test_lattices8.py
  (make flrp-test) pins the counts and re-derives both.
"""

from __future__ import annotations

import itertools
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, List, Optional, Sequence, Tuple

from eqsearch import tables_from_leq
from lattice import TargetLattice

Leq = Tuple[Tuple[bool, ...], ...]
Cover = Tuple[int, int]

# The number of lattices with n elements up to isomorphism (OEIS A006966).
KNOWN_COUNTS: Dict[int, int] = {1: 1, 2: 1, 3: 1, 4: 2, 5: 5, 6: 15, 7: 53, 8: 222}

OUT_JSON = Path("scripts/python/flrp/out/lattices8_census.json")
STANZA_DIR = Path("scripts/python/flrp/inputs/lat8")

# Table 1 of Kjos-Hanssen's note: (number, number of the dual, covers on
# 0..7 with 0 the bottom and 7 the top), transcribed from the text.  The 54
# lattices the note calls neither distributive nor ordinal nor parallel sums.
KJOS_HANSSEN_TABLE1: Tuple[Tuple[int, int, str], ...] = (
    (16, 89, "0<1 0<2 1<3 1<4 1<5 1<6 2<3 3<7 4<7 5<7 6<7"),
    (22, 112, "0<1 0<2 1<3 1<5 1<6 2<3 2<4 3<7 4<7 5<7 6<7"),
    (35, 35, "0<1 0<2 0<3 1<4 1<5 1<6 2<4 3<4 4<7 5<7 6<7"),
    (36, 90, "0<1 0<3 1<2 1<5 1<6 2<4 3<4 4<7 5<7 6<7"),
    (45, 113, "0<1 0<2 1<4 1<5 1<6 2<3 3<4 4<7 5<7 6<7"),
    (46, 118, "0<1 0<2 1<3 1<5 1<6 2<3 3<4 4<7 5<7 6<7"),
    (54, 59, "0<1 0<2 0<3 1<4 1<5 1<6 2<5 3<4 4<7 5<7 6<7"),
    (55, 99, "0<1 0<3 1<2 1<4 1<6 2<5 3<4 4<7 5<7 6<7"),
    (59, 54, "0<1 0<2 0<3 1<4 1<6 2<4 2<5 3<4 4<7 5<7 6<7"),
    (60, 114, "0<1 0<2 1<3 1<6 2<4 2<5 3<4 4<7 5<7 6<7"),
    (61, 61, "0<1 0<2 0<3 1<5 1<6 2<4 2<5 3<4 4<7 5<7 6<7"),
    (62, 100, "0<1 0<3 1<2 1<6 2<4 2<5 3<4 4<7 5<7 6<7"),
    (65, 152, "0<1 0<2 1<3 1<6 2<3 2<5 3<4 4<7 5<7 6<7"),
    (66, 140, "0<1 0<2 1<5 1<6 2<3 2<5 3<4 4<7 5<7 6<7"),
    (69, 128, "0<1 0<3 1<2 1<4 2<5 2<6 3<4 4<7 5<7 6<7"),
    (71, 129, "0<1 0<3 1<2 2<4 2<5 2<6 3<4 4<7 5<7 6<7"),
    (76, 142, "0<1 0<2 1<4 1<6 2<3 3<4 3<5 4<7 5<7 6<7"),
    (77, 158, "0<1 0<2 1<3 1<6 2<3 3<4 3<5 4<7 5<7 6<7"),
    (89, 16, "0<1 0<2 0<3 0<4 1<5 1<6 2<5 3<5 4<5 5<7 6<7"),
    (90, 36, "0<1 0<3 0<4 1<2 1<6 2<5 3<5 4<5 5<7 6<7"),
    (91, 91, "0<1 0<4 1<2 1<3 1<6 2<5 3<5 4<5 5<7 6<7"),
    (99, 55, "0<1 0<2 0<4 1<5 1<6 2<3 3<5 4<5 5<7 6<7"),
    (100, 62, "0<1 0<2 0<4 1<3 1<6 2<3 3<5 4<5 5<7 6<7"),
    (101, 101, "0<1 0<4 1<2 1<6 2<3 3<5 4<5 5<7 6<7"),
    (102, 115, "0<1 0<2 1<4 1<6 2<3 3<5 4<5 5<7 6<7"),
    (103, 119, "0<1 0<2 1<3 1<4 1<6 2<3 3<5 4<5 5<7 6<7"),
    (107, 116, "0<1 0<2 1<5 1<6 2<3 2<4 3<5 4<5 5<7 6<7"),
    (108, 153, "0<1 0<2 1<3 1<6 2<3 2<4 3<5 4<5 5<7 6<7"),
    (112, 22, "0<1 0<2 0<3 0<4 1<5 1<6 2<6 3<5 4<5 5<7 6<7"),
    (113, 45, "0<1 0<3 0<4 1<2 1<5 2<6 3<5 4<5 5<7 6<7"),
    (114, 60, "0<1 0<2 0<4 1<3 1<6 2<6 3<5 4<5 5<7 6<7"),
    (115, 102, "0<1 0<4 1<2 1<3 2<6 3<5 4<5 5<7 6<7"),
    (116, 107, "0<1 0<2 1<3 1<4 1<6 2<6 3<5 4<5 5<7 6<7"),
    (118, 46, "0<1 0<3 0<4 1<2 2<5 2<6 3<5 4<5 5<7 6<7"),
    (119, 103, "0<1 0<4 1<2 1<3 2<5 2<6 3<5 4<5 5<7 6<7"),
    (121, 130, "0<1 0<4 1<2 2<3 2<6 3<5 4<5 5<7 6<7"),
    (128, 69, "0<1 0<2 0<3 1<5 1<6 2<4 3<4 4<5 5<7 6<7"),
    (129, 71, "0<1 0<2 0<3 1<4 1<6 2<4 3<4 4<5 5<7 6<7"),
    (130, 121, "0<1 0<3 1<2 1<6 2<4 3<4 4<5 5<7 6<7"),
    (135, 144, "0<1 0<2 1<5 1<6 2<3 3<4 4<5 5<7 6<7"),
    (136, 155, "0<1 0<2 1<4 1<6 2<3 3<4 4<5 5<7 6<7"),
    (137, 159, "0<1 0<2 1<3 1<6 2<3 3<4 4<5 5<7 6<7"),
    (140, 66, "0<1 0<2 0<3 1<5 1<6 2<6 3<4 4<5 5<7 6<7"),
    (141, 141, "0<1 0<3 1<2 1<5 2<6 3<4 4<5 5<7 6<7"),
    (142, 76, "0<1 0<2 0<3 1<4 1<6 2<6 3<4 4<5 5<7 6<7"),
    (143, 146, "0<1 0<3 1<2 1<4 2<6 3<4 4<5 5<7 6<7"),
    (144, 135, "0<1 0<2 1<3 1<6 2<6 3<4 4<5 5<7 6<7"),
    (146, 143, "0<1 0<3 1<2 2<5 2<6 3<4 4<5 5<7 6<7"),
    (149, 149, "0<1 0<3 1<2 2<4 2<6 3<4 4<5 5<7 6<7"),
    (152, 65, "0<1 0<3 0<4 1<2 2<5 2<6 3<6 4<5 5<7 6<7"),
    (153, 108, "0<1 0<4 1<2 1<3 2<5 2<6 3<6 4<5 5<7 6<7"),
    (155, 136, "0<1 0<4 1<2 2<3 2<5 3<6 4<5 5<7 6<7"),
    (158, 77, "0<1 0<2 0<4 1<3 2<3 3<5 3<6 4<5 5<7 6<7"),
    (159, 137, "0<1 0<4 1<2 2<3 3<5 3<6 4<5 5<7 6<7"),
)

# The ten lattices of the note without a known representation ("none found"
# in Table 1), by the note's numbers.
KJOS_HANSSEN_OPEN: Tuple[int, ...] = (60, 62, 91, 100, 101, 102, 114, 115, 121, 130)


# --- enumeration --------------------------------------------------------------

def strict_orders(m: int) -> Iterator[Tuple[Tuple[bool, ...], ...]]:
    """Every strict partial order on range(m) for which the natural order is a
    linear extension (i below j only when i < j), as a matrix; every finite
    poset has such a labeling, so every isomorphism type occurs."""
    pairs = [(i, j) for i in range(m) for j in range(i + 1, m)]
    for mask in range(1 << len(pairs)):
        rel = [[False] * m for _ in range(m)]
        for bit, (i, j) in enumerate(pairs):
            if mask >> bit & 1:
                rel[i][j] = True
        if all(not (rel[i][j] and rel[j][k]) or rel[i][k]
               for i in range(m) for j in range(i + 1, m) for k in range(j + 1, m)):
            yield tuple(tuple(row) for row in rel)


def with_bounds(rel: Sequence[Sequence[bool]]) -> Leq:
    """The reflexive order on range(m + 2) with a new bottom 0 and top m + 1
    around the strict order `rel` on the middle elements 1..m."""
    m = len(rel)
    n = m + 2
    leq = [[i == j or i == 0 or j == n - 1 for j in range(n)] for i in range(n)]
    for i in range(m):
        for j in range(m):
            if rel[i][j]:
                leq[i + 1][j + 1] = True
    return tuple(tuple(row) for row in leq)


def is_lattice(leq: Leq) -> bool:
    """Every pair has a least upper bound and a greatest lower bound."""
    n = len(leq)
    up = [sum(1 << j for j in range(n) if leq[i][j]) for i in range(n)]
    down = [sum(1 << j for j in range(n) if leq[j][i]) for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            ub = up[i] & up[j]
            if not any(up[u] == ub for u in range(n) if ub >> u & 1):
                return False
            lb = down[i] & down[j]
            if not any(down[u] == lb for u in range(n) if lb >> u & 1):
                return False
    return True


def _profiles(leq: Leq) -> List[Tuple[int, int]]:
    n = len(leq)
    return [(sum(leq[j][i] for j in range(n)), sum(leq[i][j] for j in range(n)))
            for i in range(1, n - 1)]


def canonical_form(leq: Leq) -> Tuple[Tuple[Tuple[int, int], ...], int, Tuple[int, ...]]:
    """A complete isomorphism invariant of a bounded lattice: the sorted
    (down-count, up-count) profiles of the middle elements, and the least
    encoding of the middle order over all profile-preserving relabelings.
    Also returns the relabeling (new position -> old middle index) that
    attains it."""
    n = len(leq)
    m = n - 2
    prof = _profiles(leq)
    order = sorted(range(m), key=lambda i: (prof[i], i))
    groups: List[List[int]] = []
    for i in order:
        if groups and prof[groups[-1][0]] == prof[i]:
            groups[-1].append(i)
        else:
            groups.append([i])
    best_code: Optional[int] = None
    best_perm: Tuple[int, ...] = ()
    for choice in itertools.product(*(itertools.permutations(g) for g in groups)):
        perm = tuple(itertools.chain.from_iterable(choice))
        code = 0
        for a in range(m):
            for b in range(m):
                code = (code << 1) | int(leq[perm[a] + 1][perm[b] + 1])
        if best_code is None or code < best_code:
            best_code, best_perm = code, perm
    assert best_code is not None
    return tuple(sorted(prof)), best_code, best_perm


def relabel(leq: Leq, perm: Sequence[int]) -> Leq:
    """The order with the middle elements listed in the order `perm`."""
    n = len(leq)
    full = (0,) + tuple(p + 1 for p in perm) + (n - 1,)
    return tuple(tuple(leq[full[a]][full[b]] for b in range(n)) for a in range(n))


def enumerate_lattices(n: int) -> List[Leq]:
    """Canonical representatives of the lattices with n elements, one per
    isomorphism type, in the order of their canonical forms."""
    if n == 1:
        return [((True,),)]
    found: Dict[Tuple[Tuple[Tuple[int, int], ...], int], Leq] = {}
    for rel in strict_orders(n - 2):
        leq = with_bounds(rel)
        if not is_lattice(leq):
            continue
        prof, code, perm = canonical_form(leq)
        key = (prof, code)
        if key not in found:
            found[key] = relabel(leq, perm)
    return [found[k] for k in sorted(found)]


# --- structure ----------------------------------------------------------------

def covers(leq: Leq) -> Tuple[Cover, ...]:
    n = len(leq)
    return tuple((a, b) for a in range(n) for b in range(n)
                 if a != b and leq[a][b]
                 and not any(c not in (a, b) and leq[a][c] and leq[c][b] for c in range(n)))


def leq_from_covers(n: int, covs: Sequence[Cover]) -> Leq:
    leq = [[i == j for j in range(n)] for i in range(n)]
    for a, b in covs:
        leq[a][b] = True
    for k in range(n):
        for i in range(n):
            if leq[i][k]:
                for j in range(n):
                    if leq[k][j]:
                        leq[i][j] = True
    return tuple(tuple(row) for row in leq)


def dual(leq: Leq) -> Leq:
    n = len(leq)
    return tuple(tuple(leq[n - 1 - b][n - 1 - a] for b in range(n)) for a in range(n))


def format_covers(covs: Sequence[Cover]) -> str:
    return " ".join(f"{a}<{b}" for a, b in covs)


def middle_components(leq: Leq) -> List[FrozenSet[int]]:
    """The connected components of the comparability graph on the proper
    part (everything but the bottom and the top)."""
    n = len(leq)
    middle = list(range(1, n - 1))
    seen: set = set()
    comps: List[FrozenSet[int]] = []
    for s in middle:
        if s in seen:
            continue
        comp = {s}
        stack = [s]
        while stack:
            x = stack.pop()
            for y in middle:
                if y not in comp and (leq[x][y] or leq[y][x]):
                    comp.add(y)
                    stack.append(y)
        seen |= comp
        comps.append(frozenset(comp))
    return sorted(comps, key=lambda c: (len(c), sorted(c)))


def component_shape(leq: Leq, comp: FrozenSet[int]) -> Tuple[int, int, int]:
    """(size, number of minimal elements, number of maximal elements) of the
    induced subposet; the component is an interval, hence a lattice, exactly
    when both counts are one."""
    mins = [i for i in comp if not any(j != i and leq[j][i] for j in comp)]
    maxs = [i for i in comp if not any(j != i and leq[i][j] for j in comp)]
    return len(comp), len(mins), len(maxs)


def is_distributive(lat: TargetLattice) -> bool:
    n = lat.size
    return all(lat.meet[x][lat.join[y][z]] == lat.join[lat.meet[x][y]][lat.meet[x][z]]
               for x in range(n) for y in range(n) for z in range(n))


def is_adjoined_ordinal_sum(leq: Leq) -> bool:
    n = len(leq)
    return any(all(leq[x][y] or leq[y][x] for y in range(n)) for x in range(1, n - 1))


def _normal_form(parent: Sequence[int]) -> Tuple[int, ...]:
    leader: Dict[int, int] = {}
    out = []
    for i, p in enumerate(parent):
        out.append(leader.setdefault(p, i))
    return tuple(out)


def _partition_join(p: Sequence[int], q: Sequence[int]) -> Tuple[int, ...]:
    n = len(p)
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for r in (p, q):
        for i in range(n):
            a, b = find(i), find(r[i])
            if a != b:
                parent[max(a, b)] = min(a, b)
    return _normal_form([find(i) for i in range(n)])


def principal_congruence(lat: TargetLattice, a: int, b: int) -> Tuple[int, ...]:
    """The least lattice congruence identifying a and b, by fixpoint."""
    n = lat.size
    part = _normal_form([a if i in (a, b) else i for i in range(n)])
    part = _partition_join(part, part)
    while True:
        new = part
        for x in range(n):
            for y in range(x + 1, n):
                if new[x] != new[y]:
                    continue
                for c in range(n):
                    for table in (lat.meet, lat.join):
                        u, v = table[x][c], table[y][c]
                        if new[u] != new[v]:
                            new = _partition_join(new, _normal_form(
                                [u if i in (u, v) else i for i in range(n)]))
        if new == part:
            return part
        part = new


def lattice_congruences(lat: TargetLattice, leq: Leq) -> int:
    """The number of lattice congruences: the join-closure of the principal
    congruences of the covers."""
    n = lat.size
    gens = {principal_congruence(lat, a, b) for a, b in covers(leq)}
    con = {tuple(range(n))} | gens
    frontier = list(con)
    while frontier:
        x = frontier.pop()
        for y in list(con):
            z = _partition_join(x, y)
            if z not in con:
                con.add(z)
                frontier.append(z)
    return len(con)


# --- the census ----------------------------------------------------------------

@dataclass(frozen=True)
class Record:
    """One eight-element lattice and what is known of it formally."""
    index: int                      # position in this module's enumeration, 1-based
    covers: str                     # covers on 0..7, bottom 0, top 7
    distributive: bool
    adjoined_ordinal_sum: bool
    components: Tuple[Tuple[int, int, int], ...]   # (size, #minimal, #maximal)
    disconnected: bool              # the note's "parallel sum" criterion
    snow_sum: bool                  # two components, each an interval: Lemma 3.10
    parachute: bool                 # every component has a least element
    dual_parachute: bool            # every component has a greatest element
    con_size: int                   # number of lattice congruences
    simple: bool
    dual_index: int
    kjos_hanssen: Optional[int]     # the note's number when in its Table 1
    kjos_hanssen_status: str        # "table 1: representation", "table 1: none found",
                                    # "formal: distributive", "formal: adjoined ordinal sum",
                                    # "formal: parallel sum", or "formal: parallel sum, UNSUPPORTED"


def kjos_hanssen_index() -> Dict[Tuple[Tuple[Tuple[int, int], ...], int], int]:
    """Canonical form -> the note's number, for the 54 lattices of Table 1."""
    out = {}
    for number, _dual, text in KJOS_HANSSEN_TABLE1:
        covs = [(int(a), int(b)) for a, b in re.findall(r"(\d)<(\d)", text)]
        leq = leq_from_covers(8, covs)
        if not is_lattice(leq):
            raise ValueError(f"Table 1 entry #{number} is not a lattice")
        prof, code, _perm = canonical_form(leq)
        out[(prof, code)] = number
    return out


def census(n: int = 8) -> List[Record]:
    lattices = enumerate_lattices(n)
    keys = [canonical_form(l)[:2] for l in lattices]
    position = {k: i for i, k in enumerate(keys)}
    kh = kjos_hanssen_index() if n == 8 else {}
    records: List[Record] = []
    for i, leq in enumerate(lattices):
        lat = tables_from_leq(f"L{n}.{i + 1}", leq)
        comps = middle_components(leq)
        shapes = tuple(component_shape(leq, c) for c in comps)
        disconnected = len(comps) >= 2
        snow = len(comps) == 2 and all(s[1] == 1 and s[2] == 1 for s in shapes)
        distributive = is_distributive(lat)
        adjoined = is_adjoined_ordinal_sum(leq)
        con_size = lattice_congruences(lat, leq)
        dual_key = canonical_form(dual(leq))[:2]
        number = kh.get(keys[i])
        if number is not None:
            status = ("table 1: none found" if number in KJOS_HANSSEN_OPEN
                      else "table 1: representation")
        elif distributive:
            status = "formal: distributive"
        elif adjoined:
            status = "formal: adjoined ordinal sum"
        elif disconnected:
            status = ("formal: parallel sum" if snow
                      else "formal: parallel sum, UNSUPPORTED")
        else:
            status = "none (not in Table 1)"
        records.append(Record(
            index=i + 1,
            covers=format_covers(covers(leq)),
            distributive=distributive,
            adjoined_ordinal_sum=adjoined,
            components=shapes,
            disconnected=disconnected,
            snow_sum=snow,
            parachute=disconnected and all(s[1] == 1 for s in shapes),
            dual_parachute=disconnected and all(s[2] == 1 for s in shapes),
            con_size=con_size,
            simple=con_size == 2,
            dual_index=position[dual_key] + 1,
            kjos_hanssen=number,
            kjos_hanssen_status=status))
    return records


def unsupported(records: Sequence[Record]) -> List[Record]:
    """The lattices the note counts as parallel sums that Snow's lemma does
    not cover."""
    return [r for r in records if r.kjos_hanssen_status == "formal: parallel sum, UNSUPPORTED"]


def summary(records: Sequence[Record]) -> Dict[str, int]:
    kinds = {
        "lattices": len(records),
        "distributive": sum(r.distributive for r in records),
        "adjoined ordinal sums": sum(r.adjoined_ordinal_sum for r in records),
        "disconnected proper part (the note's parallel sums)": sum(r.disconnected for r in records),
        "of at least one kind": sum(r.distributive or r.adjoined_ordinal_sum or r.disconnected
                                    for r in records),
        "of no kind": sum(not (r.distributive or r.adjoined_ordinal_sum or r.disconnected)
                          for r in records),
        "in Table 1": sum(r.kjos_hanssen is not None for r in records),
        "Snow parallel sums (two interval components)": sum(r.snow_sum for r in records),
        "disconnected, not distributive, not Snow": len(unsupported(records)),
        "simple lattices": sum(r.simple for r in records),
        "simple and unsupported": sum(r.simple for r in unsupported(records)),
    }
    return kinds


def stanza(record: Record, leq: Leq) -> dict:
    lat = tables_from_leq(f"L8.{record.index}: {describe(record)}", leq)
    return {"name": lat.name, "size": lat.size,
            "meet": [list(row) for row in lat.meet],
            "join": [list(row) for row in lat.join]}


def describe(record: Record) -> str:
    parts = []
    for size, mins, maxs in record.components:
        parts.append(f"{size}-element component with {mins} minimal and {maxs} maximal")
    kind = "parachute" if record.parachute else ("dual parachute" if record.dual_parachute else "glued sum")
    return f"{kind}; " + ", ".join(parts)


def write_stanzas(records: Sequence[Record], lattices: Sequence[Leq], directory: Path) -> List[Path]:
    directory.mkdir(parents=True, exist_ok=True)
    written = []
    for r in unsupported(records):
        path = directory / f"l8_{r.index}.json"
        path.write_text(json.dumps(stanza(r, lattices[r.index - 1]), indent=2) + "\n")
        written.append(path)
    return written


def census_json(records: Sequence[Record]) -> str:
    return json.dumps({
        "format": "flrp-lattices8 v1",
        "summary": summary(records),
        "unsupported": [r.index for r in unsupported(records)],
        "records": [asdict(r) for r in records],
    }, indent=2) + "\n"


def main(argv: Sequence[str]) -> int:
    args = list(argv[1:])
    out_json: Optional[Path] = None
    stanza_dir: Optional[Path] = None
    if "--json" in args:
        k = args.index("--json")
        out_json = Path(args[k + 1])
        del args[k:k + 2]
    if "--stanzas" in args:
        k = args.index("--stanzas")
        stanza_dir = Path(args[k + 1])
        del args[k:k + 2]
    if args:
        print(__doc__)
        return 2
    lattices = enumerate_lattices(8)
    records = census(8)
    for key, value in summary(records).items():
        print(f"{value:4d}  {key}")
    print()
    print("Disconnected proper part, not distributive, not a Snow parallel sum:")
    print(f"{'index':>6} {'dual':>5} {'|Con|':>5}  covers (0 bottom, 7 top)                         components (size, #min, #max)")
    for r in unsupported(records):
        comps = " ".join(f"({s},{a},{b})" for s, a, b in r.components)
        print(f"{r.index:>6} {r.dual_index:>5} {r.con_size:>5}  {r.covers:<50} {comps}")
    if out_json is not None:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(census_json(records))
        print(f"\ncensus written to {out_json}")
    if stanza_dir is not None:
        paths = write_stanzas(records, lattices, stanza_dir)
        print(f"{len(paths)} stanzas written under {stanza_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
