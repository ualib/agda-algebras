"""Freese's cg2 worklist algorithm, instrumented to emit proof traces.

This is the engine of the WP-6 certificate pipeline (issue #457): the
congruence-generation algorithm of R. Freese, *Computing congruences
efficiently* (https://math.hawaii.edu/~ralph/Preprints/cg2.pdf), run on a
finite algebra given by operation tables, recording every block merge together
with its justification — a seed pair, or a unary polynomial translate applied
to an earlier merge.  The recorded list is the *Freese trace* that the Agda
checker ``Setoid.Congruences.Certificates.Congruence`` re-verifies; nothing
computed here is trusted until that checker accepts it.

Design constraints, per ``docs/notes/flrp-wp6-freese-certificates.md``:

+ deterministic — seeds in list order, a FIFO worklist, operation symbols,
  coordinates, and frozen tuples in ascending order — so the same input always
  yields byte-identical certificates;
+ the trace records *element* pairs (not union-find roots), because the
  checker justifies each merge as the image of an earlier merged pair;
+ union-find internals (union by size, path compression) are engine-side
  devices only and leave no imprint on the certificate beyond the final
  normal-form parent vector.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Deque, Dict, List, Sequence, Tuple, Union

Pair = Tuple[int, int]


class CertificateError(Exception):
    """A structural problem with the input or an impossible claim."""


@dataclass(frozen=True)
class Operation:
    """A finitary operation on ``range(card)`` given by its value table.

    The table is nested lists of depth ``arity`` (a plain ``int`` for a
    nullary operation): ``table[a1][a2]...[ak]`` is the value at
    ``(a1, ..., ak)``.
    """

    name: str
    arity: int
    table: object

    def apply(self, args: Sequence[int]) -> int:
        if len(args) != self.arity:
            raise CertificateError(
                f"operation {self.name}: expected {self.arity} arguments, got {len(args)}")
        value: object = self.table
        for a in args:
            if not isinstance(value, list) or not 0 <= a < len(value):
                raise CertificateError(f"operation {self.name}: malformed table")
            value = value[a]
        if not isinstance(value, int):
            raise CertificateError(f"operation {self.name}: malformed table")
        return value


@dataclass(frozen=True)
class Algebra:
    """A finite algebra: carrier ``range(card)`` plus operation tables."""

    name: str
    card: int
    operations: Tuple[Operation, ...]


def validate_algebra(alg: Algebra) -> None:
    """Check that every table has the right shape and in-range entries."""

    def check(op: Operation, table: object, depth: int) -> None:
        if depth == 0:
            if not (isinstance(table, int) and 0 <= table < alg.card):
                raise CertificateError(f"operation {op.name}: entry out of range")
        else:
            if not (isinstance(table, list) and len(table) == alg.card):
                raise CertificateError(f"operation {op.name}: wrong table shape")
            for sub in table:
                check(op, sub, depth - 1)

    if alg.card <= 0:
        raise CertificateError("the carrier must be nonempty")
    for op in alg.operations:
        check(op, op.table, op.arity)


@dataclass(frozen=True)
class SeedJust:
    """The merged pair is (at) position ``seed`` of the seed list."""

    seed: int


@dataclass(frozen=True)
class TranslateJust:
    """The merged pair is the image of trace entry ``ref`` (an absolute,
    0-based trace position) under the translate of operation ``op`` moving
    coordinate ``coord``, the remaining coordinates frozen at ``frozen``.

    ``frozen`` has full arity length; its entry at ``coord`` is dead data
    (written as 0 by convention, overwritten by the checker)."""

    op: int
    coord: int
    frozen: Tuple[int, ...]
    ref: int


Justification = Union[SeedJust, TranslateJust]


@dataclass(frozen=True)
class Merge:
    """One justified merge of the cg2 worklist run."""

    lhs: int
    rhs: int
    why: Justification


@dataclass(frozen=True)
class CgResult:
    """The outcome of one cg2 run: the generated congruence as a parent
    vector in Freese normal form, plus the trace that generates it."""

    parent: Tuple[int, ...]
    trace: Tuple[Merge, ...]


class UnionFind:
    """Union-find with union by size and path compression (engine-side)."""

    def __init__(self, n: int) -> None:
        self._parent: List[int] = list(range(n))
        self._size: List[int] = [1] * n

    def find(self, x: int) -> int:
        root = x
        while self._parent[root] != root:
            root = self._parent[root]
        while self._parent[x] != root:
            self._parent[x], x = root, self._parent[x]
        return root

    def union(self, x: int, y: int) -> bool:
        """Merge the blocks of x and y; True iff they were distinct."""
        rx, ry = self.find(x), self.find(y)
        if rx == ry:
            return False
        if self._size[rx] < self._size[ry]:
            rx, ry = ry, rx
        self._parent[ry] = rx
        self._size[rx] += self._size[ry]
        return True

    def normal_form(self, n: int) -> Tuple[int, ...]:
        """The partition as a parent vector in Freese normal form: every
        index points directly at the least element of its block."""
        least: Dict[int, int] = {}
        for i in range(n):
            least.setdefault(self.find(i), i)
        return tuple(least[self.find(i)] for i in range(n))


def forest_edges(parent: Sequence[int]) -> List[Pair]:
    """The forest edges of a parent vector, in the checker's order: each
    non-root index ascending, paired with its root.  This must match the
    Agda-side ``forestEdges`` exactly, since join traces use it as the seed
    list."""
    return [(i, p) for i, p in enumerate(parent) if p != i]


def congruence_generated_by(alg: Algebra, seeds: Sequence[Pair]) -> CgResult:
    """Run the cg2 worklist from the seed pairs, recording the merge trace.

    Seed pairs whose endpoints are already related produce no merge (the
    checker does not require them to); every union actually performed is
    recorded, so replaying the trace reproduces the returned partition —
    which is exactly what the checker's C2 replay verifies."""
    uf = UnionFind(alg.card)
    trace: List[Merge] = []
    queue: Deque[Tuple[Pair, int]] = deque()

    def record(lhs: int, rhs: int, why: Justification) -> None:
        trace.append(Merge(lhs, rhs, why))
        queue.append(((lhs, rhs), len(trace) - 1))

    for position, (a, b) in enumerate(seeds):
        if uf.union(a, b):
            record(a, b, SeedJust(position))

    while queue:
        (x, y), ref = queue.popleft()
        for op_index, op in enumerate(alg.operations):
            for coord in range(op.arity):
                for rest in product(range(alg.card), repeat=op.arity - 1):
                    frozen = rest[:coord] + (0,) + rest[coord:]
                    u = op.apply(rest[:coord] + (x,) + rest[coord:])
                    v = op.apply(rest[:coord] + (y,) + rest[coord:])
                    if uf.union(u, v):
                        record(u, v, TranslateJust(op_index, coord, frozen, ref))

    return CgResult(parent=uf.normal_form(alg.card), trace=tuple(trace))
