"""numpy-accelerated backend for the Eq(n) search (issue #486).

Same semantics as the pure-Python functions of ``eqsearch.py`` — the same
partition enumeration order, the same assignment plan, the same
classification-by-relation-set, the same closure verdicts — so
``survey_fast`` produces reports byte-identical to ``survey`` wherever both
run; the test suite pins that parity.  What changes is scale: meet and join
tables are built by vectorized kernels (first-occurrence normal forms for
meets, alternating block-min label propagation for joins), candidate
filtering in the embedding search is mask arithmetic over whole partition
tables, and orbit generation relabels a class under every point permutation
at once.  This is what makes ``Eq(8)`` (``Bell(8) = 4140``) a minutes-scale
sweep; the 2026-07-22 ``L7`` run that settled the eight-point frontier
(4,112,640 copies, 108 classes, none closed — see
``docs/notes/flrp-l7-eq6.md`` § 5 and ``out/l7_eq8_report.json``) used
exactly this engine.

numpy is deliberately NOT a dependency of ``eqsearch.py`` and is not in the
nix dev shell; this module is imported only by the ``--fast`` CLI path and
by its own (skippable) tests.  Install numpy in any convenient way (for
instance ``python3 -m venv .venv && .venv/bin/pip install numpy``) to use it.
"""

from __future__ import annotations

from itertools import permutations
from typing import Dict, List, Sequence, Set, Tuple

import numpy as np

from cg2 import CertificateError
from eqsearch import (ClassReport, Copy, EqTables, TargetLattice,
                      all_partitions, assignment_plan, closure_report,
                      validate_target)


# ---------------------------------------------------------------------------
# Vectorized partition kernels

def normal_form_rows(keys: np.ndarray) -> np.ndarray:
    """Rows of arbitrary block labels, renormalized: each entry becomes the
    first index in its row carrying the same label (the least member of its
    block, i.e. the Freese normal form)."""
    eq = keys[:, None, :] == keys[:, :, None]          # eq[r, y, x]
    return eq.argmax(axis=1).astype(np.int8)           # first y with equal key


def meet_rows(p: np.ndarray, others: np.ndarray, n: int) -> np.ndarray:
    """Meets of one parent vector with every row of ``others``."""
    keys = p[None, :].astype(np.int16) * n + others
    return normal_form_rows(keys)


def join_rows(p: np.ndarray, others: np.ndarray, n: int) -> np.ndarray:
    """Joins of one parent vector with every row of ``others``: alternating
    min-label propagation over the two block structures until fixpoint; the
    limit labels every element with the least member of its join block."""
    count = others.shape[0]
    labels = np.broadcast_to(np.arange(n, dtype=np.int8), (count, n)).copy()
    p_eq = p[None, :] == p[:, None]                    # p_eq[y, x], fixed
    q_eq = others[:, None, :] == others[:, :, None]    # q_eq[r, y, x]
    sentinel = np.int8(n)
    for _ in range(2 * n):
        spread = np.where(p_eq[None, :, :], labels[:, :, None], sentinel)
        step = spread.min(axis=1).astype(np.int8)
        spread = np.where(q_eq, step[:, :, None], sentinel)
        step = spread.min(axis=1).astype(np.int8)
        if np.array_equal(step, labels):
            break
        labels = step
    return labels


class FastTables:
    """Meet and join tables of Eq(n) as numpy ``int16`` arrays, over the same
    canonical partition list as ``eqsearch.EqTables`` (so indices agree).
    Exposes ``parts``/``index``/``bot``/``top``/``n`` with the pure types, so
    the pure closure test runs against it unchanged."""

    def __init__(self, n: int) -> None:
        self.n = n
        self.parts = all_partitions(n)                 # tuples, canonical order
        self.index: Dict[Tuple[int, ...], int] = {p: i for i, p in enumerate(self.parts)}
        self.bot = self.index[tuple(range(n))]
        self.top = self.index[(0,) * n]
        count = len(self.parts)
        matrix = np.array(self.parts, dtype=np.int8)
        self.matrix = matrix
        self.powers = (n ** np.arange(n)).astype(np.int64)
        lut = np.full(n ** n, -1, dtype=np.int32)
        lut[matrix.astype(np.int64) @ self.powers] = np.arange(count)
        self.lut = lut
        self.meet = np.empty((count, count), dtype=np.int16)
        self.join = np.empty((count, count), dtype=np.int16)
        for i in range(count):
            self.meet[i] = self._codes(meet_rows(matrix[i], matrix, n))
            self.join[i] = self._codes(join_rows(matrix[i], matrix, n))

    def _codes(self, rows: np.ndarray) -> np.ndarray:
        idx = self.lut[rows.astype(np.int64) @ self.powers]
        if (idx < 0).any():
            raise CertificateError("vectorized kernel produced a non-canonical row")
        return idx.astype(np.int16)


# ---------------------------------------------------------------------------
# The embedding search, vectorized over candidate partitions

def sublattice_copies_fast(lat: TargetLattice, ft: FastTables) -> List[Copy]:
    """Every embedding of the target into Eq(n) with bounds at the diagonal
    and the total relation — the same copies, in the same order, as the pure
    ``sublattice_copies``, with each step's candidate filtering done as mask
    arithmetic over the whole partition table."""
    bot, top = validate_target(lat)
    plan = assignment_plan(lat, bot, top)
    count = len(ft.parts)
    arange = np.arange(count, dtype=np.int16)
    phi: List[int] = [-1] * lat.size
    phi[bot], phi[top] = ft.bot, ft.top
    used: Set[int] = {ft.bot, ft.top}
    found: List[Tuple[int, ...]] = []

    def candidates(step_index: int) -> np.ndarray:
        step = plan[step_index]
        z = step.element
        mask = np.ones(count, dtype=bool)
        for u, v, r, is_meet in step.checks:
            table = ft.meet if is_meet else ft.join
            if u == z and v == z:                      # r == z by idempotence
                continue
            if u == z or v == z:
                other = v if u == z else u
                row = table[phi[other]]
                mask &= (row == arange) if r == z else (row == phi[r])
            else:                                      # z is the result only
                mask &= arange == table[phi[u], phi[v]]
        mask[list(used)] = False
        return np.nonzero(mask)[0]

    def extend(step_index: int) -> None:
        if step_index == len(plan):
            found.append(tuple(phi))
            return
        z = plan[step_index].element
        for value in candidates(step_index):
            phi[z] = int(value)
            used.add(int(value))
            extend(step_index + 1)
            used.remove(int(value))
            phi[z] = -1

    extend(0)
    return sorted(found)


# ---------------------------------------------------------------------------
# Classification, with vectorized orbit generation

def _orbit_keys(copy: Copy, ft: FastTables,
                perms: np.ndarray) -> np.ndarray:
    """All relabelings of one copy under every point permutation: unique
    sorted rows of partition indices, one row per orbit member."""
    n, k = ft.n, len(copy)
    vecs = ft.matrix[list(copy)]                       # (k, n)
    count = perms.shape[0]
    images = np.empty((count, k, n), dtype=np.int8)
    images[np.arange(count)[:, None, None],
           np.arange(k)[None, :, None],
           perms[:, None, :]] = vecs[None, :, :]
    flat = normal_form_rows(images.reshape(count * k, n))
    codes = ft.lut[flat.astype(np.int64) @ ft.powers].reshape(count, k)
    codes.sort(axis=1)
    return np.unique(codes, axis=0)


def classify_fast(copies: Sequence[Copy], ft: FastTables) -> List[Tuple[Copy, int]]:
    """The same classification as the pure ``classify`` — copies identified
    by their unordered relation sets, first-found representatives in sorted
    order, orbit sizes counting distinct relation sets — with each class's
    orbit generated by one vectorized relabeling pass."""
    perms = np.array(list(permutations(range(ft.n))), dtype=np.int64)
    seen: Set[bytes] = set()
    classes: List[Tuple[Copy, int]] = []
    distinct = 0
    for copy in copies:
        key = np.sort(np.array(copy, dtype=np.int64)).tobytes()
        if key in seen:
            continue
        orbit = _orbit_keys(copy, ft, perms)
        for row in orbit.astype(np.int64):
            seen.add(row.tobytes())
        classes.append((copy, int(orbit.shape[0])))
        distinct += int(orbit.shape[0])
    if distinct != len({tuple(sorted(c)) for c in copies}):
        raise CertificateError("fast orbit sweep lost copies (relabeling bug)")
    return classes


# ---------------------------------------------------------------------------
# The fast survey

def survey_fast(lat: TargetLattice, n: int) -> Tuple[List[ClassReport], int]:
    """Drop-in replacement for ``eqsearch.survey``: identical reports and
    copy count, computed with the vectorized kernels.  Closure verdicts are
    delegated to the pure implementation (they are per-class and cheap), so
    the two backends cannot drift on the part that matters."""
    ft = FastTables(n)
    copies = sublattice_copies_fast(lat, ft)
    return ([closure_report(copy, size, ft)          # type: ignore[arg-type]
             for copy, size in classify_fast(copies, ft)], len(copies))
