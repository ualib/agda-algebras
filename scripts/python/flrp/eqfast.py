"""numpy-accelerated backend for the Eq(n) search (issue #486).

File: scripts/python/flrp/eqfast.py

Description:

  Same semantics as the pure-Python functions of ``eqsearch.py`` — the same
  partition enumeration order, the same assignment plan, the same
  classification-by-relation-set, the same closure verdicts — so
  ``survey_fast`` produces reports byte-identical to ``survey`` wherever both
  run; the test suite pins that parity.

  What changes is scale:

  +  meet and join tables are built by vectorized kernels (first-occurrence normal
     forms for meets, alternating block-min label propagation for joins),

  +  candidate filtering in the embedding search is mask arithmetic over whole
     partition tables, and

  +  orbit generation relabels a class under every point permutation at once.

  This is what brings ``Eq(8)`` (``Bell(8) = 4140``) within reach at all: the
  committed ``out/l7_eq8_report.json`` — the eight-point frontier result for ``L7``
  (4,112,640 copies, 108 classes, none closed; see ``docs/notes/flrp-l7-eq6.md`` § 5)
  — is this engine's output, cross-validated figure for figure against an independent
  schedule-specific implementation.

  The ``--group-rep`` restriction of issue #494 (``survey_fast(..., uniform=True)``,
  semantics in ``eqsearch``) runs over ``FastUniformTables``: the tiny uniform pool
  replaces the Bell(n) census, rows are encoded by binary search over the sorted
  pool codes instead of the dense ``n^n`` lookup table (~1.5 GB at ``n = 9``,
  ~40 GB at ``n = 10`` — the sizes the restriction exists to reach), and orbit
  generation is chunked so ``10!`` relabelings fit in memory.

  The run took about three hours on one core, not minutes: the generic height-ordered
  assignment plan defers join constraints, so intermediate prefix counts balloon; the
  known fix is a constraint-density-guided assignment order (follow-up on #486).

  numpy is deliberately NOT a dependency of the pure tools: this module is
  imported only by the ``--fast`` CLI path and by its own tests, both of which
  degrade gracefully without it (a clear error, clean skips).  The repository's
  nix dev shell ships numpy (``flake.nix``), so under ``nix develop`` the fast
  path works out of the box; outside the shell, install numpy in any
  convenient way (for instance
  ``python3 -m venv .venv && .venv/bin/pip install numpy``).

Usage:

  There is no separate CLI; ``--fast`` on ``eqsearch.py`` routes the survey
  through this backend, with reports byte-identical to the pure engine's:

    python3 scripts/python/flrp/eqsearch.py TARGET.json N --fast [--json REPORT.json]
    python3 scripts/python/flrp/eqsearch.py scripts/python/flrp/inputs/l7_lattice.json 7 --fast

  Measured scale on one core: ``Eq(6)`` in about 2 s, ``Eq(7)`` in about 30 s,
  ``Eq(8)`` in about three hours (the committed ``out/l7_eq8_report.json``;
  see the README's fast-backend note for why, and for the planned fix).
"""

from __future__ import annotations

from itertools import permutations
from typing import Dict, List, Sequence, Set, Tuple, Union

import numpy as np

from cg2 import CertificateError
from eqsearch import (ClassReport, Copy, TargetLattice,
                      all_partitions, assignment_plan, closure_report,
                      uniform_partitions, validate_target)


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
        self.universe = self.parts                     # Inv(M) ranges over all of Eq(n)
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
            self.meet[i] = self.codes_of(meet_rows(matrix[i], matrix, n))
            self.join[i] = self.codes_of(join_rows(matrix[i], matrix, n))

    def codes_of(self, rows: np.ndarray) -> np.ndarray:
        """Canonical indices of normal-form rows via the dense lookup table;
        a miss means a kernel produced a non-canonical row, which is a bug."""
        idx = self.lut[rows.astype(np.int64) @ self.powers]
        if (idx < 0).any():
            raise CertificateError("vectorized kernel produced a non-canonical row")
        return idx.astype(np.int16)


class FastUniformTables:
    """Meet and join tables over the uniform pool only — the fast backend of
    the ``--group-rep`` sweep (issue #494), mirroring ``eqsearch``'s
    ``UniformTables``: ``parts`` is ``uniform_partitions(n)`` (bounds
    included) and a table entry is ``-1`` where the true meet or join in
    Eq(n) leaves the pool, which the candidate masks of the embedding
    search read as a failed placement.  Rows are encoded by binary search
    over the sorted pool codes rather than a dense ``n^n`` lookup table
    (~1.5 GB at ``n = 9``, ~40 GB at ``n = 10`` — the sizes this
    restriction exists to reach).  ``universe`` carries all of Eq(n), so
    the delegated pure closure test keeps its unrestricted meaning."""

    def __init__(self, n: int) -> None:
        self.n = n
        self.parts = uniform_partitions(n)             # tuples, canonical order
        self.index: Dict[Tuple[int, ...], int] = {p: i for i, p in enumerate(self.parts)}
        self.bot = self.index[tuple(range(n))]
        self.top = self.index[(0,) * n]
        self.universe = all_partitions(n)              # Inv(M) ranges over all of Eq(n)
        count = len(self.parts)
        matrix = np.array(self.parts, dtype=np.int8)
        self.matrix = matrix
        self.powers = (n ** np.arange(n)).astype(np.int64)
        codes = matrix.astype(np.int64) @ self.powers
        order = np.argsort(codes)                      # codes are little-endian,
        self._sorted_codes = codes[order]              # so NOT in parts order
        self._pool_at = order.astype(np.int32)         # pool index per sorted slot
        self.meet = np.empty((count, count), dtype=np.int16)
        self.join = np.empty((count, count), dtype=np.int16)
        for i in range(count):
            self.meet[i] = self.codes_of(meet_rows(matrix[i], matrix, n))
            self.join[i] = self.codes_of(join_rows(matrix[i], matrix, n))

    def codes_of(self, rows: np.ndarray) -> np.ndarray:
        """Pool indices of normal-form rows, with ``-1`` for a row outside
        the pool — the out-of-pool sentinel of the restricted tables."""
        keys = rows.astype(np.int64) @ self.powers
        pos = np.minimum(np.searchsorted(self._sorted_codes, keys),
                         len(self._sorted_codes) - 1)
        return np.where(self._sorted_codes[pos] == keys,
                        self._pool_at[pos], -1).astype(np.int16)


# The fast sweep's table interface: full Eq(n) tables or the restricted pool.
Tables = Union[FastTables, FastUniformTables]


# ---------------------------------------------------------------------------
# The embedding search, vectorized over candidate partitions

def sublattice_copies_fast(lat: TargetLattice, ft: Tables) -> List[Copy]:
    """Every embedding of the target into Eq(n) with bounds at the diagonal
    and the total relation — the same copies, in the same order, as the pure
    ``sublattice_copies``, with each step's candidate filtering done as mask
    arithmetic over the whole partition table.  Over restricted tables the
    ``-1`` out-of-pool sentinel can never equal a candidate index or a
    placed value, so the same masks are the pool-membership test."""
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
        if step_index == len(plan) - 1:
            # bulk-record the leaf level: the mask already excludes used
            # values, so each candidate completes one embedding
            z = plan[step_index].element
            proto = list(phi)
            for value in candidates(step_index):
                proto[z] = int(value)
                found.append(tuple(proto))
            return
        z = plan[step_index].element
        for value in candidates(step_index):
            phi[z] = int(value)
            used.add(int(value))
            extend(step_index + 1)
            used.remove(int(value))
            phi[z] = -1

    if len(plan) == 0:
        found.append(tuple(phi))
    else:
        extend(0)
    return sorted(found)


# ---------------------------------------------------------------------------
# Classification, with vectorized orbit generation

ORBIT_CHUNK = 250_000   # permutations per relabeling block: bounds the
                        # normal-form pass's memory at 10! without changing
                        # results (unique-of-uniques is chunk-independent)


def _orbit_keys(copy: Copy, ft: Tables, perms: np.ndarray) -> np.ndarray:
    """All relabelings of one copy under every point permutation: unique
    sorted rows of partition indices, one row per orbit member."""
    n, k = ft.n, len(copy)
    vecs = ft.matrix[list(copy)]                       # (k, n)
    chunks: List[np.ndarray] = []
    for start in range(0, perms.shape[0], ORBIT_CHUNK):
        block = perms[start:start + ORBIT_CHUNK]
        count = block.shape[0]
        images = np.empty((count, k, n), dtype=np.int8)
        images[np.arange(count)[:, None, None],
               np.arange(k)[None, :, None],
               block[:, None, :]] = vecs[None, :, :]
        flat = normal_form_rows(images.reshape(count * k, n))
        codes = ft.codes_of(flat).reshape(count, k).astype(np.int64)
        if (codes < 0).any():
            raise CertificateError("orbit relabeling left the partition pool")
        codes.sort(axis=1)
        chunks.append(np.unique(codes, axis=0))
    return np.unique(np.concatenate(chunks), axis=0)


def classify_fast(copies: Sequence[Copy], ft: Tables) -> List[Tuple[Copy, int]]:
    """The same classification as the pure ``classify`` — copies identified
    by their unordered relation sets, first-found representatives in sorted
    order, orbit sizes counting distinct relation sets — with each class's
    orbit generated by one vectorized relabeling pass and all set keys
    produced by bulk byte slicing rather than per-row Python objects.  The
    permutations are streamed straight into a compact array: at ``n = 10``
    there are 3.6 M of them, and a Python list of tuples would dwarf the
    array itself."""
    if not copies:
        return []
    perms = np.fromiter(permutations(range(ft.n)),
                        dtype=np.dtype((np.int8, ft.n)))
    width = len(copies[0])
    keys = np.sort(np.array(copies, dtype=np.int64), axis=1)
    key_bytes = keys.tobytes()
    step = width * 8
    seen: Set[bytes] = set()
    classes: List[Tuple[Copy, int]] = []
    marked = 0
    for i, copy in enumerate(copies):
        if key_bytes[i * step:(i + 1) * step] in seen:
            continue
        orbit = _orbit_keys(copy, ft, perms).astype(np.int64)
        orbit_bytes = orbit.tobytes()
        seen.update(orbit_bytes[j * step:(j + 1) * step]
                    for j in range(orbit.shape[0]))
        classes.append((copy, int(orbit.shape[0])))
        marked += int(orbit.shape[0])
    if marked != np.unique(keys, axis=0).shape[0]:
        raise CertificateError("fast orbit sweep lost copies (relabeling bug)")
    return classes


# ---------------------------------------------------------------------------
# The fast survey

def survey_fast(lat: TargetLattice, n: int,
                uniform: bool = False) -> Tuple[List[ClassReport], int]:
    """Drop-in replacement for ``eqsearch.survey``: identical reports and
    copy count, computed with the vectorized kernels.  Closure verdicts are
    delegated to the pure implementation (they are per-class and cheap), so
    the two backends cannot drift on the part that matters.  With
    ``uniform`` the sweep runs over the uniform pool (the ``--group-rep``
    restriction of issue #494), closure verdicts still over all of Eq(n)."""
    ft: Tables = FastUniformTables(n) if uniform else FastTables(n)
    copies = sublattice_copies_fast(lat, ft)
    return ([closure_report(copy, size, ft)          # type: ignore[arg-type]
             for copy, size in classify_fast(copies, ft)], len(copies))
