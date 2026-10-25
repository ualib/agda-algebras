#!/usr/bin/env python3
"""
File: scripts/python/theme/test_build_fonts.py

Description: Tests for ``build_fonts.py``'s check mode.

  ``make fonts-check`` must fail when any file ``make fonts`` writes differs
  from what the pins produce, the licenses included (an edited license once
  passed it, because the check compared only the faces and ``fonts.css``).
  These tests drive the pure parts, ``outputs`` and ``stale``, over files in a
  temporary directory; nothing here downloads anything.  ``build_fonts.py``
  imports fontTools, so run them inside ``nix develop`` (``make fonts-test``);
  each prints ``N/N passed`` and the run exits non-zero on failure.
"""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import build_fonts as bf  # noqa: E402

_TMP = tempfile.TemporaryDirectory(prefix="build-fonts-test-")

FACE = bf.Face("x.woff2", "X", "https://example.invalid/x.ttf", "0" * 64)
SUBSET = bf.Subset(FACE, b"woff2 bytes", 3, frozenset({65}), frozenset())
LICENSES = {"OFL-X.txt": b"license text\r\n"}


def tree(name: str, files: dict[str, bytes]) -> Path:
    """A directory holding exactly `files`."""
    root = Path(_TMP.name) / name
    root.mkdir()
    for n, data in files.items():
        (root / n).write_bytes(data)
    return root


def expected() -> dict[str, bytes]:
    return bf.outputs([SUBSET], "/* css */", LICENSES)


def test_outputs_name_the_faces_the_stylesheet_and_the_licenses() -> None:
    assert sorted(expected()) == ["OFL-X.txt", "fonts.css", "x.woff2"]


def test_a_tree_that_matches_is_up_to_date() -> None:
    assert bf.stale(tree("same", expected()), expected()) == []


def test_an_edited_license_is_stale() -> None:
    files = expected() | {"OFL-X.txt": b"license text\r\na local edit\r\n"}
    assert bf.stale(tree("edited", files), expected()) == ["OFL-X.txt"]


def test_a_license_with_other_line_endings_is_stale() -> None:
    # What `core.autocrlf=input` would have committed without .gitattributes.
    files = expected() | {"OFL-X.txt": b"license text\n"}
    assert bf.stale(tree("lf", files), expected()) == ["OFL-X.txt"]


def test_a_missing_file_is_stale() -> None:
    files = {k: v for k, v in expected().items() if k != "OFL-X.txt"}
    assert bf.stale(tree("missing", files), expected()) == ["OFL-X.txt"]


def test_a_changed_face_or_stylesheet_is_stale() -> None:
    files = expected() | {"x.woff2": b"other", "fonts.css": b"/* edited */"}
    assert bf.stale(tree("faces", files), expected()) == ["fonts.css", "x.woff2"]


def test_every_license_is_pinned() -> None:
    assert all(len(sha) == 64 for _name, _url, sha in bf.LICENSES)


def _run() -> int:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failures = []
    for t in tests:
        try:
            t()
        except AssertionError as e:  # noqa: PERF203
            failures.append((t.__name__, e))
    for name, err in failures:
        print(f"FAIL {name}: {err}")
    print(f"{len(tests) - len(failures)}/{len(tests)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(_run())
