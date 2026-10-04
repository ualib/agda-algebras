#!/usr/bin/env python3
"""Tests for the link rewriting in ``mkdocs_hooks.py``.

Dependency-free: run directly with ``python3 scripts/python/test_mkdocs_hooks.py``
(prints ``OK`` and exits 0 on success) or under ``pytest`` if it is installed.
Only ``on_page_markdown``'s rewriting of reference-style definitions is covered
here; inline links are exercised by every site build.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import mkdocs_hooks as mh  # noqa: E402


def render(text: str) -> str:
    """The Markdown the hook hands MkDocs for ``text``."""
    return mh.on_page_markdown(text, page=None, config=None, files=None)


# --------------------------------------------------------------------------- #
# A definition that climbs to the repository root is retargeted like an inline
# link: a script or a root file to GitHub, a page to its site URL.
# --------------------------------------------------------------------------- #
def test_definition_to_a_script_goes_to_github() -> None:
    assert render("[build]: ../../scripts/python/playground/build_assets.py") \
        == f"[build]: {mh.REPO_BLOB}scripts/python/playground/build_assets.py"


def test_definition_to_a_root_file_goes_to_github() -> None:
    assert render("[notice]: ../../NOTICE") == f"[notice]: {mh.REPO_BLOB}NOTICE"


def test_definition_to_a_module_goes_to_its_page() -> None:
    assert render("[hsp]: ../../src/Setoid/Varieties/HSP.lagda.md#top") \
        == "[hsp]: /Setoid/Varieties/HSP/#top"


def test_definition_keeps_its_title() -> None:
    assert render('[n]: ../../NOTICE "the notice"') \
        == f'[n]: {mh.REPO_BLOB}NOTICE "the notice"'


# --------------------------------------------------------------------------- #
# What is left alone: a sibling page MkDocs resolves itself, a definition that
# does not climb, a footnote, and anything inside a fenced block.
# --------------------------------------------------------------------------- #
def test_sibling_page_is_left_to_mkdocs() -> None:
    line = "[guide]: ../site-guide.md#the-playground"
    assert render(line) == line


def test_definition_that_does_not_climb_is_left_alone() -> None:
    line = "[notice]: assets/agda/NOTICE.txt"
    assert render(line) == line


def test_footnote_is_not_a_definition() -> None:
    line = "[^1]: ../../NOTICE says so."
    assert render(line) == line


def test_fenced_definition_is_left_alone() -> None:
    text = "```\n[notice]: ../../NOTICE\n```"
    assert render(text) == text


# --------------------------------------------------------------------------- #
def main() -> int:
    tests = [v for k, v in sorted(globals().items())
             if k.startswith("test_") and callable(v)]
    for t in tests:
        t()
    print(f"OK ({len(tests)} tests)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
