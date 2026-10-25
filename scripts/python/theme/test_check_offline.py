#!/usr/bin/env python3
"""
File: scripts/python/theme/test_check_offline.py

Description: Tests for ``check_offline.py``.

  Dependency-free: run directly with
  ``python3 scripts/python/theme/test_check_offline.py`` (prints ``N/N
  passed`` and exits non-zero on failure) or under ``pytest`` if it is
  installed.  Nothing here needs MkDocs or a built site: each test is a
  fragment of HTML or CSS, or a small tree written into a temporary
  directory.  The first tests are the teeth: the exact markup Material emits
  when `theme.font` is left on, the @import the old theme carried, and the
  attribute that makes Material call api.github.com, each of which the check
  must catch.
"""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_offline as co  # noqa: E402

_TMP = tempfile.TemporaryDirectory(prefix="check-offline-test-")

# What Material 9.x writes into every page's <head> unless `theme.font: false`.
GOOGLE_FONTS = (
    '<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>'
    '<link rel="stylesheet" href="https://fonts.googleapis.com/css?family=Inter:300,400,700'
    '%7CRoboto+Mono:400,700&display=fallback">')


def urls(findings: tuple[co.Finding, ...]) -> list[str]:
    return sorted(f.url for f in findings)


# --------------------------------------------------------------------------- #
# The teeth: the three leaks the site actually had.
# --------------------------------------------------------------------------- #
def test_catches_a_google_fonts_link() -> None:
    found = co.findings_in_html("p.html", f"<html><head>{GOOGLE_FONTS}</head></html>")
    assert len(found) == 2, found
    assert any("fonts.googleapis.com" in u for u in urls(found))
    assert any("fonts.gstatic.com" in u for u in urls(found))


def test_catches_a_cdn_import_in_a_stylesheet() -> None:
    css = '@import url("https://cdn.jsdelivr.net/gh/cormullion/juliamono/webfonts/juliamono.css");'
    found = co.findings_in_css("custom.css", css)
    assert urls(found) == ["https://cdn.jsdelivr.net/gh/cormullion/juliamono/webfonts/juliamono.css"]
    assert found[0].what == "stylesheet @import"


def test_catches_materials_repository_chip_fetch() -> None:
    html = '<a href="https://github.com/ualib/agda-algebras" class="md-source" data-md-component="source">x</a>'
    found = co.findings_in_html("p.html", html)
    assert len(found) == 1 and "api.github.com" in found[0].url


# --------------------------------------------------------------------------- #
# What is not a request.
# --------------------------------------------------------------------------- #
def test_a_hyperlink_is_not_a_request() -> None:
    assert co.findings_in_html("p.html", '<a href="https://github.com/ualib/agda-lattices">x</a>') == ()


def test_canonical_link_is_not_a_request() -> None:
    html = '<link rel="canonical" href="https://agda-algebras.universalalgebra.org/Setoid/">'
    assert co.findings_in_html("p.html", html) == ()


def test_relative_root_relative_and_inline_urls_stay_on_the_origin() -> None:
    html = ('<link rel="stylesheet" href="../assets/stylesheets/main.css">'
            '<link rel="icon" href="/assets/lambda.png">'
            '<script src="assets/js/agda-copy.js?h=1234"></script>'
            '<img src="data:image/png;base64,AAAA">')
    assert co.findings_in_html("p.html", html) == ()
    css = "@font-face { src: url('juliamono-text.woff2') format('woff2'); } a { background: url(data:image/svg+xml,x) }"
    assert co.findings_in_css("fonts.css", css) == ()


def test_a_url_in_a_css_comment_is_not_a_request() -> None:
    assert co.findings_in_css("x.css", "/* was: @import url('https://cdn.example/x.css'); */") == ()


# --------------------------------------------------------------------------- #
# What is.
# --------------------------------------------------------------------------- #
def test_a_link_without_rel_counts_as_a_fetch() -> None:
    assert urls(co.findings_in_html("p.html", '<link href="https://cdn.example/x.css">')) == [
        "https://cdn.example/x.css"]


def test_an_unknown_rel_fails_closed() -> None:
    html = '<link rel="canonical modulepreload" href="https://cdn.example/m.js">'
    assert len(co.findings_in_html("p.html", html)) == 1


def test_protocol_relative_and_srcset_urls_are_caught() -> None:
    html = ('<script src="//cdn.example/d3.js"></script>'
            '<img srcset="a.png 1x, https://cdn.example/b.png 2x">')
    assert urls(co.findings_in_html("p.html", html)) == ["//cdn.example/d3.js", "https://cdn.example/b.png"]


def test_inline_style_element_and_attribute_are_checked() -> None:
    html = ('<style>@import "https://fonts.example/a.css"; body { background: url(https://x.example/b.png) }</style>'
            '<div style="background-image: url(\'https://x.example/c.png\')"></div>')
    assert urls(co.findings_in_html("p.html", html)) == [
        "https://fonts.example/a.css", "https://x.example/b.png", "https://x.example/c.png"]


# --------------------------------------------------------------------------- #
# The scan over a tree, and its refusal to pass on nothing.
# --------------------------------------------------------------------------- #
def test_scan_reports_pages_stylesheets_and_findings() -> None:
    root = Path(_TMP.name) / "site"
    (root / "assets").mkdir(parents=True)
    (root / "index.html").write_text("<html><head>" + GOOGLE_FONTS + "</head></html>", encoding="utf-8")
    (root / "assets" / "x.css").write_text("a { color: red }", encoding="utf-8")
    report = co.scan(root).unwrap()
    assert (report.pages, report.stylesheets, len(report.findings)) == (1, 1, 2)
    assert "FAIL: 2 off-origin request(s)" in co.render(report)


def test_scan_of_a_tree_without_a_site_is_an_error() -> None:
    empty = Path(_TMP.name) / "empty"
    empty.mkdir()
    assert co.scan(empty).is_err


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
