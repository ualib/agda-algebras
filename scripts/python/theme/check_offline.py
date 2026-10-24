#!/usr/bin/env python3
"""
File: scripts/python/theme/check_offline.py

Description: Fail when a built page or stylesheet requests anything from
  another origin (#531, #621).

  The site promises that a reader's browser contacts nobody but this site: no
  font CDN, no script host, no API.  The promise broke twice in quiet ways
  before this check existed.  Material's default `theme.font` emits a
  stylesheet link to fonts.googleapis.com on every page, and the old theme
  `@import`-ed JuliaMono from jsDelivr, three stylesheets deep where no grep of
  the HTML would look.  Neither failed anything; a reader behind a proxy simply
  got substitute fonts.

  This is the static half of the check, the one CI runs on every build
  (`make offline-check`, after `make site-full`).  It reads every `.html` and
  `.css` file under the built site and reports each reference that makes a
  browser fetch from an absolute URL:

    +  in HTML, `src` on script, img, iframe, embed, source, track, audio,
       video and input; `srcset`; `poster`; `data` on object; and `href` on a
       <link> whose `rel` names any relation a browser fetches (a <link> with
       no `rel` counts as a fetch, and `rel="canonical"`, which Material emits
       with an absolute URL by design, does not);
    +  in CSS, whether a stylesheet file, a <style> element or a `style`
       attribute: every `url(...)` and every `@import`;
    +  one known script-borne request: Material's repository chip carries
       `data-md-component="source"`, and its bundle answers that attribute by
       fetching api.github.com for star and fork counts on every page load.
       The override in overrides/partials/source.html drops the attribute; a
       page that has it again means the override was lost.

  What a static check cannot see is a request a script makes for another
  reason.  `make offline-audit` loads every page in a real browser and records
  the network log, which covers that; it needs a Chromium, so it is a local
  target, run before a pull request that touches the theme.

Design Principles:
  Pure core, effectful shell: `findings_in_html` and `findings_in_css` map a
  document's text to its findings and touch nothing; `scan` reads the tree;
  `main` prints and sets the exit code.  The relations a browser does not
  fetch are an allow-list, so a relation nobody anticipated fails closed.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from _utils import ErrorType, PipelineError, Result, sequence_results  # noqa: E402
from _utils.file_ops import read_text  # noqa: E402


@dataclass(frozen=True)
class Finding:
    """One off-origin request: where it is, what makes it, and its URL."""
    path: str
    what: str
    url: str


# `<link rel>` values a browser never fetches on its own.  Everything else
# (stylesheet, icon, preconnect, dns-prefetch, preload, prefetch,
# modulepreload, manifest, and any relation not listed) counts as a fetch.
NON_FETCHING_RELS: frozenset[str] = frozenset({
    "alternate", "author", "bookmark", "canonical", "external", "help",
    "license", "me", "next", "nofollow", "noopener", "noreferrer", "prev",
    "search", "tag",
})

# The attributes that make a browser fetch, by element.
FETCHING_ATTRS: dict[str, tuple[str, ...]] = {
    "script": ("src",),
    "img": ("src", "srcset"),
    "iframe": ("src",),
    "embed": ("src",),
    "source": ("src", "srcset"),
    "track": ("src",),
    "audio": ("src",),
    "video": ("src", "poster"),
    "input": ("src",),
    "object": ("data",),
}

ABSOLUTE = re.compile(r"^\s*(?:[a-zA-Z][a-zA-Z0-9+.-]*:)?//", re.ASCII)
LOCAL_SCHEMES = re.compile(r"^\s*(?:data|blob|about):", re.IGNORECASE)
CSS_URL = re.compile(r"""url\(\s*(['"]?)(.*?)\1\s*\)""", re.IGNORECASE | re.DOTALL)
CSS_IMPORT = re.compile(r"""@import\s+(?:url\()?\s*(['"])(.*?)\1""", re.IGNORECASE)
CSS_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)


def off_origin(url: str) -> bool:
    """Does fetching `url` leave the page's origin?

    Relative and root-relative URLs stay on the origin, and so do the inline
    schemes.  Any URL with an authority (`https://host/`, `//host/`) is taken
    to leave it, the site's own host included: the same page is served from a
    preview or a local server, where that host is another origin.
    """
    return bool(ABSOLUTE.match(url)) and not LOCAL_SCHEMES.match(url)


def srcset_urls(value: str) -> tuple[str, ...]:
    """The URLs of a `srcset`: comma-separated, each before its descriptor."""
    return tuple(part.split()[0] for part in value.split(",") if part.split())


def findings_in_css(path: str, css: str, where: str = "stylesheet") -> tuple[Finding, ...]:
    """Every `url()` and `@import` in a stylesheet that leaves the origin."""
    text = CSS_COMMENT.sub("", css)
    imports = tuple(Finding(path, f"{where} @import", m.group(2))
                    for m in CSS_IMPORT.finditer(text) if off_origin(m.group(2)))
    urls = tuple(Finding(path, f"{where} url()", m.group(2))
                 for m in CSS_URL.finditer(text) if off_origin(m.group(2)))
    return imports + tuple(f for f in urls if f.url not in {i.url for i in imports})


class _Collector(HTMLParser):
    """Gathers the fetching references of one HTML document.

    HTMLParser is callback-driven, so this one class holds state; it is
    confined to `findings_in_html`, which hands back an immutable tuple.
    """

    def __init__(self, path: str) -> None:
        super().__init__(convert_charrefs=True)
        self.path = path
        self.found: list[Finding] = []
        self.in_style = False
        self.style_text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        a = {k: (v or "") for k, v in attrs}
        if tag == "link":
            rels = frozenset(a.get("rel", "").lower().split())
            fetches = not rels or bool(rels - NON_FETCHING_RELS)
            if fetches and off_origin(a.get("href", "")):
                self.found.append(Finding(self.path, f"<link rel=\"{a.get('rel', '')}\">", a["href"]))
        for attr in FETCHING_ATTRS.get(tag, ()):
            if attr in a:
                urls = srcset_urls(a[attr]) if attr == "srcset" else (a[attr],)
                self.found.extend(Finding(self.path, f"<{tag} {attr}>", u)
                                  for u in urls if off_origin(u))
        if "style" in a:
            self.found.extend(findings_in_css(self.path, a["style"], f"<{tag} style>"))
        if a.get("data-md-component") == "source":
            self.found.append(Finding(
                self.path, "Material repository chip (data-md-component=\"source\")",
                "https://api.github.com/repos/..."))
        if tag == "style":
            self.in_style = True

    def handle_endtag(self, tag: str) -> None:
        if tag == "style" and self.in_style:
            self.found.extend(findings_in_css(self.path, "".join(self.style_text), "<style>"))
            self.in_style, self.style_text = False, []

    def handle_data(self, data: str) -> None:
        if self.in_style:
            self.style_text.append(data)


def findings_in_html(path: str, html: str) -> tuple[Finding, ...]:
    """Every reference in an HTML document that makes a browser leave the origin."""
    c = _Collector(path)
    c.feed(html)
    c.close()
    return tuple(c.found)


def findings_in_file(root: Path, file: Path) -> Result[tuple[Finding, ...], PipelineError]:
    """Read one built file and check it by its kind."""
    rel = file.relative_to(root).as_posix()
    check = findings_in_html if file.suffix == ".html" else findings_in_css
    return read_text(file).map(lambda text: check(rel, text))


@dataclass(frozen=True)
class Report:
    """What a scan read and what it found."""
    pages: int
    stylesheets: int
    findings: tuple[Finding, ...]


def scan(root: Path) -> Result[Report, PipelineError]:
    """Check every page and stylesheet under a built site."""
    if not (root / "index.html").is_file():
        return Result.err(PipelineError(
            ErrorType.FILE_NOT_FOUND, f"{root}/index.html not found; build the site first (make site)"))
    files = sorted(p for p in root.rglob("*") if p.suffix in (".html", ".css") and p.is_file())
    return sequence_results([findings_in_file(root, f) for f in files]).map(
        lambda per_file: Report(
            pages=sum(1 for f in files if f.suffix == ".html"),
            stylesheets=sum(1 for f in files if f.suffix == ".css"),
            findings=tuple(x for fs in per_file for x in fs)))


def render(report: Report) -> str:
    """The report `make offline-check` prints, one line per distinct finding."""
    head = f"checked {report.pages} pages and {report.stylesheets} stylesheets"
    if not report.findings:
        return head + "\nOK: no page or stylesheet requests anything from another origin"
    distinct = sorted({(f.what, f.url) for f in report.findings})
    lines = [f"  {what}: {url}\n      first in {next(f.path for f in report.findings if (f.what, f.url) == (what, url))}"
             f" ({sum(1 for f in report.findings if (f.what, f.url) == (what, url))} occurrence(s))"
             for what, url in distinct]
    return "\n".join([head, f"FAIL: {len(report.findings)} off-origin request(s)", *lines])


def main() -> int:
    ap = argparse.ArgumentParser(description="Fail when a built page requests another origin.")
    ap.add_argument("site", nargs="?", default="site", type=Path, help="the built site (default: site)")
    args = ap.parse_args()
    result = scan(args.site)
    if result.is_err:
        print(f"error: {result.unwrap_err().message}", file=sys.stderr)
        return 2
    report = result.unwrap()
    print(render(report))
    return 1 if report.findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
