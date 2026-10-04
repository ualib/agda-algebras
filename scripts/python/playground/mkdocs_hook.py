"""
File: scripts/python/playground/mkdocs_hook.py

Description: The playground's half of the site build: publish what
  `build_assets.py` built, and expand each `<!-- playground: NAME -->` marker
  into an exercise.

  An exercise on the page is three things, in the following order:

    +  the code, from `docs/playground/NAME.agda`, colored by Agda's own
       highlighting, which the build recorded when it checked the file, with
       the classes every other code block on this site wears;
    +  what Agda says about each goal in it, also recorded by the build: the
       goal's type and its context, newest first, as Emacs shows them;
    +  one paragraph saying what checking it would download, and how much,
       with the URLs and byte counts the page script needs as data
       attributes.

  With JavaScript off, that is the whole exercise, and it already shows a
  goal's type and context in this library's code, from the real checker.
  With it on, `docs/assets/js/playground.js` adds a button after the
  paragraph and leaves the paragraph standing, so the reader who can press
  it is told no less than the one who cannot.

  `<!-- playground-assets -->` expands into a table of what the downloads
  are and what they were built from, read from the same manifest.

Design Principles:
  *Nothing is fetched until a reader asks, and the size is stated first.*
  The sizes in the sentence are read here, at build time, from the manifest
  the asset build wrote beside the files it measured, so a sentence cannot
  quote a size the file does not have.

  *A missing build is said, a stale one is refused.*  `make site` without
  `make playground` first has no assets, and the page then shows the code
  with a sentence saying the checker is not part of this build: that is a
  fast preview, not a failure.  Assets whose recorded exercise differs from
  the file on disk would show a reader one text and check another, so the
  build stops.

  *URLs carry a version.*  The zone in front of the site serves scripts and
  other static files with `max-age=14400` (measured 2026-10-04, as
  williamdemeo/website measured for its own zone), so for four hours after a
  deploy a returning reader could hold an old worker against a new page.  The
  worker's directory is published under a name that changes with its content,
  because its modules import each other by relative path and a query on one
  URL would not reach the others; the checker and the images carry their
  manifest hashes as a query.

Provenance:
  Adapted from `scripts/python/playground_hook.py` of williamdemeo/website at
  commit 952e5eb (MIT, Copyright 2026 William DeMeo; see NOTICE): the hashed
  worker directory, `_humanize`, and the consent sentence's shape are that
  file's; the highlighted code, the goal display and the asset table are new.
"""
from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import sys
from decimal import ROUND_HALF_UP, Decimal
from html import escape
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from mkdocs.config.defaults import MkDocsConfig
from mkdocs.exceptions import PluginError
from mkdocs.structure.files import File, Files
from mkdocs.structure.pages import Page
from mkdocs.utils import get_relative_url

# MkDocs loads this file by path; the builder beside it holds the manifest's
# shape, which the hook and `make playground-check` must agree on.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from build_assets import shape_errors  # noqa: E402

log = logging.getLogger("mkdocs.plugins.ualib.playground")

# A marker is a line of its own.  Mentioned inside a sentence or a code span
# (the site guide does both), it is text about a marker and stays text.
MARKER = re.compile(r"^[ \t]*<!--\s*playground:\s*([A-Za-z0-9]+)\s*-->[ \t]*$", re.MULTILINE)
ASSETS_MARKER = re.compile(r"^[ \t]*<!--\s*playground-assets\s*-->[ \t]*$", re.MULTILINE)

#: Where `make playground` writes, relative to the repository root, unless
#: `PLAYGROUND_OUT` names another directory; the Makefile exports it, so the
#: site publishes what the build it ran wrote and checked.
BUILT = ".playground"
#: Where the built files are published in the site.
ASSETS = "assets/agda"
#: The exercise files, relative to docs_dir.
EXERCISES = "playground"
#: The page's own scripts, in load order, added to the page that has
#: exercises and to no other: the library's 340 pages do not need them.
PAGE_SCRIPTS = ("assets/js/playground-input.js", "assets/js/playground-paint.js",
                "assets/js/playground.js")
#: The worker and the modules it imports, published under a hashed copy of
#: this directory (see `on_files`).
WORKER_DIR = "assets/js/playground"
WORKER_FILES = ("checker.js", "wasi.js", "tar.js", "protocol.js", "edits.js", "session.js")

def worker_dir(docs_dir: Path) -> str:
    """Where the worker is published: `assets/js/playground-<hash>`, a name
    that changes with its content.  The hash covers all its files together,
    since they are one program.  A function of the files on disk, so that
    `on_files`, which publishes the worker there, and `on_page_markdown`,
    which points the page at it, agree without sharing state."""
    sources = [docs_dir / WORKER_DIR / name for name in WORKER_FILES]
    missing = [str(p) for p in sources if not p.is_file()]
    if missing:
        raise PluginError(f"the playground's worker is incomplete: {missing}")
    tag = hashlib.sha256(b"".join(p.read_bytes() for p in sources)).hexdigest()[:8]
    return f"{WORKER_DIR}-{tag}"


def _built_dir(config: MkDocsConfig) -> Path:
    root = Path(config["config_file_path"]).resolve().parent
    return root / os.environ.get("PLAYGROUND_OUT", BUILT)


def _manifest(config: MkDocsConfig) -> Optional[Dict]:
    """The asset build's manifest, or None when there has been no build.  One
    that does not parse, or lacks what the page reads, stops the build with a
    message saying so, not a traceback."""
    path = _built_dir(config) / "manifest.json"
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except ValueError as err:
        raise PluginError(f"{path} is not readable JSON ({err}); run `make playground`.")
    problems = shape_errors(data)
    if problems:
        raise PluginError(f"{path} lacks what the page reads ({'; '.join(problems)}); "
                          "run `make playground`.")
    return data


def on_files(files: Files, config: MkDocsConfig) -> Files:
    """Publish the worker under `worker_dir`, and the built assets, if there
    are any, under `assets/agda/`.

    The plain copies of the worker are removed from the build, so the site
    carries one worker and it is the versioned one."""
    docs_dir = Path(config["docs_dir"])
    worker = worker_dir(docs_dir)
    for name in WORKER_FILES:
        plain = files.get_file_from_path(f"{WORKER_DIR}/{name}")
        if plain is not None:
            files.remove(plain)
        files.append(File.generated(config, f"{worker}/{name}",
                                    abs_src_path=str(docs_dir / WORKER_DIR / name)))

    manifest = _manifest(config)
    if manifest is None:
        log.info("🧩  playground: no assets built (run `make playground`); "
                 "the page will show its exercises without a checker")
        return files
    built = _built_dir(config)
    published = ["manifest.json", manifest["checker"]["file"], *manifest["images"]]
    absent = [name for name in published if not (built / name).is_file()]
    if absent:
        raise PluginError(f"the playground's manifest names files {built} does not "
                          f"hold: {absent}; run `make playground`.")
    # The sizes are what the consent sentences quote; a build cut short can
    # leave new files beside an old manifest, and a reader would then be told
    # one size and sent another.  (`make playground-check` also hashes them.)
    sizes = {manifest["checker"]["file"]: manifest["checker"]["gzip_bytes"],
             **{name: image["gzip_bytes"] for name, image in manifest["images"].items()}}
    wrong = [name for name, size in sizes.items() if (built / name).stat().st_size != size]
    if wrong:
        raise PluginError(f"{wrong} in {built} are not the size the manifest says; "
                          "run `make playground`.")
    for name in published:
        files.append(File.generated(config, f"{ASSETS}/{name}", abs_src_path=str(built / name)))
    log.info(f"🧩  playground: published {len(published)} assets under {ASSETS}/")
    return files


def _rounded(value: float, places: int) -> str:
    """`value` to `places` decimals as JavaScript's `toFixed` writes it: the
    exact binary value, halves away from zero.  Python's own formatting
    rounds halves to even, and 2,560 bytes would be "2 KB" here and "3 KB" on
    the button beside it."""
    return str(Decimal(value).quantize(Decimal(1).scaleb(-places), rounding=ROUND_HALF_UP))


def _humanize(count: int) -> str:
    """Bytes as a reader would say them, matching playground.js' `bytes`."""
    if count >= 1048576:
        return f"{_rounded(count / 1048576, 0 if count >= 10485760 else 1)} MB"
    if count >= 1024:
        return f"{_rounded(count / 1024, 0)} KB"
    return f"{count} bytes"


def code_points(text: str) -> List[str]:
    """The text as Agda counts it: one entry per code point (Python's own
    indexing), which is what Agda's highlighting positions count."""
    return list(text)


def highlighted(source: str, ranges: Sequence[Sequence]) -> str:
    """The source as HTML, each highlighted range in a span with its
    classes.  `ranges` are `[from, to, classes]`, code point positions from 1
    with `to` exclusive, as Agda sends them; they do not overlap."""
    chars = code_points(source)
    out: List[str] = []
    at = 0
    for start, end, classes in sorted(ranges, key=lambda r: r[0]):
        start, end = max(start - 1, at), min(end - 1, len(chars))
        if start >= end:
            continue
        out.append(escape("".join(chars[at:start])))
        out.append(f'<span class="{escape(classes, quote=True)}">'
                   f'{escape("".join(chars[start:end]))}</span>')
        at = end
    out.append(escape("".join(chars[at:])))
    return "".join(out)


def goal_display(goals: Sequence[Dict]) -> str:
    """Each goal's type and context, as the build's checker reported them."""
    def entry(e: Dict) -> str:
        scope = "" if e["inScope"] else ' class="agda-context__hidden"'
        note = "" if e["inScope"] else ' <span class="agda-context__note">(not in scope)</span>'
        return (f"<dt{scope}>{escape(e['name'])}</dt>"
                f"<dd{scope}>{escape(e['type'])}{note}</dd>")

    return "".join(
        f'<div class="agda-goal"><p class="agda-goal__head">'
        f'<span class="agda-goal__id">?{g["id"]}</span> '
        f'<span class="agda-goal__type">{escape(g["type"])}</span></p>'
        f'<dl class="agda-context">{"".join(entry(e) for e in g["context"])}</dl></div>'
        for g in goals
    )


def sentence(manifest: Dict, image: str, peers: int) -> str:
    """The consent sentence, as plain text.  `peers` is how many exercises
    on the page name the same image."""
    checker, img = manifest["checker"], manifest["images"][image]
    shared = (f"  The library files are shared with {peers - 1} other exercise"
              f"{'' if peers == 2 else 's'} on this page." if peers > 1 else "")
    return (f"Checking this needs Agda {manifest['agda']} compiled to WebAssembly: "
            f"{_humanize(checker['gzip_bytes'])} for the checker and "
            f"{_humanize(img['gzip_bytes'])} for the {img['interfaces']} compiled "
            f"modules this exercise imports.{shared}  Nothing is downloaded until you "
            f"ask, and nothing you type leaves this tab.")


def _url(uri: str, page: Page, files: Files) -> str:
    """An asset's URL relative to the page, resolved through the build, so
    that a gate naming a file the build does not carry fails the build."""
    file = files.get_file_from_path(uri)
    if file is None:
        raise PluginError(f"the playground needs `{uri}`, which the build has not.")
    return get_relative_url(file.url, page.file.url)


def exercise_html(name: str, source: str, manifest: Optional[Dict], peers: Dict[str, int],
                  page: Page, files: Files, worker: str) -> str:
    """One exercise: the code, the goals, and the gate, whose worker is the
    one published under `worker`.  Without a manifest, the code alone,
    plainly, and a sentence saying why."""
    slug = re.sub(r"(?<!^)(?=[A-Z])", "-", name).lower()
    if manifest is None:
        return (f'<div class="agda-exercise" id="ex-{slug}">\n'
                f'<pre class="agda-exercise__code"><code>{escape(source)}</code></pre>\n'
                f'<p class="agda-exercise__status">The checker is not part of this build '
                f'of the site (run <code>make playground</code> before <code>make site</code>).</p>\n'
                f'</div>')
    ex = manifest["exercises"][name]
    image = ex["image"]
    checker = manifest["checker"]
    version = lambda file: manifest["images"][file]["tar_sha256"][:8]  # noqa: E731
    attributes = {
        "class": "agda-exercise__gate",
        "data-file": ex["file"],
        "data-worker": _url(f"{worker}/checker.js", page, files),
        "data-checker": _url(f"{ASSETS}/{checker['file']}", page, files)
                        + "?h=" + checker["wasm_sha256"][:8],
        "data-checker-bytes": str(checker["gzip_bytes"]),
        "data-image": _url(f"{ASSETS}/{image}", page, files) + "?h=" + version(image),
        "data-image-bytes": str(manifest["images"][image]["gzip_bytes"]),
        # Every image that can run this exercise, its own first: one already
        # downloaded for another exercise serves this one for nothing.
        "data-served": " ".join(_url(f"{ASSETS}/{f}", page, files) + "?h=" + version(f)
                                for f in ex["served_by"]),
    }
    gate = " ".join(f'{k}="{escape(v, quote=True)}"' for k, v in attributes.items())
    count = len(ex["goals"])
    return (
        f'<div class="agda-exercise" id="ex-{slug}" data-exercise="{escape(name)}">\n'
        f'<pre class="Agda agda-exercise__code"><code>'
        f'{highlighted(source, ex["highlighting"])}</code></pre>\n'
        f'<div class="agda-goals agda-goals--built">'
        f'<p class="agda-goals__note">What Agda says about {"this goal" if count == 1 else "these goals"}, '
        f'from the check made when this page was built:</p>'
        f'{goal_display(ex["goals"])}</div>\n'
        f'<p {gate}>{escape(sentence(manifest, image, peers[image]))}</p>\n'
        f'</div>'
    )


def assets_table(manifest: Optional[Dict]) -> str:
    """What the downloads are, with their sizes and provenance."""
    if manifest is None:
        return "<p>The checker and its library files are not part of this build of the site.</p>"
    checker = manifest["checker"]
    rows = [(f"The checker, Agda {manifest['agda']}", "", _humanize(checker["gzip_bytes"]))] + [
        (f"Library files for {', '.join(image['exercises'])}", str(image["interfaces"]),
         _humanize(image["gzip_bytes"]))
        for image in manifest["images"].values()
    ]
    library = manifest["built_from"]["agda-algebras"]
    stdlib = manifest["built_from"]["standard-library"]
    body = "".join(f"<tr><td>{escape(a)}</td><td>{b}</td><td>{escape(c)}</td></tr>" for a, b, c in rows)
    commit = library["commit"]
    dirty = " with local changes" if library.get("dirty") else ""
    return (
        '<table class="agda-assets"><thead><tr><th>Download</th><th>Compiled modules</th>'
        f'<th>Size</th></tr></thead><tbody>{body}</tbody></table>\n'
        f'<p class="agda-assets__provenance">Built from '
        f'<a href="https://github.com/{escape(library["repository"])}/tree/{escape(commit)}">'
        f'{escape(library["repository"])} at {escape(commit[:7])}</a>{dirty}, and the Agda '
        f'standard library {escape(str(stdlib["version"]))}; the checker is '
        f'<code>{escape(manifest["upstream"]["asset"])}</code> from '
        f'<a href="https://github.com/{escape(manifest["upstream"]["repository"])}/releases/tag/'
        f'{escape(manifest["upstream"]["release"])}">{escape(manifest["upstream"]["repository"])}</a>, '
        f'unmodified.</p>'
    )


def scripts(page: Page, files: Files, docs_dir: Path) -> str:
    """The page's scripts, deferred, each URL carrying its content's hash.

    Deferred, so that they run after the document is parsed and after
    Material's own bundle, which defines the `document$` they subscribe to;
    hashed, for the reason the module docstring gives."""
    tags = []
    for uri in PAGE_SCRIPTS:
        digest = hashlib.sha256((docs_dir / uri).read_bytes()).hexdigest()[:8]
        tags.append(f'<script defer src="{escape(_url(uri, page, files), quote=True)}?h={digest}"></script>')
    return "\n".join(tags)


def check_fresh(manifest: Dict, sources: Dict[str, str]) -> None:
    """Refuse assets built from other exercise text than the files hold."""
    stale = [name for name, text in sources.items()
             if manifest["exercises"].get(name, {}).get("source_sha256")
             != hashlib.sha256(text.encode("utf-8")).hexdigest()]
    if stale:
        raise PluginError(f"the playground's assets were built from other text for "
                          f"{stale} than docs/{EXERCISES}/ holds; run `make playground`.")


def on_page_markdown(markdown: str, page: Page, config: MkDocsConfig, files: Files) -> str:
    names = MARKER.findall(markdown)
    if not names and not ASSETS_MARKER.search(markdown):
        return markdown
    repeated = sorted({n for n in names if names.count(n) > 1})
    if repeated:
        raise PluginError(f"playground exercises marked more than once: {repeated}")
    docs_dir = Path(config["docs_dir"])
    paths = {n: docs_dir / EXERCISES / f"{n}.agda" for n in names}
    absent = [str(p) for p in paths.values() if not p.is_file()]
    if absent:
        raise PluginError(f"playground markers name exercises with no file: {absent}")
    sources = {n: p.read_text(encoding="utf-8") for n, p in paths.items()}
    manifest = _manifest(config)
    if manifest is not None:
        unknown = [n for n in names if n not in manifest["exercises"]]
        if unknown:
            raise PluginError(f"the playground's manifest has no exercises {unknown}; "
                              "add them to build_assets.py's IMAGES and run `make playground`.")
        check_fresh(manifest, sources)
    peers: Dict[str, int] = {}
    if manifest is not None:
        for n in names:
            image = manifest["exercises"][n]["image"]
            peers[image] = peers.get(image, 0) + 1
    worker = worker_dir(docs_dir) if manifest is not None else WORKER_DIR
    out = MARKER.sub(lambda m: exercise_html(m.group(1), sources[m.group(1)], manifest,
                                             peers, page, files, worker), markdown)
    out = ASSETS_MARKER.sub(lambda m: assets_table(manifest), out)
    return out + ("\n\n" + scripts(page, files, docs_dir) + "\n" if names and manifest else "")
