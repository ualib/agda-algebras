#!/usr/bin/env python3
"""
File: scripts/python/playground/test_mkdocs_hook.py

Description: Tests for mkdocs_hook.py, the playground's half of the site
  build, run against temporary docs and build directories without a site
  build.

  What the hook writes is what a reader without JavaScript gets, and what the
  page script reads its URLs and sizes from, so these tests pin it closely:

  +  the code block: Agda's highlighting positions are code points counted
     from 1 with the end exclusive, astral characters count once, the input
     may be unsorted or run past the text, and every `<`, `>` and `&` is
     escaped whether or not it sits in a span;
  +  the goal display, with the bindings Agda knows and the reader cannot
     name marked as such;
  +  the consent sentence, whose sizes must read as `playground.js` writes
     the same numbers, and whose peers clause counts the other exercises on
     the page that share the image;
  +  the gate's data attributes: URLs relative to the page and resolved
     through the build's files, each carrying its content hash, and the
     images that can serve the exercise listed with its own first;
  +  the refusals: a stale build, a manifest without an exercise the page
     marks, a marker twice, a marker with no file;
  +  `on_files` and `on_page_markdown` end to end, on a page with two
     exercises and the assets table, with a build and without one.

  Pages and files are mkdocs' own `File` and `Files`; the config is a
  dictionary with the few keys the hook and `File.generated` read.

  A test marked as an expected failure pins a known defect of the code under
  test; when the defect is fixed, unittest reports an unexpected success and
  the suite fails until the marker is removed.

      python3 scripts/python/playground/test_mkdocs_hook.py
"""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Callable, Dict, List, Optional

sys.path.insert(0, str(Path(__file__).resolve().parent))

from mkdocs.exceptions import PluginError  # noqa: E402
from mkdocs.structure.files import File, Files  # noqa: E402

import mkdocs_hook as H  # noqa: E402


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


GRAFT = ("module Graft where\n\n"
         "-- 𝑨 < 𝑩 & \"so\"\n"
         "graft : Term Y → (Y → Term X) → Term X\n"
         "graft t σ = ?\n")
INTERPRET = ("module Interpret where\n\n"
             "_✦_ : Interpretation 𝑆₁ 𝑆₂ → Term X → Term X\n"
             "I ✦ t = ?\n")


def manifest() -> Dict:
    """A manifest in the builder's shape, with the real build's sizes."""
    return {
        "agda": "2.8.0",
        "standard_library": "2.3",
        "upstream": {"repository": "agda-web/agda-wasm-dist", "release": "v2.8.0-ghc9.10.3-r0",
                     "asset": "agda-wasm-v2.8.0-ghc9.10.3-r0.zip", "sha256": "1aa2fb20" + "0" * 56},
        "checker": {"file": "agda-opt.wasm.gz", "wasm_bytes": 31524760,
                    "wasm_sha256": "0eb63cef" + "1" * 56, "gzip_bytes": 9703518},
        "built_from": {
            "standard-library": {"version": "2.3", "path": "/nix/store/x-standard-library-2.3"},
            "agda-algebras": {"repository": "ualib/agda-algebras",
                              "commit": "d683c79bb4a9db8380ba409e706b0eb766284f70", "dirty": False},
        },
        "argv": ["agda", "-i", "/work"],
        "images": {
            "terms.tar.gz": {"exercises": ["Graft"], "interfaces": 22, "gzip_bytes": 378681,
                             "tar_sha256": "edeff17d" + "2" * 56},
            "interpretations.tar.gz": {"exercises": ["Interpret"], "interfaces": 75,
                                       "gzip_bytes": 6251569, "tar_sha256": "bf08982a" + "3" * 56},
        },
        "exercises": {
            "Graft": {
                "file": "Graft.agda", "image": "terms.tar.gz",
                "served_by": ["terms.tar.gz", "interpretations.tar.gz"],
                "source_sha256": sha(GRAFT),
                "goals": [{"id": 0, "range": None, "type": "Term X", "context": [
                    {"name": "σ", "type": "Y → Term X", "inScope": True},
                    {"name": "X", "type": "Type X.χ", "inScope": False}]}],
                # `graft` opening line 4, and the hole, the last character
                # before the final newline: positions in code points, so 𝑨
                # and 𝑩 on line 3 are one each.
                "highlighting": [[37, 42, "Function"], [88, 89, "Hole"]],
            },
            "Interpret": {
                "file": "Interpret.agda", "image": "interpretations.tar.gz",
                "served_by": ["interpretations.tar.gz"],
                "source_sha256": sha(INTERPRET),
                "goals": [{"id": 0, "range": None, "type": "Term X", "context": []},
                          {"id": 1, "range": None, "type": "Term X", "context": []}],
                "highlighting": [],
            },
        },
    }


def script_text(uri: str) -> str:
    """A page script's stand-in text, distinct per script, so that each
    script's version hash is its own."""
    return f"// {uri}\n"


class Config(dict):
    """The keys the hook reads, and the attributes `File.generated` reads."""

    def __getattr__(self, key: str) -> object:
        try:
            return self[key]
        except KeyError as exc:
            raise AttributeError(key) from exc


class Site:
    """A temporary checkout: mkdocs.yml, a docs tree with the exercises and
    the page's scripts, and, if asked, a build in `.playground/`."""

    def __init__(self, built: Optional[Dict] = None) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="test-mkdocs-hook-")
        self.root = Path(self.tmp.name)
        self.docs = self.root / "docs"
        self.site = self.root / "site"
        (self.root / "mkdocs.yml").write_text("site_name: test\n", encoding="utf-8")
        self.write(f"{H.EXERCISES}/Graft.agda", GRAFT)
        self.write(f"{H.EXERCISES}/Interpret.agda", INTERPRET)
        for uri in H.PAGE_SCRIPTS:
            self.write(uri, script_text(uri))
        for name in H.WORKER_FILES:
            self.write(f"{H.WORKER_DIR}/{name}", f"// worker {name}\n")
        if built is not None:
            self.build(built)
        self.config = Config(docs_dir=str(self.docs), site_dir=str(self.site),
                             config_file_path=str(self.root / "mkdocs.yml"),
                             use_directory_urls=True,
                             plugins=SimpleNamespace(_current_plugin=None))
        self.page = SimpleNamespace(file=self.file("playground.md"))

    def write(self, uri: str, text: str) -> None:
        path = self.docs / uri
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def build(self, built: Dict) -> None:
        out = self.root / H.BUILT
        out.mkdir(exist_ok=True)
        (out / "manifest.json").write_text(json.dumps(built, ensure_ascii=False), encoding="utf-8")
        for name in [built["checker"]["file"], *built["images"]]:
            (out / name).write_bytes(b"\x1f\x8b stand-in")

    def file(self, uri: str) -> File:
        return File(uri, str(self.docs), str(self.site), True)

    def discovered(self) -> Files:
        """The files mkdocs finds in docs/, before any hook runs."""
        return Files([self.file(str(p.relative_to(self.docs)))
                      for p in sorted(self.docs.rglob("*")) if p.is_file()]
                     + [self.page.file])

    def published(self, built: Optional[Dict]) -> Files:
        """The files after `on_files`, written out by hand: the worker where
        the hook's global says, and the assets under `assets/agda/`."""
        uris = [*H.PAGE_SCRIPTS, *[f"{H._worker_dir}/{n}" for n in H.WORKER_FILES]]
        if built is not None:
            uris += [f"{H.ASSETS}/{n}" for n in ["manifest.json", built["checker"]["file"],
                                                  *built["images"]]]
        return Files([self.file(u) for u in uris] + [self.page.file])

    def close(self) -> None:
        self.tmp.cleanup()


class HookTest(unittest.TestCase):
    """Every test starts and ends with the worker where the hook keeps it
    before `on_files` runs, since `on_files` moves it, module-wide."""

    def setUp(self) -> None:
        H._worker_dir = H.WORKER_DIR

    def tearDown(self) -> None:
        H._worker_dir = H.WORKER_DIR

    def refused(self, run: Callable[[], object], *needles: str) -> None:
        with self.assertRaises(PluginError) as caught:
            run()
        for needle in needles:
            self.assertIn(needle, str(caught.exception))


# ── The code block ──────────────────────────────────────────────────────────


class Highlighted(HookTest):

    def test_positions_are_code_points_from_one_end_exclusive(self) -> None:
        """highlighted: [1, 2) is the first character, and text between spans is kept."""
        self.assertEqual(H.highlighted("f = x", [[1, 2, "Function"], [5, 6, "Bound"]]),
                         '<span class="Function">f</span> = <span class="Bound">x</span>')
        self.assertEqual(H.highlighted("graft t", [[1, 6, "Function Operator"]]),
                         '<span class="Function Operator">graft</span> t')

    def test_an_astral_character_is_one_position(self) -> None:
        """highlighted: 𝑨 is one code point, as Agda counts it, though two UTF-16 units."""
        self.assertEqual(
            H.highlighted("𝑨 → 𝑩 x", [[1, 2, "Bound"], [3, 4, "Symbol"], [5, 6, "Bound"],
                                      [7, 8, "Bound"]]),
            '<span class="Bound">𝑨</span> <span class="Symbol">→</span> '
            '<span class="Bound">𝑩</span> <span class="Bound">x</span>')

    def test_html_is_escaped_inside_and_outside_spans(self) -> None:
        """highlighted: < > & are escaped in a span, between spans, and with no spans at all."""
        source = "x < y && z > w"
        self.assertEqual(
            H.highlighted(source, [[1, 2, "Bound"], [5, 6, "Bound"], [7, 9, "Operator"]]),
            '<span class="Bound">x</span> &lt; <span class="Bound">y</span> '
            '<span class="Operator">&amp;&amp;</span> z &gt; w')
        self.assertEqual(H.highlighted("a < b", [[3, 4, "Symbol"]]),
                         'a <span class="Symbol">&lt;</span> b')
        self.assertEqual(H.highlighted(source, []), "x &lt; y &amp;&amp; z &gt; w")

    def test_unsorted_ranges_are_placed_in_order(self) -> None:
        """highlighted: the ranges' order in the input does not matter."""
        ranges = [[5, 6, "Bound"], [1, 2, "Function"], [3, 4, "Symbol"]]
        self.assertEqual(H.highlighted("f = x", ranges),
                         H.highlighted("f = x", sorted(ranges)))
        self.assertEqual(H.highlighted("f = x", ranges),
                         '<span class="Function">f</span> <span class="Symbol">=</span> '
                         '<span class="Bound">x</span>')

    def test_a_range_past_the_end_is_cut_or_dropped(self) -> None:
        """highlighted: a range running past the text is cut there; one wholly past it is dropped."""
        self.assertEqual(H.highlighted("ab", [[2, 99, "Hole"]]), 'a<span class="Hole">b</span>')
        self.assertEqual(H.highlighted("ab", [[1, 2, "Bound"], [10, 20, "Hole"]]),
                         '<span class="Bound">a</span>b')


class Goals(HookTest):

    def test_goal_display_marks_what_is_not_in_scope(self) -> None:
        """goal_display: each goal's id and type, its context, out-of-scope entries marked."""
        html = H.goal_display(manifest()["exercises"]["Graft"]["goals"])
        self.assertIn('<span class="agda-goal__id">?0</span> '
                      '<span class="agda-goal__type">Term X</span>', html)
        self.assertIn("<dt>σ</dt><dd>Y → Term X</dd>", html)
        self.assertIn('<dt class="agda-context__hidden">X</dt>'
                      '<dd class="agda-context__hidden">Type X.χ '
                      '<span class="agda-context__note">(not in scope)</span></dd>', html)
        self.assertEqual(html.count("(not in scope)"), 1)

    def test_goal_display_escapes_names_and_types(self) -> None:
        """goal_display: a type with < and & is escaped."""
        html = H.goal_display([{"id": 3, "type": "a < b", "context": [
            {"name": "_&_", "type": "A → B → A", "inScope": True}]}])
        self.assertIn("a &lt; b", html)
        self.assertIn("<dt>_&amp;_</dt>", html)


# ── The consent sentence ────────────────────────────────────────────────────


class Sentence(HookTest):

    # `bytes(n)` in playground.js gives these, under node 22 (2026-10-04).
    AS_PLAYGROUND_JS = {
        0: "0 bytes", 1023: "1023 bytes", 1024: "1 KB", 1536: "2 KB", 49692: "49 KB",
        378681: "370 KB", 1048575: "1024 KB", 1048576: "1.0 MB", 1511328: "1.4 MB",
        6251569: "6.0 MB", 9703518: "9.3 MB", 10485759: "10.0 MB", 10485760: "10 MB",
        38727934: "37 MB",
    }
    # Exact halves, where JavaScript's toFixed and Math.round round up and
    # Python's format and round() round to even.
    TIES = {2560: "3 KB", 1310720: "1.3 MB", 11010048: "11 MB"}

    def test_sizes_read_as_playground_js_writes_them(self) -> None:
        """_humanize: bytes, KB rounded, MB to one place below 10 and none from 10."""
        for count, said in self.AS_PLAYGROUND_JS.items():
            self.assertEqual(H._humanize(count), said, count)

    def test_exact_halves_round_as_playground_js_does(self) -> None:
        """_humanize: an exact half rounds up, as in playground.js."""
        for count, said in self.TIES.items():
            self.assertEqual(H._humanize(count), said, count)

    def test_an_image_of_its_own_is_one_sentence_without_peers(self) -> None:
        """sentence: the checker's and the image's sizes, the image's module count, no peers."""
        self.assertEqual(
            H.sentence(manifest(), "terms.tar.gz", 1),
            "Checking this needs Agda 2.8.0 compiled to WebAssembly: 9.3 MB for the checker "
            "and 370 KB for the 22 compiled modules this exercise imports.  Nothing is "
            "downloaded until you ask, and nothing you type leaves this tab.")

    def test_the_peers_clause_counts_the_others(self) -> None:
        """sentence: one other exercise, then two others, sharing the image."""
        two = H.sentence(manifest(), "interpretations.tar.gz", 2)
        self.assertIn("6.0 MB for the 75 compiled modules this exercise imports.  The library "
                      "files are shared with 1 other exercise on this page.  Nothing", two)
        three = H.sentence(manifest(), "interpretations.tar.gz", 3)
        self.assertIn("shared with 2 other exercises on this page.", three)


# ── The exercise ────────────────────────────────────────────────────────────


class Exercise(HookTest):

    def setUp(self) -> None:
        super().setUp()
        self.site = Site()

    def tearDown(self) -> None:
        self.site.close()
        super().tearDown()

    def test_without_a_manifest_the_code_is_plain_and_the_reason_said(self) -> None:
        """exercise_html: no build gives the escaped code and the not-built sentence, no gate."""
        html = H.exercise_html("Graft", GRAFT, None, {}, self.site.page, Files([]))
        self.assertTrue(html.startswith('<div class="agda-exercise" id="ex-graft">\n'), html)
        self.assertIn('<pre class="agda-exercise__code"><code>module Graft where\n\n'
                      '-- 𝑨 &lt; 𝑩 &amp; &quot;so&quot;\n', html)
        self.assertIn("The checker is not part of this build of the site", html)
        self.assertNotIn("data-", html)
        self.assertNotIn("<span", html)

    def test_the_slug_splits_a_camel_case_name(self) -> None:
        """exercise_html: the anchor of ComposeHoms is ex-compose-homs."""
        html = H.exercise_html("ComposeHoms", "x", None, {}, self.site.page, Files([]))
        self.assertIn('id="ex-compose-homs"', html)

    def test_with_a_manifest_the_gate_carries_versioned_relative_urls(self) -> None:
        """exercise_html: data attributes relative to the page, each with its hash, own image first."""
        m = manifest()
        html = H.exercise_html("Graft", GRAFT, m, {"terms.tar.gz": 1}, self.site.page,
                               self.site.published(m))
        expected = {
            "class": "agda-exercise__gate",
            "data-file": "Graft.agda",
            "data-worker": "../assets/js/playground/checker.js",
            "data-checker": "../assets/agda/agda-opt.wasm.gz?h=0eb63cef",
            "data-checker-bytes": "9703518",
            "data-image": "../assets/agda/terms.tar.gz?h=edeff17d",
            "data-image-bytes": "378681",
            "data-served": "../assets/agda/terms.tar.gz?h=edeff17d "
                           "../assets/agda/interpretations.tar.gz?h=bf08982a",
        }
        gate = " ".join(f'{k}="{v}"' for k, v in expected.items())
        self.assertIn(f"<p {gate}>Checking this needs Agda 2.8.0", html)
        self.assertIn('data-exercise="Graft"', html)

    def test_with_a_manifest_the_code_is_highlighted_and_the_goals_shown(self) -> None:
        """exercise_html: Agda's classes on the code, then the goal display for one goal."""
        m = manifest()
        html = H.exercise_html("Graft", GRAFT, m, {"terms.tar.gz": 1}, self.site.page,
                               self.site.published(m))
        self.assertIn('<pre class="Agda agda-exercise__code"><code>module Graft where', html)
        self.assertIn('-- 𝑨 &lt; 𝑩 &amp; &quot;so&quot;\n<span class="Function">graft</span> : Term', html)
        self.assertIn('graft t σ = <span class="Hole">?</span>\n</code></pre>', html)
        self.assertIn("What Agda says about this goal,", html)
        self.assertIn("<dt>σ</dt>", html)
        two = H.exercise_html("Interpret", INTERPRET, m, {"interpretations.tar.gz": 1},
                              self.site.page, self.site.published(m))
        self.assertIn("What Agda says about these goals,", two)

    def test_an_asset_the_build_does_not_carry_fails_the_build(self) -> None:
        """exercise_html: a served image missing from the site's files is a PluginError."""
        m = manifest()
        files = self.site.published(m)
        files.remove(files.get_file_from_path("assets/agda/interpretations.tar.gz"))
        self.refused(lambda: H.exercise_html("Graft", GRAFT, m, {"terms.tar.gz": 1},
                                             self.site.page, files),
                     "assets/agda/interpretations.tar.gz")


class Freshness(HookTest):

    def test_fresh_sources_pass(self) -> None:
        """check_fresh: the files the build checked pass."""
        H.check_fresh(manifest(), {"Graft": GRAFT, "Interpret": INTERPRET})

    def test_a_changed_source_fails_the_build(self) -> None:
        """check_fresh: one changed character is a PluginError naming the exercise."""
        self.refused(lambda: H.check_fresh(manifest(), {"Graft": GRAFT + " ", "Interpret": INTERPRET}),
                     "Graft", "make playground")

    def test_a_source_the_manifest_lacks_fails_the_build(self) -> None:
        """check_fresh: an exercise with no recorded hash is stale."""
        self.refused(lambda: H.check_fresh(manifest(), {"Compose": "module Compose where\n"}),
                     "Compose")


class AssetsTable(HookTest):

    def test_the_table_lists_each_download_with_its_provenance(self) -> None:
        """assets_table: a row per download, the commit linked, the upstream release named."""
        html = H.assets_table(manifest())
        self.assertIn("<tr><td>The checker, Agda 2.8.0</td><td></td><td>9.3 MB</td></tr>", html)
        self.assertIn("<tr><td>Library files for Graft</td><td>22</td><td>370 KB</td></tr>", html)
        self.assertIn("<tr><td>Library files for Interpret</td><td>75</td><td>6.0 MB</td></tr>", html)
        self.assertIn('<a href="https://github.com/ualib/agda-algebras/tree/'
                      'd683c79bb4a9db8380ba409e706b0eb766284f70">ualib/agda-algebras at d683c79</a>, '
                      "and the Agda standard library 2.3", html)
        self.assertIn('<a href="https://github.com/agda-web/agda-wasm-dist/releases/tag/'
                      'v2.8.0-ghc9.10.3-r0">agda-web/agda-wasm-dist</a>', html)
        self.assertNotIn("local changes", html)

    def test_a_dirty_build_says_so(self) -> None:
        """assets_table: a build with uncommitted files says it has local changes."""
        m = manifest()
        m["built_from"]["agda-algebras"]["dirty"] = True
        self.assertIn("at d683c79</a> with local changes, and", H.assets_table(m))

    def test_without_a_manifest_the_table_is_a_sentence(self) -> None:
        """assets_table: no build, one sentence."""
        self.assertEqual(H.assets_table(None), "<p>The checker and its library files are not "
                                               "part of this build of the site.</p>")


# ── The hooks, end to end ───────────────────────────────────────────────────


PAGE = ("# Playground\n\nSome prose.\n\n"
        "<!-- playground: Graft -->\n\n"
        "More prose.\n\n"
        "<!--playground:Interpret-->\n\n"
        "## What the downloads are\n\n"
        "<!-- playground-assets -->\n")


def worker_tag(docs: Path) -> str:
    """The hashed worker directory's suffix, computed apart from the hook."""
    return hashlib.sha256(b"".join((docs / H.WORKER_DIR / n).read_bytes()
                                   for n in H.WORKER_FILES)).hexdigest()[:8]


def uris(files: Files) -> List[str]:
    return sorted(f.src_uri for f in files)


class OnFiles(HookTest):

    def test_the_worker_moves_to_a_hashed_directory_and_the_assets_are_published(self) -> None:
        """on_files: one worker, under playground-<hash>; the manifest and every asset under assets/agda."""
        site = Site(built=manifest())
        try:
            files = H.on_files(site.discovered(), site.config)
            tag = worker_tag(site.docs)
            got = uris(files)
            for name in H.WORKER_FILES:
                self.assertIn(f"{H.WORKER_DIR}-{tag}/{name}", got)
                self.assertNotIn(f"{H.WORKER_DIR}/{name}", got)
            for name in ("manifest.json", "agda-opt.wasm.gz", "terms.tar.gz",
                         "interpretations.tar.gz"):
                self.assertIn(f"{H.ASSETS}/{name}", got)
            self.assertEqual(H._worker_dir, f"{H.WORKER_DIR}-{tag}")
        finally:
            site.close()

    def test_without_a_build_only_the_worker_is_published(self) -> None:
        """on_files: no build, no assets, and that is not an error."""
        site = Site()
        try:
            got = uris(H.on_files(site.discovered(), site.config))
            self.assertFalse([u for u in got if u.startswith(H.ASSETS)], got)
        finally:
            site.close()

    def test_a_manifest_naming_a_missing_file_fails_the_build(self) -> None:
        """on_files: an image the manifest names and the build lacks is a PluginError."""
        site = Site(built=manifest())
        try:
            (site.root / H.BUILT / "terms.tar.gz").unlink()
            self.refused(lambda: H.on_files(site.discovered(), site.config), "terms.tar.gz")
        finally:
            site.close()

    def test_a_manifest_without_a_section_fails_the_build(self) -> None:
        """_manifest: a manifest missing `built_from` is a PluginError."""
        m = manifest()
        del m["built_from"]
        site = Site(built=m)
        try:
            self.refused(lambda: H._manifest(site.config), "built_from")
        finally:
            site.close()


class OnPageMarkdown(HookTest):

    def render(self, site: Site, markdown: str = PAGE) -> str:
        files = H.on_files(site.discovered(), site.config)
        return H.on_page_markdown(markdown, site.page, site.config, files)

    def test_a_page_with_two_exercises_and_the_table(self) -> None:
        """on_page_markdown: both markers and the table expanded, in place, scripts appended."""
        site = Site(built=manifest())
        try:
            out = self.render(site)
            tag = worker_tag(site.docs)
        finally:
            site.close()
        self.assertNotIn("<!--", out)
        self.assertTrue(out.startswith("# Playground\n\nSome prose.\n\n"
                                       '<div class="agda-exercise" id="ex-graft" '
                                       'data-exercise="Graft">\n'), out[:200])
        self.assertLess(out.index("More prose."), out.index('id="ex-interpret"'))
        self.assertLess(out.index('id="ex-interpret"'), out.index('<table class="agda-assets">'))
        self.assertEqual(out.count('class="agda-exercise__gate"'), 2)
        self.assertEqual(out.count(f'data-worker="../assets/js/playground-{tag}/checker.js"'), 2)
        self.assertIn('data-served="../assets/agda/interpretations.tar.gz?h=bf08982a"', out)
        # One exercise to an image: no peers clause.
        self.assertNotIn("shared with", out)
        # The page's scripts close the page, in load order, each versioned
        # by its own content.
        tags = [f'<script defer src="../{uri}?h={sha(script_text(uri))[:8]}"></script>'
                for uri in H.PAGE_SCRIPTS]
        self.assertTrue(out.endswith("\n\n" + "\n".join(tags) + "\n"), out[-400:])

    def test_two_exercises_on_one_image_share_it(self) -> None:
        """on_page_markdown: each exercise on a shared image counts the other one."""
        m = manifest()
        m["exercises"]["Interpret"].update(image="terms.tar.gz", served_by=["terms.tar.gz"])
        m["images"]["terms.tar.gz"]["exercises"] = ["Graft", "Interpret"]
        del m["images"]["interpretations.tar.gz"]
        m["exercises"]["Graft"]["served_by"] = ["terms.tar.gz"]
        site = Site(built=m)
        try:
            out = self.render(site)
        finally:
            site.close()
        self.assertEqual(out.count("The library files are shared with 1 other exercise "
                                   "on this page."), 2)

    def test_without_a_build_the_page_is_plain(self) -> None:
        """on_page_markdown: no build gives plain code, the table's sentence, and no scripts."""
        site = Site()
        try:
            out = self.render(site)
        finally:
            site.close()
        self.assertEqual(out.count("The checker is not part of this build of the site"), 2)
        self.assertIn("The checker and its library files are not part of this build", out)
        self.assertNotIn("<script", out)
        self.assertNotIn("data-", out)

    def test_a_page_without_markers_is_untouched(self) -> None:
        """on_page_markdown: a page with no marker comes back as it went in."""
        site = Site(built=manifest())
        try:
            text = "# Elsewhere\n\nNo exercises here.\n"
            self.assertIs(H.on_page_markdown(text, site.page, site.config, Files([])), text)
        finally:
            site.close()

    def test_the_refusals(self) -> None:
        """on_page_markdown: a marker twice, a marker with no file, an exercise the build lacks, a stale file."""
        site = Site(built=manifest())
        try:
            self.refused(lambda: self.render(site, PAGE + "\n<!-- playground: Graft -->\n"),
                         "more than once", "Graft")
            self.refused(lambda: self.render(site, "<!-- playground: Compose -->\n"),
                         "Compose.agda")
            site.write(f"{H.EXERCISES}/Compose.agda", "module Compose where\nx = ?\n")
            self.refused(lambda: self.render(site, "<!-- playground: Compose -->\n"),
                         "no exercises ['Compose']")
            site.write(f"{H.EXERCISES}/Graft.agda", GRAFT.replace("?", "{! !}"))
            self.refused(lambda: self.render(site), "Graft", "make playground")
        finally:
            site.close()


if __name__ == "__main__":
    unittest.main(verbosity=2)
