#!/usr/bin/env python3
"""
File: scripts/python/playground/test_build_assets.py

Description: Tests for build_assets.py, the builder of the playground's
  downloads, run without Agda, without a WASI runtime and without the network.

  The build proves itself: it checks every exercise under the shipped
  WebAssembly and refuses to finish unless each check type-checks exactly one
  module.  Nothing here repeats that.  What these tests pin is the pure half
  that the build and `--check` rest on, each rule against the defect it
  exists for:

  +  the plan: which modules seed an image, which images can serve an
     exercise, and every way a plan can be unbuildable;
  +  the provenance parsers: a library's version and include directories, and
     a GitHub remote in both of its spellings;
  +  the mapping from a file in a library to the module it defines, which
     decides what an image keeps, for sources (literate or not) and for
     interfaces beside them or under `_build`;
  +  the byte formats the page reads: gzip with nothing in its header that
     varies, and tars that the page's reader (`tar.js`) can read, which means
     ustar with long paths split into `prefix`, and regular files where the
     staging tree has hard links;
  +  the interaction protocol as the build reads it: commands quoted as
     agda2-mode quotes them, the prompts stripped, the goals and their
     contexts, and the `Checking` count that decides acceptance;
  +  the manifest rules and the offline gate (`check`), on a synthetic build
     directory with one defect at a time.

  A test marked as an expected failure pins a known defect of the code under
  test; when the defect is fixed, unittest reports an unexpected success and
  the suite fails until the marker is removed.

      python3 scripts/python/playground/test_build_assets.py
"""

from __future__ import annotations

import gzip
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from typing import Dict, List, Sequence, Tuple
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import build_assets as B  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]


# ── Helpers ─────────────────────────────────────────────────────────────────


def line(obj: Dict) -> str:
    """One response as Agda writes it: compact JSON, non-ASCII as itself."""
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))


def interval(start: int, end: int, row: int, col: int) -> Dict:
    return {"start": {"pos": start, "line": row, "col": col},
            "end": {"pos": end, "line": row, "col": col + end - start}}


def ustar_headers(tar: bytes) -> List[Tuple[str, bytes, bytes, int]]:
    """Each header of a tar as the page's reader sees it: the path (with
    ustar's `prefix` joined in front of `name`), the type flag, the magic and
    version, and the size.  Written from the format, not from `tarfile`, so
    that it cannot hide a header kind `tarfile` would absorb (a pax record, a
    GNU long name), which is exactly what `tar.js` refuses."""
    found: List[Tuple[str, bytes, bytes, int]] = []
    at = 0
    while at + 512 <= len(tar):
        block = tar[at:at + 512]
        if block == bytes(512):
            break
        name = block[0:100].split(b"\0", 1)[0].decode("utf-8")
        size = int(block[124:136].split(b"\0", 1)[0].strip() or b"0", 8)
        prefix = block[345:500].split(b"\0", 1)[0].decode("utf-8")
        found.append((f"{prefix}/{name}" if prefix else name, block[156:157],
                      block[257:265], size))
        at += 512 + -(-size // 512) * 512
    return found


def exercise(name: str, source: str = "", solution: str = "") -> B.Exercise:
    return B.Exercise(
        name=name,
        source=source or f"module {name} where\n\nx : Set₁\nx = ?\n",
        solution=solution or f"module {name} where\n\nx : Set₁\nx = Set\n",
    )


# ── The plan ────────────────────────────────────────────────────────────────


class Plan(unittest.TestCase):

    def test_modules_of_reads_the_quoted_nodes(self) -> None:
        """modules_of: one name per quoted node of Agda's graph, sorted; the edges add none."""
        dot = ('digraph dependencies {\n'
               '   m0[label="Seed"];\n'
               '   m1[label="Overture.Terms.Basic"];\n'
               '   m2[label="Agda.Primitive"];\n'
               '   m3[label="Data.Product.Function.Dependent.Propositional"];\n'
               '   m0 -> m1;\n   m1 -> m2;\n   m0 -> m3;\n   m3 -> m2;\n}\n')
        self.assertEqual(B.modules_of(dot), (
            "Agda.Primitive", "Data.Product.Function.Dependent.Propositional",
            "Overture.Terms.Basic", "Seed"))

    def test_imports_of_finds_imports_wherever_they_sit(self) -> None:
        """imports_of: open and bare imports, at top level and in a where block, once each."""
        source = ("module Main where\n"
                  "open import Overture.Signatures using ( 𝓞 ; 𝓥 )\n"
                  "import Level\n"
                  "f = y\n  where open import Data.Nat using ( y )\n"
                  "open import Level using ( Level )\n")
        self.assertEqual(B.imports_of(source), ("Data.Nat", "Level", "Overture.Signatures"))

    def test_module_name_is_the_top_level_module_line(self) -> None:
        """module_name: the name on the first `module NAME ... where` line, or None."""
        self.assertEqual(B.module_name("module Graft where\n\nx = ?\n"), "Graft")
        self.assertEqual(B.module_name("-- a header\nmodule Compose {𝑆 : Signature 𝓞 𝓥} where\n"),
                         "Compose")
        # A commented-out module line is not a module line.
        self.assertIsNone(B.module_name("-- module Graft where\nx = ?\n"))
        self.assertIsNone(B.module_name("open import Level\n"))

    def test_holes_in_counts_both_hole_syntaxes(self) -> None:
        """holes_in: every `?` and every `{!`, which is the number of goals in an exercise."""
        self.assertEqual(B.holes_in("f = ?\ng = {! x !}\nh = {!!}\n"), 3)
        self.assertEqual(B.holes_in("f = x\n"), 0)

    def test_seed_of_imports_the_union_bare_sorted_and_once(self) -> None:
        """seed_of: a module named Seed, one bare import per module, sorted and deduplicated."""
        self.assertEqual(B.seed_of(["Overture.Terms.Basic", "Level", "Overture.Terms.Basic"]),
                         "module Seed where\nimport Level\nimport Overture.Terms.Basic\n")

    def test_serving_names_every_image_whose_closure_holds_the_needs(self) -> None:
        """serving: the images whose closure contains an exercise's, in plan order."""
        closures = {"terms": ("A", "B"), "interpretations": ("A", "B", "C"), "other": ("C",)}
        self.assertEqual(B.serving(closures, ("A", "B")), ("terms", "interpretations"))
        self.assertEqual(B.serving(closures, ("A", "C")), ("interpretations",))
        self.assertEqual(B.serving(closures, ("D",)), ())


class PlanErrors(unittest.TestCase):

    def setUp(self) -> None:
        self.exercises = {n: exercise(n) for n in ("Graft", "Interpret")}
        self.images = (B.Image("terms", ("Graft",)), B.Image("interpretations", ("Interpret",)))

    def errors(self, images: Sequence[B.Image], exercises: Dict[str, B.Exercise]) -> List[str]:
        return B.plan_errors(images, exercises)

    def test_a_sound_plan_has_no_errors(self) -> None:
        """plan_errors: none for two images, each naming one well-formed exercise."""
        self.assertEqual(self.errors(self.images, self.exercises), [])

    def test_the_committed_plan_is_buildable(self) -> None:
        """plan_errors: none for IMAGES and the committed exercise files."""
        names = [n for image in B.IMAGES for n in image.exercises]
        read = B.read_exercises(ROOT / B.EXERCISE_DIR, names)
        self.assertTrue(read.is_ok, read)
        self.assertEqual(B.plan_errors(B.IMAGES, read.unwrap()), [])

    def test_an_image_no_exercise_names_is_refused(self) -> None:
        """plan_errors: an image with no exercises is refused."""
        errors = self.errors(self.images + (B.Image("empty", ()),), self.exercises)
        self.assertIn("empty: no exercise names it", errors)

    def test_a_name_the_marker_cannot_say_is_refused(self) -> None:
        """plan_errors: a lowercase or underscored name is refused."""
        for name in ("graft", "Not_This", "Two Words"):
            exercises = {**self.exercises, name: exercise(name)}
            errors = self.errors(self.images + (B.Image("x", (name,)),), exercises)
            self.assertIn(f"{name}: not a name the page's marker accepts", errors)

    def test_an_exercise_named_by_two_images_is_refused(self) -> None:
        """plan_errors: one exercise on two images is refused, once."""
        images = self.images + (B.Image("homomorphisms", ("Graft",)),)
        errors = self.errors(images, self.exercises)
        self.assertEqual(errors.count("Graft: named by more than one image"), 1, errors)

    def test_an_exercise_with_no_file_is_refused(self) -> None:
        """plan_errors: a name with no exercise file is refused."""
        errors = self.errors(self.images + (B.Image("x", ("Compose",)),), self.exercises)
        self.assertIn("Compose: no exercise file", errors)

    def test_a_file_whose_module_is_another_is_refused(self) -> None:
        """plan_errors: an exercise or a solution that is not `module NAME` is refused."""
        wrong = {**self.exercises,
                 "Graft": exercise("Graft", source="module Main where\nx = ?\n")}
        self.assertIn("Graft: its exercise is not `module Graft`", self.errors(self.images, wrong))
        wrong = {**self.exercises,
                 "Graft": exercise("Graft", solution="module Main where\nx = Set\n")}
        self.assertIn("Graft: its solution is not `module Graft`", self.errors(self.images, wrong))

    def test_an_exercise_with_nothing_to_fill_is_refused(self) -> None:
        """plan_errors: an exercise with no goal is refused."""
        wrong = {**self.exercises,
                 "Graft": exercise("Graft", source="module Graft where\nx = Set\n")}
        self.assertIn("Graft: the exercise has no goal to fill", self.errors(self.images, wrong))

    def test_a_solution_with_a_goal_left_is_refused(self) -> None:
        """plan_errors: a solution that still has a goal is refused."""
        wrong = {**self.exercises,
                 "Graft": exercise("Graft", solution="module Graft where\nx = {! !}\n")}
        self.assertIn("Graft: the solution still has a goal in it", self.errors(self.images, wrong))


# ── Provenance and the library layout ───────────────────────────────────────


class Libraries(unittest.TestCase):

    def test_library_version_comes_from_the_name_line_only(self) -> None:
        """library_version: the version on `name:`, never one on `depend:`."""
        self.assertEqual(B.library_version("name: standard-library-2.3\ninclude: src\n"), "2.3")
        self.assertEqual(B.library_version("name:standard-library-2.3.1\n"), "2.3.1")
        # This library's own file depends on a versioned library and has no
        # version of its own; reading `depend:` would record 2.3 for it.
        self.assertIsNone(B.library_version(
            "name: agda-algebras\ndepend: standard-library-2.3\ninclude: src\n"))
        self.assertIsNone(B.library_version("include: src\n"))

    def test_repository_slug_reads_both_spellings_of_a_github_remote(self) -> None:
        """repository_slug: owner/name from the SSH and the HTTPS spelling, with or without .git."""
        for remote in ("git@github.com:ualib/agda-algebras.git\n",
                       "https://github.com/ualib/agda-algebras.git",
                       "https://github.com/ualib/agda-algebras\n",
                       "https://github.com/ualib/agda-algebras/",
                       "ssh://git@github.com/ualib/agda-algebras.git"):
            self.assertEqual(B.repository_slug(remote), "ualib/agda-algebras", remote)
        # A name that contains `.git` keeps it.
        self.assertEqual(B.repository_slug("git@github.com:williamdemeo/williamdemeo.github.io.git"),
                         "williamdemeo/williamdemeo.github.io")

    def test_repository_slug_refuses_what_is_not_a_github_repository(self) -> None:
        """repository_slug: None for another host, an owner alone, or a deeper path."""
        for remote in ("", "https://gitlab.com/ualib/agda-algebras.git",
                       "https://github.com/ualib", "https://github.com/ualib/agda-algebras/tree/master"):
            self.assertIsNone(B.repository_slug(remote), remote)

    def test_include_dirs_in_declaration_order(self) -> None:
        """include_dirs: the include line's paths in order, and () without one."""
        self.assertEqual(B.include_dirs((ROOT / "agda-algebras.agda-lib").read_text(encoding="utf-8")),
                         ("src",))
        self.assertEqual(B.include_dirs("name: x\ninclude: src other/dir\n"), ("src", "other/dir"))
        self.assertEqual(B.include_dirs("name: x\ndepend: y\n"), ())

    def test_strip_build_drops_only_a_build_prefix(self) -> None:
        """strip_build: `_build/<version>/agda/` goes; any other path stays as it is."""
        self.assertEqual(B.strip_build(Path("_build/2.8.0/agda/src/Overture/Basic.agdai")),
                         Path("src/Overture/Basic.agdai"))
        for kept in ("src/Overture/Basic.agdai", "_build/2.8.0", "_build/2.8.0/other/src/A.agdai"):
            self.assertEqual(B.strip_build(Path(kept)), Path(kept))

    def test_module_of_reads_sources_and_interfaces(self) -> None:
        """module_of: literate and plain sources, interfaces beside them and under _build."""
        src = (Path("src"),)
        cases = {
            "src/Overture/Terms/Basic.lagda.md": "Overture.Terms.Basic",
            "src/Overture/Terms/Basic.agdai": "Overture.Terms.Basic",
            "_build/2.8.0/agda/src/Overture/Terms/Basic.agdai": "Overture.Terms.Basic",
            "src/Data/Nat/Properties.agda": "Data.Nat.Properties",
            "src/Level.agda": "Level",
        }
        for path, module in cases.items():
            self.assertEqual(B.module_of(Path(path), src), module, path)

    def test_module_of_is_none_outside_every_include(self) -> None:
        """module_of: None for a file outside the includes, a non-module, or a sibling directory."""
        src = (Path("src"),)
        for path in ("scripts/Main.agda", "README.md", "standard-library.agda-lib",
                     "src/README.md", "src.agda",
                     # A directory whose name only starts with the include's.
                     "srcfoo/Main.agda", "_build/2.8.0/agda/srcfoo/Main.agdai"):
            self.assertIsNone(B.module_of(Path(path), src), path)

    def test_module_of_uses_the_include_that_holds_the_file(self) -> None:
        """module_of: with two includes, the path below whichever contains the file."""
        includes = (Path("src"), Path("lib/extra"))
        self.assertEqual(B.module_of(Path("lib/extra/A/B.agda"), includes), "A.B")
        self.assertEqual(B.module_of(Path("src/C.agda"), includes), "C")


# ── The byte formats ────────────────────────────────────────────────────────


class Gzip(unittest.TestCase):

    def test_gzip_bytes_is_deterministic_with_mtime_zero(self) -> None:
        """gzip_bytes: two calls agree, the header's mtime is zero, no file name, round trips."""
        data = b"module Seed where\n" * 100
        first, second = B.gzip_bytes(data), B.gzip_bytes(data)
        self.assertEqual(first, second)
        self.assertEqual(first[:2], b"\x1f\x8b")
        # Two calls inside one second agree whatever the mtime, so the header
        # is read directly: bytes 4 to 8 are the mtime, bit 3 of byte 3 a name.
        self.assertEqual(first[4:8], bytes(4))
        self.assertEqual(first[3] & 0x08, 0)
        self.assertEqual(gzip.decompress(first), data)


class Tar(unittest.TestCase):

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="test-build-assets-")
        self.root = Path(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def tree(self, name: str) -> Path:
        """A small staging tree: the argv, a library file, a nested interface."""
        top = self.root / name
        (top / "lib/agda-algebras/src/Overture").mkdir(parents=True)
        (top / "work").mkdir()
        (top / "agda.argv").write_text("".join(a + "\n" for a in B.ARGV), encoding="utf-8")
        (top / "lib/agda-algebras/src/Overture/Basic.lagda.md").write_text(
            "# Basic\n\n```agda\nmodule Overture.Basic where\n```\n", encoding="utf-8")
        (top / "lib/agda-algebras/src/Overture/Basic.agdai").write_bytes(bytes(range(256)) * 3)
        return top

    def test_tar_bytes_is_deterministic(self) -> None:
        """tar_bytes: the same tree packs to the same bytes, whatever its times, modes or place."""
        one, two = self.tree("one"), self.tree("two")
        os.utime(two / "agda.argv", (1, 1))
        os.utime(two / "lib", (2_000_000_000, 2_000_000_000))
        (two / "agda.argv").chmod(0o600)
        self.assertEqual(B.tar_bytes(one), B.tar_bytes(one))
        self.assertEqual(B.tar_bytes(one), B.tar_bytes(two))

    def test_tar_bytes_pins_every_varying_field(self) -> None:
        """tar_bytes: owner 0 and unnamed, mtime 0, modes 644 and 755, sorted."""
        with tarfile.open(fileobj=io.BytesIO(B.tar_bytes(self.tree("t"))), mode="r:") as fh:
            members = fh.getmembers()
        self.assertEqual([m.name for m in members], sorted(m.name for m in members))
        for m in members:
            self.assertEqual((m.uid, m.gid, m.uname, m.gname, m.mtime), (0, 0, "", "", 0), m.name)
            self.assertEqual(m.mode, 0o755 if m.isdir() else 0o644, m.name)

    def test_tar_bytes_writes_plain_ustar(self) -> None:
        """tar_bytes: every header is ustar, and every entry a file or a directory."""
        headers = ustar_headers(B.tar_bytes(self.tree("t")))
        self.assertTrue(headers)
        for path, kind, magic, _ in headers:
            self.assertEqual(magic, b"ustar\x0000", path)
            self.assertIn(kind, (b"0", b"5"), path)

    def test_a_long_path_is_split_into_prefix_and_round_trips(self) -> None:
        """tar_bytes: a path over 100 bytes goes into ustar's prefix and reads back whole."""
        top = self.tree("t")
        deep = Path("lib/standard-library/src") / ("Algebra" * 8) / ("Construct" * 5) / "Properties.agdai"
        self.assertGreater(len(str(deep).encode("utf-8")), 100)
        (top / deep).parent.mkdir(parents=True)
        (top / deep).write_bytes(b"interface bytes")
        tar = B.tar_bytes(top)
        with tarfile.open(fileobj=io.BytesIO(tar), mode="r:") as fh:
            self.assertEqual(fh.extractfile(str(deep)).read(), b"interface bytes")
        headers = {path.rstrip("/"): kind for path, kind, _, _ in ustar_headers(tar)}
        self.assertEqual(headers.get(str(deep)), b"0", sorted(headers))
        self.assertEqual(B.longest_path(tar), len(str(deep).encode("utf-8")))

    def test_a_hard_linked_file_is_written_with_its_bytes(self) -> None:
        """tar_bytes: the second name of a hard link is a regular file carrying the bytes."""
        # The images are cut from hard-linked copies of one staging tree
        # (`cut_image`), and a link entry carries no bytes for the reader.
        top = self.tree("t")
        first = top / "lib/agda-algebras/src/Overture/Basic.agdai"
        second = top / "work/Linked.agdai"
        os.link(first, second)
        self.assertEqual(first.stat().st_nlink, 2)
        tar = B.tar_bytes(top)
        with tarfile.open(fileobj=io.BytesIO(tar), mode="r:") as fh:
            for name in ("lib/agda-algebras/src/Overture/Basic.agdai", "work/Linked.agdai"):
                member = fh.getmember(name)
                self.assertTrue(member.isreg(), f"{name} is type {member.type!r}")
                self.assertEqual(member.size, first.stat().st_size, name)
                self.assertEqual(fh.extractfile(member).read(), first.read_bytes(), name)
        self.assertEqual(B.count_interfaces(tar), 2)


# ── The interaction protocol ────────────────────────────────────────────────


class Checking(unittest.TestCase):

    def test_checking_count_counts_indented_nested_lines(self) -> None:
        """checking_count: every `Checking` line, an indented nested one too."""
        output = ("Checking Seed (/work/Seed.agda).\n"
                  " Checking Overture.Signatures (/lib/agda-algebras/src/Overture/Signatures.lagda.md).\n"
                  "  Checking Level (/lib/standard-library/src/Level.agda).\n"
                  "Finished Seed.\n")
        self.assertEqual(B.checking_count(output), 3)

    def test_checking_count_ignores_other_lines(self) -> None:
        """checking_count: zero for a run that only loaded, or mentions Checking mid-line."""
        self.assertEqual(B.checking_count(""), 0)
        self.assertEqual(B.checking_count("warning: Checking Seed was skipped\nLoading Level\n"), 0)


class HaskellString(unittest.TestCase):

    # The build and the page must send Agda the same bytes for the same
    # text, so these are also the cases protocol.js' haskellString must meet,
    # and the last test holds the two to each other when node is on PATH.
    CASES = {
        "plain ASCII": ("/work/Graft.agda", '"/work/Graft.agda"'),
        "a quote": ('say "x"', '"say \\"x\\""'),
        "a backslash": ("a\\b", '"a\\\\b"'),
        "a newline": ("a\nb", '"a\\nb"'),
        "a tab, as decimal with the terminator": ("a\tb", '"a\\9\\&b"'),
        "NUL and DEL": ("\x00\x7f", '"\\0\\&\\127\\&"'),
        "a BMP character": ("λ x → x", '"\\x3bb\\& x \\x2192\\& x"'),
        "an astral character": ("𝑨", '"\\x1d468\\&"'),
        # The terminator keeps a following digit out of the number.
        "a digit after an escape": ("𝑆₁1", '"\\x1d446\\&\\x2081\\&1"'),
    }

    def test_haskell_string_quotes_as_agda2_mode_does(self) -> None:
        """haskell_string: ASCII as itself, quote, backslash, newline, controls, BMP, astral."""
        for label, (text, quoted) in self.CASES.items():
            self.assertEqual(B.haskell_string(text), quoted, label)

    @unittest.skipUnless(shutil.which("node"), "node is not on PATH")
    def test_haskell_string_agrees_with_protocol_js(self) -> None:
        """haskell_string: byte for byte what protocol.js' haskellString writes, under node."""
        module = (ROOT / "docs/assets/js/playground/protocol.js").as_uri()
        script = (f'import {{ haskellString }} from "{module}";'
                  "const texts = JSON.parse(process.argv[1]);"
                  "process.stdout.write(JSON.stringify(texts.map(haskellString)));")
        texts = [text for text, _ in self.CASES.values()]
        done = subprocess.run(["node", "--input-type=module", "-e", script, json.dumps(texts)],
                              capture_output=True, text=True, timeout=60)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(json.loads(done.stdout), [B.haskell_string(t) for t in texts])

    def test_interaction_stream_is_a_load_and_one_query_per_goal(self) -> None:
        """interaction_stream: the load, then goal_type_context for goals 0 to n-1."""
        self.assertEqual(B.interaction_stream("/work/Graft.agda", 2), (
            'IOTCM "/work/Graft.agda" NonInteractive Direct (Cmd_load "/work/Graft.agda" [])\n'
            'IOTCM "/work/Graft.agda" None Direct '
            '(Cmd_goal_type_context Simplified 0 noRange "")\n'
            'IOTCM "/work/Graft.agda" None Direct '
            '(Cmd_goal_type_context Simplified 1 noRange "")\n'))
        self.assertEqual(B.interaction_stream("/work/𝑨.agda", 0),
                         'IOTCM "/work/\\x1d468\\&.agda" NonInteractive Direct '
                         '(Cmd_load "/work/\\x1d468\\&.agda" [])\n')


STATUS = {"kind": "Status", "status": {"checked": False, "showImplicitArguments": False,
                                       "showIrrelevantArguments": False}}
RUNNING = {"debugLevel": 1, "kind": "RunningInfo", "message": "Checking Graft (/work/Graft.agda).\n"}
HIGHLIGHT = {"direct": True, "kind": "HighlightingInfo", "info": {"remove": False, "payload": [
    {"atoms": ["keyword"], "definitionSite": None, "note": "", "range": [1, 7], "tokenBased": "TokenBased"},
    {"atoms": ["module"], "definitionSite": None, "note": "", "range": [8, 13], "tokenBased": "TokenBased"},
    {"atoms": ["unsolvedmeta"], "definitionSite": None, "note": "", "range": [20, 21],
     "tokenBased": "NotOnlyTokenBased"},
    {"atoms": ["bound", "operator"], "definitionSite": None, "note": "", "range": [30, 31],
     "tokenBased": "TokenBased"},
    {"atoms": ["hole", "deadcode"], "definitionSite": None, "note": "", "range": [40, 41],
     "tokenBased": "NotOnlyTokenBased"},
]}}
INDIRECT = {"direct": False, "filepath": "/tmp/agda2-mode313895-0", "kind": "HighlightingInfo"}
POINTS = {"kind": "InteractionPoints", "interactionPoints": [
    {"id": 0, "range": [interval(523, 524, 16, 13)]},
    {"id": 1, "range": []},
]}


def goal_specific(goal: int, type_: str, entries: Sequence[Tuple[str, str, bool]]) -> Dict:
    """A GoalSpecific answer, its context in Agda's order: oldest binding first."""
    return {"kind": "DisplayInfo", "info": {
        "kind": "GoalSpecific",
        "interactionPoint": {"id": goal, "range": []},
        "goalInfo": {"kind": "GoalType", "rewrite": "Simplified", "type": type_, "boundary": [],
                     "typeAux": {"kind": "GoalOnly"},
                     "entries": [{"originalName": n, "reifiedName": n, "binding": b, "inScope": s}
                                 for n, b, s in entries]}}}


GOAL0 = goal_specific(0, "Term X", [("X", "Type X.χ", False), ("t", "Term Y", True),
                                    ("σ", "Y → Term X", True)])
GOAL1 = goal_specific(1, "Term X", [("f", "OperationSymbolsOf 𝑆", True)])
ERROR = {"kind": "DisplayInfo", "info": {"kind": "Error", "warnings": [], "error": {
    "message": "/work/Graft.agda:16,13-14\nX != Y of type Type"}}}


def transcript(*answers: Sequence[Dict]) -> str:
    """Agda's output for a stream of commands: a prompt, with no newline,
    before each command's answers, and one standing alone at the end, then
    wasmtime's stderr.  A command with no answer leaves its prompt directly
    in front of the next one."""
    body = "".join("JSON> " + "".join(line(r) + "\n" for r in rs) for rs in answers)
    return (body + "JSON> "
            + "\nFailed to enable nonblocking on stdin: setFdOption: invalid argument (Bad file descriptor)\n")


class Responses(unittest.TestCase):

    def test_responses_strips_prompts_and_keeps_text(self) -> None:
        """responses: every prompt stripped, empty lines skipped, non-JSON kept as Text."""
        output = transcript([STATUS, RUNNING], [], [STATUS, GOAL0])
        found = B.responses(output)
        self.assertEqual(found, [
            STATUS, RUNNING,
            # A command with no answer leaves two prompts on one line.
            STATUS, GOAL0,
            {"kind": "Text", "text": "Failed to enable nonblocking on stdin: setFdOption: "
                                     "invalid argument (Bad file descriptor)"},
        ])

    def test_highlighting_of_keeps_the_direct_aspects_the_site_colors(self) -> None:
        """highlighting_of: [from, to, classes] from direct payloads, unknown aspects dropped."""
        self.assertEqual(B.highlighting_of([STATUS, HIGHLIGHT, INDIRECT]), [
            [1, 7, "Keyword"], [8, 13, "Module"], [30, 31, "Bound Operator"], [40, 41, "Hole"],
        ])

    def test_goals_of_reads_each_goal_with_its_context_newest_first(self) -> None:
        """goals_of: each goal's type, its range or None, and its context reversed."""
        found = B.responses(transcript([STATUS, RUNNING, HIGHLIGHT, POINTS], [STATUS, GOAL0],
                                       [STATUS, GOAL1]))
        goals = B.goals_of(found)
        self.assertTrue(goals.is_ok, goals)
        self.assertEqual(goals.unwrap(), [
            {"id": 0, "range": interval(523, 524, 16, 13), "type": "Term X", "context": [
                {"name": "σ", "type": "Y → Term X", "inScope": True},
                {"name": "t", "type": "Term Y", "inScope": True},
                {"name": "X", "type": "Type X.χ", "inScope": False},
            ]},
            {"id": 1, "range": None, "type": "Term X", "context": [
                {"name": "f", "type": "OperationSymbolsOf 𝑆", "inScope": True},
            ]},
        ])

    def test_goals_of_reads_the_last_list_of_interaction_points(self) -> None:
        """goals_of: the goals are the last InteractionPoints, not the first."""
        early = {"kind": "InteractionPoints", "interactionPoints": [{"id": 0, "range": []}]}
        goals = B.goals_of([early, POINTS, GOAL0, GOAL1])
        self.assertEqual([g["id"] for g in goals.unwrap()], [0, 1])

    def test_a_failed_load_is_an_error(self) -> None:
        """goals_of: an Error display is an error carrying Agda's message."""
        # goals_of once passed Agda's text to fail() as `message=`, which is
        # also fail's own first parameter, so a failed load raised TypeError
        # and the build lost the one message that says what is wrong.
        found = B.responses(transcript([STATUS, RUNNING, ERROR, POINTS],
                                       [STATUS, GOAL0], [STATUS, GOAL1]))
        try:
            goals = B.goals_of(found)
        except TypeError as exc:
            self.fail(f"goals_of raised TypeError: {exc}")
        self.assertTrue(goals.is_err)
        error = goals.unwrap_err()
        self.assertIn("does not load", error.message)
        # Wherever the fix puts Agda's text, it must survive into the error.
        self.assertIn("X != Y", error.message + repr(error.context))

    def test_a_goal_without_its_context_answer_is_an_error(self) -> None:
        """goals_of: a goal no GoalSpecific answered is an error naming it."""
        goals = B.goals_of([POINTS, GOAL0])
        self.assertTrue(goals.is_err)
        self.assertEqual(goals.unwrap_err().context["missing"], [1])

    def test_a_load_with_no_goals_is_an_error(self) -> None:
        """goals_of: no InteractionPoints, or an empty list, is an error."""
        self.assertTrue(B.goals_of([STATUS, RUNNING]).is_err)
        self.assertTrue(B.goals_of([{"kind": "InteractionPoints", "interactionPoints": []}]).is_err)


# ── The manifest and the gate ───────────────────────────────────────────────


def manifest() -> Dict:
    """A coherent manifest in the builder's shape: two images, the larger
    serving both exercises."""
    return {
        "argv": list(B.ARGV),
        "images": {
            "terms.tar.gz": {"exercises": ["Graft"]},
            "interpretations.tar.gz": {"exercises": ["Interpret"]},
        },
        "exercises": {
            "Graft": {"image": "terms.tar.gz",
                      "served_by": ["terms.tar.gz", "interpretations.tar.gz"]},
            "Interpret": {"image": "interpretations.tar.gz",
                          "served_by": ["interpretations.tar.gz"]},
        },
    }


class ManifestErrors(unittest.TestCase):

    def test_a_coherent_manifest_has_no_errors(self) -> None:
        """manifest_errors: none for a coherent manifest."""
        self.assertEqual(B.manifest_errors(manifest()), [])

    def test_an_exercise_whose_image_is_absent(self) -> None:
        """manifest_errors: an exercise naming an image the manifest lacks."""
        m = manifest()
        m["exercises"]["Graft"]["image"] = "gone.tar.gz"
        self.assertIn("Graft: its image gone.tar.gz is not in the manifest", B.manifest_errors(m))

    def test_an_exercise_its_image_does_not_list(self) -> None:
        """manifest_errors: an exercise whose own image does not list it."""
        m = manifest()
        m["images"]["terms.tar.gz"]["exercises"] = []
        self.assertIn("Graft: terms.tar.gz does not list it", B.manifest_errors(m))

    def test_served_by_must_start_with_the_own_image(self) -> None:
        """manifest_errors: served_by empty, or led by another image."""
        for served in ([], ["interpretations.tar.gz", "terms.tar.gz"]):
            m = manifest()
            m["exercises"]["Graft"]["served_by"] = served
            self.assertIn("Graft: served_by does not start with its own image",
                          B.manifest_errors(m), served)

    def test_served_by_names_only_known_images(self) -> None:
        """manifest_errors: served_by naming an image the manifest lacks."""
        m = manifest()
        m["exercises"]["Graft"]["served_by"].append("gone.tar.gz")
        self.assertIn("Graft: served_by names gone.tar.gz, which is not in the manifest",
                      B.manifest_errors(m))

    def test_an_image_listing_what_is_not_an_exercise(self) -> None:
        """manifest_errors: an image listing a name that is not an exercise."""
        m = manifest()
        m["images"]["terms.tar.gz"]["exercises"].append("Compose")
        self.assertIn("terms.tar.gz: lists Compose, which is not an exercise", B.manifest_errors(m))

    def test_the_built_manifest_holds_together(self) -> None:
        """manifest_errors: none for the manifest `make playground` wrote, when there is one."""
        path = ROOT / B.OUT_DIR / B.MANIFEST
        if not path.is_file():
            self.skipTest(f"no build at {path}; run `make playground`")
        built = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(B.manifest_errors(built), [])
        self.assertEqual(built["argv"], list(B.ARGV))


#: The real pins, read before any test patches them.
PINNED = (B.UPSTREAM_MODULE_SHA256, B.UPSTREAM_MODULE_BYTES)
FAKE_WASM = b"\x00asm\x01\x00\x00\x00 not the checker, only its stand-in" * 40


class Gate(unittest.TestCase):
    """check() on a synthetic build directory, one defect at a time.

    check() binds the checker to the pinned module's hash and size, which a
    synthetic directory cannot carry, so the pins are patched to the stand-in
    for every test but the one that shows the binding."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="test-build-assets-gate-")
        root = Path(self.tmp.name)
        self.root, self.out, self.exercises = root, root / "out", root / "exercises"
        self.out.mkdir()
        self.exercises.mkdir()
        self.packed = 0
        checker = B.gzip_bytes(FAKE_WASM)
        (self.out / B.CHECKER).write_bytes(checker)
        self.manifest = manifest()
        self.manifest["checker"] = {"file": B.CHECKER, "wasm_bytes": len(FAKE_WASM),
                                    "wasm_sha256": B.sha256(FAKE_WASM), "gzip_bytes": len(checker)}
        for name in ("terms", "interpretations"):
            self.manifest["images"][f"{name}.tar.gz"].update(self.pack(name, B.ARGV))
        for name in ("Graft", "Interpret"):
            text = f"module {name} where\n\n-- 𝑨 → 𝑩\nx : Set₁\nx = ?\n"
            (self.exercises / f"{name}.agda").write_text(text, encoding="utf-8")
            self.manifest["exercises"][name].update(
                {"file": f"{name}.agda", "source_sha256": B.sha256(text.encode("utf-8"))})
        self.write()
        self.pins = mock.patch.multiple(B, UPSTREAM_MODULE_SHA256=B.sha256(FAKE_WASM),
                                        UPSTREAM_MODULE_BYTES=len(FAKE_WASM))
        self.pins.start()

    def tearDown(self) -> None:
        self.pins.stop()
        self.tmp.cleanup()

    def pack(self, name: str, argv: Sequence[str] = (), with_argv: bool = True) -> Dict:
        """Write `<name>.tar.gz` and return what the manifest says of it."""
        self.packed += 1
        tree = self.root / "trees" / str(self.packed)
        (tree / "lib/agda-algebras/src").mkdir(parents=True)
        (tree / "work").mkdir()
        (tree / "lib/agda-algebras/src" / f"{name}.agda").write_text(
            f"module {name} where\n", encoding="utf-8")
        if with_argv:
            (tree / "agda.argv").write_text("".join(a + "\n" for a in argv), encoding="utf-8")
        tar = B.tar_bytes(tree)
        wire = B.gzip_bytes(tar)
        (self.out / f"{name}.tar.gz").write_bytes(wire)
        return {"tar_bytes": len(tar), "tar_sha256": B.sha256(tar), "gzip_bytes": len(wire)}

    def write(self) -> None:
        (self.out / B.MANIFEST).write_text(json.dumps(self.manifest, ensure_ascii=False),
                                           encoding="utf-8")

    def refused(self, *needles: str) -> None:
        got = B.check(self.out, self.exercises)
        self.assertTrue(got.is_err, f"check passed: {got}")
        message = got.unwrap_err().message
        for needle in needles:
            self.assertIn(needle, message)

    def test_a_faithful_build_passes(self) -> None:
        """check: a build that is what its manifest says passes, a line per claim."""
        got = B.check(self.out, self.exercises)
        self.assertTrue(got.is_ok, got)
        self.assertEqual(len(got.unwrap()), 1 + 2 * 2 + 2, got.unwrap())

    def test_no_manifest_is_refused(self) -> None:
        """check: a directory with no manifest."""
        (self.out / B.MANIFEST).unlink()
        self.refused("no manifest")

    def test_the_checker_is_bound_to_the_pin_not_to_the_manifest(self) -> None:
        """check: a checker the manifest describes faithfully is still refused unless pinned."""
        with mock.patch.multiple(B, UPSTREAM_MODULE_SHA256=PINNED[0],
                                 UPSTREAM_MODULE_BYTES=PINNED[1]):
            self.refused(B.CHECKER, "not what the manifest describes")

    def test_a_missing_checker_is_refused(self) -> None:
        """check: the checker file is absent."""
        (self.out / B.CHECKER).unlink()
        self.refused("missing asset")

    def test_a_checker_of_another_wire_size_is_refused(self) -> None:
        """check: the checker's size on disk differs from the one the page quotes."""
        self.manifest["checker"]["gzip_bytes"] += 1
        self.write()
        self.refused(B.CHECKER, "on the wire")

    def test_an_image_of_another_wire_size_is_refused(self) -> None:
        """check: an image's size on disk differs from the one the page quotes."""
        self.manifest["images"]["interpretations.tar.gz"]["gzip_bytes"] -= 1
        self.write()
        self.refused("interpretations.tar.gz", "on the wire")

    def test_an_image_the_manifest_does_not_describe_is_refused(self) -> None:
        """check: an image whose inflated hash differs from the manifest's."""
        self.manifest["images"]["terms.tar.gz"]["tar_sha256"] = "0" * 64
        self.write()
        self.refused("terms.tar.gz", "not what the manifest describes")

    def test_an_image_built_under_another_argv_is_refused(self) -> None:
        """check: an image whose agda.argv is not the manifest's argv."""
        self.manifest["images"]["terms.tar.gz"].update(self.pack("terms", B.ARGV[:-2]))
        self.write()
        self.refused("terms.tar.gz", "agda.argv disagrees")

    def test_an_image_without_an_argv_is_refused(self) -> None:
        """check: an image that carries no agda.argv."""
        self.manifest["images"]["terms.tar.gz"].update(self.pack("terms", with_argv=False))
        self.write()
        self.refused("terms.tar.gz", "no agda.argv")

    def test_a_stray_image_is_refused(self) -> None:
        """check: a tar in the directory that the manifest does not name."""
        (self.out / "old.tar.gz").write_bytes(B.gzip_bytes(b""))
        self.refused("old.tar.gz", "not in the manifest")

    def test_an_exercise_file_that_changed_is_refused(self) -> None:
        """check: an exercise file whose sha256 differs from the one the build checked."""
        path = self.exercises / "Interpret.agda"
        path.write_text(path.read_text(encoding="utf-8") + "\n", encoding="utf-8")
        self.refused("Interpret.agda", "not the exercise the build checked")

    def test_a_missing_exercise_file_is_refused(self) -> None:
        """check: an exercise file that is gone."""
        (self.exercises / "Graft.agda").unlink()
        self.refused("Graft.agda", "not the exercise the build checked")

    def test_an_incoherent_manifest_is_refused(self) -> None:
        """check: the manifest's own rules hold (served_by led by the own image)."""
        self.manifest["exercises"]["Graft"]["served_by"].reverse()
        self.write()
        self.refused("Graft: served_by does not start with its own image")

    def test_a_missing_image_is_reported_not_raised(self) -> None:
        """check: a missing image is a refusal, not a traceback."""
        # verified_asset has a "missing asset" answer for this, and check()
        # once called read_argv on the same path regardless, so tarfile.open
        # raised FileNotFoundError before the Result was ever sequenced.
        (self.out / "terms.tar.gz").unlink()
        try:
            got = B.check(self.out, self.exercises)
        except OSError as exc:
            self.fail(f"check raised {type(exc).__name__}: {exc}")
        self.assertTrue(got.is_err)
        self.assertIn("missing asset", got.unwrap_err().message)


if __name__ == "__main__":
    unittest.main(verbosity=2)
