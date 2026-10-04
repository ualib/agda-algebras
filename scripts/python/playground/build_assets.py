#!/usr/bin/env python3
"""
File: scripts/python/playground/build_assets.py

Description: Build the files the playground page downloads, and the manifest
  that describes them.

  The page (`docs/playground.md`, ADR-011) runs a real Agda 2.8.0, compiled to
  wasm32-wasi by `agda-web/agda-wasm-dist` and shipped unmodified.  Beside it
  go the *filesystem images*: tars of exactly the sources and interface files
  one closure of this library needs, unpacked into memory by the page's WASI
  host.  An image is a closure, not an exercise, and an exercise can run on
  any image whose closure contains its own: a reader who has loaded the
  largest image opens the smaller exercises for nothing.  Outputs, all in
  `--out` (default `.playground/`, gitignored; the site build publishes them
  under `assets/agda/`):

    agda-opt.wasm.gz    the checker, gzipped for the wire
    <image>.tar.gz      one per entry of IMAGES below
    manifest.json       what each image and exercise is, what it was built
                        from, its hashes and sizes, and what Agda said about
                        each exercise when the build checked it

  The exercises are files: `docs/playground/<Name>.agda`, as the page shows
  it (with goals to fill), and `docs/playground/solutions/<Name>.agda`, a
  finished version.  The page's code block, the editor's first text and the
  build's checks all read the same file, so they cannot disagree.

Design Principles:
  *Interfaces are built where they are cheap and proved where they are used.*
  An interface is accepted only if it sits where the reading Agda looks and
  was built under the options that Agda runs with, and a mismatch in either
  is silent: the module is simply checked again from source (the
  `measuring-agda-under-wasi` skill records both traps).  williamdemeo/website
  answers that by populating each image with the shipped wasm itself, which
  is exact and slow: 63 s for the smallest closure here, 352 s for the
  Setoid one, under wasmtime (measured 2026-10-04).  This builder populates
  with the native Agda the flake pins, the same version, in seconds, and then
  proves acceptance under the shipped wasm, which is the step that matters:
  every image is unpacked fresh and every module the page will check on it is
  checked there, and the build fails unless exactly one module, the one being
  checked, is type-checked.  Measured the same day: native interfaces are
  accepted by the wasm unchanged and load in the same time (1.89 to 1.92 s
  against 1.90 to 1.94 s for the same closure built by the wasm).

  *The argv is the image's.*  Every image carries the argv it was built and
  proved under, in `agda.argv`, and the page reads it from there rather than
  from a copy of its own.

  *Acceptance is a count.*  Agda announces what it type-checks and never what
  it loads, so the instrument is the number of `Checking` lines, unanchored,
  because Agda indents a nested one.  A count of one with exit 0 is the pass.

  *An image records what it was built from*: the standard library's store
  path and version, and this repository's commit.  The build refuses to ship
  a library source or an exercise that differs from that commit, unless told
  otherwise, and then the manifest says so.

Provenance:
  Adapted from `scripts/python/build_playground_assets.py` of
  williamdemeo/website at commit 952e5eb (MIT, Copyright 2026 William
  DeMeo; see NOTICE).  The pins, `gzip_bytes`, `tar_bytes`, `modules_of`,
  `include_dirs`, `strip_build` and the provenance checks are that file's;
  the native population, the per-exercise closures, the interaction checks
  and the exercise files are new.  The checker is `agda-web/agda-wasm-dist`,
  MIT, Copyright 2024 Agda Web, pinned by sha256 below and never modified;
  the images carry Agda's builtins (from that release), modules of the Agda
  standard library (MIT) and of this library.  Every notice those copies
  require is in `docs/assets/agda/NOTICE.txt`, published beside them.

Usage:
  python3 scripts/python/playground/build_assets.py \\
      --dist agda-wasm-v2.8.0-ghc9.10.3-r0.zip --stdlib <standard-library tree> \\
      --wasmtime wasmtime [--agda agda] [--out .playground] [--allow-dirty]
  python3 scripts/python/playground/build_assets.py --check [--out .playground]

  `make playground` supplies every argument from the flake.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import shlex
import shutil
import sys
import tarfile
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from _utils.command_runner import run_command  # noqa: E402
from _utils.pipeline_types import (  # noqa: E402
    ErrorType,
    PipelineError,
    Result,
    sequence_results,
)

# ── The pins ────────────────────────────────────────────────────────────────
#
# Bumping Agda means changing these lines and the flake's `agda-wasm-dist`
# together, and reading the output of `make playground`: a new Agda writes
# interfaces in a new format, so every image is rebuilt and the counts move.
UPSTREAM_REPO = "agda-web/agda-wasm-dist"
UPSTREAM_RELEASE = "v2.8.0-ghc9.10.3-r0"
UPSTREAM_ASSET = "agda-wasm-v2.8.0-ghc9.10.3-r0.zip"
UPSTREAM_SHA256 = "1aa2fb20e8c78bfb0ee1baf24be9517b61ad2f7e45c5c196df72a09f60d981d4"
# The module inside that zip, pinned separately, because the zip is not what
# ships and so the zip's hash proves nothing about the published file.
UPSTREAM_MODULE_SHA256 = "0eb63cefff55dd06de30a807440886af804716aeb6a4d7896f814ad2ae9d1f32"
UPSTREAM_MODULE_BYTES = 31524760
AGDA_VERSION = "2.8.0"
STDLIB_VERSION = "2.3"

OUT_DIR = Path(".playground")
EXERCISE_DIR = Path("docs/playground")
MANIFEST = "manifest.json"
CHECKER = "agda-opt.wasm.gz"
SEED = "Seed"
#: What the page's `<!-- playground: NAME -->` marker accepts: a module name.
EXERCISE_NAME = re.compile(r"[A-Z][A-Za-z0-9]*")

#: The argv every image is built and run under, without the file: the page
#: adds `--interaction-json`, the build's batch checks add the module path.
#: One argv for all of them is what lets an exercise run on a larger image.
ARGV: Tuple[str, ...] = (
    "agda",
    "--library-file=/home/.config/agda/libraries",
    "-l", "standard-library",
    "-l", "agda-algebras",
    "-i", "/work",
)
LIBRARIES = (
    "/lib/standard-library/standard-library.agda-lib",
    "/lib/agda-algebras/agda-algebras.agda-lib",
)

# The guest's environment.  `Agda_datadir=/data` reaches the builtins at
# `/data/2.8.0/lib/prim`, not `/data/lib/prim`, because this build carries the
# `use-xdg-data-home` cabal flag; the native Agda has no such flag and is
# pointed at `data/2.8.0` directly (`native_env`).
GUEST_ENV = (
    ("PWD", "/work"),
    ("HOME", "/home"),
    ("Agda_datadir", "/data"),
    ("AGDA_DIR", "/home/.config/agda"),
)


@dataclass(frozen=True)
class Image:
    """One closure's filesystem image, and the exercises that name it as
    theirs.  Its closure is the union of theirs."""

    name: str
    exercises: Tuple[str, ...]


#: The plan.  Smallest first, which is also the order of the page.  The
#: closures, measured 2026-10-04 (modules, gzipped image): terms 16 modules,
#: about 0.3 MB; interpretations 72, about 7 MB (`Overture.Signatures.Morphisms`
#: brings `Relation.Binary.PropositionalEquality`); homomorphisms 244, about
#: 39 MB (`Setoid.Algebras.Basic` imports the whole `Overture`, which brings
#: `Data.Nat.Properties` and its kind).
IMAGES: Tuple[Image, ...] = (
    Image("terms", ("Graft",)),
    Image("interpretations", ("Interpret",)),
    Image("homomorphisms", ("Compose",)),
)


@dataclass(frozen=True)
class Exercise:
    """An exercise as the page shows it, and a finished version of it."""

    name: str
    source: str
    solution: str


def fail(message: str, **context: object) -> PipelineError:
    return PipelineError(
        error_type=ErrorType.COMMAND_FAILED, message=message, context=dict(context)
    )


# ── Pure ────────────────────────────────────────────────────────────────────


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def modules_of(dot: str) -> Tuple[str, ...]:
    """The module closure `--dependency-graph` recorded: one quoted node per
    module; the edges add nothing a set does not already carry."""
    return tuple(sorted(set(re.findall(r'"([A-Za-z0-9_.]+)"', dot))))


def imports_of(source: str) -> Tuple[str, ...]:
    """Every module a file imports, wherever the `import` sits."""
    return tuple(sorted(set(re.findall(r"\bimport\s+([A-Za-z0-9_.]+)", source))))


def module_name(source: str) -> Optional[str]:
    """The name in a file's `module NAME where` line, if it has one."""
    found = re.search(r"^module\s+([A-Za-z0-9_.]+)\s.*\bwhere\b", source, re.MULTILINE)
    return found.group(1) if found else None


def holes_in(source: str) -> int:
    """An upper bound on the goals a text leaves: every `?` and every `{!`.
    Exact for the exercises, which use neither in a comment or a name."""
    return source.count("?") + source.count("{!")


def seed_of(modules: Sequence[str]) -> str:
    """The module that populates an image: one bare `import` per module, so
    that two exercises' `using` lists cannot clash in one scope."""
    return f"module {SEED} where\n" + "".join(f"import {m}\n" for m in sorted(set(modules)))


def plan_errors(images: Sequence[Image], exercises: Dict[str, Exercise]) -> List[str]:
    """What is wrong with the plan before anything is built, if anything."""
    names = [n for image in images for n in image.exercises]
    return (
        [f"{image.name}: no exercise names it" for image in images if not image.exercises]
        + [f"{n}: not a name the page's marker accepts" for n in names
           if not EXERCISE_NAME.fullmatch(n)]
        + [f"{n}: named by more than one image" for n in sorted(set(names))
           if names.count(n) > 1]
        + [f"{n}: no exercise file" for n in names if n not in exercises]
        + [f"{ex.name}: its {what} is not `module {ex.name}`"
           for ex in exercises.values()
           for what, text in (("exercise", ex.source), ("solution", ex.solution))
           if module_name(text) != ex.name]
        + [f"{ex.name}: the exercise has no goal to fill"
           for ex in exercises.values() if holes_in(ex.source) == 0]
        + [f"{ex.name}: the solution still has a goal in it"
           for ex in exercises.values() if holes_in(ex.solution) != 0]
    )


def library_version(agda_lib: str) -> Optional[str]:
    """The version an `.agda-lib`'s `name:` carries (`standard-library-2.3`)."""
    for line in agda_lib.splitlines():
        head, _, rest = line.partition(":")
        if head.strip() == "name":
            found = re.search(r"-(\d+(?:\.\d+)*)$", rest.strip())
            return found.group(1) if found else None
    return None


def repository_slug(remote: str) -> Optional[str]:
    """`owner/name` from a GitHub remote, in either of its two spellings."""
    found = re.search(r"github\.com[:/]([^/\s]+/[^/\s]+?)(?:\.git)?/?$", remote.strip())
    return found.group(1) if found else None


def include_dirs(agda_lib: str) -> Tuple[str, ...]:
    """The `include:` paths an `.agda-lib` declares, in declaration order."""
    for line in agda_lib.splitlines():
        head, _, rest = line.partition(":")
        if head.strip() == "include":
            return tuple(part for part in rest.split() if not part.startswith("--"))
    return ()


def strip_build(relative: Path) -> Path:
    """Drop a leading `_build/<version>/agda/`, leaving the source's own path.

    Agda writes an interface either beside its source or under a `_build`
    tree at the project root, and which is not a property of the build alone
    (it follows the mount; see the skill), so both are recognized here."""
    parts = relative.parts
    if len(parts) >= 3 and parts[0] == "_build" and parts[2] == "agda":
        return Path(*parts[3:])
    return relative


def module_of(relative: Path, includes: Sequence[Path]) -> Optional[str]:
    """The module a file inside a library defines, or None if it is not one.
    Literate Markdown counts: this library's sources are `.lagda.md`."""
    name = relative.name
    stem = next((name[: -len(s)] for s in (".lagda.md", ".agdai", ".agda")
                 if name.endswith(s)), None)
    if stem is None:
        return None
    inside = strip_build(relative.with_name(stem))
    for include in includes:
        n = len(include.parts)
        if len(inside.parts) > n and inside.parts[:n] == include.parts:
            return ".".join(inside.parts[n:])
    return None


def serving(closures: Dict[str, Tuple[str, ...]], needs: Tuple[str, ...]) -> Tuple[str, ...]:
    """The images, by name, whose closure contains `needs`: every one of
    them can run the exercise, since every image has the same argv."""
    return tuple(name for name, closure in closures.items() if set(needs) <= set(closure))


def gzip_bytes(data: bytes) -> bytes:
    """Deterministic gzip: no name, no timestamp, so two builds compare."""
    buf = io.BytesIO()
    with gzip.GzipFile(fileobj=buf, mode="wb", compresslevel=9, mtime=0) as fh:
        fh.write(data)
    return buf.getvalue()


def count_interfaces(tar: bytes) -> int:
    """How many compiled interfaces an image carries, counted from the bytes."""
    with tarfile.open(fileobj=io.BytesIO(tar), mode="r:") as fh:
        return sum(1 for m in fh.getmembers() if m.name.endswith(".agdai"))


def longest_path(tar: bytes) -> int:
    """The longest member path, which is what decides whether the page's tar
    reader has to read ustar's `prefix` field (it has to, past 100)."""
    with tarfile.open(fileobj=io.BytesIO(tar), mode="r:") as fh:
        return max((len(m.name.encode("utf-8")) for m in fh.getmembers()), default=0)


def tar_bytes(root: Path) -> bytes:
    """Pack a directory as ustar, sorted, with every varying field pinned.
    ustar and nothing richer, because the page's reader (`tar.js`) handles
    plain files and directories and refuses anything else.  A file is written
    as a regular file even when it is a hard link, which the images' working
    copies are (`cut_image`): a link entry would carry no bytes."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.USTAR_FORMAT) as tar:
        for path in sorted(root.rglob("*")):
            info = tar.gettarinfo(str(path), arcname=str(path.relative_to(root)))
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            info.mtime = 0
            info.mode = 0o755 if path.is_dir() else 0o644
            if not path.is_dir():
                info.type = tarfile.REGTYPE
                info.linkname = ""
                info.size = path.stat().st_size
            if path.is_dir():
                tar.addfile(info)
            else:
                with path.open("rb") as fh:
                    tar.addfile(info, fh)
    return buf.getvalue()


def checking_count(output: str) -> int:
    """How many modules a run type-checked.  Unanchored: Agda indents a
    nested `Checking` line, and `^Checking ` counts only the outermost, which
    once made a verification pass for ever while looking at nothing."""
    return len(re.findall(r"^\s*Checking ", output, re.MULTILINE))


# The interaction protocol, the part the build reads.  The page's reader is
# `docs/assets/js/playground/protocol.js`; this is the same reading, kept to
# what the build asserts and records.

def haskell_string(text: str) -> str:
    """A Haskell string literal, as agda2-mode's `agda2-string-quote` writes
    one (and as `protocol.js` does): non-ASCII as `\\xHEX\\&`."""
    def one(ch: str) -> str:
        code = ord(ch)
        if ch == '"':
            return '\\"'
        if ch == "\\":
            return "\\\\"
        if ch == "\n":
            return "\\n"
        if code < 32 or code == 127:
            return f"\\{code}\\&"
        return ch if code < 128 else f"\\x{code:x}\\&"
    return '"' + "".join(one(ch) for ch in text) + '"'


def interaction_stream(path: str, goals: int) -> str:
    """A load and one context query per goal, as one fixed stream.  The page
    paces its commands (`session.js`); the build knows the exercise loads, so
    a fixed stream asks the same questions."""
    file = haskell_string(path)
    # `Direct`, as protocol.js sends them: with `Indirect` Agda writes to a
    # temporary file, and the guest has no `/tmp`.
    lines = [f"IOTCM {file} NonInteractive Direct (Cmd_load {file} [])"] + [
        f'IOTCM {file} None Direct (Cmd_goal_type_context Simplified {i} noRange "")'
        for i in range(goals)
    ]
    return "".join(line + "\n" for line in lines)


def responses(output: str) -> List[Dict]:
    """Every JSON response in an interaction run's output, prompts removed."""
    found: List[Dict] = []
    for line in output.split("\n"):
        while line.startswith("JSON> "):
            line = line[len("JSON> "):]
        if line.strip() in ("", "JSON>"):
            continue
        try:
            parsed = json.loads(line)
        except json.JSONDecodeError:
            parsed = None
        # Every response is an object; anything else is text Agda printed,
        # kept as text as `protocol.js` keeps it.
        found.append(parsed if isinstance(parsed, dict) else {"kind": "Text", "text": line})
    return found


#: Agda's highlighting aspects, as the CSS classes its HTML backend writes and
#: this site already colors (`docs/stylesheets/custom.css`, `pre.Agda .X`).
ASPECT_CLASSES: Dict[str, str] = {
    "comment": "Comment", "keyword": "Keyword", "string": "String",
    "number": "Number", "symbol": "Symbol", "primitivetype": "PrimitiveType",
    "pragma": "Pragma", "background": "Background", "markup": "Markup",
    "bound": "Bound", "generalizable": "Generalizable",
    "inductiveconstructor": "InductiveConstructor",
    "coinductiveconstructor": "CoinductiveConstructor", "datatype": "Datatype",
    "field": "Field", "function": "Function", "module": "Module",
    "postulate": "Postulate", "primitive": "Primitive", "record": "Record",
    "argument": "Argument", "macro": "Macro", "operator": "Operator",
    "hole": "Hole",
}


def highlighting_of(found: Sequence[Dict]) -> List[List]:
    """The load's own highlighting, as `[from, to, classes]` with Agda's code
    point positions (from 1, end exclusive) and the classes the site colors."""
    return [
        [h["range"][0], h["range"][1],
         " ".join(ASPECT_CLASSES[a] for a in h["atoms"] if a in ASPECT_CLASSES)]
        for r in found if r.get("kind") == "HighlightingInfo" and r.get("direct")
        for h in r.get("info", {}).get("payload", [])
        if any(a in ASPECT_CLASSES for a in h["atoms"])
    ]


def goals_of(found: Sequence[Dict]) -> Result[List[Dict], PipelineError]:
    """Each goal of an exercise's load with its type and context, as the
    page's static goal display shows them; an error if the load failed."""
    errors = [r for r in found if r.get("kind") == "DisplayInfo"
              and r.get("info", {}).get("kind") == "Error"]
    if errors:
        return Result.err(fail("the exercise does not load",
                               agda=errors[0]["info"]["error"]["message"]))
    specific = {
        r["info"]["interactionPoint"]["id"]: r["info"]["goalInfo"]
        for r in found if r.get("kind") == "DisplayInfo"
        and r.get("info", {}).get("kind") == "GoalSpecific"
    }
    listed = [r for r in found if r.get("kind") == "InteractionPoints"]
    points = listed[-1]["interactionPoints"] if listed else []
    missing = [p["id"] for p in points if p["id"] not in specific]
    if not points or missing:
        return Result.err(fail("the exercise's goals did not all answer",
                               goals=[p["id"] for p in points], missing=missing))
    return Result.ok([
        {
            "id": p["id"],
            "range": p["range"][0] if p["range"] else None,
            "type": specific[p["id"]]["type"],
            "context": [
                {"name": e["reifiedName"], "type": e["binding"], "inScope": e["inScope"]}
                for e in reversed(specific[p["id"]].get("entries", []))
            ],
        }
        for p in points
    ])


def manifest_errors(manifest: Dict) -> List[str]:
    """What the manifest claims about images and exercises that does not
    hold together: every exercise names an image that lists it, every image
    an exercise names exists, `served_by` lists its own image first, and
    every image an exercise may run on holds its closure."""
    images = manifest.get("images", {})
    exercises = manifest.get("exercises", {})
    errors: List[str] = []
    for name, ex in exercises.items():
        own = ex.get("image")
        if own not in images:
            errors.append(f"{name}: its image {own} is not in the manifest")
            continue
        if name not in images[own].get("exercises", []):
            errors.append(f"{name}: {own} does not list it")
        served = ex.get("served_by", [])
        if not served or served[0] != own:
            errors.append(f"{name}: served_by does not start with its own image")
        errors += [f"{name}: served_by names {s}, which is not in the manifest"
                   for s in served if s not in images]
        needs = set(ex.get("closure", []))
        errors += [f"{name}: served_by names {s}, whose closure lacks "
                   f"{sorted(needs - set(images[s].get('closure', [])))[:3]}"
                   for s in served if s in images
                   and not needs <= set(images[s].get("closure", []))]
    errors += [f"{file}: lists {n}, which is not an exercise"
               for file, image in images.items() for n in image.get("exercises", [])
               if n not in exercises]
    return errors


# ── Effects ─────────────────────────────────────────────────────────────────


def verified_dist(zip_path: Path) -> Result[Path, PipelineError]:
    """The upstream zip, or an error naming the hash that did not match."""
    if not zip_path.is_file():
        return Result.err(fail(f"no such file: {zip_path}"))
    got = sha256(zip_path.read_bytes())
    if got != UPSTREAM_SHA256:
        return Result.err(fail(f"{zip_path.name} is not the pinned {UPSTREAM_ASSET}",
                               expected=UPSTREAM_SHA256, got=got))
    return Result.ok(zip_path)


def read_exercises(directory: Path, names: Sequence[str]) -> Result[Dict[str, Exercise], PipelineError]:
    """Every exercise the plan names, read from its two files."""
    missing = [str(directory / sub / f"{n}.agda") for n in names
               for sub in (".", "solutions") if not (directory / sub / f"{n}.agda").is_file()]
    if missing:
        return Result.err(fail("exercise files are missing", files=missing))
    return Result.ok({
        n: Exercise(
            name=n,
            source=(directory / f"{n}.agda").read_text(encoding="utf-8"),
            solution=(directory / "solutions" / f"{n}.agda").read_text(encoding="utf-8"),
        )
        for n in names
    })


def make_writable(root: Path) -> None:
    """Add the owner's write bit to a staged tree.  A library commonly
    arrives from a Nix store path, where everything is read-only, and then
    Agda cannot write an interface and the pruning cannot delete one."""
    for path in (root, *root.rglob("*")):
        path.chmod(path.stat().st_mode | (0o700 if path.is_dir() else 0o600))


def copy_library(source: Path, target: Path, built: Optional[Path]) -> Result[Tuple[Path, ...], PipelineError]:
    """Copy a library's `.agda-lib`, the directories it includes, and the
    interfaces `built` holds (a `_build` tree), and nothing more.

    The interfaces are a head start, not a promise: Agda checks each against
    its source and the options in force, and builds again what it rejects."""
    libs = sorted(source.glob("*.agda-lib"))
    if len(libs) != 1:
        return Result.err(fail(f"expected exactly one .agda-lib in {source}",
                               found=[p.name for p in libs]))
    target.mkdir(parents=True)
    shutil.copy2(libs[0], target / libs[0].name)
    includes = include_dirs(libs[0].read_text(encoding="utf-8"))
    if not includes:
        return Result.err(fail(f"{libs[0].name} declares no include directory"))
    for include in includes:
        shutil.copytree(source / include, target / include,
                        ignore=shutil.ignore_patterns("*.agdai", "_build"))
    if built is not None and built.is_dir():
        shutil.copytree(built, target / "_build",
                        ignore=lambda d, names: [n for n in names if (Path(d) / n).is_file()
                                                 and not n.endswith(".agdai")])
    make_writable(target)
    return Result.ok(tuple(Path(i) for i in includes))


def stage(work: Path, prim: Path, stdlib: Path, library: Path) -> Result[Dict[str, Tuple[Path, ...]], PipelineError]:
    """The tree every image is cut from, laid out as the guest sees it at `/`.
    Returns each library's include directories, which the pruning needs."""
    (work / "work").mkdir(parents=True)
    (work / "home/.config/agda").mkdir(parents=True)
    (work / "data/2.8.0").mkdir(parents=True)
    shutil.copytree(prim, work / "data/2.8.0/lib",
                    ignore=shutil.ignore_patterns("*.agdai", "_build"))
    make_writable(work / "data/2.8.0/lib")
    (work / "home/.config/agda/libraries").write_text(
        "".join(line + "\n" for line in LIBRARIES), encoding="utf-8")
    (work / "agda.argv").write_text("".join(a + "\n" for a in ARGV), encoding="utf-8")
    copies = [
        ("standard-library", stdlib, stdlib / "_build"),
        ("agda-algebras", library, library / "_build"),
    ]
    return sequence_results([
        copy_library(source, work / "lib" / name, built) for name, source, built in copies
    ]).map(lambda includes: {name: inc for (name, _, _), inc in zip(copies, includes)})


def native_libraries(work: Path, scratch: Path) -> Path:
    """A libraries file naming the staged libraries at their host paths, for
    the native Agda, which cannot see the tree at `/`.  Kept out of the tree:
    it does not ship."""
    path = scratch / "native-libraries"
    path.write_text("".join(f"{work}{line}\n" for line in LIBRARIES), encoding="utf-8")
    return path


def run_native(agda: Sequence[str], work: Path, libraries: Path, module: str,
               extra: Sequence[str] = ()) -> Result[Tuple[int, str], PipelineError]:
    """Check `work/<module>.agda` with the native Agda over the staged tree,
    under the same options the guest uses (`ARGV`), at host paths."""
    command = [
        "env", f"Agda_datadir={work}/data/2.8.0",
        *agda, "--no-default-libraries", f"--library-file={libraries}",
        "-l", "standard-library", "-l", "agda-algebras", "-i", str(work / "work"),
        *extra, str(work / "work" / f"{module}.agda"),
    ]
    return run_command(command, capture_output=True, text=True, accept=(0, 42)).map(
        lambda done: (done.returncode, (done.stdout or "") + (done.stderr or "")))


def closure_native(agda: Sequence[str], work: Path, libraries: Path, module: str,
                   source: str) -> Result[Tuple[str, ...], PipelineError]:
    """The closure of `source` (a module named `module`), from the dependency
    graph a native check of it writes.  The module itself is left out, and so
    is any file it leaves behind in `work/`."""
    (work / "work" / f"{module}.agda").write_text(source, encoding="utf-8")
    graph = work / "work" / f"{module}.dot"

    def read(done: Tuple[int, str]) -> Result[Tuple[str, ...], PipelineError]:
        status, output = done
        if status != 0 or not graph.is_file():
            return Result.err(fail(f"{module} does not check natively",
                                   returncode=status, output=output[-2000:]))
        return Result.ok(tuple(m for m in modules_of(graph.read_text(encoding="utf-8"))
                               if m != module))

    found = run_native(agda, work, libraries, module, (f"--dependency-graph={graph}",)).and_then(read)
    for leftover in (work / "work").iterdir():
        if leftover.is_dir():
            shutil.rmtree(leftover)
        else:
            leftover.unlink()
    return found


def prune_to_closure(image_dir: Path, includes: Dict[str, Tuple[Path, ...]],
                     closure: Sequence[str]) -> None:
    """Delete every library file outside the closure, then every empty
    directory.  Both halves of a closure module ship, the interface and the
    source: an interface alone is "cannot find the module" at scope checking.
    Agda's builtins are kept whole; they are small and their closure is not
    what the dependency graph says (it omits `Agda.Primitive.Cubical`)."""
    keep = set(closure)
    lib_root = image_dir / "lib"
    for path in sorted(lib_root.rglob("*"), reverse=True):
        if path.is_dir():
            if not any(path.iterdir()):
                path.rmdir()
            continue
        relative = path.relative_to(lib_root)
        if path.suffix == ".agda-lib":
            continue
        name = module_of(Path(*relative.parts[1:]), includes.get(relative.parts[0], ()))
        if name is None or name not in keep:
            path.unlink()


def cut_image(work: Path, target: Path, includes: Dict[str, Tuple[Path, ...]],
              closure: Sequence[str]) -> bytes:
    """One image: a copy of the staged tree pruned to `closure`, packed.
    The copy is of hard links, so cutting three images costs no disk."""
    shutil.copytree(work, target, copy_function=os.link)
    prune_to_closure(target, includes, closure)
    for leftover in (target / "work").iterdir():
        leftover.unlink()
    return tar_bytes(target)


def run_wasm(runtime: Sequence[str], wasm: Path, image: Path, args: Sequence[str],
             stdin: Optional[str] = None) -> Result[Tuple[int, str, float], PipelineError]:
    """Run the shipped checker over `image` mounted at the guest's root, as
    the page mounts it.  Returns the status, everything written, and seconds.
    No `--` before the guest's arguments: everything after the module path is
    already the guest's, and a `--` reaches Agda's option parser as a file."""
    command = [
        *runtime, "run", "--dir", f"{image}::/",
        *[arg for key, value in GUEST_ENV for arg in ("--env", f"{key}={value}")],
        str(wasm), *args,
    ]
    started = time.monotonic()
    return run_command(command, capture_output=True, text=True, accept=(0, 42),
                       input_text=stdin).map(
        lambda done: (done.returncode, (done.stdout or "") + (done.stderr or ""),
                      time.monotonic() - started))


def unpacked(tar: bytes, target: Path) -> Path:
    """A fresh unpacking of an image, so that no check leans on an interface
    an earlier one wrote."""
    target.mkdir(parents=True)
    with tarfile.open(fileobj=io.BytesIO(tar), mode="r:") as fh:
        fh.extractall(target, filter="data")
    return target


def batch_check(runtime: Sequence[str], wasm: Path, tar: bytes, scratch: Path,
                module: str, source: str) -> Result[Dict[str, object], PipelineError]:
    """Check `source` on a fresh unpacking of an image as the page's checker
    would, and require exit 0 and exactly one module type-checked."""
    root = unpacked(tar, scratch)
    (root / "work" / f"{module}.agda").write_text(source, encoding="utf-8")

    def judged(done: Tuple[int, str, float]) -> Result[Dict[str, object], PipelineError]:
        status, output, seconds = done
        count = checking_count(output)
        if status != 0 or count != 1:
            return Result.err(fail(
                f"{module} re-checked {count} modules with exit {status} on its image, "
                "where 1 and 0 are the pass; the image's interfaces were not all accepted",
                output=output[-2000:]))
        return Result.ok({"seconds": round(seconds, 2), "checked": count})

    return run_wasm(runtime, wasm, root, [*ARGV[1:], f"/work/{module}.agda"]).and_then(judged)


def interaction_check(runtime: Sequence[str], wasm: Path, tar: bytes, scratch: Path,
                      exercise: Exercise) -> Result[Dict[str, object], PipelineError]:
    """Load an exercise as the page shows it, ask for every goal's context,
    and keep Agda's answers: the goals, as the page's static display shows
    them, and the highlighting, which colors the page's code block."""
    root = unpacked(tar, scratch)
    path = f"/work/{exercise.name}.agda"
    (root / "work" / f"{exercise.name}.agda").write_text(exercise.source, encoding="utf-8")
    stream = interaction_stream(path, holes_in(exercise.source))

    def judged(done: Tuple[int, str, float]) -> Result[Dict[str, object], PipelineError]:
        status, output, seconds = done
        found = responses(output)
        count = sum(1 for r in found if r.get("kind") == "RunningInfo"
                    and checking_count(r.get("message", "")) > 0)
        if status != 0 or count != 1:
            return Result.err(fail(
                f"{exercise.name}: the interaction run checked {count} modules with exit "
                f"{status}, where 1 and 0 are the pass", output=output[-2000:]))
        return goals_of(found).map(lambda goals: {
            "seconds": round(seconds, 2),
            "goals": goals,
            "highlighting": highlighting_of(found),
        })

    return run_wasm(runtime, wasm, root, [*ARGV[1:], "--interaction-json"],
                    stdin=stream).and_then(judged)


def git_lines(repo: Path, *args: str) -> Result[str, PipelineError]:
    return run_command(["git", "-C", str(repo), *args], capture_output=True, text=True).map(
        lambda done: done.stdout or "")


def library_provenance(repo: Path, shipped: Sequence[str],
                       allow_dirty: bool) -> Result[Dict[str, object], PipelineError]:
    """This repository's commit, and whether every file the images and the
    page take from it is that commit's.  A record that names a commit the
    files differ from is worse than none, so a difference stops the build,
    unless `allow_dirty`, and then the record says so."""
    def record(head: str, dirty: str, remote: str) -> Result[Dict[str, object], PipelineError]:
        slug = repository_slug(remote)
        if slug is None:
            return Result.err(fail("origin does not name a GitHub repository, so the "
                                   "manifest could not say where the commit lives",
                                   origin=remote.strip()))
        if dirty.strip() and not allow_dirty:
            return Result.err(fail(
                f"the build would ship files that are not commit {head.strip()[:7]}; "
                "commit them, or pass --allow-dirty for a local build",
                files=dirty.strip()))
        return Result.ok({"repository": slug, "commit": head.strip(),
                          "dirty": bool(dirty.strip())})

    return git_lines(repo, "rev-parse", "HEAD").and_then(
        lambda head: git_lines(repo, "status", "--porcelain", "--ignored",
                               "--untracked-files=all", "--", *shipped).and_then(
            lambda dirty: git_lines(repo, "remote", "get-url", "origin").and_then(
                lambda remote: record(head, dirty, remote))))


def stdlib_provenance(tree: Path) -> Result[Dict[str, object], PipelineError]:
    """The standard library's version, which must be the pinned one, and its
    path, which for a store path names its contents."""
    libs = sorted(tree.glob("*.agda-lib"))
    if len(libs) != 1:
        return Result.err(fail(f"expected exactly one .agda-lib in {tree}"))
    version = library_version(libs[0].read_text(encoding="utf-8"))
    if version != STDLIB_VERSION:
        return Result.err(fail(f"{tree} is standard library {version}, and this "
                               f"file pins {STDLIB_VERSION}"))
    return Result.ok({"version": version, "path": str(tree.resolve())})


def shipped_from_library(tars: Sequence[bytes]) -> List[str]:
    """The files the images take from this library, as repository paths."""
    prefix = "lib/agda-algebras/"
    found = set()
    for tar in tars:
        with tarfile.open(fileobj=io.BytesIO(tar), mode="r:") as fh:
            found |= {m.name[len(prefix):] for m in fh.getmembers()
                      if m.isfile() and m.name.startswith(prefix)
                      and not m.name.endswith(".agdai") and "/_build/" not in m.name}
    return sorted(found)


@dataclass(frozen=True)
class Tools:
    """What the build runs: the native Agda, the WASI runtime, the module."""

    agda: Tuple[str, ...]
    runtime: Tuple[str, ...]
    wasm: Path


def build(args: argparse.Namespace) -> Result[Dict[str, object], PipelineError]:
    """Produce every asset and the manifest that describes them."""
    names = [n for image in IMAGES for n in image.exercises]
    exercises_read = read_exercises(Path(args.exercises), names)
    if exercises_read.is_err:
        return Result.err(exercises_read.unwrap_err())
    exercises = exercises_read.unwrap()
    problems = plan_errors(IMAGES, exercises)
    if problems:
        return Result.err(fail("the plan is not buildable", problems=problems))
    dist = verified_dist(Path(args.dist))
    if dist.is_err:
        return Result.err(dist.unwrap_err())
    stdlib_record = stdlib_provenance(Path(args.stdlib))
    if stdlib_record.is_err:
        return Result.err(stdlib_record.unwrap_err())

    with tempfile.TemporaryDirectory(prefix="playground-assets-") as tmp:
        scratch = Path(tmp)
        shutil.unpack_archive(str(dist.unwrap()), str(scratch / "dist"), "zip")
        wasm = scratch / "dist/opt/agda-opt.wasm"
        if not wasm.is_file():
            return Result.err(fail(f"the release has no opt/agda-opt.wasm ({wasm})"))
        wasm_raw = wasm.read_bytes()
        if sha256(wasm_raw) != UPSTREAM_MODULE_SHA256:
            return Result.err(fail("opt/agda-opt.wasm is not the pinned module",
                                   expected=UPSTREAM_MODULE_SHA256, got=sha256(wasm_raw)))
        tools = Tools(tuple(shlex.split(args.agda)), tuple(shlex.split(args.wasmtime)), wasm)
        return assemble(args, scratch, tools, exercises, stdlib_record.unwrap(),
                        gzip_bytes(wasm_raw), len(wasm_raw), sha256(wasm_raw))


def assemble(args: argparse.Namespace, scratch: Path, tools: Tools,
             exercises: Dict[str, Exercise], stdlib_record: Dict[str, object],
             checker_gz: bytes, wasm_bytes: int, wasm_sha: str) -> Result[Dict[str, object], PipelineError]:
    """Stage, populate, cut, prove and describe every image."""
    work = scratch / "stage"
    staged = stage(work, scratch / "dist/opt/lib", Path(args.stdlib), Path(args.library))
    if staged.is_err:
        return Result.err(staged.unwrap_err())
    includes = staged.unwrap()
    libraries = native_libraries(work, scratch)

    # The closure of each exercise, from its solution.  The first native run
    # populates everything the solutions need; the rest find it built.
    closures_by_exercise = sequence_results([
        closure_native(tools.agda, work, libraries, ex.name, ex.solution)
        for ex in exercises.values()
    ])
    if closures_by_exercise.is_err:
        return Result.err(closures_by_exercise.unwrap_err())
    needs = dict(zip(exercises, closures_by_exercise.unwrap()))
    # An image's closure is its seed's, which is the union of its exercises'.
    seeds = {image.name: seed_of([m for n in image.exercises for m in imports_of(exercises[n].solution)])
             for image in IMAGES}
    image_closures = sequence_results([
        closure_native(tools.agda, work, libraries, SEED, seeds[image.name]) for image in IMAGES
    ])
    if image_closures.is_err:
        return Result.err(image_closures.unwrap_err())
    closures = {image.name: closure for image, closure in zip(IMAGES, image_closures.unwrap())}
    uncovered = [n for image in IMAGES for n in image.exercises
                 if not set(needs[n]) <= set(closures[image.name])]
    if uncovered:
        return Result.err(fail("an exercise's closure is not inside its own image's",
                               exercises=uncovered))

    tars = {image.name: cut_image(work, scratch / "images" / image.name, includes,
                                  closures[image.name]) for image in IMAGES}
    served = {n: serving(closures, needs[n]) for n in exercises}
    # Own image first, then the others in plan order.
    owner = {n: image.name for image in IMAGES for n in image.exercises}
    served = {n: (owner[n], *[s for s in served[n] if s != owner[n]]) for n in exercises}

    proofs = prove(tools, tars, seeds, exercises, served, owner, scratch / "verify")
    if proofs.is_err:
        return Result.err(proofs.unwrap_err())
    proved = proofs.unwrap()

    shipped = shipped_from_library(list(tars.values())) + [
        str(Path(args.exercises) / sub / f"{n}.agda") for n in exercises for sub in (".", "solutions")
    ]
    library_record = library_provenance(Path(args.library), shipped, args.allow_dirty)
    if library_record.is_err:
        return Result.err(library_record.unwrap_err())

    payloads = {CHECKER: checker_gz, **{f"{name}.tar.gz": gzip_bytes(tar) for name, tar in tars.items()}}
    manifest = describe(tars, closures, needs, served, owner, exercises, proved,
                        {"standard-library": stdlib_record, "agda-algebras": library_record.unwrap()},
                        payloads, wasm_bytes, wasm_sha)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    for stale in out.glob("*.tar.gz"):
        if stale.name not in payloads:
            stale.unlink()
    for name, blob in payloads.items():
        (out / name).write_bytes(blob)
    (out / MANIFEST).write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
                                encoding="utf-8")
    return Result.ok(manifest)


def prove(tools: Tools, tars: Dict[str, bytes], seeds: Dict[str, str],
          exercises: Dict[str, Exercise], served: Dict[str, Tuple[str, ...]],
          owner: Dict[str, str], scratch: Path) -> Result[Dict[str, Dict[str, object]], PipelineError]:
    """Every check the page relies on, on fresh unpackings of the packed
    images, under the shipped wasm: each image's seed; each exercise's
    solution on every image that claims to serve it; and each exercise as the
    page shows it, by the interaction protocol, on its own image."""
    counter = iter(range(10_000))
    fresh = lambda: scratch / str(next(counter))  # noqa: E731
    seed_runs = sequence_results([
        batch_check(tools.runtime, tools.wasm, tars[name], fresh(), SEED, seeds[name])
        for name in tars
    ])
    if seed_runs.is_err:
        return Result.err(seed_runs.unwrap_err())
    solution_runs = sequence_results([
        batch_check(tools.runtime, tools.wasm, tars[image], fresh(), n, exercises[n].solution)
        .map(lambda r, image=image: {**r, "image": image})
        for n in exercises for image in served[n]
    ])
    if solution_runs.is_err:
        return Result.err(solution_runs.unwrap_err())
    shown = sequence_results([
        interaction_check(tools.runtime, tools.wasm, tars[owner[n]], fresh(), exercises[n])
        for n in exercises
    ])
    if shown.is_err:
        return Result.err(shown.unwrap_err())
    by_name = dict(zip(exercises, shown.unwrap()))
    seconds = {(r["image"], n): r["seconds"] for n, r in zip(
        [n for n in exercises for _ in served[n]], solution_runs.unwrap())}
    return Result.ok({
        n: {**by_name[n], "solution_seconds": {image: seconds[(image, n)] for image in served[n]}}
        for n in exercises
    } | {f"seed:{name}": r for name, r in zip(tars, seed_runs.unwrap())})


def describe(tars: Dict[str, bytes], closures: Dict[str, Tuple[str, ...]],
             needs: Dict[str, Tuple[str, ...]], served: Dict[str, Tuple[str, ...]],
             owner: Dict[str, str], exercises: Dict[str, Exercise],
             proved: Dict[str, Dict[str, object]], built_from: Dict[str, Dict[str, object]],
             payloads: Dict[str, bytes], wasm_bytes: int, wasm_sha: str) -> Dict[str, object]:
    """The manifest: everything the page, the hook and `--check` read."""
    return {
        "agda": AGDA_VERSION,
        "standard_library": STDLIB_VERSION,
        "upstream": {"repository": UPSTREAM_REPO, "release": UPSTREAM_RELEASE,
                     "asset": UPSTREAM_ASSET, "sha256": UPSTREAM_SHA256},
        "checker": {"file": CHECKER, "wasm_bytes": wasm_bytes, "wasm_sha256": wasm_sha,
                    "gzip_bytes": len(payloads[CHECKER])},
        "built_from": built_from,
        "argv": list(ARGV),
        "images": {
            f"{name}.tar.gz": {
                "exercises": [n for n in exercises if owner[n] == name],
                # `interfaces` is what ships, one per module a reader does not
                # check; `closure` is the dependency graph, which omits the
                # builtins that arrive without an import.
                "interfaces": count_interfaces(tar),
                "closure": list(closures[name]),
                "longest_path": longest_path(tar),
                "tar_bytes": len(tar),
                "tar_sha256": sha256(tar),
                "gzip_bytes": len(payloads[f"{name}.tar.gz"]),
                "seed_seconds": proved[f"seed:{name}"]["seconds"],
            }
            for name, tar in tars.items()
        },
        "exercises": {
            n: {
                "file": f"{n}.agda",
                "image": f"{owner[n]}.tar.gz",
                "served_by": [f"{s}.tar.gz" for s in served[n]],
                "closure": list(needs[n]),
                "source_sha256": sha256(exercises[n].source.encode("utf-8")),
                "goals": proved[n]["goals"],
                "highlighting": proved[n]["highlighting"],
                # wasmtime's, on the build machine, as a rough guide only: a
                # browser differs, and ADR-011 has the browser's figures.
                "seconds": proved[n]["seconds"],
                "solution_seconds": {f"{k}.tar.gz": v for k, v in proved[n]["solution_seconds"].items()},
            }
            for n in exercises
        },
    }


# ── The gate ────────────────────────────────────────────────────────────────


def read_argv(path: Path) -> Result[Tuple[str, ...], PipelineError]:
    """The argv an image carries, read back out of the packed tar, or why it
    could not be: a missing or damaged file is a refusal, not a traceback."""
    try:
        with tarfile.open(path, mode="r:gz") as fh:
            member = next((m for m in fh.getmembers() if m.name == "agda.argv"), None)
            handle = fh.extractfile(member) if member is not None else None
            text = handle.read().decode("utf-8") if handle is not None else None
    except (OSError, tarfile.TarError, EOFError) as err:
        return Result.err(fail(f"{path.name}: not a readable image ({err})"))
    if text is None:
        return Result.err(fail(f"{path.name}: the image carries no agda.argv"))
    return Result.ok(tuple(line for line in text.split("\n") if line != ""))


def verified_asset(out: Path, name: str, expect_sha: str, expect_bytes: int,
                   expect_wire: int) -> Result[str, PipelineError]:
    """One built asset, inflated and hashed, and its wire size compared: the
    wire size is the number the page quotes before anything is fetched."""
    path = out / name
    if not path.is_file():
        return Result.err(fail(f"missing asset: {path}"))
    if path.stat().st_size != expect_wire:
        return Result.err(fail(f"{name} is {path.stat().st_size} bytes on the wire, and the "
                               f"manifest, which the page quotes, says {expect_wire}"))
    try:
        raw = gzip.decompress(path.read_bytes())
    except (OSError, EOFError) as err:
        return Result.err(fail(f"{name} does not inflate ({err}); run `make playground`"))
    if len(raw) != expect_bytes or sha256(raw) != expect_sha:
        return Result.err(fail(f"{name} is not what the manifest describes",
                               expected_sha256=expect_sha, got_sha256=sha256(raw)))
    return Result.ok(f"{name}: {path.stat().st_size} bytes on the wire, {len(raw)} inflated")


def check(out: Path, exercises_dir: Path) -> Result[List[str], PipelineError]:
    """Prove the built assets are what the manifest says, with no runtime:
    the checker is the pinned module, every quoted size is the size on disk,
    every image is the tar described and carries the argv, the exercise files
    are the ones the build checked, and the manifest holds together.  Whether
    the interfaces are *accepted* needs a WASI runtime; the build measured
    that, and refuses to finish otherwise."""
    manifest_path = out / MANIFEST
    if not manifest_path.is_file():
        return Result.err(fail(f"no manifest: {manifest_path}; run `make playground`"))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    checker = manifest["checker"]
    claims: List[Result[str, PipelineError]] = [
        verified_asset(out, checker["file"], UPSTREAM_MODULE_SHA256, UPSTREAM_MODULE_BYTES,
                       checker["gzip_bytes"])
    ]
    for name, image in manifest["images"].items():
        asset = verified_asset(out, name, image["tar_sha256"], image["tar_bytes"],
                               image["gzip_bytes"])
        claims.append(asset)
        if asset.is_err:
            continue
        argv = read_argv(out / name)
        claims.append(argv.and_then(lambda a, name=name: Result.ok(f"{name}: argv as built")
                                    if list(a) == manifest["argv"] else
                                    Result.err(fail(f"{name}: agda.argv disagrees with the manifest"))))
    for name, ex in manifest["exercises"].items():
        path = exercises_dir / ex["file"]
        same = path.is_file() and sha256(path.read_bytes()) == ex["source_sha256"]
        claims.append(Result.ok(f"{name}: the exercise file is the one checked") if same else
                      Result.err(fail(f"{path} is not the exercise the build checked; "
                                      "run `make playground`")))
    claims += [Result.err(fail(problem)) for problem in manifest_errors(manifest)]
    claims += [Result.err(fail(f"{stray.name} is in {out} and not in the manifest"))
               for stray in sorted(out.glob("*.tar.gz")) if stray.name not in manifest["images"]]
    return sequence_results(claims)


def report(error: PipelineError) -> None:
    print(f"playground assets: {error.message}", file=sys.stderr)
    for key, value in error.context.items():
        print(f"  {key}: {value}", file=sys.stderr)


def summary(manifest: Dict) -> List[str]:
    """What a build made, a line per asset and per exercise."""
    checker = manifest["checker"]
    return (
        [f"{checker['file']} {checker['gzip_bytes']} bytes"]
        + [f"{name} {image['gzip_bytes']} bytes, {image['interfaces']} interfaces, "
           f"seed checked in {image['seed_seconds']} s"
           for name, image in manifest["images"].items()]
        + [f"{name}: {len(ex['goals'])} goal(s), loaded in {ex['seconds']} s on "
           f"{ex['image']}; runs on {', '.join(ex['served_by'])}"
           for name, ex in manifest["exercises"].items()]
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build the assets the playground downloads, or check them.")
    parser.add_argument("--out", default=str(OUT_DIR), help="where the assets go")
    parser.add_argument("--check", action="store_true",
                        help="verify built assets against their manifest")
    parser.add_argument("--dist", help=f"the pinned {UPSTREAM_ASSET}")
    parser.add_argument("--stdlib", help="the standard library tree (with src/ and _build/)")
    parser.add_argument("--library", default=".", help="this repository's checkout")
    parser.add_argument("--exercises", default=str(EXERCISE_DIR),
                        help="the exercise files (and solutions/)")
    parser.add_argument("--agda", default="agda", help="the native Agda, with arguments")
    parser.add_argument("--wasmtime", default="wasmtime",
                        help="a WASI runtime, optionally with arguments")
    parser.add_argument("--allow-dirty", action="store_true",
                        help="ship files that differ from HEAD, and record that")
    args = parser.parse_args(argv)

    if args.check:
        outcome = check(Path(args.out), Path(args.exercises))
        if outcome.is_err:
            report(outcome.unwrap_err())
            return 1
        for line in outcome.unwrap():
            print(f"playground assets: {line}")
        return 0

    missing = [f"--{n}" for n in ("dist", "stdlib") if not getattr(args, n)]
    if missing:
        print(f"playground assets: {' and '.join(missing)} are required to build",
              file=sys.stderr)
        return 2
    built = build(args)
    if built.is_err:
        report(built.unwrap_err())
        return 1
    for line in summary(built.unwrap()):
        print(f"playground assets: {line}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
