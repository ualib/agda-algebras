#!/usr/bin/env python3
"""
File: scripts/python/theme/build_fonts.py

Description: Build the site's self-hosted webfonts: subset the pinned sources,
  emit WOFF2 and ``docs/assets/fonts/fonts.css`` (issues #531 and #621).

  Every face the site uses is served from its own origin.  Until #621 the code
  face, JuliaMono, came by ``@import`` from jsDelivr, so a reader behind a
  proxy, or the day that CDN changes its paths, got every universe level and
  bold-script letter in a substitute face, mid-line, with nothing failing
  loudly.  ``theme.font: false`` in ``mkdocs.yml`` stops Material's own Google
  Fonts link; this script makes the faces that replace it.

  Run it with ``make fonts``; ``make fonts-check`` reports, writing nothing,
  whether the committed files still match what the pins produce.  The outputs
  are committed, so an ordinary build, and CI, never runs this and never needs
  the network.

Design Principles:
  +  **The interesting part of the output is which characters are in it.**  A
     page of Agda that hits one code point outside the subset falls back to
     whatever the operating system offers, mid-line.  So the subset is derived
     from a stated repertoire, by Unicode *block* rather than by a list of
     characters (see the comment above ``SYMBOL_BLOCKS``), and derived again
     whenever that repertoire changes.
  +  **Sources are pinned by SHA-256, not by a git ref.**  Upstream moving a
     branch is exactly the failure this should catch, and a hash catches it
     whatever the URL says.
  +  **The output is deterministic.**  fontTools stamps ``head.modified`` with
     the current time unless told not to; with that off, two runs produce the
     same bytes, which is what makes ``--check`` meaningful.
  +  Effects at the edges: ``fetch`` and ``main`` touch the network and the
     disk; the repertoire and range arithmetic in between is pure.

Provenance:
  Ported from the build script of williamdemeo.org's design system
  ("Constellation"), with the same pins and instance locations.  Its block
  lists gained the blocks this library's pages use, each found by `make
  font-audit` (Latin Extended Additional and Combining Diacritical Marks in
  the text faces; Miscellaneous Symbols, Miscellaneous Symbols and Arrows,
  Latin Extended Additional and Specials in JuliaMono), so the faces are a
  superset of that site's.  The combining marks moved into JuliaMono's text
  file, beside the letters they sit on (see MONO_TEXT_BLOCKS).
  Dropped in the port: the Newsreader face (the alternative system's display
  face, which this site does not have) and the static TTFs for social cards
  (this site generates none).  Its exits on a hash mismatch became Results.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import sys
import unicodedata
import urllib.request
from dataclasses import dataclass, field
from functools import reduce
from pathlib import Path
from typing import Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from _utils import ErrorType, PipelineError, Result, sequence_results  # noqa: E402

try:
    from fontTools.subset import Options, Subsetter
    from fontTools.ttLib import TTFont
    from fontTools.unicodedata import block
    from fontTools.varLib.instancer import instantiateVariableFont
except ImportError:  # pragma: no cover - the message is the whole point
    sys.exit("error: fonttools and brotli are required.\n"
             "       Run inside `nix develop`, or pip install 'fonttools[woff]' brotli.")

ROOT: Path = Path(__file__).resolve().parents[3]
OUT: Path = ROOT / "docs" / "assets" / "fonts"
CACHE: Path = ROOT / ".fonts-cache"

GF: str = "https://raw.githubusercontent.com/google/fonts/main/ofl"
JM: str = "https://raw.githubusercontent.com/cormullion/juliamono/master"

# -- Character repertoires ---------------------------------------------------
#
# For the monospace face the unit is the Unicode *block*, not a list of
# characters, and the first version of the upstream script got that wrong in a
# way worth recording (it is #531's warning).  Enumerating
# `agda-input-translations` from agda-input.el looks like the authoritative
# answer, 1,952 characters straight from the input method, and it is not:
# agda-input *inherits* from Emacs' TeX input method for everything it does not
# redefine.  ℓ, Π and the subscript digits come from there, so all four were
# missing from a subset built that way and fell back to DejaVu Sans Mono on a
# real page.  Only a browser caught it (`make font-audit` here).
#
# Shipping whole blocks costs roughly twice the bytes and removes that class of
# mistake: any character in a listed block renders, whether or not anyone
# anticipated it.  Excluded on purpose, because they are other writing systems
# rather than mathematical notation: CJK, Cyrillic, Braille, Canadian
# Syllabics, Arabic, Hebrew, the private-use areas and the legacy-computing
# symbols, together about 60% of JuliaMono's 11,191 glyphs.

ASCII: frozenset[str] = frozenset(chr(c) for c in range(0x20, 0x7F))
# U+00AD soft hyphen is invisible and trips fontTools' variable-font instancer
# on some sources; nothing renders it, so it is not worth carrying.
LATIN1: frozenset[str] = frozenset(chr(c) for c in range(0xA0, 0x100)) - {chr(0x00AD)}
# Characters from blocks too large to ship whole, but common enough in running
# prose that a substitution would show.  Deliberately not ∀ ∃ ∈ ⊆ ≅ ≡ ↦: no
# text face carries them, and anything mathematical that reaches prose lands on
# JuliaMono, the last self-hosted entry in the text stack for that reason.
PROSE: frozenset[str] = frozenset("‘’“”–—…†‡•·′″⁄←→↔⇒≈≠≤≥×÷−±°©®™№§¶")
# Blocks every text face carries in full.  Latin Extended-A is not decoration:
# names such as Jónsson and Ježek appear in this library's prose, and one
# missing letter renders in another face mid-word.  Greek is the same argument
# one step out: prose about λ-terms should not change font mid-word.  Latin
# Extended Additional is this site's addition to the upstream list: the library
# names a module construction Ḡ (U+1E20), and its page title, in Inter, fell to
# a system face mid-word until `make font-audit` found it (#621).  So are the
# Combining Diacritical Marks: prose writes Agda's `_̇_` as `𝑝 ̇ 𝑨`, a dot
# above a space, and the reader got it in Arimo.
TEXT_BLOCKS: tuple[str, ...] = ("Latin Extended-A", "Latin Extended Additional",
                                "Combining Diacritical Marks",
                                "Greek and Coptic", "General Punctuation")

# Blocks Agda notation draws on.  Split in two only to keep the download
# granular: the mathematical alphanumerics are 997 of JuliaMono's glyphs and
# about 154 KB on their own, and a page that mentions `→` without ever showing
# an 𝑨 should not pay for them.
SYMBOL_BLOCKS: tuple[str, ...] = (
    "Greek and Coptic",
    "Greek Extended",
    "Superscripts and Subscripts",
    "Letterlike Symbols",
    "Arrows",
    "Mathematical Operators",
    "Miscellaneous Technical",
    "Miscellaneous Mathematical Symbols-A",
    "Miscellaneous Mathematical Symbols-B",
    "Supplemental Arrows-A",
    "Supplemental Arrows-B",
    "Supplemental Mathematical Operators",
    "General Punctuation",
    "Supplemental Punctuation",
    "Combining Diacritical Marks",
    "Combining Diacritical Marks for Symbols",
    "Phonetic Extensions",             # ᵢ ᵣ ᵤ and the rest of the subscript letters
    "Phonetic Extensions Supplement",
    "Spacing Modifier Letters",
    "IPA Extensions",
    "Latin Extended-A",
    "Latin Extended-B",                # ƛ, which the standard library uses
    "Number Forms",
    "Geometric Shapes",
    "Box Drawing",
    "Dingbats",                        # ✓, the coverage table's mark
    # This site's additions to the upstream list, each found by `make
    # font-audit` on a real page (#621): ⚠ in the site guide's build log, ⬻
    # in the standard library's reasoning syntax on /classic/, Ḡ in a module
    # name, and U+FFFD in Agda.Builtin.Char.
    "Miscellaneous Symbols",
    "Miscellaneous Symbols and Arrows",
    "Latin Extended Additional",
    "Specials",
)
MATHALPHA_BLOCKS: tuple[str, ...] = ("Mathematical Alphanumeric Symbols",)

AGDA_INPUT_URL: str = "https://raw.githubusercontent.com/agda/agda/master/src/data/emacs-mode/agda-input.el"
AGDA_INPUT_SHA: str = "7b2b8e6c17d336c6761b58536f0837e7ae051f1b31c45d0065c5ba38bfbc00a3"


@dataclass(frozen=True)
class Face:
    """One shipped WOFF2 file."""
    out: str                                    # basename under docs/assets/fonts/
    family: str                                 # CSS font-family
    url: str
    sha256: str
    weight: int = 400
    style: str = "normal"
    axes: Mapping[str, int] = field(default_factory=dict)   # variable-font instance
    charset: str = "text"                       # text | symbols | mathalpha


JULIAMONO_SHA: str = "40a07da0d1601215eb6b89312eb44128a3e2f36675d3e1f518264bd391fc7023"
INTER_SHA: str = "29160a80ff49ddcab2c97711247e08b1fab27a484a329ce8b813d820dc559031"
INTER_ITALIC_SHA: str = "acd98e64795781b2058f07b18475e0ecee2a0fe2b42a49e2f9e37d0d6bf66ce6"
SPACE_GROTESK_SHA: str = "acad6de1fc93436f5c0f1f4137751ef04f1aea3063e7036535970ffcfbd79f72"

FACES: tuple[Face, ...] = (
    # Monospace: three files, one family name, disjoint unicode-ranges.  A run
    # of code that mixes ASCII and 𝑨 is still one face to the layout engine,
    # but a page that never shows an 𝑨 never downloads the file it lives in.
    Face("juliamono-text.woff2", "JuliaMono", f"{JM}/JuliaMono-Regular.ttf", JULIAMONO_SHA,
         charset="text"),
    Face("juliamono-symbols.woff2", "JuliaMono", f"{JM}/JuliaMono-Regular.ttf", JULIAMONO_SHA,
         charset="symbols"),
    Face("juliamono-mathalpha.woff2", "JuliaMono", f"{JM}/JuliaMono-Regular.ttf", JULIAMONO_SHA,
         charset="mathalpha"),
    # Body and interface.
    Face("inter-400.woff2", "Inter", f"{GF}/inter/Inter%5Bopsz%2Cwght%5D.ttf", INTER_SHA,
         weight=400, axes={"wght": 400, "opsz": 16}),
    Face("inter-600.woff2", "Inter", f"{GF}/inter/Inter%5Bopsz%2Cwght%5D.ttf", INTER_SHA,
         weight=600, axes={"wght": 600, "opsz": 20}),
    Face("inter-400-italic.woff2", "Inter", f"{GF}/inter/Inter-Italic%5Bopsz%2Cwght%5D.ttf",
         INTER_ITALIC_SHA, weight=400, style="italic", axes={"wght": 400, "opsz": 16}),
    # Display: headings, the hero, the figures.
    Face("spacegrotesk-600.woff2", "Space Grotesk", f"{GF}/spacegrotesk/SpaceGrotesk%5Bwght%5D.ttf",
         SPACE_GROTESK_SHA, weight=600, axes={"wght": 600}),
)

LICENSES: tuple[tuple[str, str], ...] = (
    ("OFL-JuliaMono.txt", f"{JM}/LICENSE"),
    ("OFL-Inter.txt", f"{GF}/inter/OFL.txt"),
    ("OFL-SpaceGrotesk.txt", f"{GF}/spacegrotesk/OFL.txt"),
)


# -- Effects: the network, behind a content-addressed cache --------------------

def fetch(url: str, sha256: str | None = None) -> Result[bytes, PipelineError]:
    """Download with a content-addressed cache; verify the hash when given."""
    key = hashlib.sha256(url.encode()).hexdigest()[:16] + "-" + url.rsplit("/", 1)[-1][:60]
    cached = CACHE / key
    try:
        CACHE.mkdir(exist_ok=True)
        if cached.exists():
            data = cached.read_bytes()
        else:
            with urllib.request.urlopen(url, timeout=120) as r:
                data = r.read()
            cached.write_bytes(data)
    except OSError as e:
        return Result.err(PipelineError(ErrorType.COMMAND_FAILED, f"cannot fetch {url}", cause=e))
    got = hashlib.sha256(data).hexdigest()
    if sha256 and got != sha256:
        cached.unlink(missing_ok=True)
        return Result.err(PipelineError(
            ErrorType.VALIDATION_ERROR,
            f"{url}\n       expected sha256 {sha256}\n       got             {got}\n"
            "       Upstream moved.  Review the change, then update the pin."))
    return Result.ok(data)


# -- Pure: repertoires and ranges ----------------------------------------------

def block_chars(cmap: frozenset[int], names: tuple[str, ...]) -> frozenset[str]:
    """Every code point the face has in the named Unicode blocks."""
    return frozenset(chr(cp) for cp in cmap if block(chr(cp)) in names)


def text_charset(cmap: frozenset[int], blocks: tuple[str, ...] = TEXT_BLOCKS) -> frozenset[str]:
    """The prose repertoire: a fixed core, plus whole blocks where present.

    The core is requested from every face whether or not the face has it, so
    that a gap is reported rather than quietly dropped.
    """
    return ASCII | LATIN1 | PROSE | block_chars(cmap, blocks)


# JuliaMono's text file is the one every page with code downloads, so Latin
# Extended Additional, which one module name uses, rides in the symbols file
# instead (it is in SYMBOL_BLOCKS).  The combining marks must not: a browser
# picks one face per grapheme cluster, and a face split by unicode-range is
# several faces, so `g` followed by U+0302 needs the letter and the mark in
# the same file, or the cluster falls to a system face (`make font-audit`
# found ̂, ̇ and ̄ in DejaVu Sans Mono in three modules' code).
MONO_TEXT_BLOCKS: tuple[str, ...] = tuple(b for b in TEXT_BLOCKS if b != "Latin Extended Additional")


def agda_repertoire(source: str) -> frozenset[str]:
    """The characters agda-input.el names directly.

    A lower bound on what a page of Agda contains, not the whole of it: the
    input method inherits the rest from Emacs' TeX method.  It still catches
    characters that fall outside every listed block.
    """
    a = source.index("(defcustom agda-input-translations")
    b = source.index("(defcustom agda-input-user-translations")
    return frozenset(c for c in source[a:b]
                     if ord(c) >= 0x80 and unicodedata.category(c) not in ("Cc", "Cf"))


def runs(cps: list[int]) -> list[tuple[int, int]]:
    """Maximal runs of consecutive integers in a sorted list."""
    def step(acc: list[tuple[int, int]], c: int) -> list[tuple[int, int]]:
        return acc[:-1] + [(acc[-1][0], c)] if acc and acc[-1][1] + 1 == c else acc + [(c, c)]
    return reduce(step, cps, [])


def unicode_ranges(codepoints: frozenset[int]) -> str:
    """Collapse a code point set into a CSS `unicode-range` value."""
    return ",".join(f"U+{lo:X}" if lo == hi else f"U+{lo:X}-{hi:X}"
                    for lo, hi in runs(sorted(codepoints)))


def cmap_of(data: bytes) -> frozenset[int]:
    """The code points a font file maps."""
    return frozenset(TTFont(io.BytesIO(data), lazy=True).getBestCmap())


@dataclass(frozen=True)
class Subset:
    """One face, subset: its bytes and what it covers."""
    face: Face
    blob: bytes
    glyphs: int
    covered: frozenset[int]
    missing: frozenset[int]


def subset(face: Face, data: bytes, chars: frozenset[str]) -> Subset:
    """Instance a variable font if asked, subset it to `chars`, emit WOFF2."""
    font = TTFont(io.BytesIO(data), fontNumber=0)
    if face.axes and "fvar" in font:
        have = {a.axisTag for a in font["fvar"].axes}
        font = instantiateVariableFont(font, {k: v for k, v in face.axes.items() if k in have},
                                       updateFontNames=False)
    cmap = frozenset(font.getBestCmap())
    wanted = frozenset(ord(c) for c in chars) & cmap

    opt = Options()
    opt.layout_features = ["*"]          # keep kerning and the code ligature set
    opt.drop_tables += ["DSIG"]
    opt.name_IDs = ["*"]                 # keep the family and licence names
    opt.name_legacy = False
    opt.notdef_outline = False
    s = Subsetter(options=opt)
    s.populate(unicodes=sorted(wanted))
    s.subset(font)
    # Otherwise fontTools stamps head.modified with the current time and every
    # run produces different bytes, which makes `--check` useless.
    font.recalcTimestamp = False
    font.flavor = "woff2"
    buf = io.BytesIO()
    font.save(buf)
    n = len(font.getGlyphOrder())
    font.close()
    return Subset(face, buf.getvalue(), n, wanted, frozenset(ord(c) for c in chars) - wanted)


CSS_HEADER: str = """\
/* Generated by scripts/python/theme/build_fonts.py (make fonts); do not edit.
 *
 * Every face is served from this origin.  `theme.font: false` in mkdocs.yml is
 * what stops Material emitting its own <link> to fonts.googleapis.com; without
 * it these declarations would be additions rather than replacements.
 *
 * JuliaMono is split three ways by unicode-range under one family name, so a
 * page pays only for the notation it shows.  A page with nothing but ASCII in
 * its code blocks downloads %(text)d KB and stops; `→` and `≡` pull the
 * %(symbols)d KB symbol file; an 𝑨 or a 𝓤 pulls the %(mathalpha)d KB of
 * mathematical alphanumerics on top.
 *
 * `font-display: swap` everywhere: a flash of fallback text beats invisible
 * text, and on the code faces it is also the signal that something is wrong,
 * since unstyled Agda is obvious.
 */
"""


def face_rule(s: Subset) -> str:
    """The @font-face rule for one subset."""
    return (f"@font-face {{\n"
            f"  font-family: '{s.face.family}';\n"
            f"  font-style: {s.face.style};\n"
            f"  font-weight: {s.face.weight};\n"
            f"  font-display: swap;\n"
            f"  src: url('{s.face.out}') format('woff2');\n"
            f"  unicode-range: {unicode_ranges(s.covered)};\n"
            f"}}\n")


def stylesheet(subsets: list[Subset]) -> str:
    """fonts.css: the header with the measured sizes, then one rule per face."""
    kb = {s.face.out: len(s.blob) // 1024 for s in subsets}
    return CSS_HEADER % {
        "text": kb["juliamono-text.woff2"],
        "symbols": kb["juliamono-symbols.woff2"],
        "mathalpha": kb["juliamono-mathalpha.woff2"],
    } + "\n" + "\n".join(face_rule(s) for s in subsets)


def report(subsets: list[Subset]) -> str:
    """The table `make fonts` prints: glyphs, characters, bytes and gaps."""
    rows = [f"{s.face.out:<32} {s.glyphs:>7} {len(s.covered):>7} {len(s.blob) / 1024:>8.1f}  "
            + ("-" if not s.missing else f"{len(s.missing)} not in the source face")
            for s in subsets]
    total = sum(len(s.blob) for s in subsets) / 1024
    gaps = [f"  {s.face.out}: " + ", ".join(
                f"{chr(c)} U+{c:04X} {unicodedata.name(chr(c), '?')}" for c in sorted(s.missing)[:8])
            + (" ..." if len(s.missing) > 8 else "")
            for s in subsets if s.missing]
    return "\n".join([f"{'file':<32} {'glyphs':>7} {'chars':>7} {'KB':>8}  gaps", "-" * 72, *rows,
                      "-" * 72, f"{'total':<32} {'':>7} {'':>7} {total:>8.1f}",
                      "", "gaps in detail:", *(gaps or ["  none"])])


# -- The shell -------------------------------------------------------------------

def build() -> Result[list[Subset], PipelineError]:
    """Fetch every source and subset every face."""
    def with_mono(mono: bytes, agda_src: bytes) -> Result[list[Subset], PipelineError]:
        cmap = cmap_of(mono)
        text = text_charset(cmap, MONO_TEXT_BLOCKS)
        mathalpha = block_chars(cmap, MATHALPHA_BLOCKS) - text
        agda = frozenset(c for c in agda_repertoire(agda_src.decode("utf-8")) if ord(c) in cmap)
        symbols = (block_chars(cmap, SYMBOL_BLOCKS) | agda) - text - mathalpha
        charsets = {"symbols": symbols, "mathalpha": mathalpha}

        def one(face: Face) -> Result[Subset, PipelineError]:
            def chars(data: bytes) -> frozenset[str]:
                if face.charset != "text":
                    return charsets[face.charset]
                return text if face.family == "JuliaMono" else text_charset(cmap_of(data))
            return fetch(face.url, face.sha256).map(lambda data: subset(face, data, chars(data)))
        return sequence_results([one(f) for f in FACES])

    return fetch(FACES[0].url, FACES[0].sha256).and_then(
        lambda mono: fetch(AGDA_INPUT_URL, AGDA_INPUT_SHA).and_then(
            lambda agda_src: with_mono(mono, agda_src)))


def stale(subsets: list[Subset], css: str) -> list[str]:
    """The committed files that differ from what the pins produce."""
    def differs(path: Path, content: bytes) -> bool:
        return not path.exists() or path.read_bytes() != content
    return ([s.face.out for s in subsets if differs(OUT / s.face.out, s.blob)]
            + (["fonts.css"] if differs(OUT / "fonts.css", css.encode()) else []))


def write(subsets: list[Subset], css: str) -> Result[list[str], PipelineError]:
    """Write the faces, the stylesheet and the licences."""
    def licence(name: str, url: str) -> Result[str, PipelineError]:
        def save(data: bytes) -> str:
            (OUT / name).write_bytes(data)
            return name
        return fetch(url).map(save)
    OUT.mkdir(parents=True, exist_ok=True)
    for s in subsets:
        (OUT / s.face.out).write_bytes(s.blob)
    (OUT / "fonts.css").write_text(css, encoding="utf-8")
    return sequence_results([licence(n, u) for n, u in LICENSES])


def main() -> int:
    ap = argparse.ArgumentParser(description="Build the site's self-hosted webfonts.")
    ap.add_argument("--check", action="store_true", help="report what would change; write nothing")
    args = ap.parse_args()

    built = build()
    if built.is_err:
        print(f"error: {built.unwrap_err()}", file=sys.stderr)
        return 1
    subsets = built.unwrap()
    css = stylesheet(subsets)
    print(report(subsets))
    if args.check:
        old = stale(subsets, css)
        print("\nstale: " + ", ".join(old) + "\nrun `make fonts`" if old else "\nup to date")
        return 1 if old else 0
    wrote = write(subsets, css)
    if wrote.is_err:
        print(f"error: {wrote.unwrap_err()}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
