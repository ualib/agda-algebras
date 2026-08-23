"""
File: scripts/python/_utils/agda_names.py

Description: Agda name tokenisation, and the "is this name used?" predicate.

  Shared by the corpus tools: ``unused_imports.py`` asks whether an imported
  name is referenced anywhere in the module that imported it, and
  ``docstring_audit.py`` asks whether a *defined* name is referenced anywhere in
  the corpus.  Both questions reduce to the same one — does this name, which may
  be mixfix, may be sectioned, and may back a ``syntax`` declaration, appear at a
  use site? — so the answer lives in one place.

Design Principles:
  Textual, and deliberately biased toward reporting a name as *used*.  Every
  genuine use produces a token the scan counts; the residual inaccuracy is in
  the other direction (a short name shared by two modules can look used when the
  use belongs to the other one), which is the safe way round for a linter that
  suggests deletions.
"""
from __future__ import annotations

import re
from pathlib import Path
from types import MappingProxyType
from typing import Iterable, Mapping, Optional

from .literate import file_code_lines


# Token delimiters: whitespace and the characters Agda always treats as
# separators.  Notably ``_`` , ``,`` and ``[ ]`` are NOT delimiters — they occur
# inside ordinary names (``_,_``, ``[]``, ``if_then_else_``).
_DELIM = re.compile(r"[\s(){};.@\"⦃⦄]+")
def code_tokens(code: str) -> frozenset[str]:
    """The set of name tokens appearing in a blob of code."""
    return frozenset(t for t in _DELIM.split(code) if t)


# A ``syntax`` declaration: ``syntax NAME <params> = <notation>``.  The notation
# is arbitrary, so the only way to know what a syntax-backing name looks like at
# its use sites is to read the declaration.
_SYNTAX_DECL = re.compile(r"^\s*syntax\s+(\S+)\s+(.*?)\s*=\s*(\S.*)$")

# What a syntax-backing name looks like in code: its declared notation's literal
# tokens (the ones that are not argument placeholders).
SyntaxNotations = Mapping[str, frozenset[str]]

NO_NOTATIONS: SyntaxNotations = MappingProxyType({})


def parse_syntax_decl(code_line: str) -> Optional[tuple[str, frozenset[str]]]:
    """``syntax conj-syntax g x = x ^ g`` -> ``("conj-syntax", {"^"})``, and
    ``syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B`` -> ``("Σ-syntax", {"Σ[", "∈", "]"})``.

    The literal tokens are those of the notation that are not bound on the left of
    the ``=``.  A declaration whose notation is all placeholders yields ``None``:
    there would be nothing to look for.  A declaration whose notation mentions a
    name that is *not* among its parameters yields an over-strict entry — such a
    name is a literal token as far as Agda is concerned, and no use site can
    contain it — which simply never matches; the ``Foo[`` fallback in
    :func:`is_used` then applies, so the outcome is still correct.  (A `syntax`
    declaration in that shape is usually a mistake in the declaration itself.)"""
    m = _SYNTAX_DECL.match(code_line)
    if m is None:
        return None
    name, params, notation = m.group(1), m.group(2), m.group(3)
    bound = code_tokens(params)
    literals = frozenset(t for t in code_tokens(notation) if t not in bound)
    return (name, literals) if literals else None


def harvest_syntax_notations(sources: Iterable[tuple[Path, str]]) -> dict[str, frozenset[str]]:
    """Collect every ``syntax`` declaration in the scanned corpus.  Names are
    global here rather than per-module: two modules declaring the same
    syntax-backing name are rare, and on collision we keep the *intersection* of
    the literal tokens, which can only make a name easier to count as used —
    the safe direction for a gate that must not raise false alarms.

    The same bare-name keying is a known limitation: when a corpus module and a
    library outside the corpus both export ``Foo-syntax`` with *different*
    notations, an import of the outside one is judged by the corpus notation, so
    a redundant import of the twin can go unreported.  The failure direction is
    again under-reporting, never a false alarm."""
    found: dict[str, frozenset[str]] = {}
    for _, text in sources:
        for line in file_code_lines(text):
            decl = parse_syntax_decl(line)
            if decl is None:
                continue
            name, literals = decl
            found[name] = found[name] & literals if name in found else literals
    return {n: lits for n, lits in found.items() if lits}


def name_parts(name: str) -> tuple[str, ...]:
    """The non-empty parts of a (possibly mixfix) name: ``_∙_`` -> ``('∙',)``."""
    return tuple(p for p in name.split("_") if p)


def is_used(name: str, toks: frozenset[str], notations: SyntaxNotations = NO_NOTATIONS) -> bool:
    """Is ``name`` used, given the set of tokens from a module's code?  A mixfix
    name is used when its full form or any of its operator parts appears.

    A name of the form ``Foo-syntax`` backs an Agda ``syntax`` declaration and so
    never appears verbatim at its use site; what appears is the declared notation.
    ``notations`` maps such a name to the literal tokens of its notation, harvested
    from the corpus by :func:`harvest_syntax_notations`, and the name counts as used
    when all of them appear.  Failing that, the common ``Foo[`` shape is recognised,
    which covers standard-library names such as ``Σ-syntax`` whose declaration is
    outside the corpus."""
    if name in toks:
        return True
    if name.endswith("-syntax"):
        literals = notations.get(name)
        if literals is not None and literals <= toks:
            return True
        if (name[: -len("-syntax")] + "[") in toks:
            return True
    # Operator sections keep one hole glued to the name: `_⊨ˢᵍ_` used as
    # `(_⊨ˢᵍ Th)` tokenises to `_⊨ˢᵍ`, and `(x ∙_)` to `∙_`.
    if {name.lstrip("_"), name.rstrip("_")} & toks:
        return True
    parts = name_parts(name)
    if "_" in name and parts != (name,):
        return any(p in toks for p in parts)
    return False
