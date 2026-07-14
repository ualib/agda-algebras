#!/usr/bin/env python3
"""Remove HTML ``<a id="…">`` heading anchors, relying on kramdown's
auto-generated heading slugs (M4-2a, issue #387).

For every heading of the form

    <level> <a id="TAG">TEXT</a>

the HTML wrapper is removed.  *How* depends on whether kramdown's auto-slug of
TEXT reproduces TAG, and on whether TAG is used as a cross-reference target:

  * slug(TEXT) == TAG                       ->  ``<level> TEXT``
  * slug(TEXT) != TAG and TAG unreferenced  ->  ``<level> TEXT``
  * slug(TEXT) != TAG and TAG referenced     ->  ``<level> TEXT {#TAG}``

The third case keeps the id explicitly (kramdown attribute-list syntax) so the
existing ``#TAG`` cross-reference still resolves.  Cross-references are collected
repo-wide (``src/`` + ``docs/``) so an anchor linked from another module or the
paper is preserved.  Rewrites touch only the target paths passed on the command
line; ``src/Legacy/**`` is never rewritten (but is still scanned for references).

Usage::

    python3 scripts/python/remove_heading_anchors.py src/Setoid           # dry-run report
    python3 scripts/python/remove_heading_anchors.py --apply src/Setoid   # rewrite in place
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

# A heading line that is exactly: hashes, the <a id="…"> wrapper, end of line.
HEADING_ANCHOR = re.compile(r'^(#{1,6}) *<a id="([^"]+)"> *(.*?) *</a> *$')
# Any line that mentions an <a id (used to flag forms the rewriter does not handle).
ANY_ANCHOR = re.compile(r'<a id=')
# Markdown inline-link target  ](…)  and reference-definition  [label]: …
LINK_TARGET = re.compile(r'\]\(([^)]*)\)')
REF_DEF = re.compile(r'^\s*\[[^\]]+\]:\s*(\S+)', re.MULTILINE)
FRAGMENT = re.compile(r'#([A-Za-z0-9][A-Za-z0-9_-]*)')


def kramdown_id(text: str) -> str:
    """Reproduce kramdown's ``generate_id`` (auto_ids on, no transliteration):
    strip leading non-letters, drop characters outside ``[A-Za-z0-9 -]``, turn
    spaces into hyphens, downcase; an empty result becomes ``section``."""
    s = re.sub(r'^[^A-Za-z]+', '', text)
    s = re.sub(r'[^A-Za-z0-9 -]', '', s)
    s = s.replace(' ', '-').lower()
    return s or 'section'


def collect_referenced_ids(roots: list[Path]) -> set[str]:
    """Every fragment id that appears as a link or reference-definition target."""
    refs: set[str] = set()
    for root in roots:
        for path in root.rglob('*.md'):
            text = path.read_text(encoding='utf-8')
            for target in LINK_TARGET.findall(text) + REF_DEF.findall(text):
                m = FRAGMENT.search(target)
                if m:
                    refs.add(m.group(1))
    return refs


def process_file(path: Path, referenced: set[str], apply: bool) -> list[dict]:
    """Rewrite (or report) the heading anchors in ``path``.  Returns one record
    per anchor for the report."""
    lines = path.read_text(encoding='utf-8').split('\n')
    records: list[dict] = []
    slugs_seen: dict[str, int] = {}
    for idx, line in enumerate(lines):
        m = HEADING_ANCHOR.match(line)
        if not m:
            if ANY_ANCHOR.search(line):
                records.append({'line': idx + 1, 'unhandled': line.strip()})
            continue
        hashes, tag, text = m.group(1), m.group(2), m.group(3)
        slug = kramdown_id(text)
        if slug == tag:
            action, new = 'strip (slug==tag)', f'{hashes} {text}'
            final_id = slug
        elif tag in referenced:
            action, new = 'keep  (referenced)', f'{hashes} {text} {{#{tag}}}'
            final_id = tag
        else:
            action, new = 'strip (unreferenced)', f'{hashes} {text}'
            final_id = slug
        slugs_seen[final_id] = slugs_seen.get(final_id, 0) + 1
        records.append({
            'line': idx + 1, 'tag': tag, 'slug': slug, 'action': action,
            'new': new, 'final_id': final_id,
            'both_referenced': slug != tag and slug in referenced,
        })
        if apply:
            lines[idx] = new
    # Flag any post-rewrite id collision within this file (kramdown would dedupe).
    for record in records:
        if 'final_id' in record:
            record['collision'] = slugs_seen[record['final_id']] > 1
    if apply and any('tag' in r for r in records):
        path.write_text('\n'.join(lines), encoding='utf-8')
    return records


def main(argv: list[str]) -> int:
    apply = '--apply' in argv
    targets = [Path(a) for a in argv if not a.startswith('--')]
    if not targets:
        print('usage: remove_heading_anchors.py [--apply] <path>...', file=sys.stderr)
        return 2
    referenced = collect_referenced_ids([Path('src'), Path('docs')])
    total = kept = unhandled = warnings = 0
    for target in targets:
        for path in sorted(p for p in target.rglob('*.lagda.md')
                           if 'Legacy/' not in str(p)
                           and not str(p).replace('\\', '/').endswith('Examples/Demos/HSP.lagda.md')):
            for r in process_file(path, referenced, apply):
                if 'unhandled' in r:
                    unhandled += 1
                    print(f'!! {path}:{r["line"]}: UNHANDLED anchor form: {r["unhandled"]}')
                    continue
                total += 1
                if r['action'].startswith('keep'):
                    kept += 1
                flags = ''
                if r['both_referenced']:
                    flags += '  [WARN: slug also referenced]'
                    warnings += 1
                if r['collision']:
                    flags += '  [WARN: id collides within file]'
                    warnings += 1
                print(f'{path}:{r["line"]}: [{r["action"]}] id={r["tag"]!r} slug={r["slug"]!r}{flags}')
                if r['slug'] != r['tag'] and r['action'].startswith('keep'):
                    print(f'      -> {r["new"].strip()}')
    mode = 'APPLIED' if apply else 'DRY-RUN'
    print(f'\n{mode}: {total} anchors ({kept} kept as {{#id}}, {total - kept} stripped), '
          f'{unhandled} unhandled, {warnings} warnings.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
