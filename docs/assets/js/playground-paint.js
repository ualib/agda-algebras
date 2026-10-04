/* File: docs/assets/js/playground-paint.js
 *
 * The playground editor's colored copy of its own text (`paint`), and the
 * bookkeeping that keeps Agda's highlighting attached to the right
 * characters while the reader types (`shift`).
 *
 * Provenance: `paint` is the painter of `docs/javascripts/playground-highlight.js`
 * of williamdemeo/website at commit 952e5eb (MIT, Copyright 2026 William
 * DeMeo; see NOTICE), unchanged.  That file's other half, a port of Pygments'
 * Agda lexer, is not taken: this page colors with Agda's own highlighting,
 * which the checker returns with every load, and which the build recorded for
 * the first frame.  `rangesOf`, `fromAgda` and `shift` are new.
 *
 * ## It must not disagree with the box by a character
 *
 * `paint` builds the mirror from text nodes cut from the box's own value, and
 * adds nothing but one trailing newline, which gives the box's last line its
 * height.  Nothing the reader types is parsed as markup.
 */
(function (root) {
  "use strict";

  /* Agda's highlighting aspects, as the classes its HTML backend writes and
   * this site colors (`pre.Agda .Keyword`, ...).  The same table as
   * `ASPECT_CLASSES` in scripts/python/playground/build_assets.py. */
  var ASPECTS = {
    comment: "Comment", keyword: "Keyword", string: "String",
    number: "Number", symbol: "Symbol", primitivetype: "PrimitiveType",
    pragma: "Pragma", background: "Background", markup: "Markup",
    bound: "Bound", generalizable: "Generalizable",
    inductiveconstructor: "InductiveConstructor",
    coinductiveconstructor: "CoinductiveConstructor", datatype: "Datatype",
    field: "Field", "function": "Function", module: "Module",
    postulate: "Postulate", primitive: "Primitive", record: "Record",
    argument: "Argument", macro: "Macro", operator: "Operator", hole: "Hole",
  };

  /* The UTF-16 offset of Agda's code point position `pos` (from 1). */
  function offsetOf(text, pos) {
    var units = 0;
    var points = 1;
    for (var i = 0; i < text.length && points < pos; points++) {
      var c = text.charCodeAt(i);
      var d = i + 1 < text.length ? text.charCodeAt(i + 1) : 0;
      /* A pair only when a low surrogate follows: a lone high surrogate is
       * one code point to Agda (it reads it as U+FFFD), as to edits.js. */
      var step = c >= 0xd800 && c <= 0xdbff && d >= 0xdc00 && d <= 0xdfff ? 2 : 1;
      i += step;
      units += step;
    }
    return units;
  }

  /* Agda's highlighting, `[{from, to, atoms}]` in code points, as ranges
   * `[from, to, classes]` in the UTF-16 offsets `paint` takes. */
  function fromAgda(text, highlighting) {
    return highlighting
      .map(function (h) {
        var classes = h.atoms.map(function (a) { return ASPECTS[a]; })
          .filter(Boolean).join(" ");
        return [offsetOf(text, h.from), offsetOf(text, h.to), classes];
      })
      .filter(function (r) { return r[2] !== "" && r[1] > r[0]; })
      .sort(function (a, b) { return a[0] - b[0]; });
  }

  /* The ranges a highlighted block already carries: each classed span's
   * offsets in the block's text.  This is the build's highlighting, which is
   * what the editor's first frame shows. */
  function rangesOf(block) {
    var ranges = [];
    var at = 0;
    (function walk(node) {
      for (var child = node.firstChild; child; child = child.nextSibling) {
        if (child.nodeType === 3) { at += child.nodeValue.length; continue; }
        var start = at;
        walk(child);
        /* Only the token spans: the site's copy button (agda-copy.js) is
         * appended to every `pre.Agda` and holds no text. */
        if (child.nodeName === "SPAN" && child.className && at > start) {
          ranges.push([start, at, String(child.className)]);
        }
      }
    })(block);
    return ranges.sort(function (a, b) { return a[0] - b[0]; });
  }

  /* Ranges and marks after an edit that turned `before` into `after`: those
   * wholly before the change stay, those wholly after it move by the change
   * in length, and those the change touches go.  The change is found as the
   * longest common prefix and suffix, which is exact for one insertion,
   * deletion or replacement, and every keystroke is one. */
  function shift(before, after, ranges, marks) {
    var p = 0;
    var limit = Math.min(before.length, after.length);
    while (p < limit && before.charCodeAt(p) === after.charCodeAt(p)) p++;
    var s = 0;
    while (s < limit - p &&
           before.charCodeAt(before.length - 1 - s) === after.charCodeAt(after.length - 1 - s)) s++;
    var end = before.length - s;
    var delta = after.length - before.length;
    /* Before the change, or after it; and a range moves only when it is
     * after.  Moving each end on its own would stretch a range that ends
     * exactly where text is inserted over the inserted text, so that what a
     * reader types after a token took that token's color. */
    var before = function (from, to) { return to <= p; };
    var after = function (from) { return from >= end; };
    return {
      ranges: ranges.filter(function (r) { return before(r[0], r[1]) || after(r[0]); })
        .map(function (r) { return after(r[0]) && !before(r[0], r[1]) ? [r[0] + delta, r[1] + delta, r[2]] : r; }),
      marks: marks.filter(function (m) { return before(m.from, m.to) || after(m.from); })
        .map(function (m) {
          return after(m.from) && !before(m.from, m.to)
            ? { from: m.from + delta, to: m.to + delta, kind: m.kind } : m;
        }),
    };
  }

  /* Paint `text` into `pre`: a span for each classed range, and each mark,
   * `{from, to, kind}`, wrapped round whatever it covers.  A range and a mark
   * may cross, so the text is cut at every boundary of either and each piece
   * goes into the span and the mark that cover it. */
  function paint(pre, text, ranges, marks) {
    var doc = pre.ownerDocument;
    var n = text.length;
    var clamp = function (x) { return Math.max(0, Math.min(n, x)); };

    var kept = [];
    marks.slice()
      .map(function (m) { return { from: clamp(m.from), to: clamp(m.to), kind: m.kind }; })
      .sort(function (a, b) { return a.from - b.from; })
      .forEach(function (m) {
        var last = kept[kept.length - 1];
        if (m.to > m.from && (!last || m.from >= last.to)) kept.push(m);
      });

    var cuts = [0, n];
    ranges.forEach(function (r) { cuts.push(clamp(r[0]), clamp(r[1])); });
    kept.forEach(function (m) { cuts.push(m.from, m.to); });
    cuts = cuts.sort(function (a, b) { return a - b; })
      .filter(function (x, i, all) { return i === 0 || x !== all[i - 1]; });

    var fragment = doc.createDocumentFragment();
    var holder = fragment;
    var open = null;
    var r = 0;
    var k = 0;
    for (var i = 0; i + 1 < cuts.length; i++) {
      var from = cuts[i];
      var to = cuts[i + 1];
      while (r < ranges.length && ranges[r][1] <= from) r++;
      while (k < kept.length && kept[k].to <= from) k++;
      var cls = r < ranges.length && ranges[r][0] <= from ? ranges[r][2] : null;
      var mark = k < kept.length && kept[k].from <= from ? kept[k] : null;

      if (mark !== open) {
        holder = fragment;
        if (mark) {
          holder = doc.createElement("mark");
          holder.className = "agda-mark agda-mark--" + mark.kind;
          fragment.appendChild(holder);
        }
        open = mark;
      }

      var piece = doc.createTextNode(text.slice(from, to));
      if (cls) {
        var span = doc.createElement("span");
        span.className = cls;
        span.appendChild(piece);
        holder.appendChild(span);
      } else {
        holder.appendChild(piece);
      }
    }

    /* A box whose value ends in a newline has an empty last line a caret can
     * sit on, and a <pre> drops it.  One more newline gives it back, and
     * gives a value that does not end in one nothing it lacks. */
    fragment.appendChild(doc.createTextNode("\n"));
    pre.textContent = "";
    pre.appendChild(fragment);
  }

  root.AgdaPaint = {
    offsetOf: offsetOf,
    fromAgda: fromAgda,
    rangesOf: rangesOf,
    shift: shift,
    paint: paint,
  };
})(typeof window !== "undefined" ? window : globalThis);
