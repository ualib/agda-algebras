/* Type-on-hover tooltips for Agda tokens (#429, M10-3).

   The highlighted `agda --html` output that mkdocs_gen_library.py mounts turns
   every token into `<a href="…#offset">` inside `<pre class="Agda">`, and every
   *definition* into an `<a id="offset">` at its defining occurrence.  This
   script pairs the two: hovering a linked token fetches the target page once,
   locates that definition anchor, and shows a small popover with a snippet of
   the definition — its type signature, plus the `data`/`record … where` header
   it belongs to when the anchor is a constructor or field.  The snippet keeps
   Agda's own syntax highlighting: it is cloned from the target page's tokens,
   so the existing `pre.Agda .Function` (etc.) colours apply in both schemes.

   Adapted from the tooltip first written for the formal-ledger-specifications
   site, with these changes for agda-algebras:

     + Links here use the rewritten MkDocs scheme, not the classic Agda output's
       flat `Module.html#id` siblings: `/Setoid/Algebras/Basic/#id` for library
       modules and `/classic/Data.Nat.html#id` for the standard library (see
       `rewrite_agda_hrefs` in scripts/python/mkdocs_gen_library.py).  Both forms
       are parsed through the URL API and fetched as-is; a reference whose
       definition is on the current page is read from the live DOM instead.
     + Hovering a token *at its own definition site* shows nothing — Agda links
       a definition to itself, so the popover would just echo what the reader is
       already looking at.
     + Wiring goes through Material's `document$` (like agda-copy.js and
       agda-toggle.js) and uses a single set of delegated listeners on
       `document`, so the cost is constant no matter how many thousands of
       tokens a page carries — and it survives Material's page swaps.
     + It adds the "Tooltips on/off" header control the milestone calls for,
       persisted in localStorage next to the palette and Show-more-Agda choices.

   Fetches are same-origin and read-only; the page and snippet caches are
   bounded; nothing is ever written to the target pages. */
(function () {
  // -- DOM contract + tunables ---------------------------------------------
  var HOVER_SELECTOR = 'pre.Agda a[href]';   // linked tokens in Agda blocks
  var HOVER_DELAY_MS = 120;                   // debounce before a tip appears
  var HIDE_DELAY_MS  = 60;                    // grace period before it hides
  var SNIPPET_LINES  = 14;                    // max lines shown from a definition
  var TOGGLE_KEY = 'agda-tooltips';           // localStorage: "off" disables
  var MAX_CACHED_PAGES = 16;                  // parsed target pages kept in RAM

  // Name-kind classes Agda's highlighter puts on definition links; the header
  // label shows whichever one a token carries (e.g. "Function", "Record").
  var KIND_CLASSES = new Set([
    'Argument', 'Bound', 'CoinductiveConstructor', 'Datatype', 'Field',
    'Function', 'Generalizable', 'InductiveConstructor', 'Macro', 'Module',
    'Postulate', 'Primitive', 'Record',
  ]);

  // A small tooltip/callout glyph, inlined so the header button needs no extra
  // request; the stroke follows the button's text colour via currentColor.
  var TIP_ICON =
    '<svg class="agda-tip-icon" aria-hidden="true" viewBox="0 0 24 24"' +
    ' fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"' +
    ' stroke-linejoin="round">' +
    '<path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/>' +
    '</svg>';

  // Caches: fetch each target page once, extract each snippet once.
  var pageCache = new Map();     // page URL (no hash) -> Promise<Document|null>
  var snippetCache = new Map();  // full href -> highlighted-HTML string

  var tooltipEl = null;
  var hideTimer = null;
  var showTimer = null;
  var activeAnchor = null;       // the <a> the pointer/focus is currently on
  var lastPointer = null;        // last cursor position, for placement
  var usePointer = false;        // false for keyboard focus (place by box)
  var listenersReady = false;    // delegated listeners installed once

  // Hover tooltips are meaningless where the primary input can't hover, so on
  // touch-only devices we install neither the listeners nor the toggle.
  var HOVER_NONE = !!(window.matchMedia && window.matchMedia('(hover: none)').matches);

  // On/off state.  Default on; readers who find the tips distracting turn them
  // off from the header and the choice persists across pages and visits.
  var tooltipsEnabled = readEnabled();

  function readEnabled() {
    try { return localStorage.getItem(TOGGLE_KEY) !== 'off'; }
    catch (e) { return true; }   // storage unavailable (private mode): default on
  }

  // -- Small helpers -------------------------------------------------------

  function sanitize(text) {
    // We only ever insert our own strings, but escape defensively anyway.
    var div = document.createElement('div');
    div.textContent = text == null ? '' : String(text);
    return div.innerHTML;
  }

  // "InductiveConstructor" -> "Inductive Constructor" for display.
  function displayKind(kind) {
    return kind.replace(/([a-z])([A-Z])/g, '$1 $2');
  }

  // Module display name from a rewritten href: the dotted path for a library
  // directory URL (`/Setoid/Algebras/Basic/` -> "Setoid.Algebras.Basic"), or
  // the file stem for a classic page (`/classic/Data.Nat.html` -> "Data.Nat").
  function moduleNameFromUrl(url) {
    var segs = url.pathname.split('/').filter(Boolean);
    if (!segs.length) return '';
    var last = segs[segs.length - 1];
    var name = /\.html$/.test(last) ? last.replace(/\.html$/, '') : segs.join('.');
    try { return decodeURIComponent(name); } catch (e) { return name; }
  }

  // Is this the page the reader is already on?  Then skip the fetch and read
  // the definition straight from the live DOM (same-page references are common
  // in Agda, where a proof cites lemmas defined just above it).
  function isCurrentPage(pageUrl) {
    var norm = function (s) { return s.replace(/index\.html$/, '').replace(/\/$/, ''); };
    return norm(pageUrl) === norm(window.location.origin + window.location.pathname);
  }

  function inferTokenInfo(a) {
    var classes = (a.getAttribute('class') || '').split(/\s+/).filter(Boolean);
    var kind = classes.find(function (c) { return KIND_CLASSES.has(c); }) || '';
    var isOperator = classes.indexOf('Operator') !== -1;
    var url = new URL(a.getAttribute('href') || '', window.location.href);
    var pageUrl = url.origin + url.pathname;
    var anchor = url.hash ? url.hash.slice(1) : '';
    var moduleName = moduleNameFromUrl(url);
    return {
      href: url.href,
      pageUrl: pageUrl,
      basename: a.textContent.trim() || moduleName,
      kind: kind ? displayKind(kind) + (isOperator ? ' operator' : '') : '',
      moduleName: moduleName,
      anchor: anchor,
      // True when the hovered token *is* its own definition: Agda gives the
      // defining occurrence both `id="N"` and `href="…#N"` on its own page, so
      // the popover would only echo what the reader is already looking at.
      selfDef: !!a.id && a.id === anchor && isCurrentPage(pageUrl),
    };
  }

  // -- Fetching + snippet extraction ---------------------------------------

  // Fetch and parse a target page once; concurrent hovers share the promise.
  function fetchPage(pageUrl) {
    var p = pageCache.get(pageUrl);
    if (!p) {
      p = fetch(pageUrl, { credentials: 'same-origin' })
        .then(function (res) {
          if (!res.ok) throw new Error('HTTP ' + res.status);
          return res.text();
        })
        .then(function (html) { return new DOMParser().parseFromString(html, 'text/html'); })
        .catch(function () { return null; });
      // Evict the oldest parsed pages so memory stays bounded.
      while (pageCache.size >= MAX_CACHED_PAGES) {
        pageCache.delete(pageCache.keys().next().value);
      }
      pageCache.set(pageUrl, p);
    }
    return p;
  }

  function resolveDocument(pageUrl) {
    if (isCurrentPage(pageUrl)) return Promise.resolve(document);
    return fetchPage(pageUrl);
  }

  function fetchSnippet(info) {
    // Module-level links carry no anchor; a "top of the page" snippet is rarely
    // the module header (often a hidden imports block), so skip.
    if (!info.anchor) return Promise.resolve('');

    var cached = snippetCache.get(info.href);
    if (cached !== undefined) return Promise.resolve(cached);

    return resolveDocument(info.pageUrl).then(function (dom) {
      var html = '';
      if (dom) {
        // Find the definition anchor, then its closest Agda <pre> (works for
        // both mkdocs-wrapped library pages and raw classic Agda pages; blocks
        // that custom.css hides as `hidden-source` are still in the DOM).
        var target = dom.getElementById(info.anchor);
        var pre = target ? target.closest('pre.Agda') : null;
        if (pre) {
          var ex = extractDefinitionBlock(pre.textContent || '',
            charIndexWithin(pre, target), { maxLines: SNIPPET_LINES });
          try {
            html = buildSnippetHTML(pre, ex);           // keep Agda's colours
          } catch (e) {
            html = ex.block                             // plain, escaped fallback
              ? '<pre class="Agda agda-tip-snippet">' + sanitize(ex.block) + '</pre>'
              : '';
          }
        }
      }
      snippetCache.set(info.href, html);
      return html;
    });
  }

  // Character index of `node` relative to the start of `root`, via a Range in
  // the node's own document (`root` may come from a DOMParser document, not the
  // live one).  Returns -1 if anything fails.
  function charIndexWithin(root, node) {
    try {
      var r = (root.ownerDocument || document).createRange();
      r.setStart(root, 0);
      r.setEnd(node, 0);
      return r.toString().length;
    } catch (e) {
      return -1;
    }
  }

  /* Heuristically extract a "definition block" around `anchorIndex`, returning
     the structural pieces the highlighter needs:
       - split the <pre> text into lines and find the one holding anchorIndex;
       - take the blank-line-delimited paragraph around it — in Agda a
         definition (signature + clauses, or a data/record declaration) is
         usually one such paragraph;
       - if the anchor line is indented (a field, constructor, or a where-block
         definition), climb to each enclosing header line (nearest line above
         with strictly smaller indentation), so e.g. a record field is shown
         with its `record … where` header;
       - cap at maxLines.  Returns per-line offsets so buildSnippetHTML can clone
         the matching highlighted spans, plus a plain-text `block` fallback. */
  function extractDefinitionBlock(text, anchorIndex, opts) {
    opts = opts || {};
    var maxLines = opts.maxLines || 14;
    var maxChars = opts.maxChars || 1200;

    var lines = text.split(/\r?\n/);
    var starts = new Array(lines.length);
    var acc = 0;
    for (var i = 0; i < lines.length; i++) {
      starts[i] = acc;
      acc += lines[i].length + 1;   // +1 for the newline
    }

    // Find the anchor line (or fall back to the first line).
    var iAnchor = 0;
    if (anchorIndex >= 0) {
      for (var j = 0; j < lines.length; j++) {
        if (anchorIndex < starts[j] + lines[j].length + 1) { iAnchor = j; break; }
      }
    }

    var indent = function (l) { var m = l.match(/^\s*/); return m ? m[0].length : 0; };
    var isBlank = function (l) { return /^\s*$/.test(l); };

    // 1) Paragraph containing the anchor line.
    var start = iAnchor, end = iAnchor;
    while (start > 0 && !isBlank(lines[start - 1])) start--;
    while (end + 1 < lines.length && !isBlank(lines[end + 1])) end++;

    // 2) Cap the paragraph, keeping the lines from `start` (the signature comes
    //    first); make sure the anchor line stays included.
    var truncatedBelow = false;
    if (end - start + 1 > maxLines) {
      if (iAnchor - start + 1 > maxLines) start = iAnchor;   // pathological; anchor wins
      end = start + maxLines - 1;
      if (end < iAnchor) end = iAnchor;
      truncatedBelow = true;
    }

    // 3) Climb to enclosing headers when the paragraph is indented.
    var headers = [];
    var ind = indent(lines[start]);
    if (ind > 0 && anchorIndex >= 0) {
      for (var k = start - 1; k >= 0 && ind > 0; k--) {
        var l = lines[k];
        if (isBlank(l)) continue;
        if (indent(l) < ind) { headers.unshift(k); ind = indent(l); }
      }
    }

    // Plain-text composition (fallback + cache-miss display): headers (with `⋯`
    // marking elided lines) + the paragraph, capped.
    var parts = [];
    var prev = -1;
    for (var h = 0; h < headers.length; h++) {
      if (prev >= 0 && headers[h] > prev + 1) parts.push('⋯');
      parts.push(lines[headers[h]]);
      prev = headers[h];
    }
    if (prev >= 0 && start > prev + 1) parts.push('⋯');
    for (var s = start; s <= end; s++) parts.push(lines[s]);
    if (truncatedBelow) parts.push('…');

    var block = parts.join('\n');
    if (block.length > maxChars) {
      var cut = block.lastIndexOf('\n', maxChars);
      block = block.slice(0, cut > 0 ? cut : maxChars) + '\n…';
    }

    return {
      block: block,
      headerLines: headers,
      paraStart: start,
      paraEnd: end,
      truncatedBelow: truncatedBelow,
      starts: starts,
      lines: lines,
    };
  }

  // Locate the [textNode, offset] pair for character `offset` within `root`, by
  // walking its text nodes (whose concatenation is `root.textContent`, the same
  // string extractDefinitionBlock indexed).
  function locate(root, offset) {
    var doc = root.ownerDocument || document;
    var walker = doc.createTreeWalker(root, NodeFilter.SHOW_TEXT, null);
    var acc = 0, node = null, last = null;
    while ((node = walker.nextNode())) {
      var len = node.nodeValue.length;
      if (offset <= acc + len) return [node, Math.max(0, offset - acc)];
      acc += len;
      last = node;
    }
    return last ? [last, last.nodeValue.length] : [root, 0];
  }

  function rangeForCharSpan(root, from, to) {
    var doc = root.ownerDocument || document;
    var r = doc.createRange();
    var s = locate(root, from), e = locate(root, to);
    r.setStart(s[0], s[1]);
    r.setEnd(e[0], e[1]);
    return r;
  }

  // Build the snippet as highlighted HTML by cloning the matching token spans
  // out of the target <pre> (so the `.Function`/`.Keyword`/… classes ride
  // along) and stitching them with `⋯`/`…` markers, mirroring `block`.  Line
  // boundaries fall in the whitespace between tokens, so cloned ranges always
  // contain whole `<a>` tokens.
  function buildSnippetHTML(pre, ex) {
    var host = document.createElement('pre');
    host.className = 'Agda agda-tip-snippet';
    var spanFor = function (fromLine, toLine) {
      var from = ex.starts[fromLine];
      var to = ex.starts[toLine] + ex.lines[toLine].length;
      host.appendChild(rangeForCharSpan(pre, from, to).cloneContents());
    };
    var text = function (t) { host.appendChild(document.createTextNode(t)); };

    var prev = -1;
    for (var i = 0; i < ex.headerLines.length; i++) {
      var h = ex.headerLines[i];
      if (prev >= 0 && h > prev + 1) text('⋯\n');
      spanFor(h, h);
      text('\n');
      prev = h;
    }
    if (prev >= 0 && ex.paraStart > prev + 1) text('⋯\n');
    spanFor(ex.paraStart, ex.paraEnd);
    if (ex.truncatedBelow) text('\n…');

    return host.outerHTML;
  }

  // -- Tooltip element + placement -----------------------------------------

  function createTooltip() {
    if (tooltipEl && document.body.contains(tooltipEl)) return tooltipEl;
    tooltipEl = document.createElement('div');
    tooltipEl.className = 'agda-tooltip hidden';
    tooltipEl.setAttribute('role', 'tooltip');
    tooltipEl.innerHTML = '<div class="agda-tooltip-inner"></div>';
    document.body.appendChild(tooltipEl);
    return tooltipEl;
  }

  function positionTooltip(el) {
    var pad = 12;
    var vw = window.innerWidth;
    var vh = window.innerHeight;
    var rect = el.getBoundingClientRect();
    var tipRect = tooltipEl.getBoundingClientRect();
    // Place by the cursor when hovering; by the element box for keyboard focus.
    var px = (usePointer && lastPointer) ? lastPointer.x : rect.left;
    var top = rect.bottom + window.scrollY + pad;
    var left = px + window.scrollX + pad;
    // If it overflows the right edge, pull it left.
    if (left + tipRect.width > window.scrollX + vw - pad) {
      left = Math.max(window.scrollX + pad, window.scrollX + vw - tipRect.width - pad);
    }
    // If it falls off the bottom, flip it above the token.
    if (top + tipRect.height > window.scrollY + vh - pad) {
      top = rect.top + window.scrollY - tipRect.height - pad;
    }
    tooltipEl.style.top = top + 'px';
    tooltipEl.style.left = left + 'px';
  }

  function renderTooltipContent(info, snippetHTML, loading) {
    var header = '<div class="agda-tip-head">' +
      (info.kind ? '<span class="agda-kind">' + sanitize(info.kind) + '</span>' : '') +
      '<code class="agda-name">' + sanitize(info.basename) + '</code>' +
      '<span class="agda-module">· ' + sanitize(info.moduleName) + '</span>' +
      '</div>';
    var body = snippetHTML
      ? snippetHTML
      : loading
        ? '<div class="agda-tip-empty agda-tip-loading">Loading preview…</div>'
        : '<div class="agda-tip-empty">No preview available.</div>';
    return header + body;
  }

  function showTooltip(a, content) {
    var el = createTooltip();
    el.querySelector('.agda-tooltip-inner').innerHTML = content;
    el.classList.remove('hidden');
    positionTooltip(a);
  }

  function hideTooltip() {
    if (tooltipEl) tooltipEl.classList.add('hidden');
  }

  // -- Hover / focus flow --------------------------------------------------

  function enterAnchor(a) {
    if (!tooltipsEnabled) return;
    activeAnchor = a;
    clearTimeout(hideTimer);
    clearTimeout(showTimer);
    showTimer = setTimeout(function () {
      if (activeAnchor !== a || !tooltipsEnabled) return;
      var info = inferTokenInfo(a);
      // A token at its own definition site would only echo itself — skip it.
      if (info.selfDef) { activeAnchor = null; hideTooltip(); return; }
      var cached = snippetCache.get(info.href);
      if (cached === undefined) {
        // Show a fast skeleton immediately, then fill in the fetched snippet.
        showTooltip(a, renderTooltipContent(info, '', true));
        fetchSnippet(info).then(function (html) {
          if (activeAnchor !== a || !tooltipsEnabled) return;   // pointer moved on
          showTooltip(a, renderTooltipContent(info, html, false));
        });
      } else {
        showTooltip(a, renderTooltipContent(info, cached, false));
      }
    }, HOVER_DELAY_MS);
  }

  function leaveAnchor() {
    activeAnchor = null;
    clearTimeout(showTimer);
    hideTimer = setTimeout(hideTooltip, HIDE_DELAY_MS);
  }

  // Delegated on `document`: mouseover/mouseout and focusin/focusout bubble, so
  // one listener each covers every current and future token.
  function onOver(evt) {
    var t = evt.target;
    if (!t || !t.closest) return;
    var a = t.closest(HOVER_SELECTOR);
    if (!a || a === activeAnchor) return;
    usePointer = (evt.type === 'mouseover');
    enterAnchor(a);
  }

  function onOut(evt) {
    var t = evt.target;
    var a = (t && t.closest) ? t.closest(HOVER_SELECTOR) : null;
    if (!a || a !== activeAnchor) return;
    // Ignore moves that stay within the same token (defensive; tokens are leaf
    // <a> elements holding only text).
    if (evt.relatedTarget && a.contains(evt.relatedTarget)) return;
    leaveAnchor();
  }

  function onMove(evt) {
    lastPointer = { x: evt.clientX, y: evt.clientY };
  }

  function installListeners() {
    if (listenersReady || HOVER_NONE) return;
    listenersReady = true;
    document.addEventListener('mouseover', onOver, { passive: true });
    document.addEventListener('mouseout', onOut, { passive: true });
    document.addEventListener('mousemove', onMove, { passive: true });
    document.addEventListener('focusin', onOver, { passive: true });
    document.addEventListener('focusout', onOut, { passive: true });
  }

  // -- Header on/off control -----------------------------------------------

  function buttonLabel(on) {
    return (on ? 'Tooltips on ' : 'Tooltips off ') + TIP_ICON;
  }

  function updateButton() {
    var btn = document.getElementById('toggle-agda-tooltips');
    if (!btn) return;
    btn.innerHTML = buttonLabel(tooltipsEnabled);
    btn.setAttribute('aria-pressed', String(tooltipsEnabled));
  }

  function setEnabled(on) {
    tooltipsEnabled = on;
    try { localStorage.setItem(TOGGLE_KEY, on ? 'on' : 'off'); }
    catch (e) { /* storage unavailable: the toggle still works per page */ }
    if (!on) { clearTimeout(showTimer); activeAnchor = null; hideTooltip(); }
    updateButton();
  }

  function installButton() {
    if (HOVER_NONE) return;
    var btn = document.getElementById('toggle-agda-tooltips');
    if (!btn) {
      btn = document.createElement('button');
      btn.id = 'toggle-agda-tooltips';
      btn.type = 'button';
      btn.title = 'Turn Agda type-on-hover tooltips on or off';
      // Sit just after the Show-more-Agda pill when present, else after the
      // site title (mirroring agda-toggle.js).
      var source = document.getElementById('toggle-agda-source');
      var title = document.querySelector('.md-header__inner > .md-header__title');
      if (source && source.parentNode) {
        source.parentNode.insertBefore(btn, source.nextSibling);
      } else if (title && title.parentNode) {
        title.parentNode.insertBefore(btn, title.nextSibling);
      } else {
        document.body.appendChild(btn);
      }
      btn.addEventListener('click', function () { setEnabled(!tooltipsEnabled); });
    }
    updateButton();
  }

  function install() {
    if (HOVER_NONE) return;
    installButton();
    installListeners();
  }

  // Mirror agda-copy.js / agda-toggle.js: Material emits `document$` on every
  // page load; fall back to DOMContentLoaded when it is unavailable.
  if (window.document$ && typeof window.document$.subscribe === 'function') {
    window.document$.subscribe(install);
  } else if (document.readyState !== 'loading') {
    install();
  } else {
    document.addEventListener('DOMContentLoaded', install);
  }
})();
