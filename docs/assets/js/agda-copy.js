/* Copy button for highlighted Agda code blocks (ADR-007).
   Material's `content.code.copy` feature only decorates its own `.highlight`
   blocks.  The `agda --html` output mounted by mkdocs_gen_library.py is a bare
   `<pre class="Agda">` (token <a> elements, no inner <code>), which Material
   skips — so we add an equivalent button ourselves.  It copies the block's
   plain source text (the rendered token text, minus the button), letting a
   reader lift a snippet straight into their own .agda file. */
(function () {
  var CLIPBOARD =
    '<svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor"' +
    ' stroke-width="2" stroke-linecap="round" stroke-linejoin="round">' +
    '<rect x="9" y="9" width="11" height="11" rx="2"/>' +
    '<path d="M5 15V5a2 2 0 0 1 2-2h10"/></svg>';
  var CHECK =
    '<svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor"' +
    ' stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round">' +
    '<path d="M20 6 9 17l-5-5"/></svg>';

  function decorate(pre) {
    if (pre.dataset.copyReady) return;
    pre.dataset.copyReady = "1";
    // Capture the clean source text before the button is appended.
    var source = pre.innerText;

    var btn = document.createElement("button");
    btn.type = "button";
    btn.className = "ualib-agda-copy md-icon";
    btn.title = "Copy this block to the clipboard";
    btn.setAttribute("aria-label", "Copy Agda source to clipboard");
    btn.innerHTML = CLIPBOARD;

    btn.addEventListener("click", function () {
      navigator.clipboard.writeText(source).then(function () {
        btn.innerHTML = CHECK;
        btn.classList.add("ualib-copied");
        window.setTimeout(function () {
          btn.innerHTML = CLIPBOARD;
          btn.classList.remove("ualib-copied");
        }, 1400);
      });
    });

    pre.appendChild(btn);
  }

  function decorateAll() {
    document.querySelectorAll("pre.Agda").forEach(decorate);
  }

  // Material ships instant navigation; `document$` emits on every page load.
  if (window.document$ && typeof window.document$.subscribe === "function") {
    window.document$.subscribe(decorateAll);
  } else if (document.readyState !== "loading") {
    decorateAll();
  } else {
    document.addEventListener("DOMContentLoaded", decorateAll);
  }
})();
