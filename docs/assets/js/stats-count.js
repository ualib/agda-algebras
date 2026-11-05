/* Count-up for the landing page's figures (the `ualib-stats` strip).

   The final figures are already in the HTML: scripts/python/corpus_stats.py
   counts them from src/ and the MkDocs hook writes them into the page at
   every build, so a crawler, a reader with JavaScript off and a reader who
   asked for reduced motion all see the counted values with this file doing
   nothing.  What it adds, when motion is allowed, is the arrival: each
   numeric figure counts up from zero the first time the strip scrolls into
   view, and lands on the value the page already held.  The animation is a
   way of arriving at a counted value, never the only carrier of it.

   Only a figure that is an integer with a suffix ("91", "24k", "100%") is
   animated; the toolchain's version ("2.9.0") is not a quantity and stays
   as it is.  The suffix is shown throughout, so the cell's width barely
   moves (the figures are set in tabular numerals, site.css).

   The `document$` subscription is the one agda-copy.js and agda-toggle.js
   use: `navigation.instant` swaps the page without a reload, and a one-shot
   listener would leave the strip static on every visit after the first.
   The `data-counted` guard stops a second pass over one page's lifetime. */
(function () {
  var DURATION = 900; /* ms; long enough to read as counting, short enough to wait for */
  var FIGURE = /^(\d+)(\D*)$/;

  function animate(el, target, suffix) {
    var start = null;
    function step(now) {
      if (start === null) start = now;
      var p = Math.min((now - start) / DURATION, 1);
      var eased = 1 - Math.pow(1 - p, 3); /* ease-out cubic */
      el.textContent = Math.round(target * eased) + suffix;
      if (p < 1) requestAnimationFrame(step);
    }
    requestAnimationFrame(step);
  }

  function countUp() {
    var nums = document.querySelectorAll(".ualib-stats .ualib-stat__num");
    if (!nums.length) return;
    if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) return;
    if (!("IntersectionObserver" in window)) return;

    var observer = new IntersectionObserver(function (entries) {
      entries.forEach(function (entry) {
        if (!entry.isIntersecting) return;
        observer.unobserve(entry.target);
        var el = entry.target;
        if (el.dataset.counted) return;
        el.dataset.counted = "1";
        /* textContent skips the ualib:stat comments around the value, and
           replacing it drops them, which the rendered page does not need. */
        var m = FIGURE.exec(el.textContent.trim());
        if (m) animate(el, parseInt(m[1], 10), m[2]);
      });
    }, { threshold: 0.4 });

    nums.forEach(function (el) { observer.observe(el); });
  }

  if (typeof document$ !== "undefined") {
    document$.subscribe(countUp);
  } else {
    document.addEventListener("DOMContentLoaded", countUp);
  }
})();
