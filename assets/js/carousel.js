/* Featured-results carousel (ADR-007, landing page).
   Shows N cards at once — N comes from the CSS variable `--per`, which the
   stylesheet sets responsively (1 on a phone, 2 on a tablet, 3 on a wide
   monitor).  Advances one card every few seconds; the leftmost slides out and
   a fresh card enters from the right.  The first `--per` cards are cloned onto
   the end so the wrap from last back to first is seamless.  A row of clickable
   dots (one per real card) marks and jumps to a card.  Pauses on hover /
   keyboard focus and when the tab is hidden; honours prefers-reduced-motion
   (no autoplay, no slide animation).  With JS off the cards are a static row.

   build() is fully idempotent: it is re-run (debounced) on resize to recompute
   `--per`, the clones, and the measured slide step, so it clears BOTH the track
   and the dots first.  Listeners that must survive rebuilds (resize, hover,
   transitionend) are attached once in initCarousel and delegate to the current
   controller. */
(function () {
  var DURATION = 550; // keep in sync with the inline transition below

  function build(root) {
    var track = root.querySelector(".ualib-carousel__track");
    var dotsWrap = root.querySelector(".ualib-carousel__dots");
    if (!track || !dotsWrap) return null;

    if (!root._cards) {
      root._cards = Array.prototype.slice.call(track.querySelectorAll(".ualib-figure"));
    }
    var cards = root._cards;
    var n = cards.length;
    if (n < 2) return null;

    var reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    var perView = parseInt(getComputedStyle(root).getPropertyValue("--per"), 10) || 1;
    perView = Math.max(1, Math.min(n, perView));

    // Rebuild the track: the real cards, then clones of the first `perView`.
    track.style.transition = "none";
    track.innerHTML = "";
    cards.forEach(function (c) { c.classList.remove("is-clone"); track.appendChild(c); });
    for (var k = 0; k < perView; k++) {
      var clone = cards[k].cloneNode(true);
      clone.classList.add("is-clone");
      clone.setAttribute("aria-hidden", "true");
      track.appendChild(clone);
    }

    // Rebuild the dots from scratch (clearing first prevents accumulation).
    dotsWrap.innerHTML = "";

    function step() {
      var first = track.querySelector(".ualib-figure");
      var gap = parseFloat(getComputedStyle(track).columnGap) || 0;
      return first.getBoundingClientRect().width + gap;
    }

    var index = 0;
    function place(animate) {
      track.style.transition = (animate && !reduce)
        ? "transform " + DURATION + "ms cubic-bezier(.4,0,.2,1)" : "none";
      track.style.transform = "translateX(" + (-index * step()) + "px)";
    }

    var dots = cards.map(function (_, k) {
      var b = document.createElement("button");
      b.type = "button";
      b.className = "ualib-carousel__dot";
      b.setAttribute("aria-label", "Show featured result " + (k + 1) + " of " + n);
      b.addEventListener("click", function () { index = k; place(true); syncDots(); api.restart(); });
      dotsWrap.appendChild(b);
      return b;
    });
    function syncDots() {
      var active = ((index % n) + n) % n;
      dots.forEach(function (d, k) {
        d.classList.toggle("is-active", k === active);
        d.setAttribute("aria-current", k === active ? "true" : "false");
      });
    }

    function advance() { index += 1; place(true); syncDots(); }

    var timer = null;
    var interval = parseInt(root.dataset.autoplay || "4000", 10);
    var api = {
      start: function () { if (reduce || timer || n < 2) return; timer = window.setInterval(advance, interval); },
      stop: function () { if (timer) { window.clearInterval(timer); timer = null; } },
      restart: function () { api.stop(); api.start(); },
      // After advancing onto the cloned tail, snap (no animation) back to the
      // identical real position — invisible, so the loop never jumps visibly.
      onTransitionEnd: function (e) {
        if (e.target !== track || e.propertyName !== "transform") return;
        if (index >= n) { index -= n; place(false); syncDots(); }
      },
    };

    place(false);
    syncDots();
    return api;
  }

  function initCarousel(root) {
    if (root.dataset.carouselReady) return;
    root.dataset.carouselReady = "1";

    var ctl = build(root);
    if (!ctl) return;
    var track = root.querySelector(".ualib-carousel__track");

    // Attached ONCE; each reads `ctl`, which resize() reassigns in place.
    track.addEventListener("transitionend", function (e) { ctl.onTransitionEnd(e); });
    root.addEventListener("mouseenter", function () { ctl.stop(); });
    root.addEventListener("mouseleave", function () { ctl.start(); });
    root.addEventListener("focusin", function () { ctl.stop(); });
    root.addEventListener("focusout", function () { ctl.start(); });
    document.addEventListener("visibilitychange", function () {
      if (document.hidden) ctl.stop(); else ctl.start();
    });

    var rt = null;
    window.addEventListener("resize", function () {
      window.clearTimeout(rt);
      rt = window.setTimeout(function () {
        ctl.stop();
        ctl = build(root) || ctl;
        ctl.start();
      }, 200);
    });

    ctl.start();
  }

  function initAll() {
    document.querySelectorAll(".ualib-carousel").forEach(initCarousel);
  }

  if (window.document$ && typeof window.document$.subscribe === "function") {
    window.document$.subscribe(initAll);
  } else if (document.readyState !== "loading") {
    initAll();
  } else {
    document.addEventListener("DOMContentLoaded", initAll);
  }
})();
