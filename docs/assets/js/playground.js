/* File: docs/assets/js/playground.js
 *
 * The playground's page controller (ADR-011).
 *
 * The page ships each exercise as Agda-highlighted code, what Agda said about
 * its goals when the page was built, and one sentence saying what checking it
 * would download.  That is the whole page with this file absent, blocked, or
 * off: an exercise a reader can read, a goal's type and context, and no dead
 * control.  What this adds is the consent gate, the editor, and a live goals
 * panel with Agda's goal commands: give, refine, case split, and the type of
 * an expression at a goal.
 *
 * Provenance: adapted from `docs/javascripts/playground.js` of
 * williamdemeo/website at commit 952e5eb (MIT, Copyright 2026 William
 * DeMeo; see NOTICE).  `Session`, the gate, the lost-worker handling and the
 * editor's mirror are that file's; the goals panel, the goal commands, the
 * covering images and the undo are new.
 *
 * ## Nothing is fetched until a reader asks
 *
 * No `fetch`, no `<link rel=preload>`, no worker is created on load; the
 * first byte crosses the wire on a click, and the button says how many bytes
 * that is before it is pressed.  The numbers are rendered from the assets'
 * own manifest by `scripts/python/playground/mkdocs_hook.py`, so they cannot
 * drift from the files.
 *
 * ## One worker, one compiled module, several images
 *
 * The 31 MB module is compiled once per visit and every exercise reuses it.
 * An image is a closure of this library, and an exercise can run on any image
 * whose closure holds its own: each gate carries the list (`data-served`), its
 * own image first.  So an exercise whose image, or a larger one, is already
 * mounted costs nothing at all, and the wording of a gate that has not been
 * pressed yet changes as the session loads things.  `announce` is that update.
 *
 * ## One run per command
 *
 * Every button is one run of the checker in the worker: load the text, do
 * what was asked at a goal, and report every goal's type and context
 * (`playground/session.js` plans it from Agda's answers).  A command that
 * changes the text (a give, a refine, a case split) changes it in the run, and
 * the run reloads it; the box receives the new text and its goals together.
 * While such a command runs the box is read-only, so that the text it
 * returns cannot overwrite typing.  A Check leaves the box writable, and a
 * result about text the reader has since changed says so.
 *
 * ## Motion
 *
 * None.  The only thing that moves is a determinate `<progress>` during a
 * download, which is state rather than decoration.
 */
(function () {
  "use strict";

  var REWRITES = [
    ["Simplified", "Simplified"],
    ["AsIs", "As written"],
    ["Normalised", "Normalized"],
  ];

  function bytes(n) {
    if (n >= 1048576) return (n / 1048576).toFixed(n >= 10485760 ? 0 : 1) + " MB";
    if (n >= 1024) return Math.round(n / 1024) + " KB";
    return n + " bytes";
  }

  function seconds(ms) {
    return ms >= 1000 ? (ms / 1000).toFixed(2) + " s" : Math.round(ms) + " ms";
  }

  function element(tag, className, text) {
    var el = document.createElement(tag);
    if (className) el.className = className;
    if (text !== undefined) el.textContent = text;
    return el;
  }

  function button(text, className) {
    var b = element("button", "agda-button" + (className ? " " + className : ""), text);
    b.type = "button";
    return b;
  }

  /* What this browser is missing, if anything.  A page that offers a button
   * it cannot honor is worse than one that says why. */
  function unsupported() {
    var missing = [];
    if (typeof Worker === "undefined") missing.push("web workers");
    if (typeof WebAssembly === "undefined" || !WebAssembly.compileStreaming) {
      missing.push("streaming WebAssembly");
    }
    if (typeof DecompressionStream === "undefined") missing.push("DecompressionStream");
    return missing;
  }

  /* ---- The session: one worker, the checker, the mounted images -------- */

  function Session(workerUrl) {
    this.workerUrl = workerUrl;
    this.worker = null;
    this.booted = false;
    this.booting = null;
    this.pending = {};
    this.nextId = 1;
    this.listeners = [];
    this.exercises = [];
    this.mounting = {};                 // image url -> its mount, in flight or done
    this.mounted = {};                  // image url -> true once the worker holds it
  }

  /* End the session: the worker, the compiled module, every mounted image,
   * and every call still waiting on it. */
  Session.prototype.close = function () {
    var self = this;
    var reason = new Error("the playground was left");
    Object.keys(this.pending).forEach(function (id) {
      self.pending[id].reject(reason);
      delete self.pending[id];
    });
    this.listeners = [];
    if (this.worker) {
      this.worker.terminate();
      this.worker = null;
    }
    this.forget();
  };

  /* Everything the worker held goes with it.  A session that remembered an
   * image after its worker died would tell a reader "nothing to download",
   * then ask a fresh worker to check against an image it never received. */
  Session.prototype.forget = function () {
    this.booted = false;
    this.booting = null;
    this.mounting = {};
    this.mounted = {};
    this.announce();
  };

  /* Every exercise re-reads what the session holds: a gate relabels its
   * button, and an open editor learns whether its checker is still there. */
  Session.prototype.announce = function () {
    this.exercises.forEach(function (exercise) { exercise.announce(); });
  };

  /* Stop whatever the worker is doing, by ending it: a run is one call into
   * WebAssembly and cannot be interrupted from outside, and a definition
   * that never terminates (a TERMINATING pragma over a loop, say) would hold
   * the worker, and every exercise on the page, for good (found in review).
   * The worker goes with everything it held; the downloads stay in the
   * browser's cache, and each editor's button says what loading again costs. */
  Session.prototype.stop = function () {
    var self = this;
    if (!this.worker) return;
    var reason = new Error("you stopped it");
    this.worker.terminate();
    this.worker = null;
    Object.keys(this.pending).forEach(function (id) {
      self.pending[id].reject(reason);
      delete self.pending[id];
    });
    this.forget();
  };

  Session.prototype.start = function () {
    if (this.worker) return;
    var self = this;
    this.worker = new Worker(this.workerUrl, { type: "module" });
    this.worker.onmessage = function (event) {
      var message = event.data;
      if (message.type === "progress") {
        self.listeners.forEach(function (fn) { fn(message); });
        return;
      }
      var waiting = self.pending[message.id];
      delete self.pending[message.id];
      if (!waiting) return;
      if (message.type === "error") waiting.reject(new Error(message.message));
      else waiting.resolve(message);
    };
    /* A module worker that fails to start reports here and never answers a
     * message, so every outstanding call is failed by hand, and the worker
     * is dropped: a dead worker accepts `postMessage` and never replies. */
    this.worker.onerror = function (event) {
      var reason = new Error(event.message || "the checker's worker failed to start");
      self.worker.terminate();
      self.worker = null;
      self.forget();
      Object.keys(self.pending).forEach(function (id) {
        self.pending[id].reject(reason);
        delete self.pending[id];
      });
    };
  };

  Session.prototype.send = function (message) {
    var self = this;
    this.start();
    return new Promise(function (resolve, reject) {
      var id = self.nextId++;
      self.pending[id] = { resolve: resolve, reject: reject };
      self.worker.postMessage(Object.assign({ id: id }, message));
    });
  };

  /* One boot per session, shared by every exercise that asks while it is in
   * flight; a failed boot is forgotten, so that a retry really fetches. */
  Session.prototype.boot = function (url) {
    var self = this;
    if (this.booted) return Promise.resolve(null);
    if (!this.booting) {
      this.booting = this.send({ cmd: "boot", url: url }).then(
        function (done) { self.booted = true; return done; },
        function (err) { self.booting = null; throw err; });
    }
    return this.booting;
  };

  /* One mount per image per session, for the same reasons. */
  Session.prototype.mount = function (url) {
    var self = this;
    if (!this.mounting[url]) {
      var attempt = this.send({ cmd: "mount", url: url }).then(
        function (done) {
          if (self.mounting[url] === attempt) self.mounted[url] = true;
          return done;
        },
        function (err) {
          if (self.mounting[url] === attempt) delete self.mounting[url];
          throw err;
        });
      this.mounting[url] = attempt;
    }
    return this.mounting[url];
  };

  /* ---- One exercise ---------------------------------------------------- */

  function Exercise(root, session) {
    var gate = root.querySelector(".agda-exercise__gate");
    var base = document.baseURI;
    this.root = root;
    this.session = session;
    this.gate = gate;
    this.code = root.querySelector(".agda-exercise__code");
    this.built = root.querySelector(".agda-goals--built");
    /* The exercise's text is the code block's: the build wrote it from the
     * same file the checker was proved on. */
    this.source = this.code.textContent;
    this.firstRanges = window.AgdaPaint ? window.AgdaPaint.rangesOf(this.code) : [];
    this.file = gate.dataset.file;
    this.checkerUrl = new URL(gate.dataset.checker, base).href;
    this.imageUrl = new URL(gate.dataset.image, base).href;
    this.served = (gate.dataset.served || gate.dataset.image).split(/\s+/)
      .filter(Boolean).map(function (u) { return new URL(u, base).href; });
    this.checkerBytes = Number(gate.dataset.checkerBytes || 0);
    this.imageBytes = Number(gate.dataset.imageBytes || 0);
    this.rewrite = "Simplified";
    this.history = [];
    this.goals = [];
  }

  /* The image this exercise runs on now: the first mounted one that serves
   * it, or null when none is. */
  Exercise.prototype.image = function () {
    for (var i = 0; i < this.served.length; i++) {
      if (this.session.mounted[this.served[i]]) return this.served[i];
    }
    return null;
  };

  /* What a press fetches now, in bytes. */
  Exercise.prototype.cost = function () {
    return (this.session.booted ? 0 : this.checkerBytes) + (this.image() ? 0 : this.imageBytes);
  };

  Exercise.prototype.price = function () {
    var cost = this.cost();
    if (cost === 0) return "Open the editor (already downloaded)";
    if (!this.session.booted) return "Load the checker and the library files (" + bytes(cost) + ")";
    return "Load the library files (" + bytes(cost) + ")";
  };

  /* The gate: the sentence the page already carries, plus a button that says
   * what pressing it costs.  The sentence stays: it is the disclosure. */
  Exercise.prototype.renderGate = function () {
    var self = this;
    this.controls = element("p", "agda-exercise__controls");
    this.button = button("", "agda-button--primary");
    this.button.addEventListener("click", function () { self.load(); });
    this.controls.appendChild(this.button);
    this.gate.after(this.controls);
    this.announce();
  };

  Exercise.prototype.announce = function () {
    if (this.editor) { this.relabel(); return; }
    if (!this.button || this.loading) return;
    this.button.textContent = this.price();
  };

  Exercise.prototype.say = function (text) {
    if (this.progressLabel) this.progressLabel.textContent = text;
  };

  /* Fetch what is missing: the checker, then this exercise's own image,
   * unless an image that serves it is already mounted. */
  Exercise.prototype.fetch = function (onProgress) {
    var self = this;
    /* Progress is posted for every download in flight, and two gates pressed
     * together would show each other's (found in review): this exercise
     * follows the checker and its own image only. */
    var own = function (message) {
      if (message.label === "checker" || !message.url || message.url === self.imageUrl) onProgress(message);
    };
    this.session.listeners.push(own);
    var stop = function () {
      var at = self.session.listeners.indexOf(own);
      if (at !== -1) self.session.listeners.splice(at, 1);
    };
    return this.session.boot(this.checkerUrl)
      .then(function () {
        self.session.announce();
        return self.image() ? null : self.session.mount(self.imageUrl);
      })
      .then(function () { stop(); self.session.announce(); },
            function (err) { stop(); self.session.announce(); throw err; });
  };

  function progressText(message) {
    return (message.label === "checker" ? "Checker" : "Library files") + ": " +
      bytes(message.got) + " of " + bytes(message.total);
  }

  Exercise.prototype.load = function () {
    var self = this;
    this.loading = true;
    this.button.disabled = true;
    if (this.progress) this.progress.remove();
    if (this.progressLabel) this.progressLabel.remove();
    this.controls.classList.remove("agda-exercise__controls--failed");
    this.progress = element("progress");
    this.progress.max = 1;
    this.progress.value = 0;
    this.progress.setAttribute("aria-label", "Download progress");
    /* Not a live region: it changes with every chunk of a 37 MB download, and
     * a screen reader would queue every change (found in review).  The
     * <progress> carries the state, and the editor's arrival ends it. */
    this.progressLabel = element("span", "agda-exercise__status");
    this.controls.appendChild(this.progress);
    this.controls.appendChild(this.progressLabel);
    this.say("Starting...");
    this.fetch(function (message) {
      if (!message.total) return;
      self.progress.value = message.got / message.total;
      self.say(progressText(message));
    }).then(function () {
      /* The editor takes the focus only from the gate's own button, or from
       * nowhere: a reader typing in another exercise while this one
       * downloaded keeps their place (found in review). */
      var focus = document.activeElement === self.button || document.activeElement === document.body;
      self.loading = false;
      self.controls.remove();
      self.renderEditor(focus);
    }, function (err) {
      self.loading = false;
      self.progress.remove();
      self.progress = null;
      self.button.disabled = false;
      self.announce();
      self.say("The checker could not be loaded: " + err.message);
      self.controls.classList.add("agda-exercise__controls--failed");
    });
  };

  /* ---- The editor ------------------------------------------------------ */

  Exercise.prototype.renderEditor = function (focus) {
    var self = this;
    var id = "agda-editor-" + (this.root.id || this.file);

    var label = element("label", "agda-editor__label", "Agda source, editable");
    label.setAttribute("for", id);

    this.editor = element("textarea", "agda-editor");
    this.editor.id = id;
    this.editor.spellcheck = false;
    this.editor.setAttribute("wrap", "off");
    this.editor.setAttribute("autocapitalize", "off");
    this.editor.setAttribute("autocomplete", "off");
    this.editor.value = this.source;
    this.editor.rows = this.source.split("\n").length + 1;
    this.text = this.source;            // the value the ranges and marks describe

    /* The highlighting is a mirror: a <pre> under the box, painted from its
     * value, with the box's own text made transparent so that its caret and
     * selection are drawn over the colored copy.  The box stays a real
     * <textarea>, so typing, undo, the input method, a screen reader and the
     * label all work on the thing they always worked on, and the mirror is
     * hidden from assistive technology.  Without playground-paint.js there
     * is no mirror and the box shows its own text. */
    var frame = element("div", "agda-editor__frame");
    this.ranges = this.firstRanges;
    this.marks = [];
    if (window.AgdaPaint) {
      this.mirror = element("pre", "Agda agda-editor__mirror");
      this.mirror.setAttribute("aria-hidden", "true");
      frame.appendChild(this.mirror);
      this.editor.addEventListener("scroll", function () { self.follow(); });
    }
    frame.appendChild(this.editor);

    /* Ctrl-Enter checks; Tab is left alone, so the box is never a keyboard
     * trap.  Agda rejects tab characters outright ("Lexical error"), which is
     * one more reason not to let Tab type one. */
    this.editor.addEventListener("keydown", function (event) {
      if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) {
        event.preventDefault();
        if (!self.lost()) self.check();
      }
    });
    this.editor.addEventListener("input", function () {
      if (window.AgdaInput) window.AgdaInput.commit(self.editor);
      self.edited();
    });
    /* The palette types where the reader last was: the editor, or the field
     * under a goal they are composing a give in (found in review: it always
     * typed into the editor, which outdated the goal being worked on). */
    this.target = this.editor;
    this.editor.addEventListener("focus", function () { self.target = self.editor; });

    this.checkButton = button("Check", "agda-button--primary");
    this.checkButton.addEventListener("click", function () {
      if (self.lost()) self.reload(); else self.check();
    });
    this.undoButton = button("Undo");
    this.undoButton.disabled = true;
    this.undoButton.addEventListener("click", function () { self.undo(); });
    /* Reset is a change like a give, and Undo takes it back. */
    this.resetButton = button("Reset");
    this.resetButton.addEventListener("click", function () {
      if (self.editor.value !== self.source) {
        self.history.push({ before: self.editor.value, after: self.source });
      }
      self.replace(self.source);
      self.editor.focus();
      self.check();
    });

    this.stopButton = button("Stop");
    this.stopButton.title = "End the checker, and with it every exercise's downloads in this tab";
    this.stopButton.hidden = true;
    this.stopButton.addEventListener("click", function () { self.session.stop(); });

    var bar = element("p", "agda-exercise__bar");
    bar.appendChild(this.checkButton);
    bar.appendChild(this.stopButton);
    bar.appendChild(this.undoButton);
    bar.appendChild(this.resetButton);
    this.hint = element("span", "agda-exercise__hint", "or press Ctrl and Enter");
    bar.appendChild(this.hint);

    var rewriteLabel = element("label", "agda-exercise__hint", "Show types ");
    this.rewriteSelect = element("select", "agda-select");
    REWRITES.forEach(function (r) {
      var option = element("option", "", r[1]);
      option.value = r[0];
      self.rewriteSelect.appendChild(option);
    });
    this.rewriteSelect.addEventListener("change", function () {
      self.rewrite = self.rewriteSelect.value;
      if (!self.lost() && !self.running) self.check();
    });
    rewriteLabel.appendChild(this.rewriteSelect);
    bar.appendChild(rewriteLabel);

    var palette = null;
    if (window.AgdaInput) {
      palette = element("p", "agda-palette");
      palette.appendChild(element("span", "agda-palette__lead",
        "Type \\to and a space for →, or click:"));
      window.AgdaInput.palette.forEach(function (entry) {
        var key = element("button", "agda-palette__key", entry.glyph);
        key.type = "button";
        var how = entry.keys.length ? " (type backslash " + entry.keys[0] + " then a space)" : "";
        key.title = entry.keys.map(function (k) { return "\\" + k; }).join("  ");
        key.setAttribute("aria-label", "Insert " + entry.glyph + how);
        key.addEventListener("click", function () {
          var field = self.target !== self.editor && self.target.isConnected ? self.target : null;
          if (field) {
            window.AgdaInput.insert(field, entry.glyph);
            return;
          }
          /* A script's insertion ignores `readOnly`, so the box's hold
           * during a give or a case split is kept here as well. */
          if (self.editor.readOnly) return;
          window.AgdaInput.insert(self.editor, entry.glyph);
          self.edited();
        });
        palette.appendChild(key);
      });
    }

    this.verdict = element("p", "agda-verdict");
    this.verdict.setAttribute("role", "status");
    this.verdict.setAttribute("aria-live", "polite");
    this.output = element("pre", "agda-output");
    this.output.hidden = true;
    this.panel = element("div", "agda-goals agda-goals--live");
    this.panel.hidden = true;

    this.code.hidden = true;
    this.gate.after(label);
    label.after(frame);
    var after = frame;
    if (palette) { after.after(palette); after = palette; }
    after.after(bar);
    bar.after(this.verdict);
    this.verdict.after(this.output);
    this.output.after(this.panel);
    this.paint();
    if (focus) this.editor.focus();
    if (typeof ResizeObserver !== "undefined" && this.mirror) {
      new ResizeObserver(function () { self.follow(); }).observe(this.editor);
    }
    this.check();
  };

  /* The value changed, by typing, a palette key, or a programmatic
   * replacement: the highlighting and the marks follow the characters they
   * were about, and those the edit touched go.  The goals panel and the
   * verdict describe the text before the edit and say so (`outdate`). */
  Exercise.prototype.edited = function () {
    var now = this.editor.value;
    if (window.AgdaPaint && now !== this.text) {
      var moved = window.AgdaPaint.shift(this.text, now, this.ranges, this.marks);
      this.ranges = moved.ranges;
      this.marks = moved.marks;
    }
    this.text = now;
    if (now !== this.checked) this.outdate();
    this.updateUndo();
    this.paint();
  };

  /* Replace the whole value, as Reset, Undo and a goal command do. */
  Exercise.prototype.replace = function (value) {
    this.editor.value = value;
    this.edited();
  };

  /* After an edit, the verdict and the goals are about other text.  They
   * stay, since they are what the reader is working on, but they stop
   * asserting it: the position controls and the goal commands are disabled,
   * and the verdict says which text it is about, once. */
  Exercise.prototype.outdate = function () {
    if (this.stale) return;
    this.stale = true;
    this.root.querySelectorAll(".agda-goal__command, .agda-verdict__where")
      .forEach(function (el) { el.disabled = true; });
    if (this.panel && !this.panel.hidden) {
      this.panelNote.textContent = "These goals are about the text before your edit; " +
        "Check again to work on them.";
    }
    /* Only a verdict about a run is about a text; "the checker stopped" or
     * "Give needs an expression" is not (found in review). */
    if (this.verdictIsRun && !this.running) {
      this.verdictIsRun = false;
      this.verdict.classList.add("agda-verdict--stale");
      this.verdict.appendChild(document.createTextNode(" · about the text before your edit"));
    }
  };

  /* Say something in the verdict line that is not a run's answer. */
  Exercise.prototype.tell = function (kind, text) {
    this.verdictIsRun = false;
    this.verdict.className = "agda-verdict" + (kind ? " agda-verdict--" + kind : "");
    this.verdict.textContent = text;
  };

  Exercise.prototype.paint = function () {
    if (!this.mirror) return;
    window.AgdaPaint.paint(this.mirror, this.editor.value, this.ranges, this.marks);
    this.follow();
  };

  /* The box scrolls and the mirror follows.  A classic horizontal scrollbar
   * takes height from the box's content and none from the mirror's, and the
   * two could then scroll different distances (found in review, with
   * scrollbars always shown): the mirror is cut short by the bar's height,
   * so that both scroll through the same area. */
  Exercise.prototype.follow = function () {
    var e = this.editor;
    var style = window.getComputedStyle(e);
    var bar = e.offsetHeight - e.clientHeight
      - parseFloat(style.borderTopWidth) - parseFloat(style.borderBottomWidth);
    this.mirror.style.bottom = Math.max(0, Math.round(bar)) + "px";
    this.mirror.scrollTop = e.scrollTop;
    this.mirror.scrollLeft = e.scrollLeft;
  };

  /* Whether the worker behind this editor, or every image that serves it,
   * is gone.  Then the editor keeps its text, says so, and Check becomes the
   * gate's button again, quoting what a press fetches.  Ctrl-Enter does not
   * fetch: a shortcut is not consent to a download. */
  Exercise.prototype.lost = function () {
    return !this.session.booted || !this.image();
  };

  Exercise.prototype.relabel = function () {
    if (this.running) return;
    var lost = this.lost();
    this.checkButton.textContent = lost ? this.price() : "Check";
    this.hint.hidden = lost;
    if (lost && !this.stopped) {
      this.stopped = true;
      this.marks = [];
      this.paint();
      this.output.hidden = true;
      this.panel.hidden = true;
      this.tell("error", "The checker stopped, so this text has not been checked.  " +
        "It is kept, and the button above says what checking it again would download.");
    } else if (!lost && this.stopped) {
      this.stopped = false;
      this.tell("", "The checker is loaded again.  Check will check this text.");
    }
  };

  Exercise.prototype.busy = function (on, editing) {
    this.running = on;
    this.checkButton.disabled = on;
    this.stopButton.hidden = !on;
    this.resetButton.disabled = on;
    this.updateUndo();
    this.rewriteSelect.disabled = on;
    /* A command that rewrites the text holds the box until it does. */
    this.editor.readOnly = on && editing;
    /* Goal commands about text the reader has since changed stay off, run or
     * no run (found in review: a run that failed turned them back on). */
    var stale = this.stale;
    this.root.querySelectorAll(".agda-goal__command, .agda-verdict__where").forEach(function (b) {
      b.disabled = on || stale || b.dataset.stale === "1";
    });
    if (!on) this.relabel();
  };

  /* The gate's fetch, from an open editor, and then the check it was for. */
  Exercise.prototype.reload = function () {
    var self = this;
    this.busy(true, false);
    this.tell("working", "Starting...");
    var failure = null;
    var step = -1;
    /* The verdict is a live region, so it moves in quarters, not chunks. */
    this.fetch(function (message) {
      if (!message.total) return;
      var quarter = Math.floor(4 * message.got / message.total);
      if (quarter === step) return;
      step = quarter;
      self.tell("working", progressText(message));
    }).catch(function (err) {
      failure = "The checker could not be loaded: " + err.message;
    }).then(function () {
      self.busy(false, false);
      if (failure) self.tell("error", failure);
      else self.check();
    });
  };

  Exercise.prototype.check = function () {
    this.run(null, "Checking...");
  };

  /* A goal command: `op` is give, refine, case or have, at goal `goal`. */
  Exercise.prototype.command = function (op, goal, text, label) {
    this.run({ op: op, goal: goal, text: text }, label + " at ?" + goal + "...");
  };

  /* Undo takes back the last give, refine, case split or Reset, and only
   * while the box still holds the text that change produced: once the reader
   * has typed since, undoing it would throw their typing away with no way
   * back, and the box's own undo (Ctrl-Z) is theirs to use instead (found in
   * review). */
  Exercise.prototype.undoable = function () {
    var last = this.history[this.history.length - 1];
    return !!last && this.editor.value === last.after;
  };

  Exercise.prototype.updateUndo = function () {
    if (!this.undoButton) return;
    var last = this.history[this.history.length - 1];
    this.undoButton.disabled = this.running || !this.undoable();
    this.undoButton.title = !last ? "Nothing to undo yet"
      : this.undoable() ? "Put back the text before the last give, refine, case split or Reset"
      : "You have typed since the last change; your editor's own undo (Ctrl-Z) takes that back";
  };

  Exercise.prototype.undo = function () {
    if (!this.undoable()) return;
    this.replace(this.history.pop().before);
    this.check();
  };

  /* One run of the checker over the box's text. */
  Exercise.prototype.run = function (action, working) {
    var self = this;
    if (this.running) return;
    if (this.lost()) { this.relabel(); return; }
    /* A byte-order mark is invisible, and Agda drops one before it counts
     * positions, so every position it answered would be one character off
     * in this box (found in review).  It goes before the run. */
    if (this.editor.value.charCodeAt(0) === 0xfeff) this.replace(this.editor.value.slice(1));
    var source = this.editor.value;
    var editing = action !== null && action.op !== "have";
    /* Where the reader was, so that the keyboard is not left on the page's
     * body when the panel is rebuilt (found in review). */
    var origin = document.activeElement;
    var goal = action ? action.goal : null;
    var sent = performance.now();
    this.busy(true, editing);
    this.stopped = false;
    this.tell("working", working);
    this.session.send({
      cmd: "run", url: this.image(), file: this.file, source: source,
      action: action, rewrite: this.rewrite,
    })
      .then(function (result) { self.report(result, source, action, performance.now() - sent); })
      .catch(function (err) {
        self.tell("error", "The checker stopped: " + err.message);
        self.output.hidden = true;
      })
      .then(function () {
        self.busy(false, editing);
        self.refocus(origin, goal);
      });
  };

  /* Put the keyboard back where the reader was, or on the same goal's field
   * in the rebuilt panel, when the run took it away. */
  Exercise.prototype.refocus = function (origin, goal) {
    var here = document.activeElement;
    if (here && here !== document.body) return;
    var field = goal === null ? null
      : this.panel.querySelector('.agda-goal__field[data-goal="' + goal + '"]')
        || this.panel.querySelector(".agda-goal__field");
    if (field) { field.focus(); return; }
    if (origin && origin.isConnected && !origin.disabled) origin.focus();
  };

  /* Agda reports a position as `File.agda:10.1-11.36`: line.column to
   * line.column, the second line omitted when the span is on one. */
  function position(text, file) {
    var name = file.replace(/[.]/g, "\\.");
    var m = text.match(new RegExp(name + ":(\\d+)\\.(\\d+)-(?:(\\d+)\\.)?(\\d+)"));
    if (!m) return null;
    return {
      line: +m[1], column: +m[2],
      endLine: m[3] ? +m[3] : +m[1], endColumn: +m[4],
    };
  }

  /* A line and column into an offset in the box.  Agda's column counts code
   * points and the box counts UTF-16 units; this library's names are mostly
   * astral, so the column is walked in code points and measured in units. */
  function offsetAt(text, line, column) {
    var lines = text.split("\n");
    var n = 0;
    for (var i = 0; i < line - 1 && i < lines.length; i++) n += lines[i].length + 1;
    return n + Array.from(lines[line - 1] || "").slice(0, column - 1).join("").length;
  }

  function tagOf(message) {
    var m = message.match(/\[([A-Za-z.]+)\]/);
    return m ? m[1] : null;
  }

  /* A range from Agda, `{start, end}` with code point `pos`, as offsets. */
  function spanOf(text, range) {
    var at = window.AgdaPaint ? window.AgdaPaint.offsetOf : null;
    if (!range || !at) return null;
    return { from: at(text, range.start.pos), to: at(text, range.end.pos) };
  }

  /* Show what a run found.  `source` is the text sent, and `result.source`
   * the text the run ended with, which a goal command changed. */
  Exercise.prototype.report = function (result, source, action, wall) {
    var self = this;
    var load = result.load;
    var text = result.source;
    /* Recorded first, so that putting the run's text in the box is not
     * taken for an edit that outdates the run. */
    this.checked = text;
    if (result.edited) {
      this.history.push({ before: source, after: text });
      this.replace(text);
    }
    var current = this.editor.value === text;
    this.stale = !current;
    this.output.textContent = "";
    this.output.hidden = true;

    var notes = [];
    var kind;
    var headline;
    var where = null;
    if (!load) {
      kind = "error";
      headline = "The checker ended without an answer";
      if (result.stderr) notes.push(result.stderr);
    } else if (load.error) {
      kind = "error";
      var tag = tagOf(load.error.message);
      headline = "Agda rejected this" + (tag ? ": " + tag : "");
      notes.push(load.error.message);
      where = position(load.error.message, this.file);
    } else if (load.errors.length) {
      /* Errors that do not stop the load: a definition that fails the
       * termination check, or a postulate under `--safe`.  Batch Agda
       * rejects such a file (exit 42), and so does the page. */
      kind = "error";
      var first = tagOf(load.errors[0]);
      headline = "Agda rejected this" + (first ? ": " + first : "");
      load.errors.forEach(function (e) { notes.push(e); });
      where = position(load.errors[0], this.file);
    } else {
      var open = load.goals.length;
      var unsolved = load.hidden.length;
      kind = open || unsolved ? "open" : "ok";
      headline = open ? "Type-correct so far, with " + (open === 1 ? "one goal" : open + " goals") + " open"
        : unsolved ? "Type-correct so far, but Agda could not solve everything"
        : "Module checked, no goals left";
      load.hidden.forEach(function (h) { notes.push("Unsolved: " + h.name + " : " + h.type); });
    }
    if (load) {
      load.notes.forEach(function (n) { notes.push(n); });
      load.warnings.forEach(function (w) { notes.push(w); });
    }

    /* What a goal command said, when it refused or had nothing to do. */
    var said = null;
    if (action && result.action) {
      var a = result.action;
      if (a.error) said = "Agda refused the " + verb(action.op) + " at ?" + action.goal + ": " + a.error.message;
      else if (a.message) said = a.message;
      if (said) { notes.unshift(said); if (kind !== "error") kind = "open"; }
    }

    this.verdict.className = "agda-verdict agda-verdict--" + kind + (current ? "" : " agda-verdict--stale");
    this.verdict.textContent = "";
    this.verdictIsRun = current;
    /* One worker serves every exercise, so a command can wait behind
     * another's run; the time shown is this run's own, and the wait is
     * said beside it (found in review). */
    var waited = wall !== undefined && wall - result.ms > 1000
      ? " (after " + seconds(wall - result.ms) + " waiting for another exercise)" : "";
    this.verdict.appendChild(document.createTextNode(
      (said ? capitalize(verb(action.op)) + " refused · " : "") + headline + " · " + seconds(result.ms) + waited));
    if (where) {
      var go = element("button", "agda-verdict__where",
        "line " + where.line + ", column " + where.column);
      go.type = "button";
      go.setAttribute("aria-label", "Select line " + where.line + ", column " + where.column + " in the editor");
      go.addEventListener("click", function () {
        var value = self.editor.value;
        self.editor.focus();
        self.editor.setSelectionRange(offsetAt(value, where.line, where.column),
                                      offsetAt(value, where.endLine, where.endColumn));
      });
      go.disabled = !current;
      this.verdict.appendChild(document.createTextNode(" · "));
      this.verdict.appendChild(go);
    }
    if (!current) {
      this.verdict.appendChild(document.createTextNode(" · about the text before your edit"));
    }
    if (notes.length) {
      this.output.textContent = notes.join("\n\n");
      this.output.hidden = false;
    }

    /* Agda's own colors for the text it checked, and its goals and error
     * marked in place, when the box still holds that text. */
    if (current && load && window.AgdaPaint) {
      if (load.highlighting.length) this.ranges = window.AgdaPaint.fromAgda(text, load.highlighting);
      this.marks = [];
      if (where) {
        this.marks.push({ from: offsetAt(text, where.line, where.column),
                          to: offsetAt(text, where.endLine, where.endColumn), kind: "error" });
      }
      (load.error ? [] : load.goals).forEach(function (g) {
        var s = spanOf(text, g.range);
        if (s) self.marks.push({ from: s.from, to: s.to, kind: "goal" });
      });
      this.paint();
    }
    /* What the reader typed under each goal survives a run that changed no
     * text: a refused give keeps its expression to be fixed (found in
     * review). */
    var typed = {};
    if (!result.edited) {
      this.panel.querySelectorAll(".agda-goal__field").forEach(function (f) { typed[f.dataset.goal] = f.value; });
    }
    this.renderGoals(load && !load.error ? load.goals : [], result.contexts || {}, text, current, typed);
    if (this.built) this.built.hidden = true;
  };

  function verb(op) {
    return { give: "give", refine: "refine", "case": "case split", have: "type query" }[op] || op;
  }

  function capitalize(s) { return s.charAt(0).toUpperCase() + s.slice(1); }

  /* What a goal holds between `{!` and `!}`, which Emacs sends with a
   * command; the empty string for `?`. */
  function holeContent(text, span) {
    if (!span) return "";
    var hole = text.slice(span.from, span.to);
    var m = hole.match(/^\{!([\s\S]*)!\}$/);
    return m ? m[1].trim() : "";
  }

  /* The goals panel: each goal's type and context, as Emacs's goal-and-
   * context display shows them, and Agda's goal commands under each. */
  Exercise.prototype.renderGoals = function (goals, contexts, text, current, typed) {
    var self = this;
    this.panel.textContent = "";
    this.goals = goals;
    if (!goals.length) { this.panel.hidden = true; return; }
    this.panelNote = element("p", "agda-goals__note", current
      ? (goals.length === 1 ? "The goal, and what is in scope there:" : "The goals, and what is in scope at each:")
      : "These goals are about the text before your edit; Check again to work on them.");
    this.panel.appendChild(this.panelNote);
    goals.forEach(function (g) {
      var info = contexts[g.id];
      var box = element("div", "agda-goal");
      var head = element("p", "agda-goal__head");
      var idButton = element("button", "agda-goal__id", "?" + g.id);
      idButton.type = "button";
      idButton.title = "Select this goal in the editor";
      idButton.className += " agda-goal__command";
      var span = spanOf(text, g.range);
      idButton.addEventListener("click", function () {
        if (!span) return;
        self.editor.focus();
        self.editor.setSelectionRange(span.from, span.to);
      });
      head.appendChild(idButton);
      head.appendChild(document.createTextNode(" "));
      head.appendChild(element("span", "agda-goal__type", info ? info.type : g.type));
      box.appendChild(head);
      if (info && info.have) {
        var have = element("p", "agda-goal__have");
        have.appendChild(element("span", "agda-goal__have-label", "Have "));
        have.appendChild(element("span", "agda-goal__type", info.have));
        box.appendChild(have);
      }
      if (info) {
        var dl = element("dl", "agda-context");
        info.context.forEach(function (e) {
          var dt = element("dt", e.inScope ? "" : "agda-context__hidden", e.name);
          var dd = element("dd", e.inScope ? "" : "agda-context__hidden", e.type);
          if (!e.inScope) dd.appendChild(element("span", "agda-context__note", " (not in scope)"));
          dl.appendChild(dt);
          dl.appendChild(dd);
        });
        box.appendChild(dl);
      }

      /* The commands, as Emacs's C-c C-SPC, C-c C-r, C-c C-c and C-c C-.:
       * what they act on is the field, which starts with what the goal holds. */
      var form = element("div", "agda-goal__commands");
      var fieldId = self.editor.id + "-goal-" + g.id;
      var fieldLabel = element("label", "agda-goal__label", "Expression or variables for ?" + g.id);
      fieldLabel.setAttribute("for", fieldId);
      var field = element("input", "agda-goal__field");
      field.id = fieldId;
      field.type = "text";
      field.spellcheck = false;
      field.setAttribute("autocapitalize", "off");
      field.setAttribute("autocomplete", "off");
      field.dataset.goal = String(g.id);
      field.value = typed && typed[g.id] ? typed[g.id] : holeContent(text, span);
      field.placeholder = "an expression, or variables to split on";
      field.addEventListener("input", function () {
        if (window.AgdaInput) window.AgdaInput.commit(field);
      });
      field.addEventListener("focus", function () { self.target = field; });
      field.addEventListener("keydown", function (event) {
        if (event.key === "Enter") { event.preventDefault(); give.click(); }
      });
      form.appendChild(fieldLabel);
      form.appendChild(field);
      var commands = [
        ["give", "Give", "Fill the goal with the expression (Emacs: C-c C-SPC)"],
        ["refine", "Refine", "Apply the expression to new goals, or, with none, introduce a constructor or a λ (C-c C-r)"],
        ["case", "Case split", "Split on the named variables (C-c C-c)"],
        ["have", "Type of", "The type of the expression in this goal's context, beside the goal's (C-c C-.)"],
      ];
      var give = null;
      commands.forEach(function (c) {
        var b = button(c[1], "agda-goal__command");
        b.title = c[2];
        if (!current) { b.disabled = true; b.dataset.stale = "1"; }
        b.addEventListener("click", function () {
          var value = field.value.trim();
          if ((c[0] === "give" || c[0] === "have") && value === "") {
            field.focus();
            self.tell("error", capitalize(verb(c[0])) + " needs an expression in the field for ?" + g.id + ".");
            return;
          }
          self.command(c[0], g.id, value, c[1]);
        });
        if (c[0] === "give") give = b;
        form.appendChild(b);
      });
      if (!current) { idButton.disabled = true; idButton.dataset.stale = "1"; }
      box.appendChild(form);
      self.panel.appendChild(box);
    });
    this.panel.hidden = false;
  };

  /* ---- Wiring ---------------------------------------------------------- */

  /* The session belonging to the page most recently wired, so that leaving
   * it can end it (Material's `document$` fires on every page). */
  var active = null;

  function playground() {
    if (active && !active.exercises.some(function (e) { return e.root.isConnected; })) {
      active.close();
      active = null;
    }
    var roots = Array.prototype.slice.call(document.querySelectorAll(".agda-exercise"))
      .filter(function (root) { return root.querySelector(".agda-exercise__gate"); });
    if (!roots.length) return;

    var missing = unsupported();
    if (missing.length) {
      roots.forEach(function (root) {
        var gate = root.querySelector(".agda-exercise__gate");
        if (gate.dataset.wired) return;
        gate.dataset.wired = "1";
        gate.after(element("p", "agda-exercise__status",
          "This browser has no " + missing.join(" and no ") +
          ", so the checker cannot run here.  The exercise and its goal above are the whole of it."));
      });
      return;
    }

    var workerUrl = new URL(roots[0].querySelector(".agda-exercise__gate").dataset.worker,
                            document.baseURI).href;
    var session = new Session(workerUrl);
    active = session;
    roots.forEach(function (root) {
      if (root.dataset.wired) return;
      root.dataset.wired = "1";
      var exercise = new Exercise(root, session);
      session.exercises.push(exercise);
      exercise.renderGate();
    });
  }

  if (typeof document$ !== "undefined") {
    document$.subscribe(playground);
  } else {
    document.addEventListener("DOMContentLoaded", playground);
  }
})();
