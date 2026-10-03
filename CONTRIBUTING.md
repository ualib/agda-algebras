# Contributing to agda-algebras

Thank you for your interest in contributing to `agda-algebras`.  This document explains how to set up a development environment, the workflow we use, and the conventions that make contributions easier to review and merge.

The library is currently under active reconstruction for the 3.0 release.  Expect some rough edges; please report them via GitHub issues.

---

## Before you start

`agda-algebras` is organized around a specific set of design principles that shape how we review contributions:

+  **Proof terms are first-class training data**.  We intend this library to serve as a high-quality corpus for machine-learning work on formal proofs.  Contributions should be written with that in mind: prefer small focused theorems over large ones, named helper lemmas over opaque rewrite chains, and rich natural-language comments alongside formal statements.
+  **One canonical form per concept**.  If a concept is already defined somewhere in the library, please use or re-export the existing definition rather than defining a parallel version with slightly different notation.  When in doubt, open a design-discussion issue first.
+  **Stable public APIs with deprecation cycles**.  Breaking changes to names or signatures in publicly-used definitions should go through at least one minor-version deprecation cycle.  Internal helpers (not re-exported, not documented) can change without notice.
+  **The Setoid tree is canonical**.  `src/Setoid/` is the canonical active development tree for 3.0.  `src/Base/` contains the pre-3.0 original development and shared foundations still in use; parts of it will be frozen as `Legacy/Base/` during the 3.0 reconstruction (see M2).  The planned `Classical/` tree (specific algebraic theories, tracked in M3) and `Cubical/` tree (long-term 4.0 target, tracked in M5) do not yet exist.  New contributions usually belong in `Setoid/`; if you're not sure where something fits, open a design-discussion issue first.

See [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md) for the milestone roadmap.

---

## Development environment

### Recommended: Nix

```bash
git clone https://github.com/ualib/agda-algebras.git
cd agda-algebras
nix develop
make check        # the library and the frozen Legacy tree
```

This pins Agda 2.8.0 and standard-library 2.3 automatically via the repository's flake.  See [`INSTALL.md`](INSTALL.md) for a walkthrough and non-Nix alternatives.

### Editor

We recommend Emacs with `agda-mode` or VSCode with the `banacorn.agda-mode` extension.  Launch your editor from inside `nix develop` so the pinned Agda is on `PATH`; if you keep several checkouts, read the next section.

### Emacs with several checkouts

`nix develop` writes, at the root of the checkout it is entered in, the
library registry `.agda/libraries` and a self-contained wrapper
`.agda/bin/agda` that runs the pinned Agda with that registry.  agda-mode runs
one Agda process for all buffers, and reads `agda2-program-name` and
`agda2-program-args` only when it starts that process, so the process checks
every file against the checkout it was started for.  A file from another
worktree then fails with `ModuleDefinedInOtherFile`, because the registry
finds the file's module in the first checkout, and a file of another Agda
project fails too.

The following, added to your Emacs configuration (`~/.config/doom/config.el`
under Doom Emacs, your `init.el` otherwise), runs each checkout's own wrapper,
and restarts Agda when `C-c C-l` comes from a different checkout from the one
the running process was started for.  Emacs need not be started inside
`nix develop`.

```elisp
;; Agda per checkout.  One Agda process serves every buffer, and agda-mode
;; reads `agda2-program-name' and `agda2-program-args' only when it starts
;; that process, so the process keeps the library registry of the checkout it
;; was started for.  This runs the wrapper .agda/bin/agda that the checkout's
;; dev shell wrote, which names that checkout's registry, and restarts the
;; process when C-c C-l comes from a different checkout.  Files outside such a
;; checkout keep `agda2-program-name' as configured.  agda-mode starts Agda
;; from the mode's body, before any hook or directory-local variable applies,
;; so the settings are bound around `agda2-restart' itself.
(defvar my/agda-process-root nil
  "The checkout the running Agda process was started for, or nil.")

(defun my/agda-checkout (file)
  "The list (ROOT PROGRAM ARGS AGDA-DIR) for FILE's checkout, or nil."
  (when-let* ((root (locate-dominating-file file ".agda/bin/agda")))
    (list root (expand-file-name ".agda/bin/agda" root) nil
          (expand-file-name ".agda" root))))

(defun my/agda-restart (restart &rest args)
  "Around `agda2-restart': start the Agda of the current buffer's checkout."
  (let ((checkout (and (buffer-file-name) (my/agda-checkout (buffer-file-name)))))
    (setq my/agda-process-root (car checkout))
    (if (null checkout)
        (apply restart args)
      (pcase-let ((`(,_root ,program ,program-args ,agda-dir) checkout))
        (let ((agda2-program-name program)
              (agda2-program-args program-args)
              (process-environment (cons (concat "AGDA_DIR=" agda-dir)
                                         process-environment)))
          (apply restart args))))))

(defun my/agda-load (load &rest args)
  "Around `agda2-load': restart Agda first if the buffer is in another checkout."
  (let ((root (and (buffer-file-name) (car (my/agda-checkout (buffer-file-name))))))
    (unless (equal root my/agda-process-root)
      (agda2-restart))
    (apply load args)))

(with-eval-after-load 'agda2-mode
  (advice-add 'agda2-restart :around #'my/agda-restart)
  (advice-add 'agda2-load :around #'my/agda-load))
```

A few facts complete the setup, as follows:

+  Enter `nix develop` once in each new worktree, and again when its
   `flake.lock` moves, to write the wrapper.
+  The wrapper calls an Agda in the Nix store by its path.  If garbage
   collection removes that Agda, agda-mode reports its version as "unknown";
   entering `nix develop` there again restores it.
+  agda-mode refuses an Agda whose version differs from its own
   (`agda2-version`), so use agda-mode 2.8.0, the version this repository
   pins; inside `nix develop`, `agda-mode locate` prints the path of its
   `agda2.el`.
+  The same snippet with one more clause, for checkouts of
   [agda-native-air](https://github.com/formalverification/agda-native-air),
   is in that repository's
   [`CONTRIBUTING.md`](https://github.com/formalverification/agda-native-air/blob/main/CONTRIBUTING.md#editing-agda-in-emacs);
   use that version if you work in both.

---

## Contribution workflow

Standard [fork-and-pull-request](https://gist.github.com/Chaser324/ce0505fbed06b947d962) workflow.

1.  Fork the repository to your GitHub account.
2.  Clone your fork and create a topic branch: `git checkout -b NNN-short-description`, where `NNN` is the issue number you're addressing.
3.  Make commits that each do one coherent thing.  Each commit message should have a single-line summary followed by an explanatory paragraph when the change is non-trivial.  Reference the issue in the commit message with `Part of #NNN`.
4.  Run `make check` locally.  Your PR must type-check.
5.  Open a pull request against `master`.  The PR title should match the issue title (e.g. `[M1-3] Add community-health files`).
6.  Be prepared to iterate based on review feedback.

### Commits vs. pull requests

Small, single-concern PRs are much easier to review than large ones.  If a change naturally decomposes into independent pieces, consider opening a sequence of smaller PRs rather than one big one — even if they land on the same branch, they can often be split for reviewability.

### Working against issues

If no issue exists for the change you want to make, **please open one first**, especially for non-trivial changes.  This gives maintainers a chance to flag design concerns before you invest time writing code.  The issue templates under `.github/ISSUE_TEMPLATE/` are there to help.

---

## Code conventions

This section describes only the most important conventions contributors are expected to follow.  For a more complete style guide, see [`docs/STYLE_GUIDE.md`](./docs/STYLE_GUIDE.md).  Please follow the style described in that document; when in doubt, or if something isn't covered in the style guide, ask in the PR.

### File pragma

Every `.agda` source file begins with:

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
```

plus `module X.Y.Z where` on the next non-comment line.

As of the 3.0 reconstruction, all of `src/` uses `--cubical-compatible`.  When the 3.0 consolidation freezes pre-reconstruction content as `Legacy/Base/` (see M2), the frozen tree will retain its historical `--without-K` pragma for stability, but new contributions will not land there.


### Naming

+  **Definitions** are named in the `lowerCamelCase` or `hyphen-case` style depending on local convention in the surrounding module.
+  **Types** start with an uppercase letter.
+  **Predicates** are typically named `IsX` for "X-ness of a single thing" (e.g. `IsHomomorphism`) and `X` for "the type of things with property X" (e.g. `Homomorphism`).
+  Avoid synonyms.  If the concept is already called `Hom` elsewhere, call it `Hom` here too.

### Comments

Every public definition should have a prose comment block immediately above it explaining what the definition is and why one would use it.  For example:

```agda
-- | `Hom 𝑨 𝑩` is the type of homomorphisms from 𝑨 to 𝑩.  A homomorphism
-- | is a function on carriers that commutes with every basic operation
-- | of the signature.  See also: `IsHomomorphism` for the predicate
-- | form, and `Base.Homomorphisms.Isomorphisms` for the isomorphism
-- | variant.
Hom : (𝑨 : Algebra α) (𝑩 : Algebra β) → Type _
Hom 𝑨 𝑩 = ...
```

These comments are not decoration — they are part of the training corpus we hope agda-algebras will become.  Think of each one as a short paragraph that would help a mathematician approaching this concept for the first time.

### Module organization

+  One concept per module where feasible.
+  Module headers name the mathematical object being developed, not the technical construction (prefer `Setoid.Algebras.Congruences` over `Setoid.Algebras.Records.QuotientRecords`).

### Imports

+  Tight `using (...)` clauses, not bare `open import X`.
+  Group imports into blocks: stdlib first, then our own modules, with a blank line between.

---

## Mathematical contributions

If you're adding a theorem or definition that's more than a trivial rearrangement:

+  Cite the mathematical source in a comment.  Textbook and page number, or paper and theorem number.  This helps future readers and provides provenance for the training corpus.
+  If the theorem has a well-known name (Birkhoff's HSP theorem, Jónsson's theorem, etc.), use it.
+  If it's novel — as opposed to a formalization of existing mathematics — say so explicitly in the comment, and consider coordinating with a maintainer before the PR.

---

## Questions

+  **Technical question about Agda or the library**: open a GitHub discussion or ask in the PR itself.
+  **Design-level question** ("should this be a record or a Σ-type?"): open an issue with the `design-discussion` label.
+  **Just want to chat**: the Agda Zulip server has an `#agda-algebras` channel (informal, low-traffic).

---

## Code of Conduct

By contributing, you agree to abide by the [Code of Conduct](CODE_OF_CONDUCT.md).


