---
title: Playground
description: >-
  Agda 2.8.0 running in your browser tab, on the library's own code: open a
  goal, see its type and what is in scope there, and fill it with Agda's own
  goal commands.
---

# Playground

This page runs Agda 2.8.0, the type checker this library is written in, in
your browser tab, on the library's own code.  It is not a recording and there
is no server: the checker is Agda itself, compiled to WebAssembly, and what it
says about your proof is what it would say in Emacs.

Each exercise below is a definition from the library with its body taken out.
Load the checker and the exercise opens in an editor.  Check it, and Agda shows
each open goal's type and what is in scope there, the way agda-mode's
goal-and-context display does.  Under each goal are agda-mode's goal commands:
give, refine, case split, and the type of an expression at the goal.

Nothing is downloaded until you ask, and each exercise says how much it would
download before you press its button.  Nothing you type leaves this tab.

## How to use it

+  **Check** (or Ctrl and Enter in the editor) asks Agda about the text in the
   editor and lists the goals it leaves.  Each goal shows its type, then its
   context, newest binding first; a binding marked "not in scope" is one Agda
   knows about but you cannot name there, such as an implicit argument you did
   not bind.
+  **The field under a goal** holds what the goal holds when you write
   `{! ... !}` in the editor, and you can also type into it directly.
   **Give** fills the goal with that expression, if it has the goal's type.
   **Refine** applies it to as many new goals as it needs; with the field
   empty, it introduces a constructor or a λ.  **Case split** splits on the
   variables named in the field.  **Type of** shows the expression's type
   beside the goal's, without changing anything.
+  **Undo** puts back the text from before the last give, refine or case
   split, and **Reset** puts back the exercise as it was.
+  **Unicode** is typed as in Emacs: a backslash, the name, and a space.
   `\to` gives →, `\MIA` gives 𝑨, `\bD` gives 𝔻, and the buttons under the
   editor insert the characters these exercises use, each telling you its
   sequence.

Every command is one run of the checker: it loads your text, does what you
asked, and reports every goal.  The first exercise answers in a fraction of a
second; the last loads more of the library and takes several seconds a
command.

## Grafting

A term over a set of variables `Y` is a tree whose leaves are variables
(`ℊ y`, for "generator") and whose nodes are operation symbols applied to
subterms (`node f ts`); [Overture.Terms.Basic][] defines them.  Given a
term `t` and a way `σ` of turning each variable into a term over `X`,
*grafting* replaces each leaf `ℊ y` of `t` by the term `σ y`.  It is
substitution, the bind of the term monad, and [Overture.Terms.Interpretation][]
defines it as `graft`.

Try a **Case split** on `t` first: Agda writes the two clauses, one per
constructor, each with a goal of its own, and names the new variables after
the constructors' own arguments (`x`, `f` and `t`).

<!-- playground: Graft -->

??? question "Three hints"

    **The leaf**.  In the clause for `ℊ x`, the goal is a term over `X` and
    `σ x` is one.  Write `σ x` in the field and press **Give**.

    **The node**.  In the clause for `node f t`, the answer is a node with
    the same symbol.  **Refine** with `node f` leaves one goal: what to put
    at each argument position.

    **The arguments**.  At position `i` the subterm is `t i`, and grafting
    it is a recursive call: give `λ i → graft (t i) σ`.

## Interpretations

An interpretation `I` of one signature in another sends each operation symbol
`f` of the first to a term of the second, a *derived operation*, whose
variables are `f`'s argument positions.  It acts on whole terms: `I ✦ t`
rewrites a term `t` of the first signature into a term of the second over the
same variables.  Variables stay where they are; at a node, the translated
subterms are grafted into the derived operation `I f`.

This exercise imports `graft` and `Interpretation` from
[Overture.Terms.Interpretation][] itself, and that module's other imports
make this download larger than the last one.

<!-- playground: Interpret -->

??? question "Two hints"

    **Split, then the leaf**.  **Case split** on `t`.  A variable translates
    to itself: give `ℊ x` (type `\Mcg` for ℊ).

    **The node**.  Use **Type of** on `I f` to see that it is a term whose
    variables are the argument positions of `f`.  Graft onto it the
    translated subterms: `graft (I f) (λ i → I ✦ t i)`.

## Homomorphisms compose

The heart of the library: algebras over a signature `𝑆` on setoids, and
homomorphisms between them.  A homomorphism from `𝑨` to `𝑩` is a setoid map
`g` that is *compatible* with every operation: applying `g` to the result of
an operation `f` on arguments `a` gives, up to `𝑩`'s equality, the same as
applying `f` in `𝑩` to the images of the arguments.  The composite of two
homomorphisms is a homomorphism; [Setoid.Homomorphisms.Properties][] proves it
as `⊙-is-hom`.

Look at the goal before you write anything.  It is an equation in `𝑪`'s
setoid, and its context holds the two compatibility proofs you need.  This
exercise loads 244 modules of the library and the standard library, and that
is the price: a large download, and several seconds for every command.

<!-- playground: Compose -->

??? question "Two hints"

    **Two steps**.  The left side is `h` applied to `g` applied to the
    operation in `𝑨`; the right side is the operation in `𝑪` applied to the
    images.  Go there through `h` applied to the operation in `𝑩` applied
    to the images under `g`: give `trans ? ?` and fill the two goals.

    **Each step**.  The first is `g`'s compatibility, carried through `h`:
    `cong h (compatible ghom)`.  The second is `h`'s own compatibility:
    `compatible hhom`.

## What the downloads are

<!-- playground-assets -->

An image is the part of the library and of the Agda standard library that
one exercise imports, each module's source with its compiled interface, so
that Agda checks only your text and loads the rest.  The sizes differ by two
orders of magnitude, and almost none of the difference is this library:
`Overture.Signatures.Morphisms` imports the standard library's
propositional equality, which brings most of its algebra hierarchy, and
`Setoid.Algebras.Basic` imports the whole `Overture`, which brings the
standard library's properties of the natural numbers, lists and finite
sets.  A larger image runs a smaller exercise too, so whichever you load
first, a smaller exercise after it downloads nothing more.

## How it works

The checker is `agda` from [agda-wasm-dist][], compiled to WebAssembly by
its authors and shipped here unmodified.  It runs in a worker, over a small
filesystem that lives in memory for the length of one command: your text, and
the image's files.  Agda's interaction protocol, the one agda-mode speaks, is
how the page asks it questions.  Each command is one run of the checker, from
its start, and the page decides each next question from Agda's last answer, so
a give is followed by a reload of the text it produced and by a query for each
goal that is left.

That shape is why the page needs no special support from the server: nothing
is shared between threads, nothing waits on input, and the page works on any
static host.  It is also why a command costs a whole load: the checker does not
stay running between commands.  [ADR-011][] records the decisions and the
measurements behind them, including the closure of every image.

## Credits

+  [Agda][agda] 2.8.0 and the [Agda standard library][agda-stdlib] 2.3, under
   their MIT-style licenses.
+  [agda-web/agda-wasm-dist][agda-wasm-dist], MIT, Copyright 2024 Agda Web:
   the build of Agda this page runs.
+  [agda-web/als-demo][als-demo], MIT, Copyright 2026 Andy Pan: the first
   demonstration of Agda in a browser, by way of the Agda language server.  No
   code of it is used here.
+  [plfa.isotopy.xyz][plfa-playground-live], built from
   [SeungheonOh/plfa-playground][plfa-playground] (MIT, Copyright 2026 Andy
   Pan): the reference implementation of an interactive Agda in a browser, for
   *Programming Language Foundations in Agda*.
+  The WASI host, worker, input method and editor are adapted from the
   [playground of williamdemeo.org][williamdemeo-playground] (MIT, Copyright
   2026 William DeMeo).

The [notices][playground-notice] for everything the page downloads are
published beside the files.

[agda]: https://github.com/agda/agda
[agda-stdlib]: https://github.com/agda/agda-stdlib
[agda-wasm-dist]: https://github.com/agda-web/agda-wasm-dist
[als-demo]: https://github.com/agda-web/als-demo
[plfa-playground-live]: https://plfa.isotopy.xyz/
[plfa-playground]: https://github.com/SeungheonOh/plfa-playground
[williamdemeo-playground]: https://williamdemeo.org/playground/
[playground-notice]: assets/agda/NOTICE.txt
