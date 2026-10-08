# Installing agda-algebras

This document describes how to set up a development environment for the agda-algebras library.  Until Agda 2.9.0 and its standard library are released, the toolchain is available only through `nix develop`: the flake pins a pre-release Agda and a patched standard library 2.3.  Options 2 to 4 below install the previous toolchain, Agda 2.8.0 and standard-library 2.3, under which the library still checks today; CI no longer tests it.

## Requirements

+  [Agda](https://agda.readthedocs.io) 2.9.0, not yet released: the flake pins agda/agda at commit [`da66a8c`](https://github.com/agda/agda/commit/da66a8c75f11d10699a6b38b261efdf244b66f2a), the `nightly` of 2026-10-05, and builds it from source
+  [standard-library](https://github.com/agda/agda-stdlib) 2.3 with the five changes it needs under Agda 2.9.0: [formalverification/agda-stdlib](https://github.com/formalverification/agda-stdlib), tag [`v2.3-agda-2.9.0`](https://github.com/formalverification/agda-stdlib/releases/tag/v2.3-agda-2.9.0), whose release notes list them
+  GNU Make
+  A text editor with Agda support (Emacs with `agda-mode`, VSCode with `banacorn.agda-mode`, or equivalent)

Agda versions before 2.8.0, and standard libraries before 2.3, are not supported on `master`.  If you must work with an older configuration, check out a pre-2.0 tag.

---

## Option 1 (required for now): Nix

Install Nix from [https://nixos.org/download.html](https://nixos.org/download.html), then enable flakes by adding the following to `~/.config/nix/nix.conf`:

```
experimental-features = nix-command flakes
```

Clone the repository and enter the development shell:

```bash
git clone https://github.com/ualib/agda-algebras.git
cd agda-algebras
nix develop
```

The `nix develop` command will download and build (on first invocation) the pinned versions of Agda and the standard library, and drop you in a shell where:

+  `agda` is on `PATH` and points to 2.9.0
+  the patched standard-library 2.3 is registered via a project-local `AGDA_DIR` at `.agda/`
+  any `~/.config/agda/libraries` entries on the host are ignored for the duration of the shell

The first `nix develop` builds Agda 2.9.0 from source, and checks the standard library with it, unless Nix can fetch them from the formalverification binary cache on [Cachix](https://www.cachix.org/), which this repository's CI uses.  Built here, they took about six and a half minutes on a 20-core workstation, with the build's memory peaking near 8 GiB (2026-10-07); a machine with fewer cores takes longer.  To fetch them instead, run `cachix use formalverification`, or add the following lines to your Nix configuration (`/etc/nix/nix.conf`, or `~/.config/nix/nix.conf` if you are a trusted user):

```
extra-substituters = https://formalverification.cachix.org
extra-trusted-public-keys = formalverification.cachix.org-1:KG/AJuuli2F4/bA56rUYC9V8ZE/Zw6iZjxJEf40cQOo=
```

Inside the shell:

```bash
make check   # type-check the entire library
make site    # build the documentation site to ./site
make serve   # preview the documentation site at http://127.0.0.1:8000
make clean   # remove build artifacts
```

To exit the shell, type `exit` or Ctrl-D.

### The pins, and moving them

`flake.lock` pins nixpkgs and Agda's own flake, whose URL in `flake.nix` names a commit of agda/agda, so `nix flake update` moves nixpkgs but never Agda.  The standard library is pinned in `flake.nix` by `stdlibRev` and `stdlibHash`.  To move it, set `stdlibRev` to the new commit, put `nixpkgs.lib.fakeHash` in `stdlibHash`'s place, run `nix build`, and copy the hash the error prints after `got:`; or ask Nix for the hash directly:

```bash
nix flake prefetch --json github:formalverification/agda-stdlib/<commit> | jq -r .hash
```

A `hash mismatch in fixed-output derivation` error on a pin you did not move means the source is not the one pinned: check the commit before you accept another hash.  Move Agda and the standard library together, since each standard library checks under a narrow range of Agda versions, and once both are released, return to the nixpkgs packages, as the comment at the top of `flake.nix` says.

### Editor integration under Nix

`agda-mode` is available inside the Nix shell. The simplest pattern is to launch your editor from within `nix develop`. If you use Emacs, `M-x load-library RET agda2-mode RET` will pick up the wrapped Agda. If you use VSCode with the `banacorn.agda-mode` extension, the extension's "Agda Path" setting can be pointed at the `agda` inside the Nix shell (use `which agda` to find the absolute path).

Contributors who prefer a persistent editor configuration across shells may find [`nix-direnv`](https://github.com/nix-community/nix-direnv) useful for auto-entering the shell when they `cd` into the repo.

An Emacs launched from one checkout's shell checks every file against that
checkout, so several checkouts (worktrees, or another Agda project beside this
one) need one more step: see
[Emacs with several checkouts](CONTRIBUTING.md#emacs-with-several-checkouts).

---

> **Options 2 to 4 install the previous toolchain**, Agda 2.8.0 and standard-library 2.3, unpatched.  They stay here until Agda 2.9.0 and a standard library for it are released, when they will move to those versions.  The library still checks under 2.8.0 today, but CI tests only the toolchain the flake pins.

## Option 2: Agda's official Python installer

As of 2.8.0, Agda is a self-contained single binary distributed via the Python Package Index. This is the simplest non-Nix path:

```bash
pipx install agda==2.8.0
```

(or `pip install --user agda==2.8.0` if you don't have [pipx](https://pipx.pypa.io/)).

Then install standard-library 2.3:

```bash
git clone --branch v2.3 --depth 1 https://github.com/agda/agda-stdlib.git ~/agda-stdlib-2.3
mkdir -p ~/.config/agda
echo "$HOME/agda-stdlib-2.3/standard-library.agda-lib" >> ~/.config/agda/libraries
echo "standard-library-2.3" >> ~/.config/agda/defaults
```

Verify the installation from a clone of agda-algebras:

```bash
git clone https://github.com/ualib/agda-algebras.git
cd agda-algebras
make check
```

---

## Option 3: Prebuilt binary from the Agda GitHub release

Prebuilt binaries for Linux, macOS, and Windows are available on the [Agda 2.8.0 release page](https://github.com/agda/agda/releases/tag/v2.8.0). Download the appropriate archive, extract the `agda` binary, and place it somewhere on your `PATH`.

On macOS, prebuilt binaries are not notarized; you may need to remove the quarantine attribute before they run. See the [Agda 2.8.0 installation documentation](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html) for details.

Set up the standard library as in Option 2.

---

## Option 4: Build from source via cabal

```bash
cabal update
cabal install Agda-2.8.0 --program-suffix=-2.8.0
```

Then run `agda-2.8.0 --emacs-mode setup` to configure Emacs. (Note: as of Agda 2.8.0, the `agda-mode` executable has been superseded by `agda --emacs-mode`; your editor configuration may need updating. See the [Agda 2.8.0 changelog](https://hackage.haskell.org/package/Agda-2.8.0/changelog) for details.)

Set up the standard library as in Option 2.

---

## Verifying the installation

From a clone of agda-algebras:

```bash
agda --version           # "Agda version 2.9.0" in nix develop; 2.8.0 after Options 2 to 4
make check               # should run to completion without errors
```

`make check` takes a few minutes on a laptop.

---

## Troubleshooting

**Agda can't find standard-library**.  Inside `nix develop`, the shell writes a project-local libraries file that should Just Work. Outside the Nix shell, verify that `~/.config/agda/libraries` references your standard-library 2.3 installation (note that older Agda versions used `~/.agda/libraries`; 2.8.0 uses `~/.config/agda/` but falls back to `~/.agda/` for backward compatibility).

**Build is slow**.  The library is large.  From an empty `_build` directory, `make check` checks every module of the library, which takes about a minute and a half on a recent workstation when the standard library's interfaces already exist (the Nix shell provides them prebuilt), and longer when the standard library has to be checked too.  Incremental rebuilds (changing one module) are much faster thanks to Agda's interface-file caching.

For other issues, please [open a GitHub issue](https://github.com/ualib/agda-algebras/issues).


