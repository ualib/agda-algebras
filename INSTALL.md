# Installing agda-algebras

This document describes how to set up a development environment for the agda-algebras library.  The library targets Agda 2.9.0 and standard-library 2.4.1.  `nix develop` (Option 1) gives exactly the toolchain CI tests; Options 2 and 3 install the same versions without Nix.

## Requirements

+  [Nix](https://nixos.org) 2.28 or later, with flakes enabled (Option 1, recommended)
+  [Agda](https://agda.readthedocs.io) [2.9.0](https://github.com/agda/agda/releases/tag/v2.9.0); nixpkgs does not package it yet, so the flake pins agda/agda at the release's tag and builds it from source
+  [standard-library](https://github.com/agda/agda-stdlib) [2.4.1](https://github.com/agda/agda-stdlib/releases/tag/v2.4.1), the release made for Agda 2.9.0
+  GNU Make
+  A text editor with Agda support (Emacs with `agda-mode`, VSCode with `banacorn.agda-mode`, or equivalent)

Agda versions before 2.9.0, and standard libraries before 2.4, are not supported on `master`.  If you must work with an older configuration, check out a pre-2.0 tag.

---

## Option 1 (recommended): Nix

Install Nix 2.28 or later from [https://nixos.org/download.html](https://nixos.org/download.html) (`nix --version` says which you have), then enable flakes by adding the following to `~/.config/nix/nix.conf`:

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
+  standard-library 2.4.1 is registered via a project-local `AGDA_DIR` at `.agda/`
+  any `~/.config/agda/libraries` entries on the host are ignored for the duration of the shell

The first `nix develop` builds Agda 2.9.0 from source, and checks the standard library with it, unless Nix can fetch them from the formalverification binary cache on [Cachix](https://www.cachix.org/), which this repository's CI uses.  Built on a 20-core workstation, they took 22 minutes on 2026-11-24, when several of Agda's Haskell dependencies had to be built as well (six and a half minutes for the October pre-release, with those dependencies cached and the build's memory peaking near 8 GiB); a machine with fewer cores takes longer.  To fetch them instead, run `cachix use formalverification`, or add the following lines to your Nix configuration (`/etc/nix/nix.conf`, or `~/.config/nix/nix.conf` if you are a trusted user):

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
nix flake prefetch --json github:agda/agda-stdlib/<commit> | jq -r .hash
```

A `hash mismatch in fixed-output derivation` error on a pin you did not move means the source is not the one pinned: check the commit before you accept another hash.  Move Agda and the standard library together, since each standard library checks under a narrow range of Agda versions, and once nixpkgs packages Agda 2.9.0, return to the nixpkgs packages, as the comment at the top of `flake.nix` says.

No public cache holds the pinned Agda, which Agda's own flake builds from source, so after moving either pin, push the dev shell's closure to the formalverification cache before CI runs, or CI's type-check job has to build Agda within its 30 minutes.  The push needs the cache's write token (`cachix authtoken`):

```bash
nix develop --profile /tmp/aa-dev -c true && cachix push formalverification /tmp/aa-dev
```

### Editor integration under Nix

`agda-mode` is available inside the Nix shell. The simplest pattern is to launch your editor from within `nix develop`. If you use Emacs, `M-x load-library RET agda2-mode RET` will pick up the wrapped Agda. If you use VSCode with the `banacorn.agda-mode` extension, the extension's "Agda Path" setting can be pointed at the `agda` inside the Nix shell (use `which agda` to find the absolute path).

Contributors who prefer a persistent editor configuration across shells may find [`nix-direnv`](https://github.com/nix-community/nix-direnv) useful for auto-entering the shell when they `cd` into the repo.

An Emacs launched from one checkout's shell checks every file against that
checkout, so several checkouts (worktrees, or another Agda project beside this
one) need one more step: see
[Emacs with several checkouts](CONTRIBUTING.md#emacs-with-several-checkouts).

---

## Option 2: Prebuilt binary from the Agda GitHub release

Prebuilt binaries for Linux, macOS, and Windows are available on the [Agda 2.9.0 release page](https://github.com/agda/agda/releases/tag/v2.9.0). Download the appropriate archive, extract the `agda` binary, and place it somewhere on your `PATH`.

On macOS, prebuilt binaries are not notarized; you may need to remove the quarantine attribute before they run. See the [Agda 2.9.0 installation documentation](https://agda.readthedocs.io/en/v2.9.0/getting-started/installation.html) for details.

Then install standard-library 2.4.1:

```bash
git clone --branch v2.4.1 --depth 1 https://github.com/agda/agda-stdlib.git ~/agda-stdlib-2.4.1
mkdir -p ~/.config/agda
echo "$HOME/agda-stdlib-2.4.1/standard-library.agda-lib" >> ~/.config/agda/libraries
echo "standard-library-2.4" >> ~/.config/agda/defaults
```

Verify the installation from a clone of agda-algebras:

```bash
git clone https://github.com/ualib/agda-algebras.git
cd agda-algebras
make check
```

Agda's Python installer on PyPI (`pip install agda`) offers nothing later than Agda 2.7.0.1 (checked 2026-11-24), so it cannot install the Agda this library needs.

---

## Option 3: Build from source via cabal

```bash
cabal update
cabal install Agda-2.9.0 --program-suffix=-2.9.0
```

Then run `agda-2.9.0 --emacs-mode setup` to configure Emacs (since Agda 2.8.0, `agda --emacs-mode` replaces the `agda-mode` executable; see the [Agda changelog](https://hackage.haskell.org/package/Agda-2.9.0/changelog)).

Set up the standard library as in Option 2.

---

## Verifying the installation

From a clone of agda-algebras:

```bash
agda --version           # "Agda version 2.9.0"
make check               # should run to completion without errors
```

`make check` takes a few minutes on a laptop.

---

## Troubleshooting

**`NAR hash mismatch in input 'github:agda/agda/…'`**.  Your Nix is probably older than 2.28.  Agda's tree holds six empty directories, the paths of its submodules, and Nix 2.26.3 drops them when it unpacks the tree, so it computes another hash than the one `flake.lock` records (Nix 2.28.6 and later keep them).  Upgrade Nix to 2.28 or later: for an installation made by the official installer, `nix upgrade-nix` does it.

**Agda can't find standard-library**.  Inside `nix develop`, the shell writes a project-local libraries file that should Just Work. Outside the Nix shell, verify that `~/.config/agda/libraries` references your standard-library 2.4.1 installation (note that older Agda versions used `~/.agda/libraries`; 2.8.0 and later use `~/.config/agda/` but fall back to `~/.agda/` for backward compatibility).

**Build is slow**.  The library is large.  From an empty `_build` directory, `make check` checks every module of the library, which takes about a minute and a half on a recent workstation when the standard library's interfaces already exist (the Nix shell provides them prebuilt), and longer when the standard library has to be checked too.  Incremental rebuilds (changing one module) are much faster thanks to Agda's interface-file caching.

For other issues, please [open a GitHub issue](https://github.com/ualib/agda-algebras/issues).


