# Installing agda-algebras

This document describes how to set up a development environment for the agda-algebras library. The **recommended** path is Nix, which pins Agda 2.8.0 and standard-library 2.3 automatically. The alternative paths are for contributors who cannot or prefer not to use Nix.

## Requirements

+  [Agda](https://agda.readthedocs.io) 2.8.0 or later (2.8.0 is what we pin)
+  [standard-library](https://github.com/agda/agda-stdlib) 2.3
+  GNU Make
+  A text editor with Agda support (Emacs with `agda-mode`, VSCode with `banacorn.agda-mode`, or equivalent)

Older versions of Agda or the standard library are not supported on `master`. If you must work with an older configuration, check out a pre-2.0 tag.

---

## Option 1 (recommended): Nix

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

+  `agda` is on `PATH` and points to 2.8.0
+  standard-library 2.3 is registered via a project-local `AGDA_DIR` at `.agda/`
+  any `~/.config/agda/libraries` entries on the host are ignored for the duration of the shell

Inside the shell:

```bash
make check   # type-check the entire library
make html    # generate clickable HTML to ./html/
make clean   # remove build artifacts
```

To exit the shell, type `exit` or Ctrl-D.

### Editor integration under Nix

`agda-mode` is available inside the Nix shell. The simplest pattern is to launch your editor from within `nix develop`. If you use Emacs, `M-x load-library RET agda2-mode RET` will pick up the wrapped Agda. If you use VSCode with the `banacorn.agda-mode` extension, the extension's "Agda Path" setting can be pointed at the `agda` inside the Nix shell (use `which agda` to find the absolute path).

Contributors who prefer a persistent editor configuration across shells may find [`nix-direnv`](https://github.com/nix-community/nix-direnv) useful for auto-entering the shell when they `cd` into the repo.

---

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
echo "standard-library" >> ~/.config/agda/defaults
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
agda --version           # should print "Agda version 2.8.0"
make check               # should run to completion without errors
```

`make check` takes a few minutes on a laptop.

---

## Troubleshooting

**Agda can't find standard-library.** Inside `nix develop`, the shell writes a project-local libraries file that should Just Work. Outside the Nix shell, verify that `~/.config/agda/libraries` references your standard-library 2.3 installation (note that older Agda versions used `~/.agda/libraries`; 2.8.0 uses `~/.config/agda/` but falls back to `~/.agda/` for backward compatibility).

**Warnings about `UnsupportedIndexedMatch`.** These are expected on some of our own pattern-matching definitions under `--cubical-compatible` and are suppressed at the library level via a flag in `agda-algebras.agda-lib`. They do not indicate bugs.

**Build is slow.** The library is large and uses computationally expensive features (`--cubical-compatible` implies full unfolding). A full `make check` is ~5 minutes on a modern laptop. Incremental rebuilds (changing one module) are much faster thanks to Agda's interface-file caching.

For other issues, please [open a GitHub issue](https://github.com/ualib/agda-algebras/issues).


