# ualib.gitlab.io

## Introduction

This repository contains all documentation for `lean-ualib`, the Lean Universal Algebra Library.

The resulting documentation is served at ualib.org (which points to https://ualib.gitlab.io/).

The documentation is built using Sphinx and restructured text.  It may also require `convert` (https://imagemagick.org) for image conversion.


-------------------------------------------

## How to build the docs

The build requires python 3 (install `python3-venv` on ubuntu).

```
make install-deps
# make images  # Actually, we have no images yet, but this command may be required in future.
make html
make latexpdf
```

+ `make install-deps` is only required the first time, and only if you want to use the bundled version of Sphinx and Pygments with improved syntax highlighting for Lean.

+ `make images` will be required once we have some images in the documentation (we don't yet); also, it is only required the first time or if you add new latex source to `latex_images` after that.

------------------------------------------

## How to test the Lean code snippets

```
make leantest
```

## How to contribute

Pull requests with corrections are welcome. Please follow our `commit conventions <https://github.com/leanprover/lean/blob/master/doc/commit_convention.md>`. If you have questions about whether a change will be considered helpful, please contact Jeremy Avigad, ``avigad@cmu.edu``.
