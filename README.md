# ualib.gitlab.io

This is the main repository for the Agda Universal Algebra Library (UALib), a library of Agda modules for universal algebra and related subjects, and the associated html and pdf documentation.

Below are instructions for getting the Agda UALib installed on your machine.  I hope that these steps work for you; they work on my Ubuntu 18.04 machine, but I haven't tested them on a fresh distro, or any other OS, so... 

...in any case, please [email me](mailto:williamdemeo@gmail.com) if you have trouble.

---------------------------

## Introduction

This repository contains the source code, as well as files that generate [documentation](https://ualib.gitlab.io/), for the [Agda Universal Algebra Library](https://gitlab.com/ualib/ualib.gitlab.io), aka [Agda UALib](https://gitlab.com/ualib/ualib.gitlab.io).

The docs are served at [ualib.org](https://ualib.gitlab.io/), and are automatically generated from the .lagda files using the script [generate-md](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/generate-md). See the section on [Generating the documentation](#generating-the-documentation) below.

-----------------------------

## Install Agda

Agda [2.6.1](https://agda.readthedocs.io/en/v2.6.1/getting-started/installation.html) is required. 

If you don't have Agda and agda2-mode installed, follow the [official installation instructions](https://agda.readthedocs.io/en/v2.6.0/getting-started/installation.html) or [Martin Escardo's installation instructions](INSTALL_AGDA.md) to help you set up Agda and Emacs.

-----------------------------

## Download the UALib

[Clone](https://docs.gitlab.com/ee/gitlab-basics/command-line-commands.html) the repository to your local machine with a command like the following:

``` sh
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
cd ualib.gitlab.io
```

or, if you don't have your Gitlab account [configured with ssh keys](https://docs.gitlab.com/ee/ssh/),

``` sh
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
cd ualib.gitlab.io
```

After installing agda and cloning the ualib.gitlab.io repository, you should be able to work with the Agda UALib source code contained in the .lagda files under the ualib.gitlab.io/UALib directory.

--------------------------------------------

## Generating the documentation

(**To do** update this section with better, more complete instructions)


The shell script `generate-md` type-checks all the `.lagda` and then generates markdown (`.md`) files in the html directory.

* This script is used for editing the notes in conjunction with `jekyll serve --watch --incremental` so that after an update it is only necessary to reload the page on the browser to view it.


--------------------------------


## Acknowledgements

A great source of information and inspiration for the Agda UALib is [Marin Escardo's lecture notes on HoTT/UF in Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html).

See also Martin's [HoTT/UF github repository](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes) and [Type Topology github repository](https://github.com/martinescardo/TypeTopology).

-------------------------------
