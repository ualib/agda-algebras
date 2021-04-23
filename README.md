# ualib.gitlab.io

The [Agda Universal Algebra Library](https://ualib.gitlab.io/) ([UniversalAlgebra](https://ualib.gitlab.io/)) is a library of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in dependent type theory using the [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) proof assistant language.

This is the main repository for the Agda UniversalAlgebra. Below are instructions for getting the UniversalAlgebra installed on your machine.  I hope that these steps work for you; they work on my Ubuntu 18.04 machine, but I haven't tested them on a fresh distro, or any other OS, so... 

...in any case, please [email me](mailto:williamdemeo@gmail.com) if you have trouble.

---------------------------

## Introduction

This repository contains the source code, as well as files that generate [documentation](https://ualib.gitlab.io/), for the [Agda Universal Algebra Library](https://gitlab.com/ualib/ualib.gitlab.io), aka [Agda UniversalAlgebra](https://gitlab.com/ualib/ualib.gitlab.io).

The docs are served at [ualib.org](https://ualib.gitlab.io/), and are automatically generated from the .lagda files using the script [generate-md](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/generate-md). See the section on [Generating the documentation](#generating-the-documentation) below.

-----------------------------

## Install Agda

Agda ([version 2.6.1](https://agda.readthedocs.io/en/v2.6.1/getting-started/installation.html) or greater) is required. 

If you don't have it, follow the [official Agda installation instructions](https://agda.readthedocs.io/en/v2.6.0/getting-started/installation.html) or [these instructions](INSTALL_AGDA.md) by Martin Escardo.

Be sure you have [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php), [Emacs](https://www.gnu.org/software/emacs/) (or [Spacemacs](https://www.spacemacs.org/)), and [agda2-mode](https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html) for Emacs (Spacemacs) installed.

-----------------------------

## Download the UniversalAlgebra

[Clone](https://docs.gitlab.com/ee/gitlab-basics/command-line-commands.html) the repository to your local machine using **ONE** of the following alternative commands:

``` sh
git clone https://gitlab.com/ualib/ualib.gitlab.io.git
```

**OR**, if you have a gitlab account and have configured [ssh keys](https://docs.gitlab.com/ee/ssh/),


``` sh
git clone git@gitlab.com:ualib/ualib.gitlab.io.git
```

This creates a directory on your local machine called `ualib.gitlab.io`. The UniversalAlgebra source code files reside in subdirectories of `ualib.gitlab.io/UniversalAlgebra` and have the `.lagda` extension.

Having installed Agda and cloned the `ualib.gitlab.io` repository, you should now be able to work with the source code contained in the .lagda files, such as UniversalAlgebra.lagda or any of it submodules. For example, you might start by loading the file [UniversalAlgebra/Prelude/Preliminaries.lagda](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/UniversalAlgebra/Prelude/Preliminaries.lagda) into Emacs and check that Agda can type-check that file using the command `C-c C-l`.

Other Emacs keybindings are described in the [emacs-mode.html#keybindings](https://agda.readthedocs.io/en/v2.6.1.1/tools/emacs-mode.html#keybindings) section of the [Agda docs](https://agda.readthedocs.io).

--------------------------------------

## Contributing to this repository

If you wish to contribute to this repository, the best way is to use the standard [fork-clone-pull-request](https://gist.github.com/Chaser324/ce0505fbed06b947d962) workflow.  This is described nicely on [this page](https://gist.github.com/Chaser324/ce0505fbed06b947d962), but below we list the five simple steps required.

(A "pull request" is also known as a "merge request" on gitlab and its documentation.)

The following assumes you already have a [gitlab](https://gitlab.com/) or [github](https://github.com) account.  If you don't, sign up for one.  It's free. The instructions below are for gitlab, but they should work for github as well.

1. [Fork](https://docs.gitlab.com/ee/user/project/repository/forking_workflow.html#creating-a-fork) the ualib.gitlab.io repository. This makes a complete copy of the repository in your own gitlab account that you now control, so, for example, you can commit and push changes to the source code in your forked copy of the repo.

2. [Clone](https://docs.gitlab.com/ee/gitlab-basics/start-using-git.html#clone-a-repository) your fork to make a copy of it on your local machine.

3. Make some improvements to the source files or documentation in your local copy of the repository.

4. [Commit](https://docs.gitlab.com/ee/gitlab-basics/start-using-git.html#add-and-commit-local-changes) your changes to your local repository and then [Push](https://docs.gitlab.com/ee/gitlab-basics/start-using-git.html#send-changes-to-gitlabcom) your changes to your remote fork residing in your gitlab account.

5. [Submit a merge request](https://docs.gitlab.com/ee/user/project/merge_requests/creating_merge_requests.html) to alert the UniversalAlgebra team members that you would like your proposed changes to be reviewed and integrated into the official Agda UniversalAlgebra repository.


### Keeping your fork up-to-date

When improvements are made to the "upstream" ualib/ualib.gitlab.io repository, you will want to update your fork to incorporate these changes.

Below is a list of the commands that accomplish this, but see [this page](https://help.github.com/en/articles/configuring-a-remote-for-a-fork) and [this page](https://help.github.com/articles/syncing-a-fork/) for more details.

**New** Gitlab has a "mirroring" feature to keep your fork synced with the upstream repo. See [this page](https://docs.gitlab.com/ee/user/project/repository/repository_mirroring.html) for details.

1. Change to the working directory of your local copy of the repository and specify the upstream repository.

   ``` sh
   cd $HOME/git/ualib.gitlab.io # (for example)
   git remote add upstream git@gitlab.com:ualib/ualib.gitlab.io.git
   ```

2. Verify that it worked.

   ``` sh
   git remote -v
   ```

   The output should look something like this:

   ``` sh
   origin git@gitlab.com:your-user-name/ualib.gitlab.io.git (fetch)
   origin git@github.com:your-user-name/ualib.gitlab.io.git (push)
   upstream git@gitlab.com:ualib/ualib.gitlab.io.git (fetch)
   upstream git@gitlab.com:ualib/ualib.gitlab.io.git (push)
   ```

   If the foregoing fails, try

   ``` sh
   git remote add upstream https://gitlab.com/ualib/ualib.gitlab.io.git
   ```

3. In the working directory of your local project, fetch the branches and their commits from the upstream repository and merge upstream/master into your local master branch.

   ``` sh
   git fetch upstream
   git checkout master
   git merge upstream/master
   ```

   This brings your fork's master branch into sync with the upstream repository, without losing your local changes.

4. Finally, commit the changes and push to your remote fork.

   ``` sh
   git commit -m "merged changes from upstream"
   git push origin master
   ```

Now when you now visit the Gitlab page of your personal fork of the repo, you should see a message like, "This branch is even with ualib:master."

-------------------------------------

## Generating the documentation

The html pages at [ualib.org](https://ualib.gitlab.io) were generated from the [literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) Agda (.lagda) files in this repository.  These files contain formal, verified, mathematical theorems and proofs inside code environments (i.e., inside `\begin{code}...\end{code}` blocks)  as well as some mathematical discussions outside those blocks written in markdown.

The html documentation is available at [ualib.org](https://ualib.gitlab.io), so there is usually no need for end-users to generate the documentation pages locally. However, if you want to fix something or help develop improved versions of the docs or code, you may want to update and render the documentation html pages on your local machine. In that case, the instructions in this section may be helpful.

To generate the html documentation pages and serve them locally you will need bundler and jekyll.  If you're using Ubuntu 18.04 or something similar, the [INSTALL_JEKYLL.md](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/INSTALL_JEKYLL.md) file gives instructions for installing these two programs.

The html pages are generated by Agda with the following command:

```
agda --html --html-highlight=code UniversalAlgebra.lagda
```

This generates a set of markdown files that are then converted to html by jekyll with the command

```shell
bundle exec jekyll build
```

In practice, we use the script `generate-md`, *inside the UniversalAlgebra directory*, to process the `.lagda` files and put the resulting markdown output in the right place, and then using the script `jekyll-serve` to invoke the following commands

```
cp html/UniversalAlgebra.md index.md
cp html/*.html html/*.md .
bundle install --path vendor
bundle exec jekyll serve --watch --incremental
```

This causes jekyll to serve the web pages locally so we can inspect them by pointing a browser to the local server at [http://127.0.0.1:4000](http://127.0.0.1:4000).

--------------------------------

## Troubleshooting

Please [email William](mailto:williamdemeo@gmail.com) if you have any questions or problems using the UniversalAlgebra.

Comments, questions, or suggestions may also be submitted by creating a [new issue](https://gitlab.com/ualib/ualib.gitlab.io/issues/new).

--------------------

## Acknowledgements

A great source of information and inspiration for the Agda UniversalAlgebra is [Marin Escardo's lecture notes on HoTT/UF in Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html).

See also Martin's [HoTT/UF github repository](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes) and [Type Topology github repository](https://github.com/martinescardo/TypeTopology).

The author wishes to thank
[Siva Somayyajula](http://www.cs.cmu.edu/~ssomayya/),
who contributed to this project during its first year and helped get it off the ground.

Thanks also to
[Andreas Abel](http://www.cse.chalmers.se/~abela/),
[Andrej Bauer](http://www.andrej.com/index.html), 
[Clifford Bergman](https://orion.math.iastate.edu/cbergman/), 
[Venanzio Capretta](https://www.duplavis.com/venanzio/), 
[Jacques Carette](http://www.cas.mcmaster.ca/~carette/),
[Martin Escardo](https://www.cs.bham.ac.uk/~mhe), 
[Ralph Freese](https://math.hawaii.edu/~ralph/), 
[Bill Lampe](https://math.hawaii.edu/wordpress/people/william/), 
[Miklós Maróti](http://www.math.u-szeged.hu/~mmaroti/), 
[JB Nation](http://www.math.hawaii.edu/~jb/), and 
[Hyeyoung Shin](https://hyeyoungshin.github.io/)
for helpful discussions, corrections, advice, inspiration and encouragement.



### Attributions and citations

Most (if not all) of the mathematical results that formalized in the [UniversalAlgebra](https://ualib.gitlab.io) are library already well known.

Regarding the Agda source code in the [Agda UniversalAlgebra](https://gitlab.com/ualib/ualib.gitlab.io/), this is mainly due to the author with one major caveat: we benefited greatly from, and the library depends upon, the lecture notes on [Univalent Foundations and Homotopy Type Theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html) and the [Type Topology](https://github.com/martinescardo/TypeTopology) Agda Library by [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe).  The author is indebted to Martin for making his library and notes available and for teaching a course on type theory in Agda at the [Midlands Graduate School in the Foundations of Computing Science](http://events.cs.bham.ac.uk/mgs2019/) in Birmingham in 2019.

-------------------------------

## License and citation information

<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/"><img alt="Creative Commons License" style="border-width:0" src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png" /></a><br /><span xmlns:dct="http://purl.org/dc/terms/" property="dct:title">The Agda Universal Algebra Library</span> by <a xmlns:cc="http://creativecommons.org/ns#" href="https://williamdemeo.gitlab.io/" property="cc:attributionName" rel="cc:attributionURL">William DeMeo</a> is licensed under a <a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/">Creative Commons Attribution-ShareAlike 4.0 International License</a>.<br />Based on a work at <a xmlns:dct="http://purl.org/dc/terms/" href="https://gitlab.com/ualib/ualib.gitlab.io" rel="dct:source">https://gitlab.com/ualib/ualib.gitlab.io</a>.

### Citing the Agda UniversalAlgebra

If you use the Agda UniversalAlgebra or wish to refer to it or its documentation in a publication or on a web page, please use the following BibTeX data:

```bibtex
@article{DeMeo:2021,
 author        = {William DeMeo},
 title         = {The {A}gda {U}niversal {A}lgebra {L}ibrary and 
                  {B}irkhoff's {T}heorem in {D}ependent {T}ype {T}heory}, 
 journal       = {CoRR},
 volume        = {abs/2101.10166},
 year          = {2021},
 eprint        = {2101.10166},
 archivePrefix = {arXiv},
 primaryClass  = {cs.LO},
 url           = {https://arxiv.org/abs/2101.10166},
 note          = {source code: \url{https://gitlab.com/ualib/ualib.gitlab.io}},
 biburl        = {https://dblp.org/rec/journals/corr/abs-2101-10166.bib},
 bibsource     = {dblp computer science bibliography, https://dblp.org}
}
```

----------------

**Author**. [William DeMeo](https://williamdemeo.gitlab.io)

**Affiliation**. [Department of Algebra](https://www.mff.cuni.cz/en/ka), [Charles University in Prague](https://cuni.cz/UKEN-1.html)

