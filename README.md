# ualib.gitlab.io

Agda [2.6.0](https://agda.readthedocs.io/en/v2.6.0/getting-started/installation.html) is required. Consult Martin Escardo's [installation instructions](INSTALL.md) to help you set up Agda and Emacs.

* The (literate) `*.lagda` files are used to generate the `html` pages with the script `./build`.

* This also generates raw `.agda` files in the director `./raw-agda` using  `illiterator.hs`.

* The program `agdatomd.hs` converts from `.lagda` to `.md` for use by the script `fastloop`.

* This script is used for editing the notes in conjunction with `jekyll serve --watch --incremental` so that after an update it is only necessary to reload the page on the browser to view it.

* The script `slowloop` serves the same purpose, but calls Agda instead of `agdatomd`, via the script `generatehtml`, so that we get syntax highlighting in the html pages. This can be very slow depending on which `lagda` file is changed. This means that after the first is reload, one is likely to see the Agda code without syntax highlighting.

* It is possible to run `./slowloop`, `./fastloop` and `jekyll serve` in parallel, and we do this for editing these notes.

* The loop scripts use `inotifywait` to detect `lagda` file changes and trigger the appropriate conversion actions.

* The `install` action of the `makefile` allows to run an additional action for particular requirements of users or environments, in a file `additionally`, which is not distributed and is ignored by `git`. If this file doesn't exist, an empty executable file is created.


## OLD STUFF


As of 22 June 2019, **this is still a work in progress**.

## Introduction

This repository contains the source code, as well as files that generate [documentation](https://ualib.gitlab.io/), for the [Agda Universal Algebra Library](https://gitlab.com/ualib/agda-ualib?nav_source=navbar), aka [agda-ualib](https://gitlab.com/ualib/agda-ualib?nav_source=navbar).

The docs are served at [ualib.org](https://ualib.gitlab.io/), and may be built directly from the .lagda files or from the .rst [reStructuredText](http://docutils.sourceforge.net/rst.html) files using [Sphinx](http://www.sphinx-doc.org).

-------------------------------------------

## Compiling and editing instructions

To get started editing the [reStructuredText](http://docutils.sourceforge.net/rst.html) (rst) files, follow the steps below.

**Disclaimer**. I hope that these steps work for you; they work on my Ubuntu 18.04 machine, but I haven't tested them on a fresh distro, or any other OS, so... 

In any case, please [email me](mailto:williamdemeo@gmail.com) if you have trouble.

1. **Clone the repository**

   ``` sh
   git clone git@gitlab.com:ualib/ualib.gitlab.io.git
   cd ualib.gitlab.io
   ```

2. **Make sure python and pip are installed**.  (I'm not sure if you need version 3...?)

   To install version 2 on (e.g., Ubuntu) linux:

   ``` sh
   sudo apt install python python-pip
   ```

   To install version 3 on (e.g., Ubuntu) linux:

   ``` sh
   sudo apt install python3 python3-pip
   ```

3. **Install pdf2svg**.

   ``` sh
   sudo apt install pdf2svg
   ```

4. **Install Sphinx and extensions**. In the ``ualib.gitlab.io`` directory, run

   ``` sh
   make install-deps
   ```

5. **Build the html version** of the book and view the result in a browser.

   ``` sh
   make html
   google-chrome _build/html/index.html
   ```

6. **Edit the rst files** and rebuild. (See the section on [Editing rst files](#editing-rst-files).)

-------------------------------

## Contributing instructions

Pull requests with corrections are welcome.

If you have questions about whether a change will be considered helpful, please [send an email William DeMeo](mailto:williamdemeo@gmail.com).

### Method 1: fork/pull-request

If you expect to contribute improvements to the source code, instead of cloning directly from the master branch of the official repository, it is advisable to first [fork](https://docs.gitlab.com/ee/gitlab-basics/fork-project.html) the repository to your own Gitlab account, and then [clone](https://docs.gitlab.com/ee/gitlab-basics/command-line-commands.html) your own fork (i.e., copy the repo files to the local harddrive of your pc). 

1. Login to your Gitlab account, navigate to the [ualib.gitlab.io repository](https://gitlab.com/ualib/ualib.gitlab.io), then click the [Fork link](https://gitlab.com/ualib/ualib.gitlab.io/-/forks/new) on the upper right and select the account into which you wish to fork the repo.

2. [Clone](https://docs.gitlab.com/ee/gitlab-basics/command-line-commands.html) the forked repository to your local drive with a command like

   ``` sh
   git clone git@gitlab.com:ualib/ualib.gitlab.io.git
   cd ualib.gitlab.io
   ```

   or, if you don't have your Gitlab account [configured with ssh keys](https://docs.gitlab.com/ee/ssh/),

   ``` sh
   git clone https://gitlab.com/ualib/ualib.gitlab.io.git
   cd ualib.gitlab.io
   ```

3. Modify the source code as described in the [Compiling and editing instructions](#compiling-and-editing-instructions) section.

4. Recommend that your changes be incorporated into the official master branch of the [ualib.gitlab.io repository](https://gitlab.com/ualib/ualib.gitlab.io).

### Method 2 (for team members)

If you have permission to push changes directly to the official ualib.gitlab.io repository, you don't have to bother with creating forks and pull requests. Instead, you can simply clone the repository to your local drive, make changes, and then commit and push them.

---------------------------------------------

## Typical Workflow

Once you have a clone of the [ualib.gitlab.io repo](https://gitlab.com/ualib/ualib.gitlab.io) on your hard drive, carry out the following series of steps (repeatedly, as necessary) to improve the repo's content.

1. **Important**. Before editing any of the files, first check that the files in your local repository are up-to-date and reflect the latest changes that you or other team members have made (otherwise, merging mayhem is likely).

   If you are working on a clone of the official repository, you can simply do `git pull`.

   If you are working on a clone of your own fork of the repository, please follow the instructions in the section on [Keeping your fork up-to-date](#keeping-your-fork-up-to-date).

2. **Build the html version** of the book and view the result in a browser.

   ``` sh
   make html
   google-chrome _build/html/index.html
   ```

3. **Edit the rst files** and then rebuild (repeat step 2). See the section on [Editing rst files](#editing-rst-files).

4. If you like your changes, stage and commit them to your local repository, then push to your remote fork; e.g.,

   ``` sh
   git commit -m "fixed a bug in the bar method of the Foo class"
   git push
   ```

5. Create a pull request by navigating to your fork's Gitlab page and clicking the **Pull Request** link (which appears next to a message like, "This branch is 1 commit ahead of ualib:master").

   Try to include an informative comment stating the reason for your proposed changes.

-------------------------------

## Editing rst files

The docs are built from [reStructuredText](http://docutils.sourceforge.net/rst.html) (.rst) files using [Sphinx](http://www.sphinx-doc.org).

Here are some resources to help you get started editing [reStructuredText](http://docutils.sourceforge.net/rst.html) files.

+ [Official Sphinx Documentation](http://www.sphinx-doc.org/en/master/)
+ [quickref.html](http://docutils.sourceforge.net/docs/user/rst/quickref.html)
+ [rest_syntax.html](https://thomas-cokelaer.info/tutorials/sphinx/rest_syntax.html)

------------------------------------------


## Keeping your fork up-to-date

When improvements are made to the "upstream" ualib/ualib.gitlab.io repository, you will want to update your fork to incorporate these changes.

Below is a list of the commands that accomplish this, but see [this page](https://help.github.com/en/articles/configuring-a-remote-for-a-fork) and [this page](https://help.github.com/articles/syncing-a-fork/) for more details.

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

-----------------------

## Troubleshooting

Please [email William](mailto:williamdemeo@gmail.com) if you get stuck with any of the above steps.

Please [post](https://gitlab.com/ualib/ualib.gitlab.io/issues/new) comments, questions, or suggestions using [the issues link](https://gitlab.com/ualib/ualib.gitlab.io/issues/new).

---------------------------

## <a id="about-this-website">About this website</a>

The pages on this web site were generated from a set of [literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) Agda (.lagda) files, with the formal, verified, mathematical development written in the [Agda][] language and appearing within `\begin{code}...\end{code}` blocks, alongside of which is some mathematical discussions outside of the code blocks written in the [Markdown][] language.

The html pages are generated by first running the `lagda2md`script which does the following:

1. Process all .lagda source files in the library with one Agda command,

   `agda --html --html-highlight=code UALib.lagda`
   
   This first type-checks all files on which the top UALib module depends and then generates a set of .html and .tex files in the `html` directory.
   
2. The .tex files produced by Step 1 are actually in markdown format.  We move these .tex files into the main directory, renaming each one with to have the .md extension, with commands like the following:
   
   `mv html/UALib.tex ${main_dir}/UALib.md`

Then, in the top level directory of the repository, we run `jekyll build`, which processes each .md files and produces a corresponding html file in the directory `_site/`.

[Issues][] or [merge requests][] contributing comments, bug fixes or other improvements are most welcomed.

* Submit a new [issue][] or [feature request][].

* Submit a new [merge request][].
As mentioned above, this site is generated by [Agda][] and [jekyll][] from source files consisting of a variety of lagda, markdown, css and html files which affect the content and its appearance on the page.

See [this page](https://jekyllrb.com/docs/themes/#overriding-theme-defaults) for information about how I customized the look of the presentation.

[This page](https://htmlcolorcodes.com/color-picker/) has a nice color-picker app for choosing html color codes.
