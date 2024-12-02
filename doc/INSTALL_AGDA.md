Installation of Agda and Emacs
==============================

*The instructions below were created by Martin Escardo to help students set up Agda for the Midlands Graduate School in 2019.  We have updated the instructions with a few minor modifications. Martin's original installation instructions are available at*

https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/blob/master/INSTALL.md

---------------------------

This file describes how to install Agda 2.6.1 and Emacs. Please follow the installation instructions for your operating system.

If you experience any issues, please take a look at the [Troubleshooting section](#Troubleshooting).

---------------------------------------

## GNU/Linux

### Arch Linux and derivatives such as Manjaro Linux

Simply install Agda 2.6.1 and Emacs by
```bash
sudo pacman -Sy agda emacs
```
and to set up Emacs with Agda mode, run
```bash
agda-mode setup
sudo agda-mode compile
```

### Debian and Ubuntu

Start by installing `emacs`, `git`, `ghc`, `cabal-install`, `alex` and `happy` using the package manager:
```bash
sudo apt install emacs git ghc cabal-install alex happy
```
Next, create a directory `ualib` for the Agda UALib in your home directory:
```bash
mkdir ~/ualib
```

If you want to try [spacemacs](https://www.spacemacs.org/), there are some config files in the [emacs directory](https://gitlab.com/ualib/ualib.gitlab.io/-/tree/master/emacs) along with some tips in the [emacs/README.md](emacs/README.md) file.


#### Standard Agda installation
This section describes the standard way to install Agda 2.6.1. If this does not work, then please try the instructions using Git.
```bash
cd ~/ualib
mkdir agda
cd agda
cabal sandbox init
cabal update
cabal install Agda
```
That last command above should take quite a long time to finish.

Now continue with [Setting up Emacs to work with Agda](#Setting-up-Emacs-to-work-with-Agda).

#### Agda installation using Git
Inside that directory, we download and install Agda 2.6.1:
```bash
cd ~/ualib
git clone https://github.com/agda/agda
cd agda
git checkout release-2.6.1  # (cf. Hint below)
cabal sandbox init
cabal update
cabal install
```

*Hint*. These notes depend on release 2.6.1, but just in case you want to see what other Agda releases are available, type the *parital* command `git checkout release-` and hit the `Tab` key a few times.

#### Setting up Emacs to work with Agda
Finally, we set up Emacs to work with Agda:

```bash
cd ~/ualib/agda/.cabal-sandbox/bin/
touch ~/.emacs
cp ~/.emacs ~/.emacs.backup
./agda-mode setup
./agda-mode compile
cp ~/.emacs ~/ualib/
cp ~/.emacs.backup ~/.emacs
cd ~/ualib
echo '#!/bin/bash' > ualib-emacs
echo 'PATH=~/ualib/agda/.cabal-sandbox/bin/:$PATH emacs --no-init-file --load ~/ualib/.emacs \$@' >> ualib-emacs
chmod +x ualib-emacs
```

Now to get Emacs with Agda mode, start Emacs using:

```bash
cd ~/ualib
./ualib-emacs
```

Finally, you may wish to make the emacs startup script runnable from anywhere.  This is optional, but to do so you could make a symbolic link in your personal `bin` directory so you can simply type `ualib-emacs` at the command line (from any directory) to launch the configuration of emacs we have just setup.

```
mkdir -p $HOME/bin
ln -s ~/ualib/ualib-emacs $HOME/bin/ualib-emacs
```

---------------------------------------------

## MacOS
We will use the [Nix Package Manager](https://nixos.org/nix/).

Open a terminal and run
```bash
curl https://nixos.org/nix/install | sh
```
Follow the instructions output by the script. The installation script requires that you have sudo access.

Install `alex`, `happy` and `emacs` using `nix-env`.
```bash
nix-env -iA nixpkgs.haskellPackages.alex nixpkgs.haskellPackages.happy emacs
```

Next, create a directory `ualib` for the Agda UALib in your home directory:
```bash
mkdir ~/ualib
```

### Standard Agda installation
This section describes the standard way to install Agda 2.6.1. If this does not work, then please try the instructions using Git.

Inside that directory, we download and install Agda 2.6.1 using `nix-shell`.
```bash
nix-shell -p zlib ghc cabal-install
cd ~/ualib
mkdir agda
cd agda
cabal sandbox init
cabal update
ZLIB="$(nix-build --no-out-link "<nixpkgs>" -A zlib)"
LIBRARY_PATH=${ZLIB}/lib cabal install Agda
```

Close the terminal, open a new one and continue by following the GNU/Linux instructions from [Setting up Emacs to work with Agda](#Setting-up-Emacs-to-work-with-Agda) on.

### Agda installation using Git
We download and install Agda 2.6.0 using `nix-shell` and `git`:
```bash
nix-shell -p zlib ghc cabal-install git
cd ~/ualib
git clone https://github.com/agda/agda
cd agda
git checkout release-2.6.1    # (cf. Hint below)
cabal sandbox init
cabal update
ZLIB="$(nix-build --no-out-link "<nixpkgs>" -A zlib)"
LIBRARY_PATH=${ZLIB}/lib cabal install
```
  
*Hint*. These notes depend on release 2.6.1, but just in case you want to see what other Agda releases are available, type the *parital* command `git checkout release-` and hit the `Tab` key a few times.

Close the terminal, open a new one and continue by following the GNU/Linux instructions from [Setting up Emacs to work with Agda](#Setting-up-Emacs-to-work-with-Agda) on.

## Windows

The easiest way is probably to install linux in a virtual machine (for example ubuntu 18.04 in VirtualBox). A web search gives tutorials and videos explaining how to do that. If we find a more direct way, we will include it here.

## Troubleshooting

In this section we describe some problems that have been encountered during compilation, and how to fix them.

#### During `cabal install` Agda 2.5.4... appears, rather than Agda 2.6.1

This is not a problem and perfectly fine, albeit confusing.

#### The command `cabal install` fails with `invalid byte sequence`

The full error looks like:
```
happy: src/full/Agda/Syntax/Parser/Parser.y: hGetContents: invalid argument (invalid byte sequence)
```

Try prefixing `cabal install` with `LANG=C.UTF-8`, i.e.
```bash
$ LANG=C.UTF-8 cabal install
```

#### Some unicode symbols (e.g. 𝟘 𝟙) appear as weird squares
Try adding
```
(set-fontset-font "fontset-default" nil
                  (font-spec :name "DejaVu Sans"))
```
to the file `~/ualib/.emacs`.

### Example Agda section of Emacs config file 

```lisp
;; BEGIN AGDA-config ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (setq load-path (cons "~/.cabal/bin" load-path))
  (setenv "LD_LIBRARY_PATH"
    (let ((current (getenv "LD_LIBRARY_PATH"))
          (new "/usr/local/lib:~/.cabal/lib"))
    (if current (concat new ":" current) new)))
  (load-file (let ((coding-system-for-read 'utf-8))
             (shell-command-to-string "agda-mode locate")))
  (set-fontset-font "fontset-default" nil
                  (font-spec :name "DejaVu Sans"))
  (setq auto-mode-alist
    (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
  (add-hook 'agda2-mode-hook (lambda ()
       (setq smartparens-mode nil)
       (setq electric-indent-mode nil) ) )
;; END AGDA-config ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
```
