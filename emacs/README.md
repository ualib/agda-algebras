## <a id="spacemacs">Spacemacs</a>

Personally, I use [spacemacs](https://www.spacemacs.org/) instead of [Emacs](https://www.gnu.org/software/emacs/)) now. There are many things I like about spacemacs, but I cannot wholeheartedly recommend it those who wish to avoid possibly painful installation and configuration processes.

But if you're still reading this, perhaps your masochistic tendencies have got the better of you and you feel you must give [spacemacs](https://www.spacemacs.org/) a try.  In that case, I wish you luck and will leave you with my configuration files for your reference.

### Spacemacs config files

* [ualib-emacs] is the command I use to launch spacemacs.

* .spacemacs custom configuration file (loaded on startup of spacemacs)

* .emacs custom configuration file (loaded on startup of spacemacs)


**Important** The file  [ualib-emacs]() should be placed in a directory that's in your `PATH` [environment variable](https://help.ubuntu.com/community/EnvironmentVariables) and made executable. E.g., in my case,

```
chmod a+x ualib-emacs
mv ualib-emacs ~/bin
```

If the `~/bin` directory is not already in your `PATH`, then you could add it by

```
export PATH=$HOME/bin:$PATH
```

To make the change permanent, see [how to add a directory to the path](https://askubuntu.com/questions/60218/how-to-add-a-directory-to-the-path) at AskUbuntu.

**Important** The .spacemacs file should be place in your home directory.

**Important** To use the .emacs file posted here, along with the start-up script ualib-emacs, you must place the .emacs file in the directory ~/emacs.d (and you should probably remove or change the name of any other .emacs files you have lying around in, say, your home directory, because multiple .emacs files get confusing.

Here's what I would do:

```
mv ~/.emacs{,-old}  ## in case you already have a .emacs file
mkdir -p ~/.emacs.d
cp ualib.gitlab.io/emacs/.emacs ~/.emacs.d/
```

The last command above copies the `.emacs` file that ships with ualib.gitlab.io into your `~/.emacs.d/` directory.
