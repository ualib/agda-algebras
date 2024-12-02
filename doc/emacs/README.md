## <a id="spacemacs">Spacemacs</a>

Personally, I use [spacemacs](https://www.spacemacs.org/) (instead of [Emacs](https://www.gnu.org/software/emacs/)) now. There are many things I like about spacemacs, but I cannot wholeheartedly recommend it those who wish to avoid possibly painful installation and configuration processes.

But if you're still reading this, perhaps your masochistic tendencies have got the better of you and you feel you must give [spacemacs](https://www.spacemacs.org/) a try.  In that case, I wish you luck and will leave you with my configuration files for your reference.

### Spacemacs config files

* [ualib-emacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/ualib-emacs) is the command I use to launch spacemacs.

* [.spacemacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/.spacemacs) custom configuration file (loaded on startup of spacemacs)

* [.emacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/.emacs) custom configuration file (loaded on startup of spacemacs)


**Important**. It is assumed you have already installed Agda 2.6.1 in the directory `~/ualib/` following the instructions in the [INSTALL_AGDA.md](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/INSTALL_AGDA.md) file.

**Important**. The [.spacemacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/.spacemacs) custom configuration file should be place in your home directory.

**Important**. To use the [.emacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/.emacs)  custom configuration file that's included in this repository and the start-up script [ualib-emacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/ualib-emacs), do:

* place [.emacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/.emacs) in the directory `~/ualib/` that you created when you installed Agda, and 

* place [ualib-emacs](https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/emacs/ualib-emacs) in a directory that's in your `PATH` [environment variable](https://help.ubuntu.com/community/EnvironmentVariables) and made executable. E.g., in my case,

  ```
  chmod a+x ualib-emacs
  mv ualib-emacs ~/bin
  ```

  If the `~/bin` directory is not already in your `PATH`, then you could add it by

  ```
  export PATH=$HOME/bin:$PATH
  ```

  To make the change permanent, see [how to add a directory to the path](https://askubuntu.com/questions/60218/how-to-add-a-directory-to-the-path) at AskUbuntu.

