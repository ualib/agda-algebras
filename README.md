# agda-algebras

This is a copy of the Agda Universal Algebra Library which depends the [Standard Library](https://github.com/agda/agda-stdlib) of the [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) proof assistant language.
It is currently under active reconstruction, and should be regarded as alpha software.  (The previous version of the Agda Universal Algebra Library, which was called UALib, was based on the [Type Topology](https://github.com/martinescardo/TypeTopology) library of [Martín Escardó][].)

---------------------------

## Introduction

This repository contains the source code, as well as the files used to generate 
the [documentation](https://ualib.guthub.io/agda-algebras), for (this version of) the 
[Agda Universal Algebra Library](https://github.com/ualib/agda-algebras).  (Documentation for the previous version is available at [ualib.org](https://ualib.gitlab.io).)

-----------------------------

## Documentation

Agda was used to generate html pages for each module. These pages are now served at

[https://ualib.org](https://ualib.org)

(The previous version of the agda-algebras library, called UALib, is documented at [ualib.org](https://ualib.gitlab.io).)

----------------------------------

## Install Agda

Agda ([version 2.6.1](https://agda.readthedocs.io/en/v2.6.1/getting-started/installation.html) or greater) is required. 

If you don't have it, follow the [official Agda installation instructions](https://agda.readthedocs.io/en/v2.6.0/getting-started/installation.html).


For reference, the following is a list of commands that should correctly install Agda version 2.6.2 on a Ubuntu 18.04 machine. Please submit an issue or pull request if these commands don't work for you.

```
cabal update
git clone git@github.com:agda/agda.git
cd agda
git checkout release-2.6.2
cabal install Agda-2.6.2 --program-suffix=-2.6.2  # (takes a very long time)
cd ~/.cabal/bin/
touch ~/.emacs
cp ~/.emacs ~/.emacs.backup
./agda-mode-2.6.2 setup
./agda-mode-2.6.2 compile
mkdir -p ~/bin
cp ~/.emacs ~/bin
cp ~/.emacs.backup ~/.emacs
cd ~/bin
echo '#!/bin/bash' > agdamacs
echo 'PATH=~/.cabal/bin:$PATH emacs --no-init-file --load ~/bin/.emacs $@' >> agdamacs
chmod +x agdamacs
echo 'export PATH=~/bin:~/.cabal/bin:$PATH' >> ~/.profile
```

Now invoking the command `agdamacs` will launch emacs with Agda 2.6.2 and agda-mode installed.)

-----------------------------

## Contributing to this repository

If you wish to contribute to this repository, the best way is to use the
standard [fork-clone-pull-request](https://gist.github.com/Chaser324/ce0505fbed06b947d962)
workflow.

-------------------------------------

## Credits

The [agda-algebras][] library is developed and maintained by the *ualib/agda-algebras development team*.

### The agda-algebras development team

[Jacques Carette][]  
[William DeMeo][]  


### Acknowledgements and attributions

We thank [Andreas Abel][], [Jeremy Avigad][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration and encouragement.

Most of the mathematical results formalized in the [agda-algebras][] are well known. Regarding the source code in the [agda-algebras][] library, this is mainly due to the contributors listed above.

### References

The following Agda documentation and tutorials helped inform and improve the [agda-algebras][] library, especially the first one in the list.

* Escardo, [Introduction to Univalent Foundations of Mathematics with Agda][]
* Wadler, [Programming Languages Foundations in Agda][]
* Bove and Dybjer, [Dependent Types at Work][]
* Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
* Norell and Chapman, [Dependently Typed Programming in Agda][]

Finally, the official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the (open source) [Agda Standard Library][] source code are also quite useful.


### How to cite the Agda Universal Algebra Library

[![DOI](https://zenodo.org/badge/360493064.svg)](https://zenodo.org/badge/latestdoi/360493064)

To cite the [agda-algebras][] software library in a publication or on a web page, please use the following BibTeX entry:

```bibtex
@misc{ualib_v2.0.1,
  author       = {De{M}eo, William and Carette, Jacques},
  title        = {{T}he {A}gda {U}niversal {A}lgebra {L}ibrary (agda-algebras)},
  year         = 2021,
  note         = {{D}ocumentation available at https://ualib.org},
  version      = {2.0.1},
  doi          = {10.5281/zenodo.5765793},
  howpublished = {{G}it{H}ub.com},
  note         = {{V}er.~2.0.1; source code: \href{https://zenodo.org/record/5765793/files/ualib/agda-algebras-v.2.0.1.zip?download=1}{agda-algebras-v.2.0.1.zip}, {G}it{H}ub repo: \href{https://github.com/ualib/agda-algebras}{github.com/ualib/agda-algebras}},
}                  
```

To cite the [formalization of Birkhoff's HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem), please use the following BibTeX entry:

```bibtex
@article{DeMeo:2021,
 author        = {De{M}eo, William and Carette, Jacques},
 title         = {A {M}achine-checked {P}roof of {B}irkhoff's {V}ariety {T}heorem
                  in {M}artin-{L}\"of {T}ype {T}heory}, 
 journal       = {CoRR},
 volume        = {abs/2101.10166},
 year          = {2021},
 eprint        = {2101.2101.10166},
 archivePrefix = {arXiv},
 primaryClass  = {cs.LO},
 url           = {https://arxiv.org/abs/2101.10166}
 note          = {Source code: \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}}
}
```

If you're looking for the latest (setoid-based) formalization of Brkhoff's Theorem, see the [Proof of the HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) in the html documentation, or the source code of the [Setoid.Varieties.HSP][] module in the file [Setoid/Varieties/HSP.lagda][] in the [agda-algebras][] GitHub repository.

-------------------------------

## License

<a rel="license" href="http://creativecommons.org/licenses/by-sa/4.0/"><img
alt="Creative Commons License" style="border-width:0"
src="https://i.creativecommons.org/l/by-sa/4.0/88x31.png" /></a><br /><span
xmlns:dct="http://purl.org/dc/terms/" property="dct:title">The Agda Universal
Algebra Library</span> by <a xmlns:cc="http://creativecommons.org/ns#"
href="https://williamdemeo.gitlab.io/" property="cc:attributionName"
rel="cc:attributionURL">William DeMeo</a> and the [Agda Algebras Development Team](https://github.com/ualib/agda-algebras#the-agda-algebras-development-team) is licensed under a <a rel="license"
href="http://creativecommons.org/licenses/by-sa/4.0/">Creative Commons
Attribution-ShareAlike 4.0 International License</a>.<br />Based on a work at
<a xmlns:dct="http://purl.org/dc/terms/"
href="https://gitlab.com/ualib/ualib.gitlab.io"
rel="dct:source">https://gitlab.com/ualib/ualib.gitlab.io</a>.


<!-- ---------------- -->

<!-- **Author**. [William DeMeo](https://williamdemeo.gitlab.io) -->

<!-- **Affiliation**. [Department of Algebra](https://www.mff.cuni.cz/en/ka), [Charles University in Prague](https://cuni.cz/UKEN-1.html) -->



[Jeremy Avigad]: http://www.andrew.cmu.edu/user/avigad/
[Andreas Abel]: http://www.cse.chalmers.se/~abela/
[Andrej Bauer]: http://www.andrej.com/index.html
[Clifford Bergman]: https://orion.math.iastate.edu/cbergman/
[Cliff Bergman]: https://orion.math.iastate.edu/cbergman/
[Venanzio Capretta]: https://www.duplavis.com/venanzio/
[Jacques Carette]: http://www.cas.mcmaster.ca/~carette/
[William DeMeo]: https://williamdemeo.gitlab.io/
[Martín Escardó]: https://www.cs.bham.ac.uk/~mhe
[Ralph Freese]: https://math.hawaii.edu/~ralph/
[Bill Lampe]: https://math.hawaii.edu/wordpress/people/william/
[Miklós Maróti]: http://www.math.u-szeged.hu/~mmaroti/
[JB Nation]: http://www.math.hawaii.edu/~jb/
[Hyeyoung Shin]: https://hyeyoungshin.github.io/
[Siva Somayyajula]: http://www.cs.cmu.edu/~ssomayya/

[agda-algebras]: https://github.com/ualib/agda-algebras
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html
[Programming Languages Foundations in Agda]: https://plfa.github.io/
[Dependent Types at Work]: http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf
[Formalization of Universal Algebra in Agda]: http://www.sciencedirect.com/science/article/pii/S1571066118300768
[Dependently Typed Programming in Agda]: http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Agda Language Reference]: https://agda.readthedocs.io/en/v2.6.1.3/language
[Agda Standard Library]: https://agda.github.io/agda-stdlib/
[Agda Tools]: https://agda.readthedocs.io/en/v2.6.1.3/tools/
[Agda Tutorial]: https://people.inf.elte.hu/pgj/agda/tutorial/Index.html
[Agda User's Manual]: https://agda.readthedocs.io/en/v2.6.1.3/
[Agda Wiki]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[agda2-mode]: https://agda.readthedocs.io/en/v2.6.1.3/tools/emacs-mode.html
[Algebraic Effects and Handlers]: https://www.cs.uoregon.edu/research/summerschool/summer18/topics.php#Bauer
[Bergman (2012)]: https://www.amazon.com/gp/product/1439851298/ref=as_li_tl?ie=UTF8&camp=1789&creative=9325&creativeASIN=1439851298&linkCode=as2&tag=typefunc-20&linkId=440725c9b1e60817d071c1167dff95fa
