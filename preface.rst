.. FILE      : preface.rst
.. AUTHOR    : William DeMeo  <williamdemeo@gmail.com>
.. DATE      : 17 May 2019
.. UPDATED   : 21 Jul 2020
.. COPYRIGHT : (c) 2020 William DeMeo



Preface
========

To support formalization in type theory of research level mathematics in universal algebra and related fields, we are developing a software library, called the `Agda Universal Algebra Library`_ (agda-ualib_ ).  Our library contains formal statements and proofs of some of the core, foundational definitions and results universal algebra and is written in Agda_.

Agda_ is a programming language and `proof assistant`_, or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful *proof tactics* for proving things about the objects that inhabit these types. 

------------------------

Vision and Goals
----------------------

The idea for the the Agda Universal Algebra Library (agda-ualib_) originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of `type theory`_ ---in particular, `dependent types`_ and `inductive types`_) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

Primary Goals
~~~~~~~~~~~~~~~~~~~~

The first goal of the agda-ualib_ project is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and possibly risky investment of time and resources.  However, we believe our subject is well served by a new, modern, `constructive <constructive mathematics>`_ presentation of its foundations.  Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

.. Specific examples will be given below in :numref:`subalgebras-in-Agda`, :numref:`terms-in-Agda`, and :numref:`clones-in-Agda`.

Secondary Goals
~~~~~~~~~~~~~~~~~~~~

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our intermediate-term objectives include

+ developing domain specific "proof tactics" to express the idioms of universal algebra,
+ incorporating automated proof search for universal algebra, and
+ formalizing theorems emerging from our own mathematics research,
+ documenting the resulting software libraries so they are usable by other working mathematicians.

For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.

-----------------------------------

Intended audience
------------------

This document describes the Agda Universal Algebra Library (agda-ualib_) in enough detail so that working mathematicians (and possibly some normal people, too) might be able to learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying new mathematics.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, :cite:`Bergman:2012` or :cite:`McKenzie:1987`, and to a lesser extent category theory, as presented in categorytheory.gitlab.io_ or :cite:`Riehl:2017`.

Some prior exposure to `type theory`_ and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to the appendix and glossary, while simultaneously consulting one or more of the references mentioned in :ref:`references` to fill in gaps as needed.
  
Finally, it is assumed that while reading these materials the reader is actively experimenting with Agda using emacs_ with its `agda2-mode`_ extension installed.

-------------------------

Installing the library
-----------------------------

The main repository for the agda-ualib_ is https://gitlab.com/ualib/ualib.gitlab.io (which will become publicly available again in the summer of 2020).

There are installation instructions in the main README.md file in that repository, but really all you need to do is have a working Agda (and agda2-mode) installation and clone the agda-ualib_ repository with, e.g.,

   .. code-block:: bash

      git clone git@gitlab.com:ualib/ualib.gitlab.io.git

   OR

   .. code-block:: bash

      git clone https://gitlab.com/ualib/ualib.gitlab.io.git

(We assume you have Agda_ and agda2-mode_ installed on your machine. If not, follow the directions on `the main Agda website <Agda>`_ to install them.)

-----------------------------------

Unicode hints
--------------

At the end of each chapter of this documentation we show how to produce in Emacs agda2-mode_ some of the fancy unicode characters that we use in our code. For example, we might say "type ``\MCI`` to produce the symbol 𝓘".  We hope these occasional hints are convenient for the reader, but they are not meant to be comprehensive. Instead, information about unicode symbols is readily available in Emacs agda2-mode_; simply place the cursor on the character of interest and enter the command ``M-x describe-char``; alternatively, use the shortcut ``M-m h d c``. To see a full list of available characters, enter ``M-x desscribe-input-method`` (or ``C-h I``).

---------------------------------------------------

Acknowledgments
---------------

Besides the main authors and developers of agda-ualib_ (William DeMeo and Siva Somayyajula), a number of other people have contributed to the project in one way or another.

Special thanks go to `Clifford Bergman`_, `Venanzio Capretta`_, `Andrej Bauer`_, `Miklós Maróti`_, and `Ralph Freese`_, for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project, often without even knowing it.

The first author would also like to thank his postdoctoral advisors and their institutions for supporting (sometimes without their knowledge) work on this project. These include `Libor Barto`_ and Charles University in Prague (Nov 2019--Jun 2021), `Peter Mayr`_ and University of Colorado in Boulder (Aug 2017--May 2019), `Ralph Freese`_ and the University of Hawaii in Honolulu (Aug 2016--May 2017), `Cliff Bergman`_ and Iowa State University in Ames (Aug 2014--May 2016).


Attributions and citations
~~~~~~~~~~~~~~~~~~~~~~~~~~

William DeMeo and Siva Somayyajula (hereinafter, "The Authors") are the developers of the `Agda Universal Algebra Library`_ (agda-ualib_).

Regarding the mathematical results that are implemented in the agda-ualib_ library, as well as the presentation and informal statements of these results in the documentation, The Authors makes no claims to originality.

Regarding the Agda source code in the agda-ualib_ library, this is mainly due to The Authors.

HOWEVER, we have benefited from the outstanding lecture notes on `Univalent Foundations and Homotopy Type Theory <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes>`_ and the `Type Topology`_ Agda Library, both by `Martin Hötzel Escardo <https://www.cs.bham.ac.uk/~mhe>`_.  The first author is greatly indebted to Martin for teaching him about type theory in Agda at the `Midlands Graduate School in the Foundations of Computing Science <http://events.cs.bham.ac.uk/mgs2019/>`_ in Birmingham in 2019.

The development of the agda-ualib_ and its documentation is informed by and benefits from the references listed in the :ref:`references` section below.

----------------------

.. _references:

References
------------

The following Agda documentation and tutorials are excellent.  They have been quite helpful to The Author of agda-ualib_, and have informed the development of the latter and its documentation.

* Altenkirk, `Computer Aided Formal Reasoning`_
* Bove and Dybjer, `Dependent Types at Work`_
* Escardo, `Introduction to Univalent Foundations of Mathematics with Agda`_
* Gunther, Gadea, Pagano, `Formalization of Universal Algebra in Agda`_
* János, `Agda Tutorial`_
* Norell and Chapman, `Dependently Typed Programming in Agda`_
* Wadler, `Programming Language Foundations in Agda`_

Finally, the official `Agda Wiki`_, `Agda User's Manual`_, `Agda Language Reference`_, and the (open source) `Agda Standard Library`_ source code are also quite useful.

-----------------------------------


.. include:: hyperlink_references.rst

