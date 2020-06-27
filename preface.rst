.. file: preface.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 17 May 2019
.. Updated: 29 Jan 2020
.. Copyright (c) 2019 William DeMeo



Preface
========

To support formalization in type theory of research level mathematics in universal algebra and related fields, we are developing a software library, called the `Agda Universal Algebra Library`_ (aka agda-ualib, aka ⋀𝗀𝖽𝖺 ⋀𝗅𝗀𝖾𝖻𝗋𝖺).  Our library contains formal statements and proofs of some of the core, foundational definitions and results universal algebra.

We will define some useful datatypes for implementing universal algebra in the `Agda proof assistant <http://hackage.haskell.org/package/Agda-2.6.0.1>`_.

------------------------

Vision
----------

The idea for the ⋀𝗀𝖽𝖺 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 library originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand types (of `type theory`_ ---in particular, `dependent types`_ and `inductive types`_) make possible elegant formal representations of recursively defined objects, as well as concise proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

Agda_ is a programming language and `proof assistant`_, or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful `proof tactics`_ [1]_ for proving properties of the objects that inhabit these types. 

The goal of the ⋀𝗀𝖽𝖺 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 project is to formalize, in the Agda language, the substantial edifice upon which our mathematical research stands, demonstrating that our work can be implemented formally and effectively in type theory in such a way that we and other working mathematicians can use the resulting library to conduct and formalize further mathematics research.

Our field is deep and its history rich, so encoding all of our subject's foundations may seem like a daunting task and possibly risky investment of time and resources.  However, our view is that the basics of the theory could be well served by a modernized and (where possible) `constructive <constructive mathematics>`_ presentation, so that universal algebra could be naturally codified in the language of type theory and formally implemented in, and verified by, the Agda proof assistant.

.. Specific examples will be given below in :numref:`subalgebras-in-Agda`, :numref:`terms-in-Agda`, and :numref:`clones-in-Agda`.

-----------------------------------

Objectives
---------------

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal of the Agda development team is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our main objectives include

+ developing domain specific "proof tactics" to express the idioms of universal algebra,
+ incorporating automated proof search for universal algebra, and
+ formalizing theorems emerging from our own mathematics research,
+ documenting the resulting software libraries so they are usable by other working mathematicians.

For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Our goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.

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

(We assume you have ``Agda`` and ``agda2-mode`` installed on your machine. If not, follow the directions on `the main Agda website <Agda>`_ to install them.)

-----------------------------------

Acknowledgments
---------------

This manual, as well as the software library that it documents, are open access projects maintained on Gitlab by `William DeMeo <mailto:williamdemeo@gmail.com>`_.

Besides Dr. DeMeo, a number of other people have contributed to this project---some directly, others indirectly.  Special thanks go to `Clifford Bergman`_, `Siva Somayyajula`_, `Venanzio Capretta`_, `Andrej Bauer`_, `Miklós Maróti`_, `Ralph Freese`_, and `Jeremy Avigad`_ for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project, often without even knowing it.

Attributions and citations
~~~~~~~~~~~~~~~~~~~~~~~~~~

William DeMeo and Siva Somayyajula (hereinafter, "The Authors") are the developers of the `Agda Universal Algebra Library`_ (`agda-ualib`_).

Regarding the mathematical results that are implemented in the `agda-ualib`_ library, as well as the presentation and informal statements of these results in the documentation, The Authors makes no claims to originality.

Regarding the Agda source code in the `agda-ualib`_ library, this is mainly due to The Authors.

HOWEVER, we have benefited from the outstanding lecture notes on `Univalent Foundations and Homotopy Type Theory <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes>`_ and the `Type Topology`_ Agda Library, both by `Martin Hötzel Escardo <https://www.cs.bham.ac.uk/~mhe>`_.  The first author is greatly indebted to Martin for teaching him about type theory in Agda at the `Midlands Graduate School in the Foundations of Computing Science <http://events.cs.bham.ac.uk/mgs2019/>` in Birmingham in 2019.

The development of the `agda-ualib`_ and its documentation is informed by and benefits from the references listed in the :ref:`references` section below.

----------------------

.. _references:

References
------------

The following Agda documentation and tutorials are excellent.  They have been quite helpful to The Author of `agda-ualib`_, and have informed the development of the latter and its documentation.

* Altenkirk, `Computer Aided Formal Reasoning`_
* Bove and Dybjer, `Dependent Types at Work`_
* Escardo, `Introduction to Univalent Foundations of Mathematics with Agda`_
* Gunther, Gadea, Pagano, `Formalization of Universal Algebra in Agda`_
* János, `Agda Tutorial`_
* Norell and Chapman, `Dependently Typed Programming in Agda`_
* Wadler, `Programming Language Foundations in Agda`_

Finally, the official `Agda Wiki`_, `Agda User's Manual`_, `Agda Language Reference`_, and the (open source) `Agda Standard Library`_ source code are also quite useful.

-----------------------------------


.. rubric:: Footnotes

.. [1]
   See, e.g., `this <http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/33/slides/Ulf.pdf>`_ or
   `that <https://www.cs.cornell.edu/Info/Projects/NuPrl/book/node94.html>`_.

----------------------

.. include:: hyperlink_references.rst

