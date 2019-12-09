.. File: preface.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 17 May 2019
.. Updated: 6 Nov 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

=======
Preface
=======

Due to a claims of plagiarism, I have removed the notes that I had previously posted here.

I apologize if you are visiting this page hoping to learn how to use Lean to do mathematics.

Please consult the "official" sources.

.. To support formalization in type theory of research level mathematics in universal algebra and related fields, we have developed a software library, called the `Lean Universal Algebra Library`_ ("Lean Algebra" or 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺).  Our library contains formal statements and proofs of some of the core, foundational definitions and results universal algebra.

.. Vision
.. ----------

.. The idea for 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand types (of :term:`type theory`---in particular, :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`) make possible elegant formal representations of recursively defined objects, as well as concise proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

.. Lean_ is a programming language and :term:`proof assistant`, or "interactive theorem prover" (ITP), that not only supports dependent and inductive types, but also provides powerful :term:`proof tactics <proof tactic>` for proving properties of the objects that inhabit these types. 

.. The goal of the 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 project is to formalize, in the Lean language, the substantial edifice upon which our mathematical research stands, demonstrating that our work can be implemented formally and effectively in type theory in such a way that we and other working mathematicians can use the resulting library to conduct and formalize further mathematics research.

.. Our field is deep and its history rich, so encoding all of our subject's foundations may seem like a daunting task and possibly risky investment of time and resources.  However, our view is that the basics of the theory could be well served by a modernized and (where possible) :term:`constructive` presentation, so that universal algebra could be naturally codified in the language of type theory and formally implemented in, and verified by, the Lean proof assistant.

.. .. Specific examples will be given below in :numref:`subalgebras-in-lean`, :numref:`terms-in-lean`, and :numref:`clones-in-lean`.

.. -----------------------------------

.. Objectives
.. ---------------

.. We wish to emphasize that our ultimate objective is not a mere translation of existing results into a more modern and formal language.  Indeed, one important goal of the Lean development team is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Lean.

.. To this end, our main objectives include

.. + developing domain specific "proof tactics" to express the idioms of universal algebra,
.. + incorporating automated proof search for universal algebra, and
.. + formalizing theorems emerging from our own mathematics research,
.. + documenting the resulting software libraries so they are useable by other working mathematicians.

.. For our own mathematics research, we believe a proof assistant equipped with specialized libraries for universal algebra, as well as domain-specific tactics to automate proof idioms of our field, will be extremely useful. Our goal is to demonstrate (to ourselves and colleagues) the utility of such libraries and tactics for proving new theorems.

.. -----------------------------------

.. Why Lean?
.. ---------

.. Lean_ is a relatively new programming language and proof assistant developed at Microsoft Research and Carnegie Mellon University. The language draws on decades of experience in interactive and automated theorem provers (e.g., `Coq`_, Isabelle/HOL, and Z3). Its logic is very expressive and facilitates powerful proof automation. The system is easy to extend via :term:`metaprograms <metaprogram>` that can be written *in the Lean language itself*. In this way, Lean narrows the gap between interactive and automated theorem proving.

.. Because it is designed and developed by logicians and computer scientists working together to create a language and syntax that presents mathematical theorems and proofs *as they should be*, working in the language feels almost as natural as working in the informal language of mathematics. Therefore, the Lean libraries that we develop should be easily adopted by working mathematicians, including those who lack special training in computer science.

.. We chose the Lean proof assistant for these reasons, but there are other reasons Lean has turned out to be an excellent platform for this project. For instance, it is unique among computer-based theorem proving tools in that its *proofs tend to be easy to read and understood*. In fact, working in Lean often leads to formal proofs that are clearer and more concise than proofs that are constructed and presented in the language of informal mathematics.

.. Lean is a relatively young language, and its domain-specific libraries are small but growing. Thus is the stage at which we must be involved in Lean's development. If this effort rests solely on the shoulders of our expert and eminently capable colleagues in computer science, then the sophisticated libraries and powerful tools that they produce may, in the end, fail to meet the basic needs and expectations of the working mathematician.

.. We conclude this section with a remark that is important for those interested in `homotopy type theory`_ (HoTT).  Unfortunately, the current version of Lean does not fully support the :term:`proof-relevant` mathematics on which the univalent foundations program is based. There is, however, a frozen version of of the language (`Lean 2`_) which does support HoTT. [1]_

.. The next release of Lean will be `Lean 4`_ which, at the time of this writing, is not yet released.  Lean 4 has been in the works for quite some time.  We do not know whether Lean 4 will support proof-relevant mathematics and the univalent foundations program.

.. -----------------------------------

.. Intended audience
.. ------------------

.. This document describes the Lean Algebra project and the associated Lean Universal Algebra Library (lean-ualib_) in enough detail so that working mathematicians (and possibly some normal people) might be able to learn enough about Lean and its libraries to put them to use when creating, formalizing, and verifying new mathematics.

.. While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, :cite:`Bergman:2012` or :cite:`McKenzie:1987`, and to a lesser extent category theory, as presented in categorytheory.gitlab.io_ or :cite:`Riehl:2017`. (Category theory is not really needed until :numref:`Chapter %s <postmodern-algebra>`.)

.. Some prior exposure to :term:`type theory` and Lean would be helpful, but even without this background one might still be able to get something useful out of this by referring to the appendix and glossary, while simultaneously consulting one or more of the following references to fill in gaps as needed:

..   + `Lean Tutorial`_
..   + `Theorem Proving in Lean`_
..   + `Lean Reference Manual`_
..   + `Logic and Proof`_
..   + `Type Theory and Formal Proof`_ :cite:`Nederpelt:2014`

.. Finally, it is assumed that while reading this manual the reader is actively experimenting with Lean using vscode_ with its `lean extension`_ installed.  It is possible to interface with Lean using the Emacs_ editor, but users of Emacs must keep in mind that some of our instructions may not work in that environment.  (For example, we will explain how one produces certain special unicode characters, and the procedure may be different for other IDE's.)

.. -------------------------

.. Installing the library
.. -----------------------------

.. The main repository for the lean-ualib_ is https://gitlab.com/ualib/lean-ualib.

.. There are installation instructions in the main README.md file in that repository. Nonetheless, here is a summary.

.. (We assume you have the ``lean`` and ``leanpkg`` programs installed on your machine. If not, follow the directions on `the main Lean website <Lean>`_ to install them.)

.. #. clone the lean-ualib_ repository with, e.g.,

..    .. code-block:: bash

..       git clone git@gitlab.com:ualib/lean-ualib.git


..    OR

..    .. code-block:: bash

..       git clone https://gitlab.com/ualib/lean-ualib.git


.. #. Change into the lean-ualib directory and run `leanpkg build`:

..    .. code-block:: bash

..       cd lean-ualib; leanpkg build

.. -----------------------------------

.. Acknowledgments
.. ---------------

.. This manual and the software library that it documents are open access projects maintained on Gitlab. Besides the main authors, a number of other people have contributed to the 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 project.  We are especially grateful to Jeremy Avigad, Andrej Bauer, Clifford Bergman, Venanzio Capretta, Peter Jipsen, Miklos Maroti, and Ralph Freese for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project (often without knowing it).

.. ----------------------

.. Feedback
.. --------

.. This is a work in progress and any feedback you can provide us with would be much appreciated.  Please direct comments, questions, or suggestions to William DeMeo `at gmail dot com <mailto:williamdemeo@gmail.com>`_.  (Alternatively, feedback can be provided by `posting to the ualib gitlab <https://gitlab.com/ualib/lean-ualib/issues/new>`_ repository.)

.. ---------------------------

.. .. rubric:: Footnotes

.. .. [1]
..    See the `2015 post by Floris van Doorn`_ which gives a nice overview of Lean 2 for homotopy type theory.
 
.. .. [2]
..    For some reason, the following references cannot be found by the sphinx compiler when cited elsewhere unless we cite them here first: :cite:`Mitchell:1996,HoTT:2013`.

.. .. include:: hyperlink_references.rst

.. .. For some reason, the following references cannot be found by the sphinx compiler when cited elsewhere unless we cite them here first: :cite:`Mitchell:1996,Nederpelt:2014,HoTT:2013`.

