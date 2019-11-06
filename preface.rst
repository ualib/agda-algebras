.. File: preface.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 17 May 2019
.. Updated: 5 Nov 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

=======
Preface
=======

Vision
----------

To support the formalization of mathematical theorems in type theory, we have begun developing a software library, called the `Lean Universal Algebra Library`_ (or 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 for short).  Our library contains formal statements and proofs of some of the core, foundational definitions and results universal algebra.

Our vision for the 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 project originated with the observation that, on the one hand, a number of the most basic and important constructs in universal algebra can be defined recursively, while on the other hand, the types of :term:`type theory`---in particular, :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`---make possible elegant representations of recursively defined objects, as well as concise proofs of their properties.

Indeed, our mathematical theories can be codified in type theory using a Lean_, which is a programming language and :term:`proof assistant` that not only supports dependent and inductive types, but also provides powerful :term:`proof tactics <proof tactic>` for proving properties of the objects that inhabit these types.

These observations suggest that there is much to gain from implementing universal algebra in a proof assistant that facilitates working with :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`. Lean is one such proof assistant.

The goal of 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 (and this document) is to start with the edifice upon which our mathematical research stands and show that it can be encoded effectively in type theory in such a way that we and other working mathematicians can use the resulting library to do "real" research mathematics.

Our field is deep and its history rich, so encoding all of our subject's foundations is a daunting and even risky task.  However, our view is that the basics of the theory can stand to be modernized and presented in cleaner, more elegant, and more :term:`constructive` way so that universal algebra can be naturally presented in the language of type theory and formally codified in the Lean proof assistant.

.. Specific examples will be given below in :numref:`subalgebras-in-lean`, :numref:`terms-in-lean`, and :numref:`clones-in-lean`.

Finally, it is important to point out that this is not merely an exercise in translation.  Indeed, Lean was designed with the goal of creating a system in which one could conduct "real" mathematics research, and that is how we intend to use it once we have acheived the goal of implementing the most basic and important parts of the existing theory in a usable Lean library.

-----------------------------------

Objectives
---------------

Our objectives include

+ incorporating automated proof search for universal algebra;
+ formalizing theorems emerging from our own mathematics research;
+ developing domain specific "proof tactics" to express the idioms of universal algebra;
+ documenting the resulting software library so that others may find it useful.

For our own mathematics research projects, a proof assistant equipped with special libraries of definitions and results from algebra and lattice theory, as well as specialized tactics to automate the standard proof idioms of our field, will be very useful. Our goal is to demonstrate (to ourselves and our colleagues) the utility of such libraries and tactics for proving "real world" theorems.

-----------------------------------

Why Lean?
---------

We chose the Lean_ proof assistant because it is designed and developed by logicians and computer scientists working together to create a language and syntax that presents mathematical theorems and proofs *as they should be*, by which we mean that working in the language feels almost as natural as working in the informal language of mathematics and is easily adopted by mathematicians who lack special training in computer science.

Lean is a relatively new programming language and proof assistant developed at Microsoft Research and Carnegie Mellon University. Lean draws on decades of experience in interactive and automatic theorem provers (e.g., `Coq`_, Isabelle/HOL, and Z3). Its logic is very expressive, and emphasis is placed on *powerful proof automation*. The system is easy to extend via :ref:`metaprograms <metaprogramming>` developed in the same language used to express specifications and proofs in Lean. In this way, Lean narrows the gap between interactive and automated theorem proving.

There are many other reasons Lean is an excellent platform for this project. For instance, it is unique among computer-based theorem proving tools in that its *proofs tend to be easy to read and understood* without special training. In fact, working in Lean usually leads to formal proofs that are cleaner, more concise, and shorter than the corresponding proofs in the language of informal mathematics.

Lean is a very young language, and its domain-specific libraries are small but growing. We feel it is vital to get involved at this early stage and play a role in its development. If we leave it to our colleagues in computer science, they will likely have our *perceived* needs and use cases in mind, and the libraries and tools that come out of their effort may not meet the needs and expectations of most working mathematicians.

We conclude this section with a note that is important for anyone interested in `Homotopy Type Theory`_ (HoTT).  Unfortunately, the current version of Lean does not support HoTT. There is, however, a frozen version (`Lean 2`_) that does supports HoTT and there is a `2015 post by Floris van Doorn`_ that gives a nice overview of the use of Lean 2 for homotopy type theory.

-----------------------------------

Intended audience
------------------

This document describes the 𝖫∃∀𝖭 ⋀𝗅𝗀𝖾𝖻𝗋𝖺 project and the associated Lean library (lean-ualib_) Lean Universal Algebra Library with (hopefully) enough details so that working mathematicians, and possibly some normal people, might be able to learn enough about Lean and our library to put them to use when creating, formalizing, and verifying new mathematics.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra (as presented in, say, :cite:`Bergman:2012` or :cite:`McKenzie:1987`) and, to a lesser extent, category theory (as presented by categorytheory.gitlab.io_ or `Category Theory in Context`_). Category theory is not needed until :numref:`Chapter %s <postmodern-algebra>`.

Some prior exposure to :term:`type theory` and Lean would be helpful, but even without this background one might still be able to get something useful out of this by referring to the appendix and glossary, while simultaneously consulting one or more of the following references to fill in gaps as needed:

  + `Lean Tutorial`_
  + `Theorem Proving in Lean`_
  + `Lean Reference Manual`_
  + `Logic and Proof`_
  + `Type Theory and Formal Proof`_ :cite:`Nederpelt:2014`

Finally, it is assumed that while reading this manual the reader is actively experimenting with Lean using vscode_ with its `lean extension`_ installed.  It is possible to interface with Lean using the Emacs_ editor, but users of Emacs must keep in mind that some of our instructions may not work in that environment.  (For example, we will explain how one produces certain special unicode characters, and the procedure may be different for other IDE's.)

-------------------------

Installing the library
-----------------------------

The main repository for the lean-ualib_ is https://gitlab.com/ualib/lean-ualib.

There are installation instructions in the main README.md file in that repository. Nonetheless, here is a summary.

(We assume you have the ``lean`` and ``leanpkg`` programs installed on your machine. If not, follow the directions on `the main Lean website <Lean>`_ to install them.)

#. clone the lean-ualib_ repository with, e.g.,

   ```sh
   git clone git@gitlab.com:ualib/lean-ualib.git
   ```

   OR

   ```sh
   git clone https://gitlab.com/ualib/lean-ualib.git
   ```

#. Change into the lean-ualib directory and run `leanpkg build`:

   ```sh
   cd lean-ualib;
   leanpkg build
   ```

-----------------------------------

Acknowledgments
---------------

This manual and the software library that it documents are open access projects maintained on Gitlab. Besides the main authors, a number of other people have also contributed to the ualib project.  We are especially grateful to Jeremy Avigad, Andrej Bauer, Clifford Bergman, Peter Jipsen, Miklos Maroti, and Ralph Freese for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project (often without knowing it).

----------------------

Feedback
--------

This is a work in progress and any feedback you can provide us with would be much appreciated.  Please direct comments, questions, or suggestions to William DeMeo `at gmail dot com <mailto:williamdemeo@gmail.com>`_.  (Alternatively, feedback can be provided by `posting to the ualib gitlab <https://gitlab.com/ualib/lean-ualib/issues/new>`_ repository.)

---------------------------

.. rubric:: Footnotes

.. [1]
   As of this writing (9 June 2019), this documentation describes code residing in (the william_ branch of) the `lean-ualib`_ repository. Eventually, the latest code will reside on the master_ branch and the docs will describe the code on that branch.

.. [2]
   For some reason, the following references cannot be found by the sphinx compiler when cited elsewhere unless we cite them here first: :cite:`Mitchell:1996,HoTT:2013`.

.. include:: hyperlink_references.rst

.. For some reason, the following references cannot be found by the sphinx compiler when cited elsewhere unless we cite them here first: :cite:`Mitchell:1996,Nederpelt:2014,HoTT:2013`.

