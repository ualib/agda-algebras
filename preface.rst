=======
Preface
=======

This work describes the `Lean Universal Algebra Library`_ in enough detail so that people other than the library developers may be able to understand it well enough to make use of it.

-----------------------------------

Motivation
----------

To support the formalization of theorems, we are developing software libraries that contain formal statements and proofs of the core definitions and results universal algebra. Our objectives include

+ incorporating automated proof search for universal algebra;
+ formalizing theorems emerging from our own mathematics research;
+ developing domain specific "proof tactics" to express the idioms of universal algebra;
+ documenting the resulting software library so that others may find it useful.

For our own mathematics research projects, a proof assistant equipped with special libraries of definitions and results from algebra and lattice theory, as well as specialized tactics to automate the standard proof idioms of our field, will be very useful. Our goal is to demonstrate (to ourselves and our colleagues) the utility of such libraries and tactics for proving "real world" theorems.

-----------------------------------

Why Lean?
---------

We chose the Lean_ proof assistant because it is designed and developed by logicians and computer scientists working together to create a language and syntax that presents mathematical theorems and proofs *as they should be*, by which we mean that working in the language feels almost as natural as working in the informal language of mathematics and is easily adopted by mathematicians who lack special training in computer science.

Lean_ is a relatively new programming language and proof assistant developed at Microsoft Research and Carnegie Mellon University. Lean_ draws on decades of experience in interactive and automatic theorem provers (e.g., Coq, Isabelle/HOL, and Z3). Its logic is very expressive, and emphasis is placed on *powerful proof automation*. The system is easy to extend via :ref:`metaprograms <metaprogramming>` developed in the same language used to express specifications and proofs in Lean. In this way, Lean_ narrows the gap between interactive and automated theorem proving.

There are many other reasons Lean_ is an excellent platform for this project. For instance, it is unique among computer-based theorem proving tools in that its *proofs tend to be easy to read and understood* without special training. In fact, working in Lean_ usually leads to formal proofs that are cleaner, more concise, and shorter than the corresponding proofs in the language of informal mathematics.

Lean_ is a very young language, and its domain-specific libraries are small but growing. We feel it is vital to get involved at this early stage and play a role in its development. If we leave it to our colleagues in computer science, they will likely have our *perceived* needs and use cases in mind, and the libraries and tools that come out of their effort may not meet the needs and expectations of most working mathematicians.

We conclude this section with a note that is important for anyone interested in `Homotopy Type Theory`_ (HoTT).  Unfortunately, the current version of Lean_ does not support HoTT. There is, however, a frozen version (`Lean 2`_) that does supports HoTT and there is a `2015 post by Floris van Doorn`_ that gives a nice overview of the use of `Lean 2`_ for homotopy type theory.

-----------------------------------

Prerequisites
-------------

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra (as presented in, say, :cite:`Bergman:2012` or :cite:`McKenzie:1987`) and, to a lesser extent, category theory (as presented by `categorytheory.gitlab.io`_ or `Category Theory in Context`_). Category theory is not needed until :numref:`Section %s <postmodern-algebra>`.

Some prior exposure to :term:`type theory (TT) <TT>` and Lean_ would be helpful, but one could probably get by with what is included in the appendices and the glossary, consulting one or more of the following to fill in gaps as needed:

  + `Lean Tutorial <https://leanprover.github.io/tutorial/>`_
  + `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_
  + `The Lean Reference Manual <https://leanprover.github.io/reference/>`_
  + `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_
  + `Type Theory and Formal Proof <https://www.cambridge.org/vi/academic/subjects/computer-science/programming-languages-and-applied-logic/type-theory-and-formal-proof-introduction>`_

-----------------------------------

Acknowledgments
---------------

This tutorial is an open access project maintained on Gitlab. Besides the authors named below, a number of other people have also contributed to the ualib project.  We are especially grateful to Jeremy Avigad, Andrej Bauer, Clifford Bergman, Peter Jipsen, Miklos Maroti, and Ralph Freese for many helpful discussions, as well as the invaluable instruction, advice, and encouragement that they continue to lend to this project (often without knowing it).

----------------------

Feedback
--------

This is a work in progress and any feedback you can give would be much appreciated.  Please direct all comments, questions, or suggestions to `William DeMeo <mailto:williamdemeo@gmail.com>`_.

.. _Lean: https://leanprover.github.io/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _Lean Universal Algebra Library: https://github.com/UniversalAlgebra/lean-ualib/

.. _Lean 2: https://github.com/leanprover/lean2

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/

.. _Homotopy Type Theory: https://homotopytypetheory.org/

.. _categorytheory.gitlab.io: https://categorytheory.gitlab.io/index.html

.. _Category Theory in Context: http://www.math.jhu.edu/~eriehl/context.pdf