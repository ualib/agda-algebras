=======
Preface
=======

This work describes the `Lean Universal Algebra Library`_ in enough detail so that people other than the library developers may be able to understand it well enough to make use of it.

Motivation
----------

To support the formalization of theorems, we are developing software libraries that contain formal statements and proofs of the core definitions and results universal algebra. Our objectives include 

+ incorporating automated proof search for universal algebra;
+ formalizing theorems emerging from our own mathematics research;
+ developing domain specific "proof tactics" to express the idioms of universal algebra;
+ documenting the resulting software library so that others may find it useful.

For our own mathematics research projects, a proof assistant equipped with special libraries of definitions and results from algebra and lattice theory, as well as specialized tactics to automate the standard proof idioms of our field, will be very useful. Our goal is to demonstrate (to ourselves and our colleagues) the utility of such libraries and tactics for proving "real world" theorems.

Why Lean?
---------

We chose the Lean_ proof assistant because it is designed and developed by logicians and computer scientists working together to create a language and syntax that presents mathematical theorems and proofs *as they should be*, by which we mean that working in the language feels almost as natural as working in the informal language of mathematics and is easily adopted by mathematicians who lack special training in computer science.

Lean_ is a relatively new programming language and proof assistant developed at Microsoft Research and Carnegie Mellon University. Lean_ draws on decades of experience in interactive and automatic theorem provers (e.g., Coq, Isabelle/HOL, and Z3). Its logic is very expressive, and emphasis is placed on *powerful proof automation*. The system is easy to extend via :ref:`metaprograms <metaprogramming>` developed in the same language used to express specifications and proofs in Lean. In this way, Lean_ narrows the gap between interactive and automated theorem proving.

There are many other reasons Lean_ is an ideal platform for this project. For instance, it is unique among computer-based theorem proving tools in that its *proofs tend to be easy to read and understood* without special training. In fact, working in Lean_ usually leads to formal proofs that are cleaner, more concise, and shorter than the corresponding proofs in the language of informal mathematics.

Lean_ is a very young language, and its domain-specific libraries for special disciplines are small but growing. We feel it is vital for us to get involved at this early stage and play a leading role in its development. If we leave all of this to our colleagues in computer science, they will base the development on their perception of our needs, history will likely repeat itself, and it is unlikely that the libraries and tools that come out of the effort will meet the needs and
expectations of most working mathematicians.

.. _Lean: https://leanprover.github.io/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _Lean Universal Algebra Library: https://github.com/UniversalAlgebra/lean-ualib/
