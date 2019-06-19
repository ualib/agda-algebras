.. _axioms_and_computation:

Computation
===========

**Citation/Credit**. This section is based on a chapter that appeared in Logic and Proof (:cite:`logic-and-proof`).

We have seen that the version of the :term:`Calculus of Inductive Constructions` (CiC) implemented in Lean includes :term:`dependent function types <dependent function type>`, :term:`inductive types <inductive type>`, and a hierarchy of :term:`universes` that starts with an :term:`impredicative`, :term:`proof-irrelevant` ``Prop`` at the bottom.

In this chapter, we consider ways of extending the :term:`CiC` with additional axioms and rules. Extending a foundational system in such a way is often convenient; it can make it possible to prove more theorems, as well as make it easier to prove theorems that could have been proved otherwise.

But there can be negative consequences of adding additional axioms, consequences which may go beyond concerns about their correctness. In particular, the use of axioms bears on the computational content of definitions and theorems, in ways we will explore.

-------------------------------------------------

.. index:: proposition extensionality, quotient, function extensionality, law of the excluded middle, Choice

Classical and constructive reasoning
------------------------------------

Lean is designed to support both **computational** and **classical reasoning**.

Users who can stick to a "computationally pure" fragment of logic, which guarantees that closed expressions in the system evaluate to :term:`canonical normal forms <canonical normal form>`. For example, any closed computationally pure expression of type ℕ will reduce to a number value.

`Lean's standard library <lean_src>`_ defines an additional axiom, :term:`proposition extensionality`, and a :term:`quotient` construction which in turn implies the principle of :term:`function extensionality`.  These extensions are used, for example, to develop theories of sets and finite sets.

We will see below that using these theorems can block evaluation in Lean's kernel, so that closed terms of type ℕ no longer evaluate to number values.

But *Lean erases types and propositional information when compiling definitions to :term:`bytecode` for its virtual machine evaluator*, and since these axioms only add new propositions, they are compatible with that computational interpretation.

Even computationally inclined users may wish to use the classical **law of the excluded middle** axiom to reason about computation. This also blocks evaluation in the kernel, but it is compatible with compilation to :term:`bytecode`.

The `standard library <lean_src>`_ also defines a **Choice** principle that is entirely antithetical to a computational interpretation, since it magically produces "data" from a proposition asserting its existence.

Use of Choice is essential to some classical constructions, and users can import it when needed, but *expressions that use Choice to produce data do not have computational content*.  In Lean we are required to mark such definitions ``noncomputable`` to flag this fact.

Using a clever trick (known as Diaconescu's theorem), one can use :term:`proposition extensionality`, :term:`function extensionality`, and :term:`Choice` to derive the :term:`law of the excluded middle`.

*However*, as noted above, use of :term:`em` is still compatible with :term:`bytecode` compilation and :term:`code extraction`, as are other classical principles, *as long as they are not used to manufacture data*.

To summarize, then, on top of the underlying framework of :term:`universes`, :term:`dependent function types <dependent function type>`, and :term:`inductive types <inductive type>`, the `standard library <lean_src>` adds three additional (optional) components:

+ the axiom of :term:`proposition extensionality`
+ a :term:`quotient` construction, which implies :term:`function extensionality`
+ a :term:`Choice` principle, which produces data from an existential proposition.

The first two of these block normalization within Lean, but are compatible with :term:`bytecode` evaluation, whereas the third is not amenable to computational interpretation. We will spell out the details more precisely below.

----------------------------------

.. rubric:: Footnotes

.. .. [2]
..    **Answer**. Each :math:`f` "chooses" an element from each :math:`A_i`, but when the :math:`A_i` are distinct and :math:`I` is infinite, we may not be able to do this. The :ref:`Axiom of Choice <axiom-of-choice-1>` ("Choice") says you can. Gödel proved that Choice is consistent with the other axioms of set theory. Cohen proved that the negation of Choice is also consistent.

.. _Agda: https://wiki.portal.chalmers.se/agda/pmwiki.php

.. _Coq: http://coq.inria.fr

.. _NuPRL: http://www.nuprl.org/

.. _Lean: https://leanprover.github.io/

.. _Logic and Proof: https://leanprover.github.io/logic_and_proof/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _mathlib: https://github.com/leanprover-community/mathlib/

.. _lean_src: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/


