.. include:: _static/math_macros.rst

======
 Lean
======

.. Sections of set_theory.rst
.. ---------------------------
.. Products of Sets
.. Relations
..   Equivalence relations, partial orders
..   The poset induced by a preorder
..   Joins and meets
..   Relations of higher arity
.. Functions
..   Projections
.. Directed sets and inductive sets
.. Completeness and cocompleteness
.. Closure systems

.. Sections of set_theory_in_lean.rst
.. -----------------------------------
.. Union and intersection in Lean
.. Products in Lean
..   Pi Type
..   Sigma Type
.. Relations in Lean
..   Poset induced by a preorder
..   Joins and meets
..   Relations of higher arity
.. Functions in Lean
..   Projections

.. todo:: add chapter introduction

Sets in Lean
------------

The code described in this subsection comes from set.lean_, basic.lean_, and lattice.lean_.

Let :math:`S` be a set of sets of type :math:`α`.

.. _intersection-and-union:

Intersection and union
~~~~~~~~~~~~~~~~~~~~~~

In lattice.lean_, the **intersection** of the sets in :math:`S` is denoted by ``⋂₀ S``.

.. code-block:: lean

   import data.set
   variable S : set (set α)
   #check ⋂₀ S          -- answer: set α

Here is the formal definition from the file lattice.lean_.

.. code-block:: lean

    /-- Intersection of a set of sets. -/
    @[reducible]
    def sInter (S : set (set α)) : set α := Inf S

    prefix `⋂₀`:110 := sInter

The **union of sets** is implemented in lattice.lean_ similarly.

.. code-block:: lean

   @[reducible]
   def sUnion (s : set (set α)) : set α := {t | ∃ a ∈ s, t ∈ a}
   prefix `⋃₀`:110 := sUnion

-------------------------------------------

.. _products-in-lean:

Products in Lean
-----------------

.. todo:: complete this section

-------------------------------------------------

.. index:: relation, binary relation, preorder, partial order, equivalence relation
.. index:: domain, range

.. index:: equivalence relation, partial ordering
.. index:: pair: partially ordered set; poset

.. _relations-in-lean:

Relations in Lean
------------------

An **equivalence relation** is a symmetric preorder. We denote the set of all equivalence relations on a set :math:`X` by :math:`\mathrm{Eq}(X)`.

A **partial ordering** (or "partial order") is an anti-symmetric preorder.  A **partially ordered set** (or "poset") :math:`⟨X, R⟩` is a set :math:`X` along with a partial order :math:`R` defined on :math:`X`.


The poset induced by a preorder
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

.. index:: ! ordered tuples, !tuples
.. index:: ! unary relation, ! binary relation, ! ternary relation

Relations of higher arity
~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

---------------------------------

.. index:: ! function, ! inverse, ! function composition, ! restriction, ! image

Functions in Lean
------------------

.. todo:: complete this section

.. index:: ! projection, ! idempotent operation

.. _projections-in-lean:

Projections
~~~~~~~~~~~

.. todo:: complete this section

.. index:: ! generalized projection

Generalized projection
~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

.. index:: ! kernel

Kernel
~~~~~~

.. todo:: complete this section

.. index:: ! join, ! upper bound, ! least upper bound, ! supremum
.. index:: ! meet, ! lower bound, ! greatest lower bound, ! infimum

Joins and meets
~~~~~~~~~~~~~~~

.. todo:: complete this section

------------------------------

.. index:: dependent types 

.. _dependent-types-in-lean:

Dependent types in Lean
------------------------

.. todo:: complete this section

.. index:: type of; dependent functions (Pi type)

.. _pi-type:

Pi Type
~~~~~~~

The **Pi type** ``Π(x:A),B x``, also known as the **dependent function type**, generalizes the function type ``A → B`` and is called a *dependent type* because the codomain ``B x`` may depend on the value ``x: A``.

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
    { f | ∀ a ∈ i, f a ∈ s a }

.. index:: type of; dependent pairs (Sigma type)

.. _sigma-type:

Sigma Type
~~~~~~~~~~~

The **Sigma type** ``Σ(x:A),B x``, also known as the **dependent pair type**, generalizes the Cartesian product ``A × B`` by allowing the type ``B x`` of the second argument of the ordered pair to depend on the value ``x`` of the first.

.. code-block:: lean

    structure sigma {α : Type u} (β : α → Type v) :=
    mk :: (fst : α) (snd : β fst)

    structure psigma {α : Sort u} (β : α → Sort v) :=
    mk :: (fst : α) (snd : β fst)

------------------------------

.. index:: dependent type theory, inductive type, universes

.. _inductive-types-in-lean:

Inductive types in Lean
------------------------

.. todo:: complete this section

----------------------------------

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


