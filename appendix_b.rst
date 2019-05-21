.. include:: _static/math_macros.rst

.. _appendix-b:

=======================
Appendix B: Lean Basics
=======================

In this appendix we describe various features and aspects of Lean_ that we have made use of in the lean-ualib_.

Some of the things described here will come from the Lean_ standard library.  Others will be from the mathlib_ Lean community project, and possible other projects.

Some good references for this material are

  + `Lean Tutorial <https://leanprover.github.io/tutorial/>`_
  + `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_
  + `The Lean Reference Manual <https://leanprover.github.io/reference/>`_
  + `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_

.. _leans-type-hierarchy:

Lean's type hierarchy [1]_
---------------------------

Like its more mature cousins Coq and Agda, Lean_ takes for its logical foundations *dependent type theory* with *inductive types* and *universes*. However, unlike Coq or Agda, Lean's universes are *not cumulative*.  This is not a problem since, in places where we might exploit universe cumulativity in Coq, we can instead use *universe polymorphism* and the *lift map* explicitly.

Sort and Type
~~~~~~~~~~~~~

The following excerpt from the `Lean Reference Manual`_ explains the correspondence between ``Sort`` and ``Type``.

  Every type in Lean is, by definition, an expression of type ``Sort u`` for some universe level ``u``. A universe level is one of the following:

  + a natural number, ``n``
  + a universe variable, ``u`` (declared with the command universe or universes)
  + an expression ``u + n``, where ``u`` is a universe level and ``n`` is a natural number
  + an expression ``max u v``, where ``u`` and ``v`` are universes
  + an expression ``imax u v``, where ``u`` and ``v`` are universe levels

  The last one denotes the universe level 0 if ``v`` is 0, and ``max u v`` otherwise.

  .. code-block:: lean

     universes u v                    -- Lean Output
                                      -- -----------
     #check Sort u                    -- Sort u : Type u
     #check Sort 5                    -- Type 4 : Type 5
     #check Sort (u + 1)              -- Type u : Type (u+1)
     #check Sort (u + 3)              -- Type (u+2) : Type (u+3)
     #check Sort (max u v)            -- Sort (max u v) : Type (max u v)
     #check Sort (max (u + 3) v)      -- Sort (max (u+3) v) : Type (max (u+3) v)
     #check Sort (imax (u + 3) v)     -- Sort (imax (u+3) v) : Type (imax (u+3) v)
     #check Prop                      -- Prop : Type
     #check Type                      -- Type : Type 1

.. index:: keyword: Type, Type 0, Type 1, ...

Lean_ has a hierarchy of :math:`\omega`-many type universe levels. We want some operations to be *polymorphic* over type universes.

For example, ``list α`` should make sense for any type ``α``, no matter which universe ``α`` lives in. This explains why ``list`` has the following type signature:

.. code-block:: lean

   #check @list    -- answer: Type u → Type u

Here ``u`` is a variable ranging over type levels.

Think of ``Type 0`` as a universe of "small" or "ordinary" types. ``Type 1`` is then a larger universe of types that contains ``Type 0`` as an *element*, and ``Type 2`` is an even larger universe of types, that contains ``Type 1`` as an element. The list is indefinite, so that there is a ``Type n`` for every natural number ``n``. ``Type`` is an abbreviation for ``Type 0``.

.. index:: ! predicative, ! ramified, ! impredicative
.. index:: keyword: Prop

The upshot of this **ramified** arrangement is that the types described in the last paragraph are :term:`predicative`, which means that their definitions are not self-referential. By avoiding self-referential definitions, we avoid Russel's paradox. However, in certain specific situations we *do* want to employ a self-referential type, so Lean_ supplies us with exactly one. It is the type ``Prop`` of propositions, and it is :term:`impredicative` (self-referential).

.. _pattern-matching:

Pattern matching
----------------

.. todo:: complete this section

---------------------------------------

Next we collect for easy reference a list of some basic but important components from the Lean_ standard library.

.. index:: type of; dependent functions (Pi type)

.. _pi-type:

Pi Type
-------

The **Pi type** ``Π(x:A),B x``, also known as the **dependent function type**, generalizes the function type ``A → B`` and is called a *dependent type* because the codomain ``B x`` may depend on the value ``x: A``.

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
    { f | ∀ a ∈ i, f a ∈ s a }

.. index:: type of; dependent pairs (Sigma type)

.. _sigma-type:

Sigma Type
----------

The **Sigma type** ``Σ(x:A),B x``, also known as the **dependent pair type**, generalizes the Cartesian product ``A × B`` by allowing the type ``B x`` of the second argument of the ordered pair to depend on the value ``x`` of the first.

.. code-block:: lean

    structure sigma {α : Type u} (β : α → Type v) :=
    mk :: (fst : α) (snd : β fst)

    structure psigma {α : Sort u} (β : α → Sort v) :=
    mk :: (fst : α) (snd : β fst)



.. _intersection:

Union and Intersection
~~~~~~~~~~~~~~~~~~~~~~

The code described in this subsection comes from set.lean_, basic.lean_, and lattice.lean_.

Let :math:`S` be a set of sets of type :math:`α`.

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

----------------------------------------------------------

.. _coercion:

Coercion
--------

**References**. `Coercions`_ and `Coercions using Type Classes`_ sections of `TPL`_

A very nice feature of Lean, called coercion, enables us to identify two objects that we think of as "the same" but that are of different types. This kind of thing happens implicitly in virtually all informal mathematical arguments.

Here's a simple example. Suppose we have an integer :math:`z : ℤ` and a natural number :math:`n : ℕ`.  Most people would not hesitate to form the sum :math:`z + n`.  Of course, this doesn't make sense since (in type theory as well as set theory), natural numbers are not integers!  That is, :math:`ℕ ⊈ ℤ`, despite what your highschool math teacher told you.

However, it is true that the set of natural numbers can be embedded in ℤ in a natural way, and Lean_ allows us to express this embedding using coercions.

Here's how the example just discussed is handled in Lean_.

.. code-block:: lean

   variable n : ℕ
   variable z : ℤ
   #check z + n      -- z + ↑n : ℤ

Indeed, the addition is handled automatically in this case.  But notice the coercion symbol ``↑`` that appears in the output of ``#check``. The up arrow is notation for the Lean_ function ``coe``; it can be typed with ``\u``, but ``coe`` could be used instead.

In fact, an explicit ``↑`` must appear in certain cases, in particular when Lean_ is not aware in advance that a coercion is needed.

If we change the order of the arguments of ``#check`` in the example above, we get an error unless we tell Lean_ about the required coercion.

.. code-block:: lean

   -- #check n + z        -- error!
   #check ↑n + z          -- ↑n + z : ℤ

Lean_ allows various kinds of coercions using type classes; for details, see the `Coercions using Type Classes`_ section of `TPL`_.

.. _the-elaboration-engine:

Elaboration engine
------------------

On top of the Lean_ kernel there is a powerful *elaboration engine* that can

#. infer implicit universe variables;

#. infer implicit arguments, using higher order unification;

#. support overloaded notation or declarations;

#. insert coercions;

#. infer implicit arguments using type classes;

#. convert readable proofs to proof terms

#. construct terms using tactics

Lean_ does most of these things simultaneously. For example, the term constructed by type classes can be used to find out implicit arguments for functions.

(For a nice overview of the elaboration engine, see this `2015 post by Floris van Doorn`_.)

.. _metaprogramming:

Metaprogramming
---------------

Lean_ is easy to extend via **metaprogramming**. Briefly, a :term:`metaprogram` is a program whose purpose is to modify the behavior of other programs. :term:`Proof tactics <proof tactic>` form an important class of metaprograms.

An nice feature of Lean_ is that *metaprograms can be written in the Lean language* itself, rather that in the lower level language (C/C++) that was used to create Lean. Thus the metaprogramming language is the same logical language that we use to express specifications, propositions, and proofs.


--------------------------

.. rubric:: Footnotes

.. [1]
   See also the section of the `Lean Tutorial`_ called `Universe Levels <http://leanprover.github.io/tutorial/06_Inductive_Types.html>`_.


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

.. _TPL: https://leanprover.github.io/theorem_proving_in_lean/

.. _Coercions: https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#coercions

.. _Coercions using Type Classes: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

.. _Lean Tutorial: https://leanprover.github.io/tutorial/

.. _Lean Reference Manual: https://leanprover.github.io/reference/
