.. include:: _static/math_macros.rst

.. _appendix-lean-basics:

=====================
Appendix. Lean Basics
=====================

In this appendix we describe various features and aspects of Lean_ that we have made use of in the lean-ualib_.

Some of the things described here will come from the Lean_ standard library.  Others will be from the mathlib_ Lean community project, and possible other projects.

Some good references for this material are

  + `Lean Tutorial <https://leanprover.github.io/tutorial/>`_
  + `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_
  + `The Lean Reference Manual <https://leanprover.github.io/reference/>`_
  + `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_

------------------------------------------------

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

------------------------------------------------

.. _pattern-matching:

Pattern matching
----------------

.. todo:: complete this section

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

In our ``algebra`` type, we used ``has_coe_to_sort`` and ``has_coe_to_fun``. The definitions of these in the Lean_ library are as follows:

.. code-block:: lean

   class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
   (S : Sort v) (coe : a → S)

   class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
   (F : a → Sort v) (coe : Π x, F x)

------------------------------------------------

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

----------------------------------------------------------

.. _metaprogramming:

Metaprogramming
---------------

Lean_ is easy to extend via **metaprogramming**. Briefly, a :term:`metaprogram` is a program whose purpose is to modify the behavior of other programs. :term:`Proof tactics <proof tactic>` form an important class of metaprograms.

An nice feature of Lean_ is that *metaprograms can be written in the Lean language* itself, rather that in the lower level language (C/C++) that was used to create Lean. Thus the metaprogramming language is the same logical language that we use to express specifications, propositions, and proofs.

--------------------------

Comparison of ITPs
------------------

The following popular :term:`ITPs <ITP>` are all based on some flavor of :term:`dependent type` theory.  One may distinguish them by the philosophical and foundational assumptions on which they are based. Two basic criterion along these lines are whether they are :term:`intensional` or :term:`extensional` and whether they are :term:`predicative` or :term:`impredicative`.  All four of these languages support :term:`dependent types <dependent type>`.

Agda_ is an :term:`intensional`, :term:`predicative` :term:`ITP` developed at Chalmers University in (Göteborg).  It is based on Martin Lof :term:`type theory`.

.. ; url: https://wiki.portal.chalmers.se/agda/pmwiki.php .

Coq_ is an :term:`intensional`, :term:`impredicative` :term:`ITP` developed at INRIA in France.  It is based on :term:`CiC`.

.. ; url: http://coq.inria.fr .

NuPRL_ is an :term:`extensional`, :term:`predicative` :term:`ITP` developed at Cornell University in Ithaca (USA).  It is based on Martin Lof :term:`type theory`.

.. ; url: http://www.nuprl.org/

Lean_ is an :term:`extensional`, :term:`impredicative` :term:`ITP` developed at Microsoft Research and Carnegie Mellon University (USA). It is based on :term:`CiC`.

.. ; url: https://leanprover.github.io/

.. + NuPRL_ . :term:`extensional`, :term:`predicative`
.. + Coq_ .  :term:`intensional`, :term:`impredicative`
.. + Agda_ . :term:`intensional`, :term:`predicative`
.. + Lean_  :term:`extensional`, :term:`impredicative`

---------------------------------------

The Lean Standard Library
--------------------------

This section collects for easy reference a description of some of the most important basic components of the Lean_ standard library.

While Lean doesn't have a formal API, per se, you can browse the source code of the core Lean library to see what built-in mathematical objects and operations are available.  For example, some of the most important mathematical objects are implemented in the files listed below. These (and many more) can be found in (or under) the `lean/library/init <https://github.com/leanprover/lean/tree/master/library/init>`_ directory of the official Lean GitHub repository](

+ [classical.lean](https://github.com/leanprover/lean/blob/master/library/init/classical.lean)
+ [core.lean](https://github.com/leanprover/lean/blob/master/library/init/core.lean)
+ [function.lean](https://github.com/leanprover/lean/blob/master/library/init/function.lean)
+ [logic.lean](https://github.com/leanprover/lean/blob/master/library/init/logic.lean)
+ [wf.lean](https://github.com/leanprover/lean/blob/master/library/init/wf.lean)

+ In [lean/library/init/data](https://github.com/leanprover/lean/tree/master/library/init/data):
  - [nat (dir)](https://github.com/leanprover/lean/blob/master/library/init/data/nat)
  - [prod.lean](https://github.com/leanprover/lean/blob/master/library/init/data/prod.lean)
  - [quot.lean](https://github.com/leanprover/lean/blob/master/library/init/data/quot.lean)
  - [set.lean](https://github.com/leanprover/lean/blob/master/library/init/data/set.lean)
  - [sigma (dir)](https://github.com/leanprover/lean/blob/master/library/init/data/sigma/)
  
+ In [lean/library/init/algebra](https://github.com/leanprover/lean/blob/master/library/init/algebra):
  - [classes.lean](https://github.com/leanprover/lean/blob/master/library/init/algebra/classes.lean)
  - [functions.lean](https://github.com/leanprover/lean/blob/master/library/init/algebra/functions.lean)
  - [order.lean](https://github.com/leanprover/lean/blob/master/library/init/algebra/order.lean)

[Lean]: http://leanprover.github.io/ 
[VS Code]: https://code.visualstudio.com/

---------------------

.. rubric:: Footnotes

.. [1]
   See also the section of the `Lean Tutorial`_ called `Universe Levels <http://leanprover.github.io/tutorial/06_Inductive_Types.html>`_.


.. _Agda: https://wiki.portal.chalmers.se/agda/pmwiki.php

.. _Coq: http://coq.inria.fr

.. _NuPRL: http://www.nuprl.org/

.. _Lean: https://leanprover.github.io/

.. _Lean github repository:  https://github.com/leanprover/lean).

.. _Logic and Proof: https://leanprover.github.io/logic_and_proof/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _mathlib: https://github.com/leanprover-community/mathlib/

.. _Lean Standard Library: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/

.. _TPL: https://leanprover.github.io/theorem_proving_in_lean/

.. _Coercions: https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#coercions

.. _Coercions using Type Classes: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

.. _Lean Tutorial: https://leanprover.github.io/tutorial/

.. _Lean Reference Manual: https://leanprover.github.io/reference/

