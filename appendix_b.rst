.. _appendix-b:

=======================
Appendix B: Lean Basics
=======================

.. _leans-type-hierarchy:

Lean's type hierarchy
---------------------

Like its more mature cousins Coq and Agda, Lean_ takes for its logical foundations *dependent type theory* with *inductive types* and *universes*. However, unlike Coq or Agda, Lean's universes are *not cumulative*.  This is not a problem since, in places where we might exploit universe cumulativity in Coq, we can instead use *universe polymorphism* and the *lift map* explicitly.

.. index:: keyword: Type, Type 0, Type 1, ...

Lean_ has a hierarchy of :math:`\omega`-many type universe levels. We want some operations to be *polymorphic* over type universes.

For example, ``list α`` should make sense for any type ``α``, no matter which universe ``α`` lives in. This explains why ``list`` has the following type signature: 

.. code-block:: lean

   #check @list    -- answer: Type u → Type u
   
Here ``u`` is a variable ranging over type levels.

Think of ``Type 0`` as a universe of "small" or "ordinary" types. ``Type 1`` is then a larger universe of types that contains ``Type 0`` as an *element*, and ``Type 2`` is an even larger universe of types, that contains ``Type 1`` as an element. The list is indefinite, so that there is a ``Type n`` for every natural number ``n``. ``Type`` is an abbreviation for ``Type 0``.

.. index:: ! predicative, ! ramified, ! impredicative
.. index:: keyword: Prop

The upshot of this **ramified** arrangement is that the types described in the last paragraph are **predicative**, which means that their definitions are not self-referential. By avoiding self-referential definitions, we avoid Russel's paradox. However, in certain specific situations we *do* want to employ a self-referential type, so Lean_ supplies us with exactly one. It is the type ``Prop`` of propositions, and it is **impredicative** (self-referential).

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

.. _other-features:

Other features
--------------

.. _intersection:

Union and Intersection
~~~~~~~~~~~~~~~~~~~~~~

References for this subsection:

+ lean_src_ : set.lean_

+ mathlib_: basic.lean_, lattice.lean_

Let :math:`S` be a set of sets of type :math:`α`. 

In Lean_, the **intersection** of the sets in :math:`S` is denoted by ``⋂₀ S``.

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

The **union of sets** is implemented similarly.

.. code-block:: lean

   @[reducible]
   def sUnion (s : set (set α)) : set α := {t | ∃ a ∈ s, t ∈ a}
   prefix `⋃₀`:110 := sUnion

.. _coercions:

Coercions
---------

.. code-block:: lean

    class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
    (S : Sort v) (coe : a → S)

    class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
    (F : a → Sort v) (coe : Π x, F x)

.. _kernel:

Kernel
------

.. todo:: complete this section

.. _the-elaboration-engine:

Elaboration engine
------------------

On top of the Lean_ kernel there is a powerful *elaboration engine* that can

#. infer implicit universe variables;

#. infer implicit arguments, using higher order unification;

#. support overloaded notation or declarations;

#. inserts coercions;

#. infers implicit arguments using type classes;

#. convert readable proofs to proof terms

#. constructs terms using tactics

Lean_ does most of these things simultaneously. For example, the term constructed by type classes can be used to find out implicit arguments for functions.

(For a nice overview of the elaboration engine, see this `2015 post by Floris van Doorn`_.)

.. _metaprogramming:

Metaprogramming
---------------

Lean_ is easy to extend via **metaprogramming**. Briefly, a **metaprogram** is a program whose purpose is to modify the behavior of other programs.  **Proof tactics** form an important class of metaprograms. These are automated procedures for constructing and manipulating proof terms. An awesome feature of Lean_ is that  *metaprograms can be written in the Lean_ language* itself, rather that in the lower level language (C/C++) that was used to create Lean. Thus the metaprogramming language is the same logical language that we use to express specifications, propositions, and proofs.


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

