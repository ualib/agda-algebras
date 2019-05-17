.. _appendix:

========
Appendix
========

.. _basic-type-theory:

Basic type theory
-----------------

This section presents the rudiments of *type theory*, covering just enough to keep the rest of this work mostly self contained, even for readers with little or no prior background in type theory.  For more details, a nice and easy introduction to the basics is `Logic and Proof`_, and more advanced treatments are :cite:`MR3445957` and :cite:`HoTT`.

.. todo:: say something more about this

.. _

Curry-Howard
------------

The rule for *function application* corresponds, under the “Curry-Howard” or “propositions-as-types” correspondence, to the *implication elimination* rule of natural deduction (sometimes called *modus ponens*). It is the following:

This simply codifies our intuitive notion of function application, viz. applying the function :math:`f` to an inhabitant :math:`a` of the domain :math:`A`, we obtain an inhabitant :math:`f \, a` of the codomain :math:`B`. If we interpret :math:`A` and :math:`B` as propositions, :math:`f` as a proof of the implication :math:`A \to B`, and :math:`a` as a proof of :math:`A`, then the rule :math:`\mathsf{app}` becomes the implication elimination rule (*modus ponens*).

.. _

Dependent types
---------------

Lean_ is a functional programming language that supports **dependent types**. Here we give an example demonstrating that dependent types provide a more precise representation of the types of certain functions that are important in universal algebra and elsewhere. Besides being more precise and elegant, this representation is intrinsically computational.

Before getting to the example, however, we should first briefly explain what makes dependent type theory *dependent*, and why dependent types are useful. The short explanation is that types can depend on *parameters*. For example, the type ``list α`` depends on the argument ``α``, and this dependence is what distinguishes ``list ℕ`` from list ``bool``. For another example, consider the type ``vec α n``, the type of vectors of length ``n`` whose entries inhabit the type ``α``. The ``vec α n`` type depends on two parameters: the type ``α : Type`` of the elements in the vector and the length ``n : ℕ``.

Suppose we wish to write a function ``cons`` that inserts a new element at the head of a list. What type should cons have? Such a function is polymorphic: we expect the ``cons`` function for ``ℕ``, ``bool``, or an arbitrary type ``α`` to behave the same way. So it makes sense to take the type to be the first argument to ``cons``, so that for any type, ``α``, ``cons α`` is the insertion function for lists of type ``α``. In other words, for every ``α``, ``cons α`` is the function that takes an element ``a : α`` and a list ``l : list α``, and returns a new list, so that ``con α a l : list α``.

It is clear that ``cons α`` should have type ``α → list α → list α``. But what type should ``cons`` have?

A first guess might be ``Type → α → list α → list α``, but, on reflection, this does not make sense: the ``α`` in this expression does not refer to anything, whereas it should refer to the argument of type ``Type``.

In other words, assuming ``α : Type`` is the first argument to the function, the type of the next two elements are ``α`` and ``list α``. These types vary depending on the first argument, ``α``. This is an instance of a **Pi type**, or **dependent function type**. Given ``α : Type`` and ``β : α → Type``, think of ``β`` as a family of types over ``α``, that is, a type ``β a`` for each ``a : α``.

In this case, the type ``Π x : α, β x`` denotes the type of functions ``f`` with the property that, for each ``a : α``, ``f a`` is an element of ``β a``. In other words, the type of the value returned by ``f`` *depends* on its input. 

Notice that ``Π x : α, β`` makes sense for any expression ``β : Type``. When the value of ``β`` depends on ``x`` (as does, for example, the expression ``β x`` in the previous paragraph), ``Π x : α, β`` denotes a dependent function type. If ``β`` doesn't depend on ``x``, then ``Π x : α, β`` is no different from the type ``α → β``. Indeed, in dependent type theory (and in Lean_), the Pi construction is fundamental, and ``α → β`` is just notation for ``Π x : α, β`` in the special case in which ``β`` does not depend on ``x``.

.. index:: type of; dependent functions (Pi type)

The :ref:`Pi type <pi-type>` :math:`\Pi_{(x:A)}, B x`, also known as the :ref:`dependent function type <pi-type>`, generalizes the function type :math:`A → B` by allowing the codomain :math:`B x` to depend on the value :math:`x : A` of the function's "input."

The simplest example of a Pi type is the Cartesian product :math:`B_0 × B_1` which, when viewed as the collection of functions that map :math:`i ∈ \{0, 1\}` to some element of :math:`B_i`, is the type :math:`\Pi_{i : \{0, 1\}} B_i`. [1]_

.. index:: type of; dependent pairs (Sigma type)

Similarly, the :ref:`Sigma type <sigma-type>` :math:`\sum_{(x:A)}, B x`, also known as the :ref:`dependent pair type <sigma-type>`, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.

The simplest example of a Sigma type is the disjoint union :math:`B_0 \coprod B_1` which may be viewed as a collection of ordered pairs :math:`(i, b_i)`, where the first coordinate indicates to which set the second element belongs.  For example, if the two sets are :math:`B_0 = \{a, b\}` and :math:`B_1 = \{a, b, c\}` we form the disjoint union of :math:`B_0` and :math:`B_1` as follows:

.. math:: B_0 + B_1 = \{(0,a), (0,b), (1,a), (1,b), (1,c)\}.

Alternatively, some authors prefer to use the injection function to indicate the set from which an element originated.  For example, if we denote the injection into the :math:`i`-th coordinate by :math:`ι_i`, then a perfectly adequate presention of math::`B_0 + B_1` would be

.. math:: B_0 + B_1 = \{ι_0 a, ι_0 a, ι_1 a, ι_1 b, ι_1 c\}.

.. index:: dependent type theory, inductive type, universes

.. _

Inductive types
-----------------

.. todo:: say something about this

**Inductive types** and **inductive families of types**, generating only the recursor for an inductive type;

.. _

Lean's type hierarchy
---------------------

Like its more mature cousins Coq and Agda, Lean_ takes for its logical foundations *dependent type theory* with *inductive types* and *universes*. However, unlike Coq or Agda, Lean's universes are *not cumulative*.  This is not a problem since, in places where we might exploit universe cumulativity in Coq, we can instead use *universe polymorphism* and the *lift map* explicitly.

.. index:: keyword: Type
.. index:: keyword: Type 0
.. index:: keyword: Type 1
.. index:: keyword: Type n

Lean_ has a hierarchy of :math:`\omega`-many type universe levels. We want some operations to be *polymorphic* over type universes.

For example, ``list α`` should make sense for any type ``α``, no matter which universe ``α`` lives in. This explains why ``list`` has the following type signature: 

.. code-block:: lean

   #check @list    -- answer: Type u → Type u
   
Here ``u`` is a variable ranging over type levels.

Think of ``Type 0`` as a universe of "small" or "ordinary" types. ``Type 1`` is then a larger universe of types that contains ``Type 0`` as an *element*, and ``Type 2`` is an even larger universe of types, that contains ``Type 1`` as an element. The list is indefinite, so that there is a ``Type n`` for every natural number ``n``. ``Type`` is an abbreviation for ``Type 0``.

.. index:: ! predicative, ! ramified, ! impredicative
.. index:: keyword: Prop

The upshot of this **ramified** arrangement is that the types described in the last paragraph are **predicative**, which means that their definitions are not self-referential. By avoiding self-referential definitions, we avoid Russel's paradox. However, in certain specific situations we *do* want to employ a self-referential type, so Lean_ supplies us with exactly one. It is the type ``Prop`` of propositions, and it is **impredicative** (self-referential).

.. _

The elaboration engine
-----------------------

On top of the Lean_ kernel there is a powerful *elaboration engine* that can

#. infer implicit universe variables;

#. infer implicit arguments, using higher order unification;

#. support overloaded notation or declarations;

#. inserts coercions;

#. infers implicit arguments using type classes;

#. convert readable proofs to proof terms

#. constructs terms using tactics

Lean_ does most of these things simultaneously. For example, the term constructed by type classes can be used to find out implicit arguments for functions.


.. _pattern-matching

Pattern matching
----------------

.. todo:: say something about this

.. _various-types-and-sorts:

Various types and sorts
-----------------------

Here we collect for easy reference a list of some basic but important components from the Lean_ standard library.

.. index:: type of; dependent functions (Pi type)

.. _pi-type:

Pi Type
~~~~~~~

The **Pi type** ``Π(x:A),B x``, also known as the **dependent function type**, generalizes the function type ``A → B`` and is called a *dependent type* because the codomain ``B x`` may depend on the value ``x: A``.

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
    { f | ∀ a ∈ i, f a ∈ s a }

-------------------------

.. index:: type of; dependent pairs (Sigma type)

.. _sigma-type:

Sigma Type
~~~~~~~~~~

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
~~~~~~~~~

.. code-block:: lean

    class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
    (S : Sort v) (coe : a → S)

    class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
    (F : a → Sort v) (coe : Π x, F x)

.. _metaprogramming:

Metaprogramming
~~~~~~~~~~~~~~~

Lean_ is easy to extend via **metaprogramming**. Briefly, a **metaprogram** is a program whose purpose is to modify the behavior of other programs.  **Proof tactics** form an important class of metaprograms. These are automated procedures for constructing and manipulating proof terms. An awesome feature of Lean_ is that  *metaprograms can be written in the Lean_ language* itself, rather that in the lower level language (C/C++) that was used to create Lean. Thus the metaprogramming language is the same logical language that we use to express specifications, propositions, and proofs.

---------------------

.. rubric:: Footnotes

.. [1] 
   Of course, it's more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1) : b_i ∈ B_i, i = 0, 1\}`, but as usual we identify tuples with functions, which yields the :ref:`Pi type <pi-type>`.

.. _Lean: https://leanprover.github.io/

.. _Logic and Proof: https://leanprover.github.io/logic_and_proof/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _mathlib: https://github.com/leanprover-community/mathlib/

.. _lean_src: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

/-- Intersection of a set of sets. -/
@[reducible] def sInter (S : set (set α)) : set α := Inf S

prefix `⋂₀`:110 := sInter
