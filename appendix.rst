.. _appendix:

========
Appendix
========

Basic type theory
-----------------

This section presents the rudiments of *type theory*, covering just enough to keep the rest of this work mostly self contained, even for readers with little or no prior background in type theory.  For more details, a nice and easy introduction to the basics is `Logic and Proof`_, and more advanced treatments are :cite:`MR3445957` and :cite:`HoTT`.

.. todo:: insert section on type theory basics

.. index:: type of; dependent pairs (Sigma type)

.. index:: type of; dependent functions (Pi type)

The :ref:`Pi type <pi-type>` :math:`\Pi_{(x:A)}, B x`, also known as the :ref:`dependent function type <pi-type>`, generalizes the function type :math:`A → B` by allowing the codomain :math:`B x` to depend on the value :math:`x : A` of the function's "input."

The simplest example of a Pi type is the Cartesian product :math:`B_0 × B_1` which, when viewed as the collection of functions that map :math:`i ∈ \{0, 1\}` to some element of :math:`B_i`, is the type :math:`\Pi_{i : \{0, 1\}} B_i`. [1]_

Similarly, the :ref:`Sigma type <sigma-type>` :math:`\sum_{(x:A)}, B x`, also known as the :ref:`dependent pair type <sigma-type>`, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.

The simplest example of a Sigma type is the disjoint union :math:`B_0 \coprod B_1` which may be viewed as a collection of ordered pairs :math:`(i, b_i)`, where the first coordinate indicates to which set the second element belongs.  For example, if the two sets are :math:`B_0 = \{a, b\}` and :math:`B_1 = \{a, b, c\}` we form the disjoint union of :math:`B_0` and :math:`B_1` as follows:

.. math:: B_0 + B_1 = \{(0,a), (0,b), (1,a), (1,b), (1,c)\}.

Alternatively, some authors prefer to use the injection function to indicate the set from which an element originated.  For example, if we denote the injection into the :math:`i`-th coordinate by :math:`ι_i`, then a perfectly adequate presention of math::`B_0 + B_1` would be

.. math:: B_0 + B_1 = \{ι_0 a, ι_0 a, ι_1 a, ι_1 b, ι_1 c\}.

------------------------------------------

Basic type theory in Lean
-------------------------

Here we collect for easy reference a list of some basic but important components from the Lean_ standard library.

.. index:: type of; dependent functions (Pi type)

.. _pi-type:

Pi Type
-------

The **Pi type** ``Π(x:A),B x``, also known as the **dependent function type**, generalizes the function type ``A → B`` and is called a *dependent type* because the codomain ``B x`` may depend on the value ``x: A``.

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := { f | ∀ a ∈ i, f a ∈ s a }

-------------------------

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

-------------------------

.. _intersection:

Intersection
------------

(used in :numref:`Section %s <subalgebras-in-lean>`)

.. code-block:: lean

    /-- Intersection of a set of sets. -/
    @[reducible] def sInter (S : set (set α)) : set α := Inf S

    prefix `⋂₀`:110 := sInter

-------------------------

.. _coercions:


Coercions
---------

(used in :numref:`Section %s <universal-algebras-in-lean>`)


.. code-block:: lean

    class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
    (S : Sort v) (coe : a → S)

    class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
    (F : a → Sort v) (coe : Π x, F x)

---------------------

.. rubric:: Footnotes

.. [1] 
   Of course, it's more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1) : b_i ∈ B_i, i = 0, 1\}`, but as usual we identify tuples with functions, which yields the :ref:`Pi type <pi-type>`.



.. _Lean: https://leanprover.github.io/

.. _Logic and Proof: https://leanprover.github.io/logic_and_proof/