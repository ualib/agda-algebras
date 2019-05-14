========
Appendix
========

Here we collect for easy reference a list of the components from the Lean_ standard library that we have used.

.. _pi-type:

Pi Type
-------

(used in :numref:`Section %s <signatures-in-lean>`)

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := { f | ∀ a ∈ i, f a ∈ s a }

-------------------------

.. _sigma-type:

Sigma Type
----------

(used in :numref:`Section %s <signatures-in-lean>`)


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


.. _Lean: https://leanprover.github.io/
