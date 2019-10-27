.. File: postmodern_algebra_in_lean.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 2019.10.11
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: cat

.. role:: code

.. _postmodern-algebra-in-lean:

===========================
Postmodern Algebra in Lean
===========================

Categories in Lean
------------------

.. highlight:: lean

**Example**.

::

  import category_theory.category category_theory.functor
  universes u v
  open category_theory

  variable (C : Type u)
  variable [category.{u v} C]
  variables A B : C

  #check A ⟶ B   -- Type v


.. _tuple-functors-in-lean:

Tuple functors in Lean
----------------------

.. todo:: complete this section

-------------------------------------

.. _general-composition-in-lean:

General composition in Lean
---------------------------

.. todo:: complete this section

fork and eval
~~~~~~~~~~~~~

.. .. raw:: latex

..    \begin{prooftree}
..    \AXM{\exists x A(x)}
..    \AXM{}
..    \RLM{1}
..    \UIM{A(y)}
..    \noLine
..    \UIM{\vdots}
..    \noLine
..    \UIM{B}
..    \RLM{1}
..    \BIM{B}
..    \end{prooftree}

.. .. include:: latex_images/first_order_logic.8.tex

----------------------------------------------------

.. index:: F-algebra
.. index:: homomorphism
.. index:: F-algebra homomorphism


.. _f-algebras-in-lean:

F-algebras in Lean
------------------

.. todo:: complete this section

.. _f-algebra-homomorphisms-in-lean:

F-algebra homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

--------------------

.. role:: cat

.. role:: code

.. _observations-categorically-in-lean:

Observations, categorically, in Lean
----------------------------------------

.. todo:: complete this section

.. _categorytheory.gitlab.io: https://categorytheory.gitlab.io

.. _Lean: https://leanprover.github.io/
