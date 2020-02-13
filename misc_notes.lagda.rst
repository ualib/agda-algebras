.. File: misc_notes.lagda.rst
.. Author: William DeMeo
.. Date: 25 Dec 2019
.. Updated: 16 Jan 2020
.. Note: This was used for the second part of my talk at JMM Special Session.


Agda Notes
==========


.. _axiomk:

Note on axiom K
-------------------

`nlab <https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29>`_ describes **axiom K** as follows [1]_ :

  "[when added, axiom K turns `intensional type theory <https://ncatlab.org/nlab/show/intensional+type+theory>`_ ] into `extensional type theory <https://ncatlab.org/nlab/show/extensional+type+theory>`_ ---or more precisely, what is called `here <https://ncatlab.org/nlab/show/extensional+type+theory>`_ 'propositionally extensional type theory.' In the language of `homotopy type theory <https://ncatlab.org/nlab/show/homotopy+type+theory>`_ , this means that all types are `h-sets <https://ncatlab.org/nlab/show/h-sets>`_ , accordingly axiom K is incompatible with the `univalence axiom <https://ncatlab.org/nlab/show/univalence+axiom>`_ .

  "Heuristically, the axiom asserts that each `term <https://ncatlab.org/nlab/show/term>`_ of each `identity type <https://ncatlab.org/nlab/show/identity+type>`_ ``Idₐ(x,x)`` (of equivalences of a term ``x`` of type ``a``) is `propositionally equal <https://ncatlab.org/nlab/show/propositional+equality>`_ to the canonical `reflexivity <https://ncatlab.org/nlab/show/reflexive+relation>`_ equality proof ``reflₓ : Idₐ(x, x)``.

  "See also `extensional type theory -- Propositional extensionality <https://ncatlab.org/nlab/show/extensional+type+theory#PropositionalExtensionality>`_ ."

--------------------------------------------------------------------------------


Writing definitions interactively
-------------------------------------

Here is a description of some Agda key-bindings and how to use them, as we briefly mentioned in the talk.

1. Add a question mark and then type ``C-c C-l`` to create a new "hole."

2. Type ``C-c C-f`` to move into the next unfilled hole.

3. Type ``C-c C-c`` (from inside the hole) to be prompted for what type should fill the given hole.

4. Type ``t`` (or whatever variable you want to induct on) to split on the variable in the hole.

5. Type ``C-c C-f`` to move into the next hole.

6. Type ``C-c C-,`` to get the type required in the current hole.

7. Enter an appropriate object in the hole and type ``C-c C-space`` to remove the hole.

**SUMMARY**.

1. ``?`` then ``C-c C-l`` creates hole
2. ``C-c C-f`` moves to next hole
3. ``C-c C-c`` prompts for what goes in hole
4. ``m`` splits (inducts) on variable ``m`` 
5. ``C-c C-,`` in hole gets type required
6. ``C-c C-space`` removes hole

	  
--------------------------------------------

.. _concrete-examples:

Examples of algebras in Agda
------------------------------

Most of the Agda code described in this section is found in the file ``classes.agda`` residing in the ``src/data`` directory of the agda-ualib_ repository. [1]_

We now show how to express some classical algebraic structures in Agda using dependent and inductive types. In particular, we will represent the following abstract structures.

#. **magma**, :math:`⟨A, \{⋅\}⟩`, with binary op ⋅,
#. **semigroup**, :math:`⟨A, \{⋅\}⟩`, with associative binary op ⋅,
#. **quasigroup**, :math:`⟨A, \{\,^{-1}, ⋅\}⟩`, with unary op :math:`\,^{-1}`, and binary op ⋅,
#. **monoid**, :math:`⟨A, \{e, ⋅\}⟩`, with nullary op :math:`e`, and associative binary op ⋅,
#. **loop**, :math:`⟨A, \{e, \,^{-1}, ⋅\}⟩`, with nullary op :math:`e`, unary op :math:`\,^{-1}`, and binary op ⋅,
#. **group**, :math:`⟨A, \{e, \,^{-1}, ⋅\}⟩`, with with nullary op :math:`e`, unary op :math:`\,^{-1}`, and associative binary op ⋅,
#. **abelian group**, :math:`⟨A, \{0, -, +\}⟩`, with with nullary op :math:`0`, unary op :math:`\,-`, and associative binary op +,
#. **semiring**, :math:`⟨A, \{0, 1, +, ⋅\}⟩`, with nullary ops :math:`0, 1`, and associative binary ops :math:`+, ⋅`,
#. **ring**, :math:`⟨A, \{0, 1, -, +, ⋅\}⟩`, with nullary ops :math:`0, 1`, unary op :math:`-`, and associative binary ops :math:`+, ⋅`.
#. **division ring**, where every non-zero element is a unit,
#. **field**, a commutative division ring.

We will also encode **modules**.  Recall, if :math:`R` is a ring, then a **left unitary** :math:`R`-**module** (or simply :math:`R`-**module**) is an algebra :math:`⟨A, \{0, -, +\} ∪ \{f_r : r∈ R\}⟩` with an abelian group reduct :math:`⟨A, \{0, -, +\}⟩` and unary operations :math:`\{f_r: r ∈ R\}` that satisfy the following: :math:`∀ r, s ∈ R`, :math:`∀ x, y ∈ M`,

  #. :math:`f_r(x + y)  = f_r(x) + f_r(y)`
  #. :math:`f_{r+s}(x) = f_r(x) + f_s(x)`
  #. :math:`f_r(f_s(x)) = f_{rs}(x)`
  #. :math:`f_1(x) = x`.

Note that the first condition says that each :math:`f_r` is an :term:`endomorphism` of the abelian group :math:`⟨A, \{0, -, +\}⟩`, while the other conditions amount to the following: (1) the set :math:`E := \{f_r ∣ r∈ R\}` of endomorphisms is a ring with unit where multiplication is function composition, and (2) the map :math:`r ↦ f_r` is a ring :term:`epimorphism` from :math:`R` onto :math:`E`.

One reason modules are important is that every ring is, up to isomorphism, a ring of endomorphisms of some abelian group. This fact is analogous to the more familiar theorem of Cayley stating that every group is isomorphic to a group of permutations of some set.

We will also encode **vector spaces** (i.e., :math:`F`-modules in case :math:`F` happens to be a field) as well as **bilinear algebras** (algebra of the form :math:`⟨A, \{0, -, +, ⋅\} ∪ \{f_r ∣ r ∈ F\}⟩` where :math:`⟨F, \{0, 1, -, ⋅\}⟩` is a field).

Our formal representations of these concepts will be clear, concise, and computable. Moreover, we strive to develop a notation and syntax that will feel natural to working algebraists.

The overriding goal is to demonstrate the power of Agda's type system for expressing mathematical concepts precisely and constructively, and to show that if we make careful design choices at the start, then we will be able to render formal theorems *and their proofs* with approximately the same efficiency and readability of analogous informal presentations found in the mathematics literature.

Note that the code we present here is just one of the possible ways to represent algebras in Agda. Indeed, in later sections we will consider alternative implementations.

.. todo:: insert include directive pointing to source file _static/examples.agda.1.rst

.. .. include:: _static/examples.agda.1.rst

-------------------------

.. rubric:: Footnotes

.. [1]
   source: https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29
   accessed on: 29 Jan 2020

----------------------

.. include:: hyperlink_references.rst

