.. File: misc_notes.lagda.rst
.. Author: William DeMeo
.. Date: 25 Dec 2019
.. Updated: 16 Jan 2020
.. Note: This was used for the second part of my talk at JMM Special Session.


.. _axiomk:

Note on axiom K
~~~~~~~~~~~~~~~~

`ncatlab <https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29>`_  [1]_ explains **axiom K** as follows:

  "[when added, axiom K turns `intensional type theory <https://ncatlab.org/nlab/show/intensional+type+theory>`_ ] into `extensional type theory <https://ncatlab.org/nlab/show/extensional+type+theory>`_ ---or more precisely, what is called `here <https://ncatlab.org/nlab/show/extensional+type+theory>`_ 'propositionally extensional type theory.' In the language of `homotopy type theory <https://ncatlab.org/nlab/show/homotopy+type+theory>`_ , this means that all types are `h-sets <https://ncatlab.org/nlab/show/h-sets>`_ , accordingly axiom K is incompatible with the `univalence axiom <https://ncatlab.org/nlab/show/univalence+axiom>`_ .

  "Heuristically, the axiom asserts that each `term <https://ncatlab.org/nlab/show/term>`_ of each `identity type <https://ncatlab.org/nlab/show/identity+type>`_ ``Idₐ(x,x)`` (of equivalences of a term ``x`` of type ``a``) is `propositionally equal <https://ncatlab.org/nlab/show/propositional+equality>`_ to the canonical `reflexivity <https://ncatlab.org/nlab/show/reflexive+relation>`_ equality proof ``reflₓ : Idₐ(x, x)``.

  "See also `extensional type theory -- Propositional extensionality <https://ncatlab.org/nlab/show/extensional+type+theory#PropositionalExtensionality>`_ ."

--------------------------------------------------------------------------------


Writing definitions interactively
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

.. rubric:: Footnotes

.. [1]
   source: https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29
   accessed on: 29 Jan 2020

----------------------

.. include:: hyperlink_references.rst

