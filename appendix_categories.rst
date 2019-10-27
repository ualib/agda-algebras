.. File: appendix_categories.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 11 Oct 2019
.. Upated: 27 Oct 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: code

.. highlight:: lean

.. _categories:

Categories
-------------

.. glossary::

    1
      The only object is :math:`0`; the only morphism is the identity :math:`\id_0: 0 ↦ 0`.

    2
      There are two objects, :math:`0` and :math:`1`; there is one nonidentity morphism :math:`f: 0 ↦ 1`.

    3
      There are three objects, :math:`0`, :math:`1`, and :math:`2`; there are three nonidentity morphisms: :math:`f: 0 ↦ 1`, :math:`g: 1 ↦ 2`, and :math:`h: 0 ↦ 2`.

    Cat 
      the (large) category of small categories; it has small categories as objects and functors :math:`F : \mathcal C → \mathcal D` as morphisms.

    Set
      the category whose objects are the sets and whose morphisms are the functions on sets.

    Grph
      the category whose objects are the (directed) graphs; the morphisms are the :term:`graph morphisms <graph morphism>`.

    Mon
      the category whose objects are the :term:`monoids <monoid>` and whose morphisms are the :term:`monoid homomorphisms <monoid homomorphism>`.

    Par
      the category whose objects are sets and whose morphisms are the :term:`partial functions <partial function>`.

    Rel
      the category whose objects are sets and whose morphisms are the :term:`relations <relation>` on sets.

    Fin
      a category whose objects are the finite sets; the morphisms are the functions on finite sets.

    Pos
      a category whose objects are the :term:`posets <poset>`; the morphisms are the :term:`monotone functions <monotone function>`.

    Lat
      a category whose objects are the :term:`lattices <lattice>`; the morphisms are the :term:`lattice homomorphisms <lattice homomorphism>`.

    CLat
      a category whose objects are the :term:`complete lattices <complete lattice>`; the morphisms are the :term:`complete lattice homomorphisms <complete lattice homomorphism>`.

    BLat
      a category whose objects are the :term:`Boolean lattices <Boolean algebra>`; the morphisms are the :term:`Boolean lattice homomorphisms <Boolean algebra homomorphism>`.

    HLat
      a category whose objects are the :term:`Heyting lattices <Heyting algebra>`; the morphisms are the :term:`Heyting lattice homomorphisms <Heyting algebra homomorphism>`

    ACLat
      a category whose objects are :term:`algebraic <algebraic lattice>`, :term:`complete lattices <complete lattice>`; the morphisms are the :term:`complete lattice homomorphisms <complete lattice homomorphism>`.

    Arrow
      Given a category :math:`\mathcal C`, the **arrow category** :math:`\mathcal C^→` has as objects the triples :math:`(A, B, f)` satisfying :math:`A, B ∈  \mathcal C_{\mathrm{obj}}` and :math:`f ∈ \mathcal C(A,B)`, and as morphisms the pairs :math:`(h_1, h_2) : (A, B, f) → (C, D, g)` such that :math:`h_1 ∈ \mathcal C(A,C)`, :math:`h_2 ∈ \mathcal C(B, D)` and :math:`g \circ h_1 = h_2 \circ f`.

    Slice
      Given a category :math:`\mathcal C` and an object :math:`C ∈ \mathcal C_{\mathrm{obj}} `, the **slice category** :math:`\mathcal C/C` has objects the pairs :math:`(A, f)` such that :math:`f ∈ \mathcal C(A, C)`, and morphisms :math:`h : (A, f) → (B, g)` such that :math:`h ∈ \mathcal C(A, B)` and :math:`g ∘ h = f`.

    Comma
      Given categories :math:`\mathcal C` and :math:`\mathcal D` and functors :math:`F : \mathcal C → \mathcal D` and :math:`G : \mathcal C' → \mathcal D` (with a common :term:`codomain`), the **comma category** is denoted by :math:`(F ↓ G)` and has objects the triples :math:`(A, f, A')`, where :math:`A ∈ \mathcal C_{\mathrm{obj}}`, :math:`A' ∈ \mathcal C'_{\mathrm{obj}}`, and :math:`f ∈ \mathcal D(FA, GA')`, and morphisms the pairs :math:`(φ, ψ) : (A, f, A') → (B, g, B')`, where :math:`φ ∈ \mathcal C(A, B)`, :math:`ψ ∈ \mathcal C'(A',B')` and :math:`G ψ ∘ f = g ∘ F φ`.

--------------------------------

.. include:: hyperlink_references.rst

.. computationally pure
..   An expression is called **computationally pure** if
..   .. todo:: complete definition

.. pure
..   see :term:`computationally pure`

.. universe
..   .. todo:: insert definition
.. universes
..   see :term:`universe`
