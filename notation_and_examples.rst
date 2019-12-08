.. File: notation_and_examples.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 22 May 2019
.. Updated: 8 Dec 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: code

.. highlight:: lean


Notation and Examples
======================

.. contents:: :local:
    :depth: 2

Notation
---------

Throughout, we denote and define the natural numbers as the following sets

.. math:: 0 := ∅, \quad 1 := \{0\}, \quad 2 := \{0, 1\}, \quad \dots, \quad n := \{0, 1, 2, \dots, n-1\}, \quad\dots

However, as this notation is known to cause confusion, we often remind the reader that the number :math:`n` should be viewed as a set by setting it in boldface; that is, we often write 𝐧 to denote the set :math:`\{0, 1, \dots, n-1\}`.

We will denote the set of natural numbers by ω or ℕ, and we write :math:`n<ω` (or :math:`n∈ ℕ`, or :math:`n:ℕ`) to indicate that :math:`n` is a natural number.

We write :math:`i<n` (or :math:`i∈ 𝐧`, or :math:`i:𝐧`) to indicate that :math:`i` belongs to the set :math:`\{0, 1, \dots, n-1\}`.

The Cartesian product of objects :math:`A_0, A_1, \dots, A_{n-1}` is denoted by :math:`∏_𝐧 A_i := A_0 × \cdots × A_{n-1}`.

An element :math:`𝐚 ∈ ∏_𝐧 A_i` is an ordered :math:`n`-tuple, which may be specified by its graph, :math:`(𝐚(0), 𝐚(1), \dots, 𝐚(n-1))`.

Thus, tuples are functions defined on a (finite) index set, and this view may be emphasized symbolically as follows:

.. math:: 𝐚: 𝐧 → ⋃_𝐧 A_i; \ i↦ 𝐚(i) ∈ A_i.

If :math:`σ: 𝐤 → 𝐧` is a :math:`k`-tuple of numbers from 𝐧, then we can compose an n-tuple :math:`𝐚 ∈ ∏_𝐧 A_i` with σ to obtain the k-tuple :math:`𝐚 ∘ σ ∈ ∏_𝐤 A_{σ(i)}`.

Generally speaking, we will try to avoid nonstandard notational conventions, but here are two exceptions: let

.. math:: 𝐀 := ∏_𝐧 A_i \quad \text{ and } \quad 𝐀_σ := ∏_𝐤 A_{σ(i)}.

Now, if the k-tuple σ: 𝐤 → 𝐧 happens to be one-to-one, and if we let :math:`p_σ` denote the map 𝐚 ↦ 𝐚 ∘ σ, then :math:`p_σ` is the usual :term:`projection operation` from 𝐀 onto :math:`𝐀_σ`.

Thus, :math:`p_σ(𝐚)` is a k-tuple whose i-th component is (𝐚 ∘ σ)(i) = 𝐚(σ(i)).

We will make frequent use of such projections, as well as their images under the covariant and contravariant powerset functors 𝒫 and :math:`𝒫^{\leftarrow}`.

Indeed, we let :math:`\mathrm{Proj}_σ: 𝒫(𝐀) → 𝒫(𝐀_σ)` denote the **projection set function** defined for each :math:`R ⊆ 𝐀` by

.. math:: \mathrm{Proj}_σ R = 𝒫 (p_σ)(R) = \{p_σ(𝐱) ∣ 𝐱 ∈ R\} = \{𝐱 ∘ σ ∣ 𝐱 ∈ R\},

and we let :math:`\mathrm{Inj}_σ: 𝒫^←(𝐀_σ) → 𝒫^←(𝐀)` denote the **injection set function** defined for each :math:`S ⊆ 𝐀_σ` by

.. math:: \mathrm{Inj}_σ S = 𝒫^←(p_σ)(S) = \{𝐱 ∣ p_σ(𝐱) ∈ S\} = \{𝐱 ∈ 𝐀 ∣ 𝐱 ∘ σ ∈ S\}.
   :label: 19

Of course, :math:`\mathrm{Inj}_σ S` is nothing more than the inverse image of the set :math:`S` with respect to the projection function :math:`p_σ`.

We sometimes use the shorthand :math:`R_σ := \mathrm{Proj}_σ R` and :math:`S^{\overleftarrow{σ}} = \mathrm{Inj}_σ S` for the projection and injection set functions, respectively.

--------------------------

.. _examples-of-algebras:

Examples of algebras
----------------------

Recall from above that an algebra :math:`𝔸` is an ordered pair :math:`𝔸 = ⟨A, F^𝔸⟩` where :math:`A` is a nonempty set and :math:`F` is a family of finitary operations on :math:`A`.

The set :math:`A` is called the **universe** of :math:`𝔸`, and the elements :math:`f^𝔸 ∈ F` are called the **basic operations** of :math:`𝔸`.

(In practice we often write :math:`f` instead of :math:`f^𝔸` when no ambiguity could result from this shorthand.

Here is a list of a few of the most frequently encountered and historically important algebraic structures. [1]_

.. glossary:: 

   magma
     An algebra :math:`⟨A, ⋅⟩` with a single binary operation is called a **magma** (or **groupoid** or **binar**). The operation is usually denoted by :math:`+` or :math:`⋅`, and we write :math:`a+b` or :math:`a ⋅ b` (or just :math:`ab`) for the image of :math:`(a, b)` under this operation, which we call the *sum* or *product* of :math:`a` and :math:`b`, respectively.

   semigroup
     A magma :math:`⟨A, ⋅⟩` whose binary operation is associative is called a **semigroup**.  That is, a semigroup is a magma whose binary operation satisfies :math:`∀ a, b, c ∈ A`, :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)`.

   monoid
     If :math:`⟨A, ⋅⟩` is a semigroup and if :math:`e ∈ A` is a *multiplicative identity* (i.e., :math:`∀ a ∈ A`, :math:`e ⋅ a = a ⋅ e = a`), then :math:`⟨A, \{e, ⋅\}⟩` is called a **monoid**.

   group
     A **group** is a monoid along with a unary operation :math:`^{-1}` called *multiplicative inverse*. That is, the reduct :math:`⟨ A, \{e, ⋅\}⟩` is a monoid and :math:`^{-1}` satisfies :math:`a ⋅ a^{-1} =  a^{-1} ⋅ a = e`, for all :math:`a ∈ A`.
  
   Abelian group
     A group is called **abelian** just in case its binary operation is commutative, in which case we usually denote the operation by :math:`+` instead of :math:`⋅`. Also in this case we let :math:`0` (instead of :math:`e`) denote the *additive identity*, and we let :math:`-\,` (instead of :math:`^{-1}`) denote the *additive inverse*. Thus, an **abelian group** is a group :math:`𝔸 = ⟨ A, 0, -,+⟩` such that :math:`a+b = b+a` for all :math:`a, b ∈ A`.

   ring
     An algebra :math:`⟨R, \{0, -, +, ⋅\}⟩` is called a **ring** just in case the following conditions hold:

       #. the reduct :math:`⟨R, \{0, -,+\}⟩` is an abelian group,
       #. the reduct :math:`⟨R, ⋅ ⟩` is a semigroup, and
       #. "multiplication" :math:`⋅` distributes over "addition" :math:`+`; that is, :math:`∀ a, b, c ∈ R`, :math:`a ⋅ (b+c) = a ⋅ b + a ⋅ c` and :math:`(a+b)⋅ c = a ⋅ c + b ⋅ c`.

     A **ring with unity** (or **unital ring**) is an algebra :math:`⟨R, \{0, 1, -, +, ⋅\}⟩` with a ring reduct :math:`⟨R, \{0, -, +, ⋅\}⟩` and a *multiplicative identity* :math:`1 ∈ R`; that is :math:`∀ r ∈ R`, :math:`r ⋅ 1 = r = 1 ⋅ r`.

     If :math:`⟨R, \{0, 1, -, +, ⋅\}⟩` is a unital ring, an element :math:`r ∈ R` is called a **unit** if it has a multiplicative inverse, that is, there exists :math:`s ∈ R` with :math:`r ⋅ s = 1 = s ⋅ r`.  (We usually denote such an :math:`s` by :math:`r^{-1}`.)

   division ring
     A ring in which every non-zero element is a unit is called a **division ring**.

   field
     A commutative division ring is called a **field**.

   module
     Let :math:`R` be a ring with unit. A **left unitary** :math:`R`-**module** (or simply :math:`R`-**module**) is an algebra :math:`⟨M, \{0, -, +\} ∪ \{f_r : r∈ R\}⟩` with an abelian group reduct :math:`⟨M, \{0, -, +\}⟩` and unary operations :math:`\{f_r : r ∈ R\}` that satisfy the following: :math:`∀ r, s ∈ R`, :math:`∀ x, y ∈ M`,

       #. :math:`f_r(x + y)  = f_r(x) + f_r(y)`
       #. :math:`f_{r+s}(x) = f_r(x) + f_s(x)`
       #. :math:`f_r(f_s(x)) = f_{rs}(x)`
       #. :math:`f_1(x) = x`.

     Note that Condition 1 says that each :math:`f_r` is an :term:`endomorphism` of the abelian group :math:`⟨ M, \{0, -, +\}⟩`, while the other conditions amount to the following: (1) the set :math:`E := \{f_r ∣ r∈ R\}` of endomorphisms is a ring with unit where multiplication is function composition, and (2) the map :math:`r ↦ f_r` is a ring :term:`epimorphism` from :math:`R` onto :math:`E`.

     One reason modules are important is that every ring is, up to isomorphism, a ring of endomorphisms of some abelian group. This fact is analogous to the more familiar theorem of Cayley stating that every group is isomorphic to a group of permutations of some set.

   vector space
     In :math:`R` happens to be a field, then an :math:`R`-module is typically called a **vector space** over :math:`R`.

   bilinear algebra
     If :math:`𝔽 = ⟨F, \{0, 1, -, ⋅\}⟩` is a field, then the algebra :math:`𝔸 = ⟨A, \{0, -, +, ⋅\} ∪ \{f_r ∣ r ∈ F\}⟩` is called a **bilinear algebra** over :math:`𝔽` provided

       #. :math:`⟨A, \{0, -, +\} ∪ \{f_r ∣ r ∈ F\}⟩` is a vector space over :math:`𝔽` and 
       #. :math:`∀ a, b, c ∈ A`, :math:`∀ r ∈ F`,

       .. math:: \begin{gather}
                 (a + b) ⋅ c = (a ⋅ c) + (b ⋅ c),\\
                 c ⋅ (a + b) = (c ⋅ a) + (c ⋅ b),\\
                 a ⋅ f_r(b) = f_r(a ⋅ b) = f_r(a) ⋅ b.
                 \end{gather}

     If in addition :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)` for all :math:`a, b, c ∈ A`, then :math:`𝔸` is called an **associative algebra** over :math:`𝔽`. Thus an associative algebra over a field has both a vector space reduct and a ring reduct. An example of an associative algebra is the space of *linear transformations* (endomorphisms) of any vector space into itself.

--------------------

.. _examples-of-categories:

Examples of categories
-----------------------

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

---------------------------

Open problems
---------------

#. Bounded Linear Width Conjecture

#. PCSP(3-color,100-color) (or even just PCSP(3-color,6-color)) is not known to be NP-complete :cite:`Barto:2018`, :cite:`Brakensiek:2016`

#. The decision version of CSP(𝔸) and the search version are polytime equivalent :cite:`Bulatov:2005`.

   The decision version of PCSP(𝔸, 𝔹) can be reduced to the search version, but it is an open problem whether they are equivalent.

#. Let ℓ be the list of properties preserved under :term:`Maltsev product`, and suppose 𝒱 has one property in ℓ and 𝒲 has another.  Is every finite member of 𝖧(𝒱 ∘ 𝒲) is tractable?

------------------------

.. rubric:: Footnotes

.. [1]
   A list of many others may be found at http://www.math.chapman.edu/~jipsen/structures/doku.php/index.html.

----------------------

.. include:: hyperlink_references.rst


.. retract
..   todo: insert definition

.. retraction
..   todo: insert definition

..   :math:`f ∘ 𝐚`
..     If :math:`f: A → B` and :math:`a: n → A` (or :math:`a ∈ A^n`), then :math:`f ∘ 𝐚` is the element of :math:`n → B` defined for each :math:`i < n` by :math:`(f a) (i) = f(a(i))`.
 

..   :math:`φ_{𝐱}(𝐚)`
..     is shorthand for :math:`[a_0/x_0, a_1/x_1, \dots]φ(x_0, x_1, \dots)`, the sentence obtained from φ upon substituting :math:`a_i` for :math:`x_i` for each :math:`i`.
 
