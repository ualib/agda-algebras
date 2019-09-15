.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

=========
Algebras
=========

.. todo:: add chapter intro

.. index:: operation, arity, image
.. index::
   symbol: ℕ
   symbol: ̱m  

.. _operations:

Operations
----------

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m : ℕ` and say ":math:`m` has type ℕ." [1]_

For :math:`m : ℕ`, denote and define :math:`\underline m := \{0, 1, \dots, m-1\}`.

Let :math:`a[\underline m] = (a_0, a_1, \dots, a_{m-1})` denote the :ref:`mtuple <tuple-functors>` of elements :math:`a_i : A`, for each :math:`i : \underline m`.

The :ref:`mtuple <tuple-functors>` :math:`a[\underline m]` may be identified with the function :math:`a : \underline m → A`, where :math:`a(i) = a_i`, for each :math:`i : \underline m`. (See :numref:`Section %s <general-composition>` for a discussion of this identification.)

If :math:`h  : A → A`, then :math:`h ∘ a : \underline m → A` is the function whose :math:`i`-th coordinate is

.. math:: (h ∘ a)(i) = h(a(i)) = h(a_i), 

and we may formally identify the function :math:`h ∘ a : \underline m → A` with its image---that is, the **image of** :math:`\underline m` **under** :math:`h ∘ a`---which is the :ref:`mtuple <tuple-functors>`,

.. math:: (h ∘ a)[\underline m] = (h(a_0), h(a_1), \dots, h(a_{m-1})).

---------------------------

.. index:: signature

.. _signatures:

Signatures
----------

Classically, a **signature** :math:`σ = (F, ρ)` consists of a set :math:`F` of operation symbols and a function :math:`ρ : F → ℕ`.

For each operation symbol :math:`f ∈ F`, the value :math:`ρf` is the **arity** of :math:`f`. (Intuitively, the arity can be thought of as the "number of arguments" that :math:`f` takes as "input".)

If :math:`A` is a set and :math:`f` is a :math:`ρf`-ary function on :math:`A`, then we often write :math:`f : A^{ρf} → A` to indicate this.

On the other hand, the arguments of such a function form a :math:`ρf`-tuple, :math:`(a_0, a_1, \dots, a_{ρf -1})`, which may be viewed as the graph of the function :math:`a : ρf → A`, where :math:`a(i) = a_i`.

Thus, by identifying the :math:`ρf`-th power :math:`A^{ρf}` with the type :math:`ρf → A` of functions from :math:`\{0, 1, \dots, ρf -1\}` to :math:`A`, we identify the function type :math:`A^{ρf} → A` with the (functional) type :math:`(ρf → A) → A`. [2]_

.. proof:example::

   Suppose 

     :math:`g : (\underline m → A) → A` is an :math:`\underline m`-ary operation on :math:`A`, and 
   
     :math:`a : \underline m → A` is an :math:`m`-tuple on :math:`A`.

   Then :math:`g a = g(a_0, a_1, \dots, a_{m-1})` has type :math:`A`.

   Suppose

     :math:`f : (ρf → B) → B` is a :math:`ρf`-ary operation on :math:`B`,

     :math:`a : ρf → A` is a :math:`ρf`-tuple on :math:`A`, and

     :math:`h : A → B`.
      
   Then :math:`h ∘ a : ρf → B` and :math:`f (h ∘ a) : B`.

It is important to be familiar with the classical notions of signature and arity, since these are used by almost all algebraists. However, in :numref:`f-algebra` we give alternative, category theoretic definitions of these things that are sometimes easier to compute with.

--------------------------

.. index:: triple: algebra; algebraic structure; universal algebra

.. _algebraic-structures:

Algebraic structures
----------------------

An **algebraic structure** (or **algebra**) in the signature :math:`σ = (F, ρ)` is denoted by :math:`𝔸 = ⟨A, F^𝔸⟩` and consists of 

  #. :math:`A` := a set, called the *carrier* (or *universe*) of the algebra,
  #. :math:`F^𝔸 = \{ f^𝔸 ∣ f ∈ F, \ f^𝔸 : (ρ f → A) → A \}` := a set of operations on :math:`A`, and
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝔸`.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`Adamek:2011`, :cite:`Behrisch:2012`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`Meinke:1992`). These are natural generalizations that we will incorporate in our development later. (See :numref:`Chapter %s <postmodern-algebra>`.) But our first goal is to develop a working library for classical (single-sorted, set-based) universal algebra. 

---------------------------

.. index:: ! subalgebra

.. _subalgebras:

Subalgebras
-----------

This section introduces two important concepts in universal algebra, **subuniverse** and **subalgebra**.

.. A **subuniverse** of an algebra :math:`𝔸 = ⟨A, F^𝔸⟩` is a subset :math:`B ⊆ A` that is closed under the operations in :math:`F^𝔸`.

Suppose :math:`𝔸 = ⟨A, F^𝔸⟩` is an algebra. Recall, the (nonempty) set :math:`A` is called the **universe** of 𝔸.

We call a subset :math:`B ⊆ A` **closed under** (the operations in) :math:`F^𝔸` if for each :math:`f ∈ F^𝔸` and all :math:`b_0, \dots, b_{ρf-1} ∈ B` we have :math:`f(b_0, \dots, b_{ρ f-1}) ∈ B`. (Equivalently, :math:`∀ f ∈ F^𝔸,\ ∀ b : ρ f → B, \ f b ∈ B`.)

If a subset :math:`B ⊆ A` is closed under :math:`F^𝔸`, then we call :math:`B` a **subuniverse** of :math:`𝔸`.

If :math:`B ≠ ∅` is a subuniverse of 𝔸, and if we let :math:`F^𝔹 = \{ f ↾ B : f ∈ F^𝔸 \}`, then :math:`𝔹 = ⟨ B, F^𝔹 ⟩` is an algebra, called a **subalgebra** of 𝔸.

.. Equivalently, if :math:`B ≠ ∅` is a subuniverse of 𝔸 and :math:`F^{𝔹|_A} = \{f^𝔸|_B ∣ f ∈ F\}` is the set of basic operations of 𝔸 restricted to the set :math:`B`, then :math:`𝔹 = ⟨B, F^{𝔹|_A}⟩` is a **subalgebra** of 𝔸.

Conversely, all subalgebras are of this form.

If 𝔹 is a subalgebra of 𝔸, we denote this fact by :math:`𝔹 ≤ 𝔸`. Similarly, we write :math:`B ≤ 𝔸` if :math:`B` is a subuniverse of :math:`𝔸`. 

Notice that the empty set is a subuniverse of every algebra, but the universe of an algebra is never empty. 

**Fact**. If :math:`A_i ≤ 𝔸`, :math:`i ∈ I`, then :math:`⋂_{i∈ I} A_i` is a subuniverse.

.. index:: subuniverse generated by a set

Denote by :math:`𝖲 𝔸` the collection of all subalgebras of 𝔸.  

If 𝔸 is an algebra and :math:`X ⊆ A` a subset of the universe of 𝔸, then the **subuniverse of** 𝔸 **generated by** :math:`X`, denoted :math:`\operatorname{Sg}^𝔸 (X)` or :math:`⟨X⟩`, is the smallest subuniverse of 𝔸 containing the set :math:`X`.  Equivalently, 

.. math:: \mathrm{Sg}^{𝔸}(X)  =  ⋂ \{ U ∈ 𝖲 𝔸 ∣ X ⊆ U \}.
  :label: SgDef

---------------------------

.. index:: ! Subdirect product

.. _subdirect-product:

Subdirect product
-----------------

If :math:`k, n ∈ ℕ`, if :math:`A = (A_0, A_1, \dots, A_{n-1})` is a list of sets, and if :math:`σ : k → n` is a :math:`k`-tuple, then a relation :math:`R` over :math:`A` with scope :math:`σ` is a subset of the Cartesian product :math:`A_{σ(0)} × A_{σ(1)} × \cdots × A_{σ(k-1)}`.

Let :math:`F` be a set of operation symbols and for each :math:`i<n` let :math:`𝔸_i = ⟨ A_i, F ⟩` be an algebra of type :math:`F`. If :math:`𝔸 = ∏_{i<n}𝔸_i` is the product of these algebras, then a relation :math:`R` over :math:`𝔸` with scope :math:`σ` is called **compatible with** 𝔸 if it is closed under the basic operations in
:math:`F`. In other words, :math:`R` is compatible if the induced algebra :math:`ℝ = ⟨ R, F ⟩` is a subalgebra of :math:`\prod_{j<k} 𝔸_{σ(j)}`.

If :math:`R` is compatible with the product algebra and if the projection of :math:`R` onto each factor is surjective, then :math:`ℝ` is called a **subdirect product** of the algebras in the list :math:`(𝔸_{σ(0)}, 𝔸_{σ(1)}, \dots, 𝔸_{σ(k-1)})`; we denote this situation by writing :math:`ℝ ≤_{\mathrm{sd}} \prod_{j< k} 𝔸_{σ(j)}` [1]_ 

-----------------------------------------------

.. index:: ! homomorphism

.. _homomorphism:

Homomorphism
------------

Let :math:`𝔸 = ⟨ A, F^𝔸 ⟩` and :math:`𝔹 = ⟨ B, F^𝔹 ⟩` be algebras of the same signature, and let :math:`φ : A → B` be a function. Take an :math:`n`-ary operation symbol :math:`f ∈ F`, and suppose that for all :math:`a_1, \dots a_{n} ∈ A` the following equation holds:

.. math:: φ (f^𝔸 (a_1, \dots, a_{n})) = f^𝔹 (φ (a_1), \dots, φ (a_{n})).

Then :math:`φ` is said to **respect the interpretation of** :math:`f`. If :math:`φ` respects the interpretation of every :math:`f ∈ F`, then we call :math:`φ` a **homomorphism** from 𝔸 to 𝔹, and we write :math:`φ \in \operatorname{Hom}(𝔸, 𝔹)`, or simply, :math:`φ : 𝔸 → 𝔹`.

.. .. proof:observation::
..  For groups, to check that a map :math:`φ : G → H` is a homomorphism, it is enough to check that :math:`φ` respects the interpretation of the binary operation. It follows from this that such a function respects the unary and nulary operations as well.

---------------------------------

.. index:: ! epimorphism, ! monomorphism, ! automorphism

Epis, Monos, and Autos
-----------------------

.. todo:: complete this section

.. proof:definition:: Notation for homs, epis, monos, and autos

   If :math:`𝔸 = ⟨A, f^𝔸⟩` and :math:`𝔹 = ⟨B, f^𝔹⟩` are algebras, we denote and define

   + :math:`\hom(𝔸, 𝔹) =` homomorphisms from 𝔸 to 𝔹.
   + :math:`\epi(𝔸, 𝔹) =` epimorphisms from 𝔸 onto 𝔹.
   + :math:`\mono(𝔸, 𝔹) =` monomorphisms from 𝔸 into 𝔹.
   + :math:`\aut(𝔸, 𝔹) =` automorphisms from 𝔸 into and onto 𝔹.

------------------------------

.. rubric:: Footnotes

.. [1]
   For a brief and gentle introduction to type theory see the `section on axiomatic foundations <https://leanprover.github.io/logic_and_proof/axiomatic_foundations.html?highlight=type#type-theory>`_ in `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_.  Alternatively, viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. _categorytheory.gitlab.io: https://categorytheory.gitlab.io

.. _Lean: https://leanprover.github.io/
