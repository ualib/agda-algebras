.. include:: _static/math_macros.rst

.. _appendix-a:

==========================
Appendix A. Prerequisites
==========================

.. index:: ! relation, ! binary relation, ! preorder, ! partial order, ! equivalence relation

.. _relations:

Relations
---------

A **binary relation** is a set of ordered pairs. Thus, if :math:`X` is a set, a binary relation on :math:`X` is simply a subset of the Cartesian product :math:`X \times X`.

For a binary relation :math:`R`, we sometimes write :math:`x \mathrel{R} y` in place of :math:`(x, y) ∈ R`. For example, in the case of the order relation :math:`≤` on the set of natural numbers, :math:`≤` is the set :math:`\{(x, y) ∈ ℕ × ℕ : x` is less that or equal to :math:`y\}`, and we usually write :math:`x ≤ y` instead of :math:`(x, y) ∈ ≤`.

For a relation :math:`R`, we define the **domain** of :math:`R` (:math:`\dom R`) and the **range** of :math:`R` (:math:`\ran R`) by

.. math::

    x ∈  \dom R \quad & ⟺ \quad ∃ y, \, (x,y) ∈ R,\\
    x ∈ \ran R  \quad & ⟺ \quad ∃ t, \, (t,x) ∈ R.

Binary relations arise so often that we simply call them "relations," and only say "binary relation" when we want to highlight their **arity** (which is 2) and distinguish them from relations of other arities.

Some binary relations have properties that make them especially useful in a vast array of applications. For instance, a binary relation :math:`R` may or may not be

+ **reflexive**: :math:`∀ x, \, x \mathrel{R} x`,

+ **symmetric**: :math:`∀ x\, ∀ y, \, (x \mathrel{R} y \; ⟶ \; y \mathrel{R} x)`;

+ **antisymmetric**: :math:`∀  x,\, ∀ y,\, (x \mathrel{R} y ∧ y\mathrel{R} x \; ⟶ \; x=y)`;

+ **transitive**: :math:`∀ x,\, ∀ y,\, ∀ z, \, x \mathrel{R} y ∧ y \mathrel{R} z\; ⟶ \; x \mathrel{R} z)`.

A **preorder** on a set :math:`X` is a reflexive and transitive subset of :math:`X × X`.

If :math:`R` is a preorder on :math:`X`, then we call :math:`⟨X, R⟩` (or :math:`X` itself) as a **preordered set**.

.. proof:example::

   The `reachability relation <http://en.wikipedia.org/wiki/Reachability>`_ of a `directed graph <http://en.wikipedia.org/wiki/Directed_graph>`_ (possibly containing cycles) gives rise to a preorder :math:`R`, where :math:`x \mathrel{R} y` if and only if the directed graph has a path from :math:`x` to :math:`y`.

   Conversely, every preorder :math:`R` on a set :math:`X` is the reachability relation of a directed graph (simply take elements of :math:`X` to be the vertices and draw an edge from :math:`x` to :math:`y` whenever :math:`x \mathrel{R} y`).

The significance of preorders stems mainly from the fact that the two most important classes of binary relations happen to be preorders. These are *partial orders* and *equivalence relations*.

An **equivalence relation** is a symmetric preorder.

A **partial ordering** (or "partial order") is an anti-symmetric preorder.  A **partially ordered set** (or "poset") :math:`⟨X, R⟩` is a set :math:`X` along with a partial order :math:`R` defined on :math:`X`.

We denote the set of all equivalence relations on a set :math:`X` by :math:`\mathrm{Eq}(X)`.

Here are a few concrete examples of binary relations that arise often.

#. If :math:`X = ℤ` and :math:`R` is the usual :math:`≤` relation, then :math:`R` is a partial order on :math:`X`. (In fact, :math:`≤` is a :term:`total order` on :math:`ℤ` in this case.)

#. Let :math:`X` be any set and let :math:`\mathcal{P}(X)` be the collection of all subsets of :math:`X`. The subset relation :math:`y ⊆ z` (":math:`y` is a subset of :math:`z`") is a partial order on :math:`\mathcal{P}(X)`.

#. Let :math:`X = ℝ^2` and :math:`R =` ":math:`≤` on each component"; i.e., :math:`R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a_1 ≤ b_1, \, a_2 ≤ b_2 \}`. Then :math:`R` is a partial order on :math:`X`.

#. If :math:`A = ℝ^2` then :math:`R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a = (a_1, a_2), \; b = (b_1, b_2), \; a_1^2+ a_2^2 = b_1^2+ b_2^2 \}` is an equivalence relation on :math:`A`. The equivalence classes are circles centered at :math:`(0,0)`.

A **partition** of a set :math:`A` is a collection :math:`Π = \{A_i : i ∈ I\}` of non-empty subsets of :math:`A` such that

.. math:: ⋃_{i ∈ I} A_i = A \quad \text{ and } \quad  A_i ∩ A_j = ∅  \quad ∀ i ≠ j.

The :math:`A_i` are called the “blocks” of the partition.

Every partition :math:`Π` determines an equivalence relation—namely, the relation :math:`R` defined by :math:`a\mathrel{R} b` if and only if :math:`a` and :math:`b` are in the same block of :math:`Π`.

Conversely, if :math:`R` is an equivalence relation on :math:`A`, we denote the equivalence class of :math:`R` containing :math:`a` by :math:`a/R := \{b ∈ A : a \mathrel{R} b\}` and the set :math:`A/θ := \{a/θ : a ∈ A\}` of all :math:`θ` classes is a partition of :math:`A`.

Examples: preorders, partial orders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An **equivalence relation** on a set :math:`X` is a preorder that is **symmetric**. That is, an equivalence relation is a binary relation that is reflexive, symmetric, and transitive.

With any preorder :math:`X` we can associate a poset in a natural way. Since a preorder is not antisymmetric in general, we may have distinct elements :math:`x, y ∈ X` with :math:`x ≤ y` and :math:`y ≤ x`.

However, in this case we define the binary relation :math:`≅` on :math:`X` by: :math:`x ≅ y` iff :math:`x ≤ y` and :math:`y ≤ x`. [1]_

The relation ≅ so defined is an equivalence relation on :math:`X` and if we simply equate all ≅-related pairs, then we obtain a poset, denoted by :math:`X/≅`.

The elements of :math:`X/≅` are ≅-equivalence classes. These classes partition the set :math:`X` into disjoint subsets, each subset consisting of elements that are pairwise ≅-equivalent.

For :math:`x ∈ X`, the equivalence class containing the element :math:`x`---which is sometimes denoted by :math:`[x]` or :math:`[x]_≅`---is given by the set :math:`[x]=\{y ∈ X : x ≅ y\}`.

The relation ≤ defined by :math:`[x] ≤ [y]` iff :math:`x ≤ y` is a partial order on the set :math:`X/≅ := \{[x] : x ∈ X\}` of equivalence classes. The poset :math:`X/≅` is sometimes called the **poset reflection** of the preorder :math:`X`.

Let :math:`⟨ X, ≤ ⟩` be a preordered set, let :math:`A, B, C ⊆ X` be subsets, and let :math:`x ∈ X`. If :math:`a ≤ x` for all :math:`a ∈ A`, then we write :math:`A ≤ x` and we say that :math:`x` is an **upper bound** for :math:`A` in :math:`X`. (Lower bounds are defined dually.)

A **join** of :math:`A` (when it exists) is a least element in the set of all upper bounds of :math:`A` in :math:`X`. A join is sometimes called a **least upper bound** or **supremum**.

Dually, a **meet** of :math:`A` (when it exists) is a greatest element in the set of all lower bounds of :math:`A` in :math:`X`. A meet of :math:`A` is sometimes
called a **greatest lower bound** or **infimum**.

It is easy to see that joins and meets of preordered sets are determined uniquely up to ≅-equivalence. Indeed, if :math:`a` and :math:`a'` are two least upper bounds of :math:`A`, then we clearly have :math:`a ≤ a'` and :math:`a' ≤ a`; therefore, :math:`a ≅ a'`.

If a subset :math:`A` has at least one join, then we will let :math:`⋁ A` denote a choice of one of the joins of :math:`A`. Similarly, if :math:`A` has at least one meet, then we let :math:`⋀ A` denote a choice of one of the meets of :math:`A`.

To specify the preorder :math:`X` with respect to which the join or meet is taken, we write :math:`⋁_X A` and :math:`⋀_X A`, respectively.

Note that for every :math:`x ∈ X` we have :math:`⋁_X A ≤ x` iff :math:`A ≤ x`. Dually, :math:`x ≤ ⋀_X A` iff :math:`x ≤ A`.

Considering the empty subset :math:`∅ ⊆ X`, and in light of the fact that for every :math:`x ∈ X` the implication :math:`a ∈ ∅ ⟶ a ≤ x` holds, *ex falso quodlibet*, we see that the join of :math:`∅`, if it exists, must satisfy :math:`⋁ ∅ ≤ x` for all :math:`x ∈ X`. Therefore, :math:`⊥ := ⋁ ∅` is the “bottom” of any preorder in which it exists.

Dually, :math:`a ∈ ∅ ⟶ x ≤ a` also holds, *ex falso quodlibet*, so for all :math:`x ∈ X` we have :math:`⋀ ∅ ≤ x`, so we let :math:`⊤ := ⋀ ∅` be the “top” of any preorder
in which it exists.

Let :math:`⟨ X, ≤ ⟩` be a preordered set and :math:`C ⊆ X`. We call :math:`C` a **chain** of :math:`⟨ X, ≤ ⟩` if for all :math:`x, y ∈ C` either :math:`x ≤ y` or :math:`y ≤ x` holds. If, in addition, the elements of :math:`C` can be indexed by the natural numbers, then we call :math:`C` an ω-**chain**.

A subset :math:`A` of the preordered set :math:`X` is called an **antichain** if for all :math:`x, y ∈ A` we have :math:`x ≤ y` implies :math:`y ≤ x`.

.. index:: ! function

Functions
---------

A **function** (or **mapping**) is a relation :math:`F` such that for each :math:`x` in :math:`\dom F` there is only one :math:`y` such that :math:`x \mathrel{F} y`.

The following operations are most commonly applied to functions, are sometimes applied to relations, but can actually be defined for arbitrary sets :math:`A`, :math:`F`, and :math:`G`.

#. The **inverse** of :math:`F` is denoted and defined by

    .. math:: F^{-1} = \{(u, v) ∣ v \mathrel{F} u\} = \{(u, v) ∣ (v,u) ∈ F \}.

#. The **composition** of :math:`F` and :math:`G` is denoted and defined by

    .. math::

       F ∘ G = \{(u, v) ∣ ∃ t \ (u \mathrel{G} t \ ⋀ \ t \mathrel{F} v)\} = \{(u, v) ∣ ∃ t \ ((u,t) ∈ G\ ⋀ \ (t,v) ∈ F)\}.

#. The **restriction** of :math:`F` to :math:`A` is denoted and defined by

    .. math::

       F ↾ A = \{(u, v) ∣ u \mathrel{F} v \ ⋀ \ u ∈ A\} = \{(u, v) ∣ (u,v)∈ F\ ⋀ \ u \in A\}.

     We often denote this restriction by :math:`F|_A`.

#. The **image** of :math:`A` under :math:`F` is denoted and defined by

    .. math:: F[A] = \ran (F ↾ A) = \{v \mid (\exists u \in A)\; (u,v) \in F\}.

    The image :math:`F[A]` can be characterized more simply when :math:`F` is a function and :math:`A ⊆ \dom F`; in this case :math:`F[A] = \{F(u) ∣ u ∈ A\}`.

    In each case we can easily apply a subset axiom to establish the existence of the desired set. Specifically,

    .. math:: F^{-1} ⊆ \ran F × \dom F, \quad  F ∘ G ⊆ \dom G × \ran F, \quad F ↾ A ⊆ F, \quad F[A] ⊆ \ran F.

    (A more detailed justification of the definition of :math:`F^{-1}` would go as follows: By a subset axiom there is a set :math:`B` such that for every :math:`x`,

    .. math:: x ∈ B \quad ⟺ \quad  x ∈ \ran F × \dom F \ ⋀ \ ∃ u \ ∃ v \ (x = (u, v) \ ⋀ \ (v, u) ∈ F).

    It then follows that

    .. math:: x ∈ B \quad ⟺ \quad ∃ u \ ∃ v \ (x = (u, v) \ ⋀ \ (v, u) ∈ F).

    We denote this unique set :math:`B` by :math:`F^{-1}`.)

Let

.. math:: F = \{ (∅, a), (\{∅\}, b) \}.

Observe that :math:`F` is a function. We have :math:`F^{-1} = \{ (a, ∅), (b, \{∅\}) \}`. Thus, :math:`F^{-1}` is a function iff :math:`a ≠ b`.

The restriction of :math:`F` to :math:`∅` is :math:`∅`, but :math:`F ↾ \{∅\} = \{(0, a)\}`.

Consequently, :math:`F[\{\emptyset \}] = \{a\}`, in contrast to the fact that :math:`F(\{∅\}) = b`.

Assume that :math:`F: A → B`, and that :math:`A` is nonempty.

#. There exists a function :math:`G: B → A` (a “left inverse”) such that :math:`G ∘ F` is the identity function :math:`\id_{A}` on :math:`A` iff :math:`F` is one-to-one.

#. There exists a function :math:`H: B → A` (a “right inverse”) such that :math:`F ∘ H` is the identity function :math:`\id_{B}` on :math:`B` iff :math:`F` maps :math:`A` *onto* :math:`B`.

.. proof:theorem:: Axiom of Choice 1

   For any relation :math:`R` there is a function :math:`H ⊆ R` with :math:`\dom H = \dom R`.

With this axiom we can prove the sufficiency direction of part 2 of the theorem above: take :math:`H` to be a function with :math:`H ⊆ F^{-1}` and :math:`\dom H = \dom F^{-1} = B`. Then :math:`H` does what we want: Given any :math:`y ∈ B`, we have :math:`(y,H(y)) ∈ F^{-1}` hence :math:`(H(y), y) ∈ F`, and so :math:`F(H(y)) = y`.

Relations of higher arity
~~~~~~~~~~~~~~~~~~~~~~~~~

We can extend the definition of ordered pairs and define an *ordered triple* recursively.

.. math:: (x, y, z) = ((x, y), z).

Similarly, *ordered quadruples*.

.. math::

   (x_1, x_2, x_3, x_4) = ((x_1, x_2, x_3), x_4) = (((x_1,x_2),x_3),x_4).

Inductively, for each :math:`n ∈ ℕ`, if we assume the notion of ordered :math:`k`-tuple, :math:`(x_1, \dots, x_k)`, has been defined for :math:`k < n`, we can form **ordered** :math:`n`-**tuples** as follows:

.. math:: (x_1, \dots, x_{n-1}, x_n) = ((x_1, \dots, x_{n-1}), x_n).

It is convenient for reasons of uniformity to define also the 1-**tuple** :math:`(x) = x`.

We define an :math:`n`-ary relation on :math:`A` to be a set of ordered :math:`n`-tuples with all components in :math:`A`. Thus a binary (2-ary) relation on :math:`A` is just a subset of :math:`A \times A`. A ternary (3-ary) relation on :math:`A` is a subset of :math:`(A \times A) \times A`, and so on.

There is, however, a terminological quirk here. If :math:`n > 1`, then any :math:`n`-ary relation on :math:`A` is actually a binary relation, but a unary (1-ary)
relation on :math:`A` is just a subset of :math:`A`.

A :math:`k`-**ary relation** :math:`R` on a set :math:`A` is a subset of the Cartesian product :math:`A^k`.

We give some examples of relations below. In these examples, :math:`ℝ` denotes the set of real numbers, and letters :math:`a ∈ ℝ^2`, :math:`b ∈ ℝ^3` etc. denote tuples :math:`(a_0, a_1)`, :math:`(b_0, b_1, b_2)`, etc.

#. :math:`A = ℝ` and :math:`R = \{a\in ℝ^2: a_0 = a_1\} = \{(x,x) : x ∈ ℝ \}`.

(b) :math:`A = ℝ^2` (the plane) and :math:`R = \{(a,b,c) ∈ ℝ^2 × ℝ^2 × ℝ^2 : a, b, c \text{ lie on a line } \}`; i.e. triples of points that are *colinear*.

Note that a 1-ary or **unary relation** on a set :math:`A` is simply a subset of :math:`A`, a **binary relation** is a subset of :math:`A^2`, a **ternary relation** is a subset of :math:`A^3`, etc.







.. .. _basic-type-theory:

.. Basic type theory
.. -----------------

.. This section presents some of the rudiments of *type theory*.  For more details, a nice and easy introduction to the basics is `Logic and Proof`_, and more advanced treatments are :cite:`MR3445957` and :cite:`HoTT`.

.. .. todo:: say something more about this






.. _curry-howard:

Curry-Howard
------------

The rule for *function application* corresponds, under the “Curry-Howard” or “propositions-as-types” correspondence, to the *implication elimination* rule of natural deduction (sometimes called *modus ponens*). It is the following:

This simply codifies our intuitive notion of function application, viz. applying the function :math:`f` to an inhabitant :math:`a` of the domain :math:`A`, we obtain an inhabitant :math:`f \, a` of the codomain :math:`B`. If we interpret :math:`A` and :math:`B` as propositions, :math:`f` as a proof of the implication :math:`A \to B`, and :math:`a` as a proof of :math:`A`, then the rule :math:`\mathsf{app}` becomes the implication elimination rule (*modus ponens*).

.. _dependent-types:

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

The simplest example of a Pi type is the Cartesian product :math:`B_0 × B_1` which, when viewed as the collection of functions that map :math:`i ∈ \{0, 1\}` to some element of :math:`B_i`, is the type :math:`\Pi_{i : \{0, 1\}} B_i`. [2]_

.. index:: type of; dependent pairs (Sigma type)

Similarly, the :ref:`Sigma type <sigma-type>` :math:`\sum_{(x:A)}, B x`, also known as the :ref:`dependent pair type <sigma-type>`, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.

The simplest example of a Sigma type is the disjoint union :math:`B_0 \coprod B_1` which may be viewed as a collection of ordered pairs :math:`(i, b_i)`, where the first coordinate indicates to which set the second element belongs.  For example, if the two sets are :math:`B_0 = \{a, b\}` and :math:`B_1 = \{a, b, c\}` we form the disjoint union of :math:`B_0` and :math:`B_1` as follows:

.. math:: B_0 + B_1 = \{(0,a), (0,b), (1,a), (1,b), (1,c)\}.

Alternatively, some authors prefer to use the injection function to indicate the set from which an element originated.  For example, if we denote the injection into the :math:`i`-th coordinate by :math:`ι_i`, then a perfectly adequate presention of math::`B_0 + B_1` would be

.. math:: B_0 + B_1 = \{ι_0 a, ι_0 a, ι_1 a, ι_1 b, ι_1 c\}.

.. index:: dependent type theory, inductive type, universes

.. _inductive-types:

Inductive types
-----------------

.. todo:: say something about this

**Inductive types** and **inductive families of types**, generating only the recursor for an inductive type;

---------------------

Compariosn of ITPs
------------------

The following popular :term:`ITPs <ITP>` are all based on some flavor of :term:`dependent type` theory.

+ NuPRL_ (Cornell). :term:`extensional`, :term:`predicative`
+ Coq_ (INRIA).  :term:`intensional`, :term:`impredicative`
+ Agda_ (Göteborg). :term:`intensional`, :term:`predicative`
+ Lean_ (Microsoft Research, CMU) :term:`extensional`, :term:`impredicative`

.. rubric:: Footnotes

.. [1]
   Some authors call the elements :math:`x` and :math:`y` **isomorphic** in this case, but we prefer the term :math:`≅`-equivalent. 

.. [2]
   Of course, it's more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1) : b_i ∈ B_i, i = 0, 1\}`, but as usual we identify tuples with functions, which yields the :ref:`Pi type <pi-type>`.

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

