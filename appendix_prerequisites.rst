.. File: appendix_prerequisites.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 11 Oct 2019
.. Updated: 5 Nov 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. highlight:: lean

.. _prerequisites:

=============
Prerequisites
=============

.. contents:: :local:
    :depth: 2

This chapter highlights some of the basic definitions from mathematics and type theory with which (we hope) our dear reader is familiar.

We provide a mere sketch, or rough outline, that may be skimmed now or consulted later.  In fact, this appendix is included mainly to give the reader enough comfort and confidence (whether deserved or not) to fearlessly dive into the main chapters, without worrying about lack of preparation or "mathematical sophistication."

None of the material in this section is new, and there are many (probably superior) sources for this information. (See the :ref:`References Section <refs>`.)

Nonetheless, and somewhat reluctantly, we begin.

-------------------------

.. _mathematics:

Mathematics
-----------

This section highlights some basic, and by now quite standard, definitions from abstract mathematics, mostly from the field of algebra.

.. index:: ! relation, ! binary relation, ! domain, ! range, ! arity
.. index:: ! reflexive, ! symmetric, ! antisymmetric, ! transitive

.. _binary-relations:

Binary relations
~~~~~~~~~~~~~~~~~~~

A **binary relation** is a set of ordered pairs. Thus, if :math:`X` is a set, a binary relation on :math:`X` is simply a subset of the Cartesian product :math:`X \times X`.

For a binary relation :math:`R`, we sometimes write :math:`x \mathrel{R} y` in place of :math:`(x, y) ∈ R`. For example, in the case of the order relation :math:`≤` on the set of natural numbers, :math:`≤` is the set :math:`\{(x, y) ∈ ℕ × ℕ : x` is less that or equal to :math:`y\}`, and we usually write :math:`x ≤ y` instead of :math:`(x, y) ∈ ≤`.

For a relation :math:`R`, we define the **domain** of :math:`R` (:math:`\dom R`) and the **range** of :math:`R` (:math:`\ran R`) by

.. math::

    x ∈  \dom R \quad & ⟺ \quad ∃ y, \, (x,y) ∈ R,\\
    x ∈ \ran R  \quad & ⟺ \quad ∃ t, \, (t,x) ∈ R.

Binary relations arise so often that we simply call them "relations," and only say "binary relation" when we want to highlight their **arity** (which is 2) and distinguish them from relations of other arities.

Some binary relations have properties that make them especially useful in a vast array of applications. For instance, we call a binary relation :math:`R`

+ **reflexive** if :math:`∀ x ∈ X, \ x \mathrel{R} x`;

+ **symmetric** if :math:`∀ x, y ∈ X \ (x \mathrel{R} y \ → \ y \mathrel{R} x)`;

+ **antisymmetric** if :math:`∀  x, y ∈ X \ (x \mathrel{R} y ∧ y\mathrel{R} x \ → \ x=y)`;

+ **transitive** if :math:`∀ x, y, z ∈ X \ (x \mathrel{R} y ∧ y \mathrel{R} z\ → \ x \mathrel{R} z)`.


More generally, if :math:`X, Y` are sets, then a (binary) **relation from** :math:`X` to :math:`Y` is a subset of :math:`X × Y`.

.. index:: ! preorder, ! preordered set

.. _preorders:

Preorders
~~~~~~~~~~~~

A **preorder** on a set :math:`X` is a reflexive and transitive (binary) relation on :math:`X`. If :math:`R` is a preorder on :math:`X`, then we call :math:`⟨X, R⟩` (or :math:`X` itself) a **preordered set**.

.. proof:examples::

   The `reachability relation <http://en.wikipedia.org/wiki/Reachability>`_ of a `directed graph <http://en.wikipedia.org/wiki/Directed_graph>`_ (possibly containing cycles) gives rise to a preorder :math:`R`, where :math:`x \mathrel{R} y` if and only if the directed graph has a path from :math:`x` to :math:`y`.

   Conversely, every preorder :math:`R` on a set :math:`X` is the reachability relation of a directed graph (simply take elements of :math:`X` to be the vertices and draw an edge from :math:`x` to :math:`y` whenever :math:`x \mathrel{R} y`).

The significance of preorders stems mainly from the fact that the two most important classes of binary relations happen to be preorders. These are *equivalence relations* and *partial orders*.

.. index:: ! equivalence relation, ! equivalence class, ! partition, ! block, ! representative, ! kernel

.. _equivalence-relations:

Equivalence relations
~~~~~~~~~~~~~~~~~~~~~~

An **equivalence relation** is a symmetric preorder.  That is, an equivalence relation is a binary relation ≈ on a set :math:`A` such that

* ≈ is **reflexive**: :math:`∀ a ∈ A, \ a ≈ a`;
* ≈ is **symmetric**: :math:`∀ a, b ∈ A \ (a ≈ b\ →\ b ≈ a)`;
* ≈ is **transitive**: :math:`∀ a, b, c ∈ A \ (a ≈ b ∧ b ≈ c \ → \ a ≈ c)`.

.. .. math:: ∀ a ∈ A       \ a ≡ a; & \quad \text{(reflexivity)}\\
..           ∀ a, b ∈ A    \ (a ≡ b\ →\ b ≡ a) & \quad \text{(symmetry)}\\
..           ∀ a, b, c ∈ A \ (a ≡ b ∧ b ≡ c \ → \ a ≡ c) & \quad (transitivity).

If ≈ is an equivalence relation on :math:`A`, then the **equivalence class** of ≈ that contains :math:`a` is :math:`\{b ∈ A : a ≈ b\}`, which we denote by :math:`a/{≈}`.  We call this "the ≈-class containing :math:`a`", and :math:`a` is called a **representative** of the class :math:`a/{≈}`.

  *Every equivalence relation on a set determines a partition of that set as the disjoint union of the collection equivalence classes*. 

By a **partition** of :math:`A`, we mean a collection :math:`\{A_i : i ∈ I\}` of non-empty subsets of :math:`A` such that

.. math:: ⋃_{i ∈ I} A_i = A \quad \text{ and } \quad  A_i ∩ A_j = ∅  \quad ∀ i ≠ j.

Each :math:`A_i` is called a **block** of the partition.

The collection :math:`\{a/{≈} : a ∈ A\}` of all ≈-classes of :math:`A` is denoted by :math:`A/{≈}`.

Evidently, the blocks of a partition may be viewed as the equivalence classes of an equivalence relation---namely, the relation :math:`R` defined by :math:`a\mathrel{R} b` if and only if :math:`a` and :math:`b` are in the same block of the partition.

  *Every partition of a set determines an equivalence relation on that set*.

.. proof:examples::

   Here are two examples.

   If :math:`A = ℝ^2`, then
   
   .. math:: R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a = (a_1, a_2), \; b = (b_1, b_2), \; a_1^2+ a_2^2 = b_1^2+ b_2^2 \}
   
   is an equivalence relation on :math:`A`. Each equivalence class (or block) of :math:`R` is a circle centered at :math:`(0,0)` and :math:`ℝ^2` is the disjoint union of all these circles. 
   
   As another example, let
   
   .. math:: R' = \{(a, b) ∈ ℝ^2 × ℝ^2 : a = (a_1, a_2), \; b = (b_1, b_2), \; a_1- a_2 = b_1- b_2\}.
   
   Then :math:`R'` forms an equivalence relation on :math:`ℝ^2` where each equivalence class (or block) is a 45 degree line.
   
Notice that the examples :math:`R` and :math:`R'` are distinct instances of equivalence relations on the same set :math:`A = ℝ^2`.  We denote the set of all equivalence relations on a :math:`A` by :math:`\operatorname{Eq}(A)`.

There are always at least two equivalence relations in on a given set :math:`A`---namely, :math:`0_A := \{(x, y) : x = y ∈ A\}` (the smallest), and :math:`1_A := \{(x, y) : x ∈ A, y ∈ A\} = A × A` (the largest).
   
.. proof:examples::

   It is instructive, especially at the start of one's studies, to consider many examples.  Here are a few more examples that the reader is invited to confirm are indeed instances of equivalence relations.

   #. The relation on calendar days, given by ":math:`x` and :math:`y` fall on the same day of the week" is an equivalence relation.
   #. The relation on people currently alive on the planet, given by ":math:`x` and :math:`y` have the same birthday" is an equivalence relation.
   #. The relation on cities in the United States, given by ":math:`x` and :math:`y` are in the same state" is an equivalence relation.

.. index:: ! kernel

.. proof:examples::

   Two common mathematical examples are these.

   #. The :term:`kernel` of a function is an equivalence relation on :math:`X`; if :math:`f : X → Y` is a function and if :math:`x_1, x_2 ∈ X`, then we say :math:`x_1` and :math:`x_2` are **equivalent modulo the kernel of** :math:`f` and we write :math:`(x_1, x_2) ∈ \ker f` (or :math:`x₁ \mathrel{\mathrm{ker} f} x₂`) if and only if :math:`f(x_1) = f(x_2)`.
   #. The relation on lines in a plane, given by ":math:`x` and :math:`y` are parallel" is an equivalence relation.

   Here, we say that :math:`x` is congruent to :math:`y` modulo :math:`m` if they leave the same remainder when divided by :math:`m`. Soon, you will be able to prove rigorously that this is equivalent to saying that :math:`x - y` is divisible by :math:`m`.

.. index:: ! partial ordering
.. index:: pair: partially ordered set; poset

.. _partial-order-relations:

Partial order relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~

A **partial ordering** (or "partial order") is an anti-symmetric preorder.

A **partially ordered set** (or "poset") :math:`⟨X, R⟩` is a set :math:`X` along with a partial order :math:`R` defined on :math:`X`.

.. proof:examples::

   #. If :math:`X = ℤ` and :math:`R` is the usual :math:`≤` relation, then :math:`R` is a partial order on :math:`X`. (In fact, :math:`≤` is a :term:`total order` on :math:`ℤ` in this case.)

   #. Let :math:`X` be any set and let :math:`\mathcal{P}(X)` be the collection of all subsets of :math:`X`. The subset relation :math:`y ⊆ z` (":math:`y` is a subset of :math:`z`") is a partial order on :math:`\mathcal{P}(X)`.

   #. Let :math:`X = ℝ^2` and :math:`R =` ":math:`≤` on each component"; i.e., :math:`R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a_1 ≤ b_1, \, a_2 ≤ b_2 \}`. Then :math:`R` is a partial order on :math:`X`.

The poset induced by a preorder
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

With any preorder :math:`X` we can associate a poset in a natural way as we now explain.

Since a preorder is not antisymmetric in general, we may have distinct elements :math:`x, y ∈ X` with :math:`x ≤ y` and :math:`y ≤ x`.

In this case we define the binary relation :math:`≅` on :math:`X` by: :math:`x ≅ y` iff :math:`x ≤ y` and :math:`y ≤ x`.

.. index:: ! equivalence class, ! representative

The relation :math:`≅` so defined is an equivalence relation on the set :math:`X`, and as such it partitions :math:`X` into disjoint equivalence classes, :math:`X_0, X_1, \dots`, where :math:`x ≅ y` iff :math:`x, y ∈ X_i` for some :math:`i`.

Now imagine that we do not wish to distinguish between elements of a single equivalence class. Then we can think of each equivalence class as a single object and each member of a particular class can be taken as a representative of that class.

The result is a poset, denoted by :math:`X/{≅}`, whose elements are the equivalence classes of :math:`≅`.

.. These classes partition the set :math:`X` into disjoint subsets, each subset consisting of elements that are pairwise equivalent.

Precisely, for each :math:`x ∈ X`, we denote and define the **equivalence class** containing the element :math:`x` by 

.. math:: x/{≅} \; = \{y ∈ X : x ≅ y\}.

(Some authors prefer the notation :math:`[x]` or :math:`[x]_{\cong}` for the equivalence class containing :math:`x`.)

As above, we denote the set :math:`\{x/{\cong} \; : x ∈ X\}` of all :math:`\cong`-equivalence classes by :math:`X/{\cong}`.

Let :math:`⊑` denote the relation on :math:`X/{\cong}` defined as follows: :math:`∀ x \ ∀ y \ (x/{\cong} \ ⊑ y/{\cong} \ ⟺ \ x ≤ y)`.  Then, evidently, :math:`⊑` is a partial ordering on :math:`X/{\cong}`. The poset :math:`⟨ X/{\cong}, ≤ ⟩` is sometimes called the **poset reflection** of the preordered set :math:`⟨ X, ≤ ⟩`.

.. index:: ! total ordering, ! partial order, ! trichotomy property
.. index:: strict partial order
.. index:: ! pair: total ordering; linear ordering
.. index:: ! pair: strict total ordering; strict linear ordering

.. _total-and-strict-orderings:

Total and strict orderings
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A partial order ≤ on a domain :math:`A` is a **total order** (also called a **linear order**) if all elements are pairwise comparable; that is, for all :math:`a, b ∈ A`, we have either :math:`a ≤ b` or :math:`b ≤ a`.

.. proof:examples::

    Here are two examples of partial orders that are not total orders.

    #. The divides relation, :math:`x ∣ y`, on the integers.
    #. The subset relation, :math:`x ⊆ y`, on sets of elements of some domain :math:`A`.

A binary relation :math:`<` on a domain :math:`A` is a **strict partial order** if it satisfies the following:

- (irreflexive) :math:`a ≮ a` for every :math:`a` in :math:`A`
- (transitive) :math:`a < b` and :math:`b < c` implies :math:`a < c`, for every :math:`a`, :math:`b`, and :math:`c` in :math:`A`

A strict partial order is a **strict total order** (or **strict linear order**) if, in addition, it has the **trichotomy property**: :math:`a < b`, :math:`a = b`, or :math:`a > b` for every :math:`a` and :math:`b` in :math:`A`.

Here, :math:`b ≮ a` means, of course, that it is not the case that :math:`a < b`.

.. proof:prop::
   
   A strict partial order :math:`<` on :math:`A` is **asymmetric**: for every :math:`a` and :math:`b`, :math:`a < b` implies :math:`b ≮ a`.

*Proof*. Suppose :math:`a < b` and :math:`b < a`. Then, by transitivity, :math:`a < a`, contradicting irreflexivity.

On the integers, there are precise relationships between :math:`<` and :math:`≤`: :math:`x ≤ y` if and only if :math:`x < y` or :math:`x = y`, and :math:`x < y` if and only if :math:`x ≤ y` and :math:`x ≠ y`. This illustrates a more general phenomenon.

.. proof:theorem::

    Suppose ≤ is a partial order on a domain :math:`A`. Define :math:`a < b` to mean that :math:`a ≤ b` and :math:`a ≠ b`. Then :math:`<` is a strict partial order. Moreover, if ≤ is total, then so is :math:`<`.

.. proof:theorem::

    Suppose :math:`<` is a strict partial order on a domain :math:`A`. Define :math:`a ≤ b` to mean :math:`a < b` or :math:`a = b`. Then ≤ is a partial order. Moreover, if :math:`<` is total, so is ≤.

.. We will prove the second here, and leave the first as an exercise.

.. .. Proof of the first theorem:

.. **Proof**. Suppose :math:`\leq` is a partial order on :math:`A`, and :math:`<` be defined as in the statement of the theorem. Irreflexivity is immediate, since :math:`a < a` implies :math:`a \neq a`, which is a contradiction.

.. To show transitivity, suppose :math:`a < b` and :math:`b < c`. Then we have :math:`a \leq b`, :math:`b \leq c`, :math:`a \neq b`, and :math:`b \neq c`. By the transitivity of :math:`\leq`, we have :math:`a \leq c`. To show :math:`a < c`, we only have to show :math:`a \neq c`. So suppose :math:`a = c`. then, from the hypotheses, we have :math:`c < b` and :math:`b < c`, violating asymmetry. So :math:`a \neq c`, as required.

.. To establish the last claim in the theorem, suppose :math:`\leq` is total, and let :math:`a` and :math:`b` be any elements of :math:`A`. We need to show that :math:`a < b`, :math:`a = b`, or :math:`a > b`. If :math:`a = b`, we are done, so we can assume :math:`a \neq b`. Since :math:`\leq` is total, we have :math:`a \leq b` or :math:`a \leq b`. Since :math:`a \neq b`, in the first case we have :math:`a < b`, and in the second case, we have :math:`a > b`.

.. index:: ! pair: syntactic equality; semantic equality

.. _equality:

Equality
~~~~~~~~~~~~~

Let :math:`A` be a set and let ≡ be equivalence relation on :math:`A`.  Recall, this means that, in addition to being a binary relation, ≡ has three special properties.

-  ≡ is **reflexive**; :math:`∀ a ∈ A`, :math:`a ≡ a`;
-  ≡ is **symmetric**; i.e., :math:`∀ a, b ∈ A` if :math:`a ≡ b`, then :math:`b ≡ a`;
-  ≡ is **transitive**; i.e., :math:`∀ a, b, c ∈ A` if :math:`a ≡ b` and :math:`b ≡ c`, then :math:`a ≡ c`.

These three properties alone are not strong enough to characterize *equality*.

.. Consider the equivalence relation on citizens of the United States, given by ":math:`x` and :math:`y` have the same age." There are some properties that respect that equivalence. For example, suppose I tell you that John and Susan have the same age, and I also tell you that John is old enough to vote. Then you can rightly infer that Susan is old enough to vote. On the other hand, if I tell you nothing more than the facts that John and Susan have the same age and John lives in South Dakota, you cannot infer that Susan lives in South Dakota. This little example illustrates what is special about the *equality* relation: if two things are equal, then they have exactly the same properties.

In mathematics, there are many notions of equality. These are usually implicit and almost never mentioned.  Instead, one assumes that the intended notion of equality is obvious from context.

In computer science, however, such informality is unacceptable since computers cannot infer the appropriate equality in every situation.  For this reason, explicit mention of particular notions of equality is more common in computer science than in mathematics. [1]_

Here's a concrete example that illustrates what we're carrying on about.

  :math:`2 + 5` is equal to :math:`7` semantically; they are not syntactically (e.g., the first expression involves more symbols than the second).

Two basic, distinct notions of equality are

  * **syntactic equality**, where two expressions are "equal" if and only if exactly the same symbols appear in exactly the same order in each expression;
  
  * **semantic equality**, which takes two expressions to be "equal" if they have the same *meaning*; that is, they refer to (or *denote*) the same object.  

Axiomatically, every relation used to represent some notion of an equality ought to at least be an *equivalence relation* (i.e., a reflexive, symmetric, transitive binary relation).  Of course, there are a number of distinct equivalence relations on a nonempty set, so these properties do not fully characterize equality.

For a useful general definition of the equality relation on terms and formulas that suits our purposes, see the `Equality Section`_ of `Logic and Proof`_.

.. index:: ! pair: ordered tuples; tuples
.. index:: ! unary relation, ! binary relation, ! ternary relation

Relations more generally
~~~~~~~~~~~~~~~~~~~~~~~~

We can extend the definition of ordered pairs and define an **ordered triple** recursively.

.. math:: (x, y, z) = ((x, y), z).

Similarly, **ordered quadruples**.

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


Note that a 1-ary or **unary relation** on a set :math:`A` is simply a subset of :math:`A`, a **binary relation** is a subset of :math:`A^2`, a **ternary relation** is a subset of :math:`A^3`; finally, an :math:`n`-**ary relation** on :math:`A` is a subset of :math:`A^n`.

Finally, although it arises less frequently in the theory, an even more general definition of relation is worth mentioning.

Let :math:`I` be a set and for each :math:`i ∈ I` let :math:`A_i` be a set.  A **relation on** :math:`\{A_i | i ∈ I\}` is a subset of the :term:`Cartesian product` :math:`∏_{i ∈ I}A_i`. 

.. index:: ! function, ! inverse, ! function composition, ! restriction, ! image

Functions
~~~~~~~~~~~

Let :math:`X` and :math:`Y` be sets.  A **function** (or **mapping**) **from** :math:`X` **to** :math:`Y` a is a relation :math:`F ⊆ X × Y` from :math:`X` to :math:`Y` such that for each :math:`a ∈ A` there is precisely one :math:`b ∈ B` such that :math:`a \mathrel{F} b`.

As above, we call :math:`A` the domain of :math:`F` and :math:`B` the codomain, denoted :math:`\dom F` and :math:`\cod F`, respectively.

The following operations are most commonly applied to functions, are sometimes applied to relations, but can actually be defined for arbitrary sets :math:`A`, :math:`F`, and :math:`G`.

#. The **inverse** of :math:`F` is denoted and defined by

    .. math:: F^{-1} = \{(u, v) ∣ v \ F \ u \} = \{(u, v) ∣ (v,u) ∈ F \}.

#. The **composition** of :math:`F` and :math:`G` is denoted and defined by

    .. math::

       F ∘ G = \{(u, v) ∣ ∃ t \ (u \ G \ t \ ∧ \ t \ F \ v)\} = \{(u, v) ∣ ∃ t \ ((u,t) ∈ G \ ∧ \ (t,v) ∈ F)\}.

#. The **restriction** of :math:`F` to :math:`A` is denoted and defined by

    .. math::

       F ↾ A = \{(u, v) ∣ u \ F \ v \ ∧ \ u ∈ A\} = \{(u, v) ∣ (u,v) ∈ F \ ∧ \ u ∈ A\}.

    We often denote this restriction by :math:`F|_A`.

#. The **image** of :math:`A` under :math:`F` is denoted and defined by

    .. math:: F[A] = \ran (F ↾ A) = \{v ∣ (∃ u ∈ A)\  (u,v) ∈ F\}.

    We can apply a subset axiom to establish the existence of this set. Specifically,

    .. math:: F^{-1} ⊆ \ran F × \dom F, \quad  F ∘ G ⊆ \dom G × \ran F, \quad F ↾ A ⊆ F, \quad F[A] ⊆ \ran F.

    (A more detailed justification of the definition of :math:`F^{-1}` would go as follows: By a subset axiom there is a set :math:`B` such that for every :math:`x`,

    .. math:: x ∈ B \quad ⟺ \quad  x ∈ \ran F × \dom F \ ∧ \ ∃ u \ ∃ v \ (x = (u, v) \ ∧ \ (v, u) ∈ F).

    It then follows that

    .. math:: x ∈ B \quad ⟺ \quad ∃ u \ ∃ v \ (x = (u, v) \ ∧ \ (v, u) ∈ F).

    We denote this unique set :math:`B` by :math:`F^{-1}`.)

.. _overloading-confusion:

.. proof:example::

   Let :math:`F = \{ (∅, a), (\{∅\}, b) \}`. Observe that :math:`F` is a function and :math:`F^{-1} = \{ (a, ∅), (b, \{∅\}) \}`. Thus, :math:`F^{-1}` is a function iff :math:`a ≠ b`.

   The restriction of :math:`F` to :math:`∅` is :math:`∅`, but :math:`F ↾ \{∅\} = \{(0, a)\}`.

   Consequently, :math:`F[\{∅\}] = \{a\}`, in contrast to the fact that :math:`F(\{∅\}) = b`.

Arrow notation
~~~~~~~~~~~~~~

Above we emphasized that a function is a special type of relation, but it is sometimes simpler to view functions as mappings that take input values and produce output values.

To emphasize this view, the "arrow" (or "input-output") notation, :math:`F: X → Y`, is used to denote that :math:`F` is a function "from" :math:`X` "to" :math:`Y`; that is, :math:`F` is a relation, :math:`\dom F = X`, :math:`\cod F = Y`, and each :math:`x∈ X` is associated by :math:`F` with exactly one :math:`y∈ Y`.

Another simplification is the notation :math:`F(x) = y`, which is used to denote not only the fact that the pair :math:`(x, y)` belongs to the relation :math:`F`, but also the fact that :math:`F` is indeed a function.

Recall, when :math:`A` is a subset of :math:`\dom F`, we defined the image of :math:`A` under :math:`F` to be the set :math:`F(A) = \{v ∣ (∃ u ∈ A)\  (u,v) ∈ F\}`. With the "arrow" notation, this simplifies, as follows:

.. math:: F(A) :=\{ F(a) ∣ a ∈ A\}.
   :label: setmap

The abuse of notation here causes confusion only in rare cases. (:numref:`Example %s <overloading-confusion>` above is one such case.) Nonetheless, some authors prefer to denote the image of :math:`A` under :math:`F` by :math:`F[A]` (as we did in the last section) instead of :math:`F(A)` to avoid this problem. [2]_

If :math:`B` is a subset of :math:`\cod F`, then the inverse image of :math:`B` under :math:`F` is, in the "input-output" notation, :math:`F^{-1}(B) := \{ x ∈ \dom F: F\, x ∈ B \}`.

Sometimes we refer to the **image of** :math:`F` without mentioning a subset, in which case we mean the image of :math:`\dom F` under :math:`F`, which we denote by :math:`\im F`.

.. proof:theorem::

   Assume that :math:`F: A → B`, and that :math:`A` is nonempty.

   #. There exists a function :math:`G: B → A` (a “left inverse”) such that :math:`G ∘ F` is the identity function :math:`\id_A` on :math:`A` iff :math:`F` is one-to-one.

   #. There exists a function :math:`H: B → A` (a “right inverse”) such that :math:`F ∘ H` is the identity function :math:`\id_B` on :math:`B` iff :math:`F` maps :math:`A` *onto* :math:`B`.

.. _axiom-of-choice-1:

.. proof:axiom:: Axiom of Choice 1

   For any relation :math:`R` there is a function :math:`H ⊆ R` with :math:`\dom H = \dom R`.

With this axiom we can prove the sufficiency direction of item 2 of the theorem above: take :math:`H` to be a function with :math:`H ⊆ F^{-1}` and :math:`\dom H = \dom F^{-1} = B`. Then :math:`H` does what we want: Given any :math:`y ∈ B`, we have :math:`(y,H(y)) ∈ F^{-1}` hence :math:`(H(y), y) ∈ F`, and so :math:`F(H(y)) = y`.

.. index:: ! join, ! upper bound, ! least upper bound, ! supremum
.. index:: ! meet, ! lower bound, ! greatest lower bound, !infimum

.. _join-and-meet-operations:

Join and meet operations
~~~~~~~~~~~~~~~~~~~~~~~~~~

A **join** of :math:`A` (when it exists) is a least element in the set of all upper bounds of :math:`A` in :math:`X`. A join of :math:`A` is sometimes called the **least upper bound** or **supremum** of :math:`A`.

Dually, a **meet** of :math:`A` (when it exists) is a greatest element in the set of all lower bounds of :math:`A` in :math:`X`. A meet of :math:`A` is sometimes
called a **greatest lower bound** or **infimum**.

Let :math:`⟨ X, ≤ ⟩` be a preordered set, let :math:`A, B, C ⊆ X`, and let :math:`x ∈ X`. If :math:`a ≤ x` for all :math:`a ∈ A`, then we write :math:`A ≤ x` and we say that :math:`x` is an **upper bound** for :math:`A` in :math:`X` (**lower bound** is defined dually).

A **join** of :math:`A` (when it exists) is a least element in the set of all upper bounds of :math:`A` in :math:`X`. A join of :math:`A` is sometimes called a **least upper bound** or **supremum** of :math:`A`.

Dually, a **meet** of :math:`A` (when it exists) is a greatest element in the set of all lower bounds of :math:`A` in :math:`X`. A meet of :math:`A` is sometimes
called a **greatest lower bound** or **infimum** of :math:`A`.

It is easy to see that joins and meets of preordered sets are determined uniquely up to equivalence. Indeed, if :math:`a` and :math:`a'` are two least upper bounds of :math:`A`, then we clearly have :math:`a ≤ a'` and :math:`a' ≤ a`; therefore, :math:`a ≅ a'`.

If a subset :math:`A` has at least one join, then we will let :math:`⋁ A` denote a choice of one of the joins of :math:`A`. Similarly, if :math:`A` has at least one meet, then we let :math:`⋀ A` denote a choice of one of the meets of :math:`A`.

To specify the preorder :math:`X` with respect to which the join or meet is taken, we write :math:`⋁^X A` and :math:`⋀^X A`, respectively.

Note that for every :math:`x ∈ X` we have :math:`⋁^X A ≤ x` iff :math:`A ≤ x`. Dually, :math:`x ≤ ⋀^X A` iff :math:`x ≤ A`.

Considering the empty subset :math:`∅ ⊆ X`, and in light of the fact that for every :math:`x ∈ X` the implication :math:`a ∈ ∅ ⟶ a ≤ x` holds, *ex falso quodlibet*, we see that the join of :math:`∅`, if it exists, must satisfy :math:`⋁ ∅ ≤ x` for all :math:`x ∈ X`. Therefore, :math:`⋁ ∅` is the “bottom” of any preorder in which it exists; we use the symbol ⊥ to denote :math:`⋁ ∅` when it exists.

Dually, :math:`a ∈ ∅ ⟶ x ≤ a` also holds, *ex falso quodlibet*, so for all :math:`x ∈ X` we have :math:`⋀ ∅ ≤ x`, so :math:`⋀ ∅` is the “top” of any preorder
in which it exists; we use the symbol ⊤ to denote :math:`⋀ ∅` when it exists.

.. index:: ! chain, ! antichain, ! ω-chain

Let :math:`⟨ X, ≤ ⟩` be a preordered set and :math:`C ⊆ X`. We call :math:`C` a **chain** of :math:`⟨ X, ≤ ⟩` if for all :math:`x, y ∈ C` either :math:`x ≤ y` or :math:`y ≤ x` holds. If, in addition, the elements of :math:`C` can be indexed by the natural numbers, then we call :math:`C` an ω-**chain**.

A subset :math:`A` of the preordered set :math:`X` is called an **antichain** if for all :math:`x, y ∈ A` we have :math:`x ≤ y` implies :math:`y ≤ x`.

.. index:: ! directed set, ! inductive set

.. _directed-and-inductive-sets:

Directed and inductive sets
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A subset :math:`D` of a preorder is called a **directed set** if every finite subset of :math:`D` has an upper bound in :math:`D`.

That is, if :math:`F ⊆ D` and :math:`F` is finite, then there exists :math:`d ∈ D` such that :math:`f ≤ d` for all :math:`f ∈ F`.

A subset :math:`I` of a preorder :math:`X` is called an **inductive set** if :math:`⋁_X D ∈ I` for every directed subset :math:`D ⊆ X` contained in :math:`I`. That is, if :math:`D ⊆ I`, and if every finite subset of :math:`D` has an upper bound in :math:`D`, then :math:`D` as a least upper bound in :math:`I`.

.. proof:example:: 

   These examples are borrowed from :cite:`Crole:1993` (Remark 1.2.10).

   Let :math:`X = \{0, 1, 2, \dots, n, n+1, \dots, ∞, ⊤\}` be the chain with order relation satisfying :math:`0≤ 1≤ 2≤ \cdots ≤ n ≤ n+1 ≤ \cdots ≤ ∞ ≤ ⊤`.

   Let :math:`A = X - \{∞\}` and :math:`D = X -\{∞, ⊤\}`. (See Figure [fig:noninductive].)

   Then :math:`⋁_A D` exists and is equal to :math:`⊤`, since the join is taken in :math:`A`.

   However, :math:`⋁_X D = ∞ ∉ A`, so :math:`A` is not an inductive subset of :math:`X`.

.. todo:: insert figure

.. index:: ! models (v)
.. index:: ! complete, ! cocomplete
.. index:: ! directed-cocomplete preorder, ! directed-cocomplete partial order (dcpo)
.. index:: ! ω-chain cocomplete, ! ω-chain cocomplete partial order (ω-cpo)

.. _completeness-and-cocompleteness:

Completeness and cocompleteness
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The existence of meets and joins for certain kinds of subsets of a preorder is known as completeness and cocompleteness respectively.

Suppose :math:`X` is a preorder and let :math:`P` be a **property of subsets** of :math:`X`.

Given a subset :math:`A ⊆ X`, denote by :math:`A ⊨ P` the judgement ":math:`A` has property :math:`P`."  (Type ``\vDash`` to produce ⊨.)  We sometimes say :math:`A` **models** :math:`P` in this case.

If the meet :math:`⋀ A` exists for every subset :math:`A ⊆ X` for which :math:` A ⊨ P` holds, then we say that :math:`X` is :math:`P`-**complete**.

Dually, :math:`X` is called :math:`P`-**cocomplete** if the join :math:`⋁ A` exists for every subset :math:`A` with property :math:`P`.

Suppose :math:`X` is a preorder for which joins of all directed subsets exist. Then :math:`X` is called a **directed-cocomplete preorder**. If, in addition, :math:`X` happens to be a poset, then :math:`X` is a **directed-cocomplete partial order** or **dcpo**.

If :math:`X` has joins of all ω-chains, then :math:`X` is said to be ω-**chain cocomplete**.

We will refer to an ω-**chain cocomplete partial order** as a ω-cpo.

Finally, if all meets in :math:`X` exist, then we say :math:`X` is **complete**, and if all joins exist, then :math:`X` is called **cocomplete**.

It is easy to see that a preorder is complete if and only if it is cocomplete. Indeed, this follows from the next pair of equations, which are direct consequences of the defintions of ⋀ and ⋁:

.. math:: ⋀ A = ⋁ \{x ∈ X : x ≤ A\} \qquad ⋁ A = ⋀ \{x ∈ X : A ≤ x\}.

A homomorphism of dcpos :math:`X` and :math:`Y` is a function :math:`f: X → Y` that preserves the structure of :math:`X`, which is to say :math:`f` is monotone and if :math:`D ⊆ X` is directed, then :math:`f (⋁ D) =⋁ f(D)`. (The join on the right hand side exists since :math:`f` is monotone.)

A homomorphism of ω-cpos is defined analogously. A homomorphism of :term:`dcpos <dcpo>` (ω-cpos) will also be referred to as a **continuous** (ω-**continuous**) function.

.. If :math:`X` and :math:`Y` have least elements, both denoted by ⊥, then a function :math:`f: X → Y` is said to be **strict** if :math:`f(⊥) = ⊥`.

If :math:`X` is a :term:`dcpo` then the subset :math:`A ⊆ X` is a **subdcpo** of :math:`X` if every directed subset :math:`D ⊆ A` satisfies :math:`⋁_X D ∈ A`.
   
Thus if :math:`A` is a :term:`subdcpo` of :math:`X` and :math:`A` is given the restriction order from :math:`X`, then the inclusion :math:`ι : A → X` is a continuous function.

Note also that if :math:`A ⊆ X` are :term:`dcpos <dcpo>` and if :math:`ι : A → X` is continuous, then :math:`A` is a :term:`subdcpo` of :math:`X`.

If :math:`X` is a poset, :math:`D` a :term:`directed <directed set>` subset of :math:`X`, and if the join of :math:`D` in :math:`X` exists, then we denote the join of :math:`D` by :math:`⨆_X D` rather than :math:`⋁_X D`. Part of the force of the judgement :math:`⨆_X D` is that the set :math:`D` is directed.


.. index:: ! closure operator, ! closure system, ! retraction

Closure systems and operators
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let 𝔛 be a set and let :math:`𝒫(𝔛)` denote the collection of all subsets of 𝔛.

A **closure operator** on 𝔛 is a set function :math:`𝖢 : 𝒫 (𝔛) → 𝒫 {𝔛}` satisfying the following conditions, for all :math:`X, Y ∈ 𝒫 (𝔛)`, 

#. :math:`X ⊆ 𝖢 (X)`,

#. :math:`𝖢 𝖢 = 𝖢`,

#. :math:`Y ⊆ X ⟹ 𝖢 (Y) ⊆ 𝖢 (X)`.

If 𝒜 is a collection of algebras of the same type, let :math:`𝖲 𝒜` and :math:`𝖱 𝒜` denote, respectively, the collection of all :term:`subalgebras <subalgebra>` and :term:`retracts <retract>` of algebras in 𝒜.

Observe that :math:`𝖲` is a closure operator on sets of algebras of the same type.

It's easy to see that if the retraction is as defined above, then retraction operator :math:`𝖱` is not a closure operator on sets of algebras of the same type.

However, if we take our definition of **retraction** of :math:`𝔸 = ⟨ A, F ⟩` via :math:`p ∈ \mathrm{Pol}_1(𝔸)` to be

.. math:: p(𝔸) = ⟨ p(A), \{p f|_{p(A)} : f \in F\}⟩,

then :math:`𝖱` is a closure operator.

.. index:: ! tensor product

.. _tensor-product:

Tensor product
~~~~~~~~~~~~~~~~~~

If :math:`𝔹 = ⟨B, ⟩` and :math:`ℂ = ⟨C, ⟩` are :term:`modules <module>` over a :term:`ring` :math:`R`, and :math:`𝔸 = ⟨ A, 0, -\, , +⟩` is an :term:`abelian group`, then a **middle linear** map from :math:`B × C` to :math:`A` is a function :math:`f: B × C → A` such that for all :math:`b, b_1, b_2 ∈ B`, :math:`c, c_1, c_2 ∈ C`, and :math:`r ∈ R`,

      .. math:: f(b_1 + b_2, c) &= f(b_1,c) + f(b_2,c)\\
                f(b, c_1 + c_2) &= f(b,c_1) + f(b,c_2)\\
                       f(br, c) &= f(b,rc).

For fixed :math:`𝔹` and :math:`ℂ` consider the category :math:`ℳ(B,C)` whose objects are all middle linear maps on :math:`B × C`. By definition, a morphism in :math:`ℳ(B,C)` from the middle linear map
:math:`f: B × C → A`  to the middle linear map :math:`g: B × C  → A'` is a group homomorphism :math:`h: A → A'` such that the diagram

.. tikz:: [node distance=2.75cm,semithick,->]
    \node (BxC) {\(B \times C\)};
    \node (A1) [above left of=BxC] {\(A\)};
    \node (A2) [above right of=BxC] {\(A'\)};
    \path (BxC) edge node [fill=white] {\(f\)} (A1);
    \path (BxC) edge node [fill=white] {\(g\)} (A2);
    \path (A1) edge node [fill=white] {\(h\)} (A2);

is commutative.

.. proof:exercise::

   Verify that :math:`ℳ(B,C)` is a category, that :math:`\mathbf 1_A`is is the identity morphism from :math:`f` to :math:`f` and that :math:`h` is an equivalence in :math:`ℳ(B,C)` if and only if :math:`h` is an isomorphism of groups.
   
In the next theorem we shall construct a universal object in the category :math:`ℳ(B,C)`.

First, however, we need to define the *tensor product* of modules precisely.

Let

  * :math:`𝔹` be a :term:`right module` and :math:`ℂ` a :term:`left module` over a :term:`ring` :math:`R`,
  * :math:`𝔽` be the free :term:`abelian group` on the set :math:`B × C`, and 
  * :math:`𝕂` be the subgroup of :math:`𝔽` generated by all elements of the following forms: for all :math:`b,b'∈ B`, :math:`c, c'∈ C`, and :math:`r ∈ R`,

    #. :math:`(b + b',c) - (b,c) - (b',c)`;
    #. :math:`(b,c + c') - (b,c) - (b,c')`;
    #. :math:`(br,c) - (b,rc)`.

The quotient group :math:`𝔽/𝕂` is called the **tensor product** of :math:`𝔹` and :math:`ℂ`; it is denoted :math:`𝔹 ⊗_R ℂ` (or simply :math:`𝔹 ⊗ ℂ` if :math:`R = ℤ`).

The coset :math:`(b,c) + K`  of the element :math:`(b,c)` in :math:`F` is denoted :math:`b ⊗ c`; the coset of :math:`(0,0)` is denoted :math:`0`.


.. _thm-5.2:

.. proof:theorem::

   Let :math:`𝔹` and :math:`ℂ` be modules over a ring :math:`R`, and let :math:`𝔸` be an abelian group.

   If :math:`g: B × C → A` is a :term:`middle linear map`, then there exists a unique group homomorphism :math:`̄g: 𝔹 ⊗_R ℂ → 𝔸` such that :math:`ḡ \, i = g`, where :math:`i: B × C→ 𝔹 ⊗_R ℂ` is the canonical middle linear map; :math:`𝔹 ⊗_R ℂ` is uniquely determined up to isomorphism by this property. In other words :math:`i: B × C → 𝔹 ⊗_R ℂ` is universal in the category :math:`ℳ(B,C)` of all middle linear maps on :math:`B × C`.


.. SKETCH OF PROOF. Let F be the free abelian group on the set AXB, and
.. let K be the subgroup described in Definition 5.1. Since F is free, the assignment
.. {a,b) H^ g(a,b) s C determines a unique homomorphism gi : F-^ C by Theorem 2.1
.. (iv). Use the fact that g is middle linear to show that gi maps every generator of K to
.. 0. Hence K C Ker gi. By Theorem 1.7 gi induces a homomorphism g : F/K-^ C
.. such that gl(a,b) -j- K] = gi[(a,b)] = g{a,b). But F/K = A0rB and (a,b) + K
.. = a (^ b. Therefore, g : A (^r B -^ C is a homomorphism such that gi{a,b)
.. = g(a (S)b) = g(a,b) for all (a,b) e A X B; that is, gi = g.U h : A 0rB-^ Cis any
.. homomorphism with hi = g, then for any generator a0 b of A 0rB,
.. Ilia (S)b) = hiia^b) = g{a,b) = gi{a,b) = g(a (x) b).
.. Since // and g are homomorphisms that agree on the generators of A (^r B, we must
.. have h = g, whence g is unique. This proves that i : A X B -^ A (^r B is a. universal
.. object in the category of all middle linear maps on A X B, whence A 0r B is
.. uniquely determined up to isomorphism (equivalence) by Theorem 1.7.10. ■

---------------------------------

.. _type-theory:

Type theory
-----------

This section highlights some of the rudiments of type theory with which we expect our dear reader is familiar.

Here is a slogan that may be helpful to those who know about sets but have no prior exposure to type theory.

  *In set theory virtually everything* **is** *a set*.
  
  *In type theory, virtually everything* **has** *a type*.


.. index:: pair: implication elimination; modus ponens

.. _curry-howard:

Curry-Howard correspondence
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The rule for :term:`function application <eval>` corresponds, under the :term:`Curry-Howard <Curry-Howard correspondence>` (or :term:`propositions-as-types`/:term:`proofs-as-programs`) :term:`correspondence <Curry-Howard correspondence>`, to the :term:`implication elimination` rule of natural deduction (sometimes called :term:`modus ponens`). This simply codifies our intuitive notion of function application, viz., applying the function :math:`f: A → B` to an element :math:`a` of :math:`A` yields a member :math:`f\,a` of the codomain :math:`B`.

If we interpret the types :math:`A` and :math:`B` as propositions and the function :math:`f: A → B` as a proof of the proposition ":math:`A` implies :math:`B`," and if we view :math:`a` as a proof of :math:`A`, then the application rule is the so called :term:`implication elimination` rule (or, :term:`modus ponens`); that is, "if :math:`A` and :math:`A → B`, then :math:`B`."

.. index:: type of; dependent functions
.. index:: type of; dependent pairs
.. index:: type of; lists
.. index:: type of; vectors

.. _dependent-types:

Dependent types
~~~~~~~~~~~~~~~~~~~~

.. Lean_ is a :term:`functional programming` language and interactive theorem prover that supports :term:`dependent types <dependent type>`.

In this section we show how :term:`dependent types <dependent type>` can be used to represent many concepts that are important in universal algebra, in a way that is precise, elegant, and intrinsically computational. [3]_ 

Before trying to understand why dependent types are useful, it helps to know what dependent types are. So we begin by explaining what makes a type dependent.

Types can depend on *parameters*.  For example, if ``α`` is a type, then ``list α`` is the type of lists whose entries have type ``α``.  The type ``list α``  depends on the parameter ``α``. The type of vectors of length ``n`` with entries from ``α`` is sometimes denoted by ``vec α n``. This type depends on the parameter ``α`` (the type of the elements that populate the vectors) and the *value* ``n`` of type ``ℕ`` (denoting the length of the vectors).

The type ``list α`` is an example of a :term:`polymorphic type`, which is not what we mean by a "dependent type."  Of course ``list α`` does depends on the argument ``α``, and this dependence distinguishes, say, ``list ℕ`` from ``list bool``.  But the argument ``α`` is not a particular *value* (or *inhabitant*) of a type, but rather a type parameter, and we call this kind of dependence **polymorphism**.

Contrast this with the type ``vec α n``, which depends on the parameter ``α`` as well as the *value* of the variable ``n``. The dependence of the type ``vec α n`` on the value ``n`` is the sort of dependence for which we reserve the label "dependent type."

This example is somewhat misleading. It is not true that the only dependent types are those that depend on a concrete value of a type, e.g., ``n`` in the last example. In fact, types themselves inhabit other types.  Indeed, in type theory, *everything* (even types) inhabits a type.

For example, if ``α: Type``, then ``α`` is both a type in its own right and an inhabitant of the ``Type`` type (which is Lean syntax for the "ground type", or ``Sort 1``). [2]_

Consider the ``cons`` function that inserts a new element at the head of a list. What type should ``cons`` have?  Before answering, let us consider a few facts.

* For each type ``α``, ``cons α`` is the insertion function for lists of type ``list α``; it takes an element ``a:α`` and a list ``l:list α``, and returns a new list---the concatenation of ``a`` with the list ``l`` (sometimes denoted ``a::l``).

* ``cons`` is polymorphic and should behave in roughly the same way for lists with entries of type ℕ, or ``bool``, or an arbitrary type ``α``. 

* ``cons α`` has type ``α → list α → list α``.

But what about ``cons`` itself?  We might try ``cons: Type → α → list α → list α``, but this somehow choses a specific inhabitant of ``Type``---namely, ``α``---in advance, which we don't want.

Instead, since ``cons`` should be polymorphic, the caller of ``cons`` is free to choose some (any) type ``α:Type`` as the first argument; then (and only then) do we know the types, ``α`` and ``list α``, of the second and third arguments to ``cons``.

.. index:: ! Pi type
.. index:: type of; dependent functions

.. _pi-types:

Pi types
~~~~~~~~~

What we need in the situation just described is known as a :term:`Pi type`, or :term:`dependent function type <Pi type>`.  In the ``cons`` example, the correct typing judgement is

  ``cons: Π(a:Type), (α → list α → list α).``
  
Before explaining this notation and the type that it represents, let us first describe Pi types more generally.

If ``α`` is a type, we write ``α:Type``.  Then a function ``β`` of type ``α → Type`` represents a family of types, one type ``β x`` for each member ``x`` of the type ``α``.  The product of all these types is denoted by

  ``Π(a:α), β a``, 
  
which is itself a type, and is called a **dependent function type**.  This name arises because, for each inhabitant ``f: Π(a:α), β a``, we see that the type of the image ``f a`` of each ``a:α`` may depend on ``a``.  Precisely, ``f a: β a`` for each ``a:α``.

Suppose for all ``a:α`` the type ``β a`` does *not* depend on ``a``. Then ``Π(a:α), β a`` is equivalent to the (nondependent) function type ``α → β``.  Whence we see that ``α → β`` is a special case of the type ``Π(a:α), β a``. Indeed, in dependent type theory (and in Lean) Pi types may be viewed as fundamental and function types as a special case.

To summarize, for each type ``α:Type`` and for every family of types ``β: α → Type``, we have the :term:`Pi type`, ``Π(a:α), β a`` which generalizes the function type ``α → β`` by allowing each section ``β a`` of the codomain to depend on a value ``a:α`` of the domain.

.. index:: type of; booleans
.. index:: Cartesian product

.. proof:example:: Cartesian product

   The simplest example of a Pi type is the **Cartesian product** :math:`B₀ × B₁` which is the set of all functions of the form :math:`f: \{0, 1\} → B₀ ∪ B₁` such that :math:`f \, 0 ∈ B₀` and :math:`f\, 1 ∈ B₁`.

   Suppose ``B₀:Type`` and ``B₁:Type`` are types and let ``bool`` denote the **Boolean type** inhabited by just ``0`` and ``1``.
   
   Let ``B: bool → Type`` be the function defined by ``B 0 = B₀`` and ``B 1 = B₁``.
   
   Then we represent the Cartesian product :math:`B_0 × B_1` by the type ``Π(i:bool), B i``. [4]_

.. index:: ! Sigma type

.. index:: type of; dependent pairs

.. _sigma-types:

Sigma types
~~~~~~~~~~~

Similarly, a :term:`Sigma type`, also known as the `dependent pair type <sigma-type>`_, generalizes the Cartesian product ``α × β`` by allowing the *type* of the second argument of an ordered pair to depend on the *value* of the first.

Sigma types arise from a type ``α:Type`` and a "type former" ``β: α → Type``, and are denoted using the ``Σ`` symbol, as follows:

  ``Σ(a:α), β a``. 

This type is inhabited by the "dependent pairs" ``(x,y)``, where ``x`` has type ``α`` and ``y`` has type ``β x``.

.. index:: ! disjoint union

.. proof:example:: Disjoint union in general

   The simplest example of a Sigma type is the disjoint union of two types, say, ``X:Type`` and ``Y:Type``. This is comprised of all pairs of the form ``(0,x)`` for ``x:X`` and ``(1,y)`` for ``y:Y``, and is sometimes denoted by ``X ∐ Y``.
   
   Note that the value of the first coordinate of such pairs indicates the type to which the second coordinate belongs.
   
   Expressing ``X ∐ Y`` in the ``Σ`` notation, we have ``α = bool`` and ``β: bool → X ∪ Y`` where ``β 0: X`` and ``β 1: Y``. Thus,
   
     ``X ∐ Y = Σ(a:bool), β a``.

.. proof:example:: Disjoint union example

   Suppose ``X =  {a, b}`` and ``Y = {a, b, c}``. Then, 

     ``X ∐ Y = {(0,a), (0,b), (1,a), (1,b), (1,c)}``.

   If ``(i,a): X ∐ Y``, then the second coordinate is the ``a`` of type ``A`` if ``i = 0``, while ``a:B`` if ``i = 1``.
   
   Some authors prefer to use an "injection" function, say, ``ι``, to indicate the set from which an element originated; in the present example,

     ``X ∐ Y = {ι0 a, ι0 b, ι1 a, ι1 b, ι1 c}``.

   (For ι type ``\iota``; some authors write ``inl`` ("in left") and ``inr`` ("in right") for ``ι0`` and ``ι1``.)


.. index:: partial application

.. _partial-application:

Partial application
~~~~~~~~~~~~~~~~~~~~

Let :math:`I` be a nonempty set and :math:`\{A_i | i: I\}` a family of sets.

Elements of the product :math:`∏_{i∈ I} A_i` are functions :math:`a: I → ⋃_{i:I} A_{i}` such that for each :math:`i` we have :math:`a\,i: A_i`.

Let :math:`J ⊆ I` and let :math:`g: J → I` be one-to-one. Then, as above, :math:`a ∘ g: ∏_{j: J} A_{g(j)}` gives the projection of :math:`a` onto certain coordinates of the full product, namely, the coordinates :math:`\im g = \{g\, j ∣ j:J\}`.

Suppose :math:`f` is a self-map of the set :math:`A := ∏_{i: I} A_i`. That is, :math:`f: A → A`. If :math:`I = \{0, 1, \dots, n-1\}`, then :math:`A = ∏_{i=0}^{n-1} A_i` and the (curried) type of :math:`f` is

.. math:: f: A_0 → (A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

For a given :math:`a_0: A_0`, the function :math:`f` partially applied at the first coordinate has type

.. math:: f\, a_0: A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

For elements :math:`a_0` and :math:`a_1` inhabiting types :math:`A_0` and :math:`A_1` (resp.), the partial application of :math:`f` to these elements yields the following function and typing judgment:

.. math:: f a_0 a_1: A_2 → (A_3 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1}))\cdots ).

In general, for :math:`a_i: A_i`, :math:`0 ≤ i < ℓ`,

.. math:: f a_0 a_1 \dots a_{ℓ-1}: A_ℓ → (A_{ℓ+1} → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

.. Asynchronous currying
.. ~~~~~~~~~~~~~~~~~~~~~

.. It would be useful to have a means of partial function application in case the domain :math:`I` is not simply :math:`\{0, 1, \dots, n-1\}`, or in case we wish to partially apply a function to an arbitrary subset of its operands (coordinates of its domain).

.. Suppose, as above,

.. * :math:`𝔸 = ∏_{i:I} A_i`,

.. * :math:`g: J → I` (one-to-one),

.. * :math:`a ∘ g: ∏_{j:J} A_{g(j)}`, for each :math:`a : ∏_{i:I} A_i`.

.. Let :math:`f` have type :math:`∏_{i:I} A_i → ∏_{i:I} A_i`, which means that if we apply :math:`f` to an element :math:`a : ∏_{i:I} A_i` the result has the same type, that is, :math:`f a : ∏_{i:I} A_i`.

.. We may wish to apply :math:`f` to just a portion of :math:`a` but it may not be the case that :math:`I` is a subset of :math:`ℕ`, or an ordered enumeration of some other set, so there is no natural notion of “the first :math:`ℓ` operands.” Even if there was such a notion, we may wish to partially apply :math:`f` to something other than the first :math:`ℓ` operands. Therefore, we define a more general notion of partial application as follows: :math:`f` partially applied to the coordinates :math:`\im g = \{g(j) ∣ j: J\}` of the element :math:`a` gives the function : type judgment

.. .. math:: f ∘ (a ∘ g): ∏_{\substack{i: I\\ i ∉ \im g}} A_i → ∏_{i:I} A_i.

.. .. todo:: define/describe the asynchronous curry type


-----------------------------------------

.. rubric:: Footnotes

.. [1]
   It is this author's view that study of computing science heightens one's awareness and appreciation of notions of "equality", perhaps even more so than does the study of pure logic or mathematics.  (This calls to mind the fact that Eskimo's have a deep relationship with snow; see `There really are 50 Eskimo words for snow <https://www.washingtonpost.com/national/health-science/there-really-are-50-eskimo-words-for-snow/2013/01/14/e0e3f4e0-59a0-11e2-beee-6e38f5215402_story.html>`_.)

.. [2]
   At issue here is the apparent "overloadng" of the symbol :math:`F`, which is used (in the second instance in :eq:`setmap`) to denote the element :math:`F(a) ∈ Y` that is associated by :math:`F` with the element :math:`a ∈ A`, and also used (in the first instance)  the argument to :math:`F` is a set so, in the arrow notation, we really should have defined a (new) function :math:`F: 𝒫(X) → 𝒫(Y)`, whose domain and codomain are sets of sets. We could have avoided this overloading by either using square brackets, as in :math:`F[A]`, which is often done, but seems somewhat *ad hoc*.  A better solution is to make explicit use of the :term:`powerset functor`, but we postpone the proper handling of this technicality until our transition to "postmodern" algebra in :numref:`Chapter %s <postmodern-algebra>`.
 
.. [3]
   What we mean by "intrinsically computational" ought to become clearer as we progress.

.. [4]
   It is more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1): b_i ∈ B_i, i = 0, 1\}`, but identifying tuples with functions results in a :term:`Pi type`.




.. include:: hyperlink_references.rst
