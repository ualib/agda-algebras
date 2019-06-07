.. include:: _static/math_macros.rst

.. _appendix-a:

=======================================
Appendix A. Mathematical Prerequisites
=======================================

Products of Sets
-----------------

The **Cartesian product** of two sets :math:`A_0` and :math:`A_1`, denoted :math:`A_0 × A_1`, is the set of all ordered pairs :math:`(a_0, a_1)` such that :math:`a_0 ∈ A_0` and :math:`a_1 ∈ A_1`. That is, :math:`A_0 × A_1 := \{(a_0, a_1) ∣ a_0 ∈ A_0, a_1 ∈ A_1\}`.

More generally, :math:`A_0 × \cdots × A_{n-1}` is the set of sequences of length :math:`n` with :math:`i`-th element in :math:`A_i`. That is,

.. math:: A_0 × \cdots × A_{n-1} := \{(a_0, \dots,  a_{n-1}) ∣ a_0 ∈ A_0, \dots, a_{n-1} ∈ A_{n-1}\}.

Another way to view :math:`A_0 × \cdots × A_{n-1}` is as the set of all functions with domain :math:`\{0, 1, \dots, n-1\}` and range :math:`⋃_{i<n} A_i`. More generally still, the **Cartesian product** of an indexed family of sets, :math:`\{A_i : i ∈ I\}`, is the set of all functions with domain :math:`I` and range :math:`⋃_{i ∈ I} A_i` such that :math:`f(i) ∈ A_i`. That is,

.. math:: ∏_{i∈I} A_i := \{f: I → ⋃_{i∈I} A_i | f(i) ∈ A_i\}.

When :math:`A_0 = A_1 = \cdots = A`, we write :math:`A^2 := A × A` and :math:`A^n := A × \cdots × A` (:math:`n` factors), and refer to these as **Cartesian powers** of
:math:`A`.

.. proof:question::

   How do you know :math:`∏_{i∈I} A_i ≠ ∅`, even supposing :math:`I ≠ ∅` and :math:`A_i ≠ ∅` for all :math:`i ∈ I`? [1]_

.. index:: ! relation, ! binary relation, ! preorder, ! partial order, ! equivalence relation
.. index:: ! domain, ! range

.. _binary-relations:

Binary Relations
----------------

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

.. proof:examples::

   The `reachability relation <http://en.wikipedia.org/wiki/Reachability>`_ of a `directed graph <http://en.wikipedia.org/wiki/Directed_graph>`_ (possibly containing cycles) gives rise to a preorder :math:`R`, where :math:`x \mathrel{R} y` if and only if the directed graph has a path from :math:`x` to :math:`y`.

   Conversely, every preorder :math:`R` on a set :math:`X` is the reachability relation of a directed graph (simply take elements of :math:`X` to be the vertices and draw an edge from :math:`x` to :math:`y` whenever :math:`x \mathrel{R} y`).

The significance of preorders stems mainly from the fact that the two most important classes of binary relations happen to be preorders. These are *partial orders* and *equivalence relations*.

.. index:: ! equivalence relation, ! partial ordering
.. index:: pair: partially ordered set; poset

Equivalence relations and partial orders
-----------------------------------------

An **equivalence relation** is a symmetric preorder. We denote the set of all equivalence relations on a set :math:`X` by :math:`\mathrm{Eq}(X)`.

A **partial ordering** (or "partial order") is an anti-symmetric preorder.  A **partially ordered set** (or "poset") :math:`⟨X, R⟩` is a set :math:`X` along with a partial order :math:`R` defined on :math:`X`.

.. proof:examples::

   #. If :math:`X = ℤ` and :math:`R` is the usual :math:`≤` relation, then :math:`R` is a partial order on :math:`X`. (In fact, :math:`≤` is a :term:`total order` on :math:`ℤ` in this case.)

   #. Let :math:`X` be any set and let :math:`\mathcal{P}(X)` be the collection of all subsets of :math:`X`. The subset relation :math:`y ⊆ z` (":math:`y` is a subset of :math:`z`") is a partial order on :math:`\mathcal{P}(X)`.

   #. Let :math:`X = ℝ^2` and :math:`R =` ":math:`≤` on each component"; i.e., :math:`R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a_1 ≤ b_1, \, a_2 ≤ b_2 \}`. Then :math:`R` is a partial order on :math:`X`.

   #. If :math:`A = ℝ^2` then :math:`R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a = (a_1, a_2), \; b = (b_1, b_2), \; a_1^2+ a_2^2 = b_1^2+ b_2^2 \}` is an equivalence relation on :math:`A`. The equivalence classes are circles centered at :math:`(0,0)`.

A **partition** of the set :math:`A` is a collection :math:`P = \{A_i : i ∈ I\}` of non-empty subsets of :math:`A` such that

.. math:: ⋃_{i ∈ I} A_i = A \quad \text{ and } \quad  A_i ∩ A_j = ∅  \quad ∀ i ≠ j.

The :math:`A_i` are called the “blocks” of the partition.

Every partition :math:`P` determines an equivalence relation---namely, the relation :math:`R` defined by :math:`a\mathrel{R} b` if and only if :math:`a` and :math:`b` are in the same block of :math:`P`.

Conversely, if :math:`R` is an equivalence relation on :math:`A`, we denote the equivalence class of :math:`R` containing :math:`a` by :math:`a/R := \{b ∈ A : a \mathrel{R} b\}` and the set :math:`A/θ := \{a/θ : a ∈ A\}` of all :math:`θ` classes is a partition of :math:`A`.

The poset induced by a preorder
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

With any preorder :math:`X` we can associate a poset in a natural way as we now explain.

Since a preorder is not antisymmetric in general, we may have distinct elements :math:`x, y ∈ X` with :math:`x ≤ y` and :math:`y ≤ x`.

In this case we define the binary relation :math:`≅` on :math:`X` by: :math:`x ≅ y` iff :math:`x ≤ y` and :math:`y ≤ x`.

The relation ≅ so defined is an equivalence relation on :math:`X` and if we simply equate all ≅-related pairs, then we obtain a poset, denoted by :math:`X/{≅}`.

.. index:: equivalence class

The elements of :math:`X/{≅}` are called *equivalence classes*. These classes partition the set :math:`X` into disjoint subsets, each subset consisting of elements that are pairwise equivalent.  Precisely, for each :math:`x ∈ X`, we denote and define the **equivalence class** containing the element :math:`x` by 

.. math:: x/{≅} \; = \{y ∈ X : x ≅ y\}.

(Some authors prefer the notation :math:`[x]` or :math:`[x]_≅` for the equivalence class containing :math:`x`.)

We denote the set :math:`\{x/{≅} \; : x ∈ X\}` of all (≅-)equivalence classes by :math:`X/{≅}`.

Let ⊑ denote the relation on :math:`X/{≅}` defined as follows: :math:`∀ x \ ∀ y \ (x/{≅} \ ⊑ y/{≅} \ ⟺ \ x ≤ y)`.

It is easy to see that ⊑ is a partial ordering on :math:`X/{≅}`. The poset :math:`⟨ X/{≅}, ≤ ⟩` is sometimes called the **poset reflection** of the preordered set :math:`⟨ X, ≤ ⟩`.

.. index:: ! join, ! upper bound, ! least upper bound, ! supremum
.. index:: ! meet, ! lower bound, ! greatest lower bound, !infimum

Joins and meets
~~~~~~~~~~~~~~~

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

---------------------------------

.. index:: ! function, ! inverse, ! function composition, ! restriction, ! image

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

Consequently, :math:`F[\{∅\}] = \{a\}`, in contrast to the fact that :math:`F(\{∅\}) = b`.

.. proof:theorem::

   Assume that :math:`F: A → B`, and that :math:`A` is nonempty.

   #. There exists a function :math:`G: B → A` (a “left inverse”) such that :math:`G ∘ F` is the identity function :math:`\id_{A}` on :math:`A` iff :math:`F` is one-to-one.

   #. There exists a function :math:`H: B → A` (a “right inverse”) such that :math:`F ∘ H` is the identity function :math:`\id_{B}` on :math:`B` iff :math:`F` maps :math:`A` *onto* :math:`B`.

.. _axiom-of-choice-1:

.. proof:axiom:: Axiom of Choice 1

   For any relation :math:`R` there is a function :math:`H ⊆ R` with :math:`\dom H = \dom R`.

With this axiom we can prove the sufficiency direction of item 2 of the theorem above: take :math:`H` to be a function with :math:`H ⊆ F^{-1}` and :math:`\dom H = \dom F^{-1} = B`. Then :math:`H` does what we want: Given any :math:`y ∈ B`, we have :math:`(y,H(y)) ∈ F^{-1}` hence :math:`(H(y), y) ∈ F`, and so :math:`F(H(y)) = y`.

---------------------------------

.. index:: ! ordered tuples, !tuples
.. index:: ! unary relation, ! binary relation, ! ternary relation

Relations of higher arity
-------------------------

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

---------------------------------

.. index:: ! projection, ! idempotent operation

.. _projections:

Projections
-----------


An operation :math:`f : A^n → A` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`.

Examples of idempotent operations are the projection functions and these play an important role, so we introduce a sufficiently general and flexible notation for them.

Denote and define the set ℕ of natural numbers in inductively, as usual,

.. math:: 0 = ∅, \quad 1 = \{0\}, \quad  2 := \{0, 1\}, \dots, n = \{0, 1, \dots, n-1\}.

Given sets :math:`A_0, A_1, \dots, A_{n-1}`, denote their Cartesian product by

.. math:: ∏_{i < n} A_i := A_0 × A_1 × \cdots × A_{n-1}.

An element :math:`a ∈ ∏_{i<n} A_i` is an ordered :math:`n`-tuple, which may be specified by simply listing its values, :math:`a = (a(0), a(1), \dots, a(n-1))`.

Thus, tuples are functions defined on a finite (“index”) set, and we often view them this way. This fact may be emphasized by writing

.. math:: a : n → ⋃_{i < n} A_i; \ \ i ↦ a(i) ∈ A_i.

If :math:`σ : k → n` is a :math:`k`-tuple of numbers in the set :math:`n = \{0, 1, \dots, n-1\}`, then we can compose an :math:`n`-tuple :math:`a ∈ ∏_{i<n} A_i` with :math:`σ` yielding :math:`a ∘ σ ∈ ∏_{i < k} A_{σ(i)}`.

The result is a :math:`k`-tuple whose :math:`i`-th component is :math:`(a ∘ σ)(i) = a(σ(i))`.

If :math:`σ` happens to be one-to-one, then we call the following a **projection function**:

.. math:: \Proj_σ : ∏_{i< n} A_i → ∏_{i<k} A_{σ(i)};  \ \ a ↦ a ∘ σ.
   :label: projection

That is, for :math:`a ∈ ∏_{i<n} A_i` we define :math:`\Proj_σ a = a ∘ σ`.

We often apply such projection functions to subsets :math:`R ⊆ ∏_{i<n} A_i`, in which case

.. math:: \Proj_σ R &= \{ r ∘ σ  | r ∈ R \}\\
                    &= \{ (r_{σ(0)}, r_{σ(1)}, \dots, r_{σ(k-1)}) | r ∈ R \}.

The following shorthand is frequently convenient:

.. index:: kernel

.. math:: R_σ := \Proj_σ R.

.. proof:example::

   To make clear why the term “projection” is reserved for the case when :math:`σ` is one-to-one, suppose :math:`k=4`, :math:`n=3`, and consider the 4-tuple :math:`σ = (1, 0, 1, 1)`. Then :math:`σ` is the function :math:`σ : \{0,1,2,3\} → \{0,1,2\}` given by :math:`σ(0) = 1`, :math:`σ(1) = 0`, :math:`σ(2) = 1`, :math:`σ(3) = 1`, and so :math:`a ↦ a ∘ σ` is the function that takes :math:`(a_0, a_1, a_2)∈ A_0 × A_1 × A_2` to :math:`(a_1, a_0, a_1, a_1) ∈ A_1 × A_0 × A_1 × A_1`.

Let :math:`A = ∏_{i<n} A_i`, let :math:`σ : k → n` be one-to-one, and define the projection :math:`\Proj_σ` as in :eq:`projection` above. Then the **kernel**
of :math:`\Proj_σ`, which we denote by :math:`\mathbf{0}_σ`, is defined as follows:

.. math:: \mathbf{0}_σ &= \ker \Proj_σ = \{(a,a') ∈ A^2 | \Proj_σ a = \Proj_σ a'\}\\
                       &= \{ (a,a') ∈ A^2 | a ∘ σ = a' ∘ g \} = \{ (a,a') ∈ A^2 | ∀ j ∈ \im σ, \ a(j) = a'(j) \}.
   :label: kernel

It is obvious that :math:`\mathbf{0}_σ` is an equivalence relation on the set :math:`A`.

More generally, if :math:`θ` is an equivalence relation on the set :math:`∏_{j<k} A_{σ(j)}`---that is, :math:`θ ⊆ (∏_{j<k} A_{σ(j)})^2` and :math:`θ` is reflexive, symmetric, and transitive---then we define the equivalence relation :math:`θ_σ` on the set :math:`A = ∏_{i<n} A_i` as follows:

.. math:: θ_σ = \{(a, a') ∈ A^2 ∣ (a ∘ σ) \mathrel{\theta} (a' ∘ σ)\}.
   :label: 17

In other words, :math:`θ_σ` consists of all pairs in :math:`A^2` that land in :math:`θ` when projected onto the coordinates in :math:`\im σ`.

#. Recall that :math:`\Proj_σ : A → ∏_{j<k} A_{σ(j)}` is the function that maps :math:`a` to :math:`a ∘ σ`.

   Now, suppose we have a tuple :math:`(a_0, a_1, \dots, a_{p-1})\in A^p`, and suppose we intend to apply :math:`\Proj_σ` to each component, :math:`a_j`.

   To do so, we need to lift :math:`\Proj_σ` from type :math:`A → ∏_{j<k} A_{σ(j)}` to type :math:`A^p → (∏_{j<k} A_{σ(j)})^p`, which is accomplished using a functor that often goes by the name :math:`map`.

   For instance, if :math:`(a, a') ∈ A^2`, then :math:`map(\Proj_σ)(a, a') = (\Proj_σ(a), \Proj_σ(a'))`.

   Therefore,

   .. math:: θ_σ =\{(a, a') ∈ A^2 ∣ map(\Proj_σ)(a, a') ∈ θ \},

   whence, :math:`θ_g = map(\Proj_σ)^{-1}θ`.

#. If :math:`f: X → A` and :math:`g: X → B` are functions defined  on the same domain :math:`X`, then :math:`(f,g): X → A × B` is the unique function that composes with the first projection to give :math:`f` and composes with the second projection to give :math:`g`. For example, in the last remark there appears the expression :math:`(\Proj_σ(a), \Proj_σ(a')) = (a ∘ σ, a' ∘ σ)`, which has type :math:`( ∏_{j<k} A_{σ(j)} )^2`.

    In retrospect, a more appropriate name for :math:`\mathbf{0}_σ` might be :math:`Δ_σ`, or even :math:`=_σ`.

#. If the domain of :math:`σ` is a singleton, :math:`k = \{0\}`, then of course :math:`σ` is just a one-element list, say, :math:`σ = (j)`. In such cases, we write :math:`\Proj_j` instead of :math:`\Proj_{(j)}`.  Similarly, we write and :math:`\mathbf{0}_j` and :math:`θ_j` instead of :math:`\mathbf{0}_{(j)}` and :math:`θ_{(j)}`. Thus, :math:`\Proj_j a = a(j)`, and :math:`\mathbf{0}_j = \{(a, a') ∈ A^2 ∣ a(j) = a'(j)\}`, and, if :math:`θ ∈ \Con 𝔸_j`, then :math:`θ_j = \{(a, a') ∈ A^2 ∣ a(j) \mathrel{\theta} a'(j)\}`.

Here are some obvious consequences of the foregoing notation and definitions that are worth noting.

.. math::

   ⋁_{j<n}\mathbf{0}_j = A^2, \qquad \mathbf{0}_σ = ⋀_{j ∈ σ} \mathbf{0}_j, \qquad \mathbf{0}_{n} = ⋀_{j<n}\mathbf{0}_j = 0_{A}, \qquad
   θ_σ = ⋀_{j<k} θ_{σ(j)},

where :math:`0_{A}` denotes the least equivalence relation on :math:`A`, that is, :math:`0_{A}:= \{(a, a') ∈ A^2 ∣ a = a'\}`.

.. As we alluded to above, :math:`η_σ` is shorthand for :math:`(0_A)_σ`.

-----------------------------------

.. index:: generalized projections, dependent types 

Generalized projections and dependent types
-------------------------------------------

Here we present a more general way of describing projections.

Let :math:`\{𝔸_i : i ∈ I\}` be a collection of algebras of the same signature (for some :math:`I ⊆ ℕ`) and let :math:`\underline{𝔸} = ∏_{i ∈ I} 𝔸_i`. (Actually, for now it suffices to think of the :math:`𝔸_i` and :math:`\underline{𝔸}` as sets since the algebraic structure won't play a role in this section.) View the elements of :math:`\underline{𝔸}` as functions:

.. math:: a ∈ ∏_{i∈I} 𝔸_i \quad ⟷ \quad \begin{cases} a : I → ⋃_{i∈I} A_i, & \\ a(i) ∈ A_i, & ∀ i ∈ I. \end{cases}
   :label: 7
   
This correspondence simply records the fact that the product type (on the left of the ⟷ symbol) represents a special kind of function type (depicted on the right of ⟷ using the usual → notation for function types). In other words, :eq:`7` says that an element of the product type :math:`∏_{i∈I} 𝔸_i` is a function from :math:`I` into :math:`⋃_{i∈I} A_i` whose codomain :math:`A_i` *depends* on the input argument :math:`i`. Such a function (or product) type is known as a :term:`dependent type`.

Now, given a subset :math:`J ⊆ I`, a function :math:`g : J → I`, and an element :math:`a ∈ ∏_{i∈I} A_i`, consider the composition :math:`a ∘ g`. This is a function from :math:`J` to :math:`⋃_{j∈J} A_{g(j)}`, where :math:`(a ∘ g)(j) ∈ A_{g(j)}`. Again, we could express this function type using the arrow notation, “:math:`a ∘ g : J → ⋃_{j∈J} A_{g(j)}` where :math:`(a ∘ g)(j) ∈ A_{g(j)}`,” but this specification has a nicer, more compact description using a :term:`dependent function type`.

.. math:: a ∘ g ∈ ∏_{j∈J} A_{g(j)}.

Assume :math:`g` is one-to-one and define the “projection” function,

.. math:: \Proj(g) : ∏_{i∈I} A_{i} → ∏_{j∈J} A_{g(j)}

by :math:`\Proj(g): a ↦ (a ∘ g)`. That is, :math:`\Proj(g)(a) = a ∘ g`.

We could try to specify the type of :math:`\Proj` using the arrow notation as follows:

.. math::    \Proj : (J → I) → \bigl( I → \bigcup_{i∈I} A_{i} \bigr) → \bigl(J → ⋃_{i∈I} A_{i}\bigr),
   :label: 8

but the deficiencies of the arrow notation are now even more glaring. The function type specification given in :eq:`8` is imprecise and arguably misleading. The result of applying :math:`\Proj` first to some :math:`g: J → I` and then :math:`a : I → ⋃_{i∈I} A_{i}` is :math:`\Proj (g) (a) = a ∘ g`, and to say that this is a function of type :math:`J → ⋃_{i∈I} A_{i}` is ambiguous at best.

Rather, the complete, correct type specification is actually “:math:`\Proj (g) (a) : J → ⋃_{j∈J} A_{g(j)}` where :math:`\Proj (g) (a) (j) ∈ A_{g(j)}`.”

Again, we can express this more concisely with a dependent function type, :math:`\Proj (g)(a) ∈ ∏_{j∈J} A_{g(j)}`. Thus, to denote the type of :math:`\Proj`, we must add to :eq:`8` the constraints on codomains that depend on argument values. For specifying the type of a “function of higher order” (a.k.a. a “functional”), the arrow notation can be cumbersome.

The following is closer to what we want, but still imperfect:

.. math:: \Proj: (J → I) → ∏_{i∈I} A_{i} → ∏_{j∈J} A_{g(j)}.
   :label: 9

This says that :math:`\Proj` takes a function :math:`g : J → I` and a function :math:`a ∈ ∏_{i∈I} A_i` and returns the function :math:`a ∘ g ∈ ∏_{j∈J} A_{g(j)}`.

Here again we see that the arrow notation is not expressive enough because :math:`∏_{j∈J} A_{g(j)}` depends on :math:`g`, but there is no :math:`g` symbol available from earlier in :eq:`9`.

The solution is again to denote the function type as a product. Product types are very expresive and enable us to concisely specify such dependent function types. Before demonstrating this, we make one more notational adjustment. Instead of denoting set membership by :math:`a ∈ A`, we adopt the type-theoretic notation :math:`a:A`, which expresses the fact that :math:`a` *has type* :math:`A`. Thus, the full :term:`dependent type` specification of the projection operation is

.. math:: \Proj: ∏_{g:J→I} \left( ∏_{i:I} A_{i} →  ∏_{j:J} A_{g(j)} \right).

Kernels of generalized projections
----------------------------------

Let :math:`𝔸 = ∏_{i:I} 𝔸_i` be a product of algebras with the same :term:`signature`, and suppose :math:`g : J → I` is a one-to-one function, where :math:`∅ ≠ J ⊆ I ⊆ ℕ`.

Define the **kernel of the projection of** :math:`𝔸` **onto** :math:`∏_{j:J} A_{g(j)}` as follows:

.. math:: Δ_g = \{(a,a') : 𝔸^2 | a ∘ g = a' ∘ g \} = \ker (\Proj g)

This is a congruence of :math:`𝔸`. More generally, if :math:`θ` is a congruence of :math:`∏_{j:J} A_{g(j)}`, define :math:`θ_g : \Con 𝔸` as follows:

.. math:: θ_g = (\Proj g)^{-1}(θ) =  \{ (a, a') : 𝔸^2 | (a ∘ g) \mathrel{\theta} (a' ∘ g) \}.

This indicates the origin of the notation :math:`Δ_g`, where :math:`Δ` denotes the trivial (identity) relation on :math:`∏_{j:J} A_{g(j)}`. If :math:`J = \{0\}` and
:math:`g : I` is just a constant, say, :math:`g(0) = k`,
then we write :math:`\theta_k` instead of :math:`\theta_{\{k\}}`, so

.. math:: \theta_k = \{(a, a') \in 𝔸^2 : a(k) \mathrel{\theta} a'(k)\}.

(Here, :math:`\theta` must be in :math:`\Con 𝔸_k`.)

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

Fix :math:`m ∈ ℕ`. If :math:`a = (a_0, a_1, \dots, a_{m-1})` is an :math:`m`-tuple of elements from :math:`A`, then (keeping in mind that :math:`m` is the set :math:`\{0, 1, \dots, m-1\}`) it is useful to understand that this tuple is a function :math:`a : m → A`, where :math:`a(i) = a_i`, for each :math:`i<m`. If :math:`h : A → A`,
then :math:`h ∘ a : m → A` is the tuple :math:`(h(a_0), h(a_1), \dots, h(a_{m-1})) ∈ A^m`, whose :math:`i`-th coordinate is :math:`(h ∘ a)(i) = h(a(i)) = h(a_i) ∈ A`.

On the other hand, if :math:`g : A^m \to A`---equivalently, :math:`g : (m → A) → A`---then :math:`g a` is the element :math:`g(a_0, a_1, \dots, a_{m-1}) ∈ A`.

If :math:`f : (ρ f → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, if :math:`a : ρ f → A` is a :math:`ρ f`-tuple on :math:`A`, and if :math:`h : A → B`, then
:math:`h ∘ a : ρ f → B`, so :math:`f (h ∘ a) : B`.

-----------------------------------------------------

.. index:: partial function application

Partial function application
----------------------------

Let :math:`I` be a nonempty set and :math:`\{𝔸_i | i : I\}` a family of sets.

Elements of the product :math:`∏_{i∈ I} 𝔸_i` are functions :math:`a: I → ⋃_{i:I} A_{i}` such that for each :math:`i` we have :math:`a(i): A_i`.

Let :math:`J ⊆ I` and let :math:`g : J → I` be one-to-one. Then, as above, :math:`a ∘ g: ∏_{j: J} A_{g(j)}` gives the projection of :math:`a` onto certain coordinates of the full product, namely, the coordinates :math:`\im g = \{g(j) ∣ j:J\}`.

Suppose :math:`f` is a self map of the set :math:`\underline{A} := ∏_{i: I} A_i`. That is, :math:`f: \underline{A} → \underline{A}`. If :math:`I = \{0, 1, \dots, n-1\}`, then :math:`\underline{A} = ∏_{i=0}^{n-1} A_i` and the (curried) type of :math:`f` is

.. math:: f: A_0 → (A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

For a given :math:`a_0 : A_0`, the function :math:`f` partially applied at the first coordinate has type

.. math:: f(a_0): A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

To ease notation we will sometimes write function application by juxtaposition so that :math:`f a_0 := f(a_0)`, for example. For elements :math:`a_0` and :math:`a_1` inhabiting types :math:`A_0` and :math:`A_1` (resp.), the partial application of :math:`f` to these elements yields the following function : type judgment,

.. math:: f a_0 a_1 : A_2 → (A_3 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1}))\cdots ).

In general, for :math:`a_i : A_i`, :math:`0 ≤ i < ℓ`,

.. math:: f a_0 a_1 \dots a_{ℓ-1}: A_ℓ → (A_{ℓ+1} → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

It would be useful to have a means of partial function application in case the domain :math:`I` is not simply :math:`\{0, 1, \dots, n-1\}`, or in case we wish to partially apply a function to an arbitrary subset of its operands (coordinates of its domain). If we have, as above,

+ :math:`\underline{𝔸} = ∏_{i:I} A_i`,

+ :math:`g : J → I` (one-to-one),

+ :math:`a ∘ g: ∏_{j:J} A_{g(j)}`, for each :math:`a : ∏_{i:I} A_i`,

Let :math:`f` have type :math:`∏_{i:I} A_i → ∏_{i:I} A_i`, which means that if we apply :math:`f` to an element :math:`a : ∏_{i:I} A_i` the result has the same type, that is, :math:`f a : ∏_{i:I} A_i`.

We may wish to apply :math:`f` to just a portion of :math:`a` but it may not be the case that :math:`I` is a subset of :math:`ℕ`, or an ordered enumeration of some other set, so there is no natural notion of “the first :math:`ℓ` operands.” Even if there was such a notion, we may wish to partially apply :math:`f` to something other than the first :math:`ℓ` operands. Therefore, we define a more general notion of partial application as follows: :math:`f` partially applied to the coordinates :math:`\im g = \{g(j) ∣ j:J\}` of the element :math:`a` gives the function : type judgment

.. math:: f ∘ (a ∘ g): ∏_{\substack{i: I\\ i ∉ \im g}} A_i → ∏_{i:I} A_i.

.. todo:: continue to describe asynchronous curry type

--------------------------------------------

.. index:: ! directed set, ! inductive set

.. _directed-sets-and-inductive-sets:

Directed sets and inductive sets
--------------------------------

A subset :math:`D` of a preorder is called a **directed set** if every finite subset of :math:`D` has an upper bound in :math:`D`.

That is, if :math:`F ⊆ D` and :math:`F` is finite, then there exists :math:`d ∈ D` such that :math:`f ≤ d` for all :math:`f ∈ F`.

A subset :math:`I` of a preorder :math:`X` is called an **inductive set** if :math:`⋁_X D ∈ I` for every directed subset :math:`D ⊆ X` contained in :math:`I`. That is, if :math:`D ⊆ I`, and if every finite subset of :math:`D` has an upper bound in :math:`D`, then :math:`D` as a least upper bound in :math:`I`.

.. proof:example:: See Remark 1.2.10 of :cite:`MR1275826`

   Let :math:`X = \{0, 1, 2, \dots, n, n+1, \dots, ∞, ⊤\}` be the chain with order relation satisfying :math:`0≤ 1≤ 2≤ \cdots ≤ n ≤ n+1 ≤ \cdots ≤ ∞ ≤ ⊤`.

   Let :math:`A = X - \{∞\}` and :math:`D = X -\{∞, ⊤\}`. (See Figure [fig:noninductive].)

   Then :math:`⋁_A D` exists and is equal to :math:`⊤`, since the join is taken in :math:`A`.

   However, :math:`⋁_X D = ∞ ∉ A`, so :math:`A` is not an inductive subset of :math:`X`.

.. todo:: insert figure

--------------------------------------------

.. index:: ! complete, ! cocomplete
.. index:: ! directed-cocomplete preorder, ! directed-cocomplete partial order (dcpo)
.. index:: ! ω-chain cocomplete, ! ω-chain cocomplete partial order (ω-cpo)

.. _completeness-and-cocompleteness:

Completeness and cocompleteness
-------------------------------

The existence of meets and joins for certain kinds of subsets of a preorder is known as completeness and cocompleteness respectively.

Suppose :math:`X` is a preorder and let P be a **property of subsets** of :math:`X`.

Given a subset :math:`A ⊆ X`, denote by :math:`A ⊨ \mathrm P` the judgement ":math:`A` has property P."

If the meet :math:`⋀ A` exists for every subset :math:`A ⊆ X` for which :math:` A ⊨ \mathrm P` holds, then we say that :math:`X` is P-**complete**.

Dually, :math:`X` is called P-**cocomplete** if the join :math:`⋁ A` exists for every subset :math:`A` with property P.

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

-------------------------------------

.. index:: ! closure operator, ! closure system

Closure systems
---------------

Let 𝔛 be a set and let :math:`𝒫(𝔛)` denote the collection of all subsets of 𝔛.

A **closure operator** on 𝔛 is a set function :math:`𝖢 : 𝒫 (𝔛) → 𝒫 {𝔛}` satisfying the following conditions, for all :math:`X, Y ∈ 𝒫 (𝔛)`, 

#. :math:`X ⊆ 𝖢 (X)`,

#. :math:`𝖢 𝖢 = 𝖢`,

#. :math:`Y ⊆ X ⟹ 𝖢 (Y) ⊆ 𝖢 (X)`.

If 𝒜 is a collection of algebras of the same type, let :math:`𝖲 𝒜` and :math:`𝖱 𝒜` denote, respectively, the collection of all subalgebras and retracts of algebras in 𝒜.

Observe that 𝖲 is a closure operator on sets of algebras of the same type.

It's easy to see that if the retraction is as defined above, then retraction operator 𝖱 is not a closure operator on sets of algebras of the same type.

However, if we take our definition of **retraction** of :math:`𝔸 = ⟨ A, F ⟩` via :math:`p ∈ \mathrm{Pol}_1(𝔸)` to be

.. math:: p(𝔸) = ⟨ p(A), \{p f|_{p(A)} : f \in F\}⟩,

then 𝖱 is a closure operator.

--------------------------------

.. rubric:: Footnotes

.. [1]
   **Answer**. Each :math:`f` "chooses" an element from each :math:`A_i`, but when the :math:`A_i` are distinct and :math:`I` is infinite, we may not be able to do this. The :ref:`Axiom of Choice <axiom-of-choice-1>` ("Choice") says you can. Gödel proved that Choice is consistent with the other axioms of set theory. Cohen proved that the negation of Choice is also consistent.


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


