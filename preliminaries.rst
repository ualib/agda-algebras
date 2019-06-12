.. include:: _static/math_macros.rst

.. _preliminaries:

========================
Set Theory Preliminaries
========================

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


