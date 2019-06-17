.. include:: _static/math_macros.rst

.. _preliminaries:

=============
Preliminaries
=============

.. todo:: add introductory paragraph

.. index:: ! relation, ! binary relation, 
.. index:: ! domain, ! range

Binary Relations
-----------------

A **binary relation** is a set of ordered pairs. Thus, if :math:`X` is a set, a binary relation on :math:`X` is simply a subset of the Cartesian product :math:`X \times X`.

For a binary relation :math:`R`, we sometimes write :math:`x \mathrel{R} y` in place of :math:`(x, y) ∈ R`. For example, in the case of the order relation :math:`≤` on the set of natural numbers, :math:`≤` is the set :math:`\{(x, y) ∈ ℕ × ℕ : x` is less that or equal to :math:`y\}`, and we usually write :math:`x ≤ y` instead of :math:`(x, y) ∈ ≤`.

For a relation :math:`R`, we define the **domain** of :math:`R` (:math:`\dom R`) and the **range** of :math:`R` (:math:`\ran R`) by

.. math::

    x ∈  \dom R \quad & ⟺ \quad ∃ y, \, (x,y) ∈ R,\\
    x ∈ \ran R  \quad & ⟺ \quad ∃ t, \, (t,x) ∈ R.

Binary relations arise so often that we simply call them "relations," and only say "binary relation" when we want to highlight their **arity** (which is 2) and distinguish them from relations of other arities.

Some binary relations have properties that make them especially useful in a vast array of applications. For instance, a binary relation :math:`R` may or may not be

+ **reflexive**: :math:`∀ x ∈ X, \ x \mathrel{R} x`,

+ **symmetric**: :math:`∀ x, y ∈ X \ (x \mathrel{R} y \ → \ y \mathrel{R} x)`;

+ **antisymmetric**: :math:`∀  x, y ∈ X \ (x \mathrel{R} y ∧ y\mathrel{R} x \ → \ x=y)`;

+ **transitive**: :math:`∀ x, y, z ∈ X \ (x \mathrel{R} y ∧ y \mathrel{R} z\ → \ x \mathrel{R} z)`.


.. index:: ! preorder

.. _preorder:

Preorder
~~~~~~~~~

A **preorder** on a set :math:`X` is a reflexive and transitive subset of :math:`X × X`.

If :math:`R` is a preorder on :math:`X`, then we call :math:`⟨X, R⟩` (or :math:`X` itself) as a **preordered set**.

.. proof:examples::

   The `reachability relation <http://en.wikipedia.org/wiki/Reachability>`_ of a `directed graph <http://en.wikipedia.org/wiki/Directed_graph>`_ (possibly containing cycles) gives rise to a preorder :math:`R`, where :math:`x \mathrel{R} y` if and only if the directed graph has a path from :math:`x` to :math:`y`.

   Conversely, every preorder :math:`R` on a set :math:`X` is the reachability relation of a directed graph (simply take elements of :math:`X` to be the vertices and draw an edge from :math:`x` to :math:`y` whenever :math:`x \mathrel{R} y`).

The significance of preorders stems mainly from the fact that the two most important classes of binary relations happen to be preorders. These are *equivalence relations* and *partial orders*.


.. index:: ! equivalence relation, ! equivalence class, ! partition, ! block

.. _equivalence-relation:

Equivalence relation
~~~~~~~~~~~~~~~~~~~~

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

   #. The **kernel** of a function is an equivalence relation on :math:`X`; i.e., if :math:`f : X → Y` and :math:`x_1, x_2 ∈ X`, then we say :math:`x_1` and :math:`x_2` are **equivalent modulo the kernel of** :math:`f` and we write :math:`x_1 ∼ x_2` (or :math:`(x_1, x_2) ∈ \ker f`) if and only if :math:`f(x_1) = f(x_2)`.
   #. The relation on lines in a plane, given by ":math:`x` and :math:`y` are parallel" is an equivalence relation.

   Here, we say that :math:`x` is congruent to :math:`y` modulo :math:`m` if they leave the same remainder when divided by :math:`m`. Soon, you will be able to prove rigorously that this is equivalent to saying that :math:`x - y` is divisible by :math:`m`.

.. index:: ! partial ordering
.. index:: pair: partially ordered set; poset

.. _partial-order-relation:

Partial order relation
~~~~~~~~~~~~~~~~~~~~~~

A **partial ordering** (or "partial order") is an anti-symmetric preorder.  A **partially ordered set** (or "poset") :math:`⟨X, R⟩` is a set :math:`X` along with a partial order :math:`R` defined on :math:`X`.

.. proof:examples::

   #. If :math:`X = ℤ` and :math:`R` is the usual :math:`≤` relation, then :math:`R` is a partial order on :math:`X`. (In fact, :math:`≤` is a :term:`total order` on :math:`ℤ` in this case.)

   #. Let :math:`X` be any set and let :math:`\mathcal{P}(X)` be the collection of all subsets of :math:`X`. The subset relation :math:`y ⊆ z` (":math:`y` is a subset of :math:`z`") is a partial order on :math:`\mathcal{P}(X)`.

   #. Let :math:`X = ℝ^2` and :math:`R =` ":math:`≤` on each component"; i.e., :math:`R = \{(a, b) ∈ ℝ^2 × ℝ^2 : a_1 ≤ b_1, \, a_2 ≤ b_2 \}`. Then :math:`R` is a partial order on :math:`X`.

The poset induced by a preorder
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

With any preorder :math:`X` we can associate a poset in a natural way as we now explain.

Since a preorder is not antisymmetric in general, we may have distinct elements :math:`x, y ∈ X` with :math:`x ≤ y` and :math:`y ≤ x`.

In this case we define the binary relation ≡ on :math:`X` by: :math:`x ≡ y` iff :math:`x ≤ y` and :math:`y ≤ x`.

.. index:: equivalence class

The relation ≡ so defined is an equivalence relation on the set :math:`X`, and as such it partitions :math:`X` into disjoint equivalence classes, :math:`X_0, X_1, \dots` where :math:`X = ⋃ X_i` and for each :math:`i` we have :math:`x, y ∈ X_i` iff :math:`x ≡ y`.

Now imagine that we cannot differentiate elements of a single equivalence class. Then we can think of each equivalence class as a single object and every member of a particular class can be taken as a "representative" of that class.

The result is a poset, denoted by :math:`X/{≅}`, whose elements are the equivalence classes of ≡. These classes partition the set :math:`X` into disjoint subsets, each subset consisting of elements that are pairwise equivalent.  Precisely, for each :math:`x ∈ X`, we denote and define the **equivalence class** containing the element :math:`x` by 

.. math:: x/{≅} \; = \{y ∈ X : x ≅ y\}.

(Some authors prefer the notation :math:`[x]` or :math:`[x]_≅` for the equivalence class containing :math:`x`.)

We denote the set :math:`\{x/{≅} \; : x ∈ X\}` of all ≅-equivalence classes by :math:`X/{≅}`.

Let ⊑ denote the relation on :math:`X/{≅}` defined as follows: :math:`∀ x \ ∀ y \ (x/{≅} \ ⊑ y/{≅} \ ⟺ \ x ≤ y)`.

It is easy to see that ⊑ is a partial ordering on :math:`X/{≅}`. The poset :math:`⟨ X/{≅}, ≤ ⟩` is sometimes called the **poset reflection** of the preordered set :math:`⟨ X, ≤ ⟩`.


.. index:: ! total ordering, ! partial order

.. _total-and-strict-ordering:

Total and strict ordering
~~~~~~~~~~~~~~~~~~~~~~~~~

A partial order ≤ on a domain :math:`A` is a **total order** (also called a **linear order**) if all elements are pairwise comparable; that is, for all :math:`a, b ∈ A`, we have either :math:`a ≤ b` or :math:`b ≤ a`.

.. proof:examples::

    Here are two examples of partial orders that are not total orders.

    #. The divides relation, :math:`x ∣ y`, on the integers.
    #. The subset relation, :math:`x ⊆ y`, on sets of elements of some domain :math:`A`.

A binary relation :math:`<` on a domain :math:`A` is a **strict partial order** if it satisfies the following:

- (irreflexive) :math:`a ≮ a` for every :math:`a` in :math:`A`
- (transitive) :math:`a < b` and :math:`b < c` implies :math:`a < c`, for every :math:`a`, :math:`b`, and :math:`c` in :math:`A`

A strict partial order is a **strict total order** (or **strict linear order**) if, in addition, it has the **trichotomy** property: :math:`a < b`, :math:`a = b`, or :math:`a > b` for every :math:`a` and :math:`b` in :math:`A`.

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

.. _equality:

Equality
~~~~~~~~

Let :math:`A` be a set and let ≡ be equivalence relation on :math:`A`.  Recall, this means that, in addition to being a binary relation, ≡ has three special properties.

-  ≡ is **reflexive**; :math:`∀ a ∈ A`, :math:`a ≡ a`;
-  ≡ is **symmetric**; i.e., :math:`∀ a, b ∈ A` if :math:`a ≡ b`, then :math:`b ≡ a`;
-  ≡ is **transitive**; i.e., :math:`∀ a, b, c ∈ A` if :math:`a ≡ b` and :math:`b ≡ c`, then :math:`a ≡ c`.

These three properties alone are not strong enough to characterize *equality*.

.. Consider the equivalence relation on citizens of the United States, given by ":math:`x` and :math:`y` have the same age." There are some properties that respect that equivalence. For example, suppose I tell you that John and Susan have the same age, and I also tell you that John is old enough to vote. Then you can rightly infer that Susan is old enough to vote. On the other hand, if I tell you nothing more than the facts that John and Susan have the same age and John lives in South Dakota, you cannot infer that Susan lives in South Dakota. This little example illustrates what is special about the *equality* relation: if two things are equal, then they have exactly the same properties.

In mathematics, there are many notions of equality. These are usually implicit and almost never mentioned.  Instead, one assumes that the intended notion of equality is obvious from context.

In computer science, however, such informality is unacceptable since computers cannot infer the appropriate equality in every situation.  For this reason, explicit mention of particular notions of equality is more common in computer science than in mathematics. [1]_

To see what we're going on about, consider two basic, distinct notions of equality---**syntactic equality**, where two expressions are "equal" if and only if exactly the same symbols appear in exactly the same order in each expression, and **semantic equality**, which takes two expressions to be equal if they have the same "meaning", or if they refer to or denote the same object.  

For example, :math:`2 + 5` is semantically, but not syntactically, equal to :math:`7`.

Axiomatically, we assume that every relation used to represent some notion of an equality must be an *equivalence relation*.  That is, it must be a reflexive, symmetric, transitive binary relation.  Of course, there are a number of distinct equivalence relations on a nonempty set, so these properties do not fully characterize equality.

If two expressions denote the same thing, then we should be able to substitute one for any other in any expression. It is convenient to adopt the following convention: if :math:`r` is any term, we may write :math:`r(x)` to indicate that the variable :math:`x` may occur in :math:`r`. Then, if :math:`s` is another term, we can thereafter write :math:`r(s)` to denote the result of replacing :math:`s` for :math:`x` in :math:`r`. The substitution rule for terms thus reads as follows: if :math:`s = t`, then :math:`r(s) = r(t)`.

We already adopted a similar convention for formulas: if we introduce a formula as :math:`A(x)`, then :math:`A(t)` denotes the result of substituting :math:`t` for :math:`x` in :math:`A`. With this in mind, we can write the rules for equality as follows:

.. raw:: html

   <img src="_static/first_order_logic.10.png">

.. raw:: latex

   \begin{center}
   \AXM{}
   \UIM{t = t}
   \DP
   \quad
   \AXM{s = t}
   \UIM{t = s}
   \DP
   \quad
   \AXM{r = s}
   \AXM{s = t}
   \BIM{r = t}
   \DP
   \\
   \ \\
   \AXM{s = t}
   \UIM{r(s) = r(t)}
   \DP
   \quad
   \AXM{s = t}
   \AXM{P(s)}
   \BIM{P(t)}
   \DP
   \end{center}

Here, the first substitution rule governs terms and the second substitution rule governs formulas. In the next chapter, you will learn how to use them.

Using equality, we can define even more quantifiers.

-  We can express "there are at least two elements :math:`x` such that :math:`A(x)` holds" as :math:`∃ x \ ∃ y \ (x ≠ y ∧ A(x) ∧ A(y))`.

-  We can express "there are at most two elements :math:`x` such that :math:`A(x)` holds" as :math:`∀ x \ ∀ y \ ∀ z \ (A(x) ∧ A(y) ∧ A(z) → x = y ∨ y = z ∨ x = z)`. This states that if we have three elements :math:`a` for which :math:`A(a)` holds, then two of them must be equal.

-  We can express "there are exactly two elements :math:`x` such that :math:`A(x)` holds" as the conjunction of the above two statements.

As an exercise, write out in first order logic the statements that there are at least, at most, and exactly three elements :math:`x` such that :math:`A(x)` holds.

In logic, the expression :math:`∃! x \ A(x)` is used to express the fact that there is a *unique* :math:`x` satisfying :math:`A(x)`, which is to say, there is exactly one such :math:`x`. As above, this can be expressed as follows:

.. math::

   ∃ x \ A(x) ∧ ∀ y \ ∀ y' \ (A(y) ∧ A(y') → y = y').

The first conjunct says that there is at least one object satisfying :math:`A`, and the second conjunct says that there is at most one. The same thing can be expressed more concisely as follows:

.. math::

   ∃ x \ (A(x) ∧ ∀ y \ (A(y) → y = x)).

You should think about why this second expression works. In the next chapter we will see that, using the rules of natural deduction, we can prove that these two expressions are equivalent.

--------------------------------------

.. index:: equivalence class, ! quotient, 

.. _quotients:

Quotients
---------

Given an equivalence relation on :math:`A`, there is an important mathematical construction known as forming the *quotient* of :math:`A` modulo the equivalence relation.

As above, for each :math:`a ∈ A`, let :math:`a/{≡}` denote the set :math:`\{ b ∈ A ∣ b ≡ a \}` of those elements of :math:`A` that are equivalent to :math:`a` modulo ≡. We call :math:`a/{≡}` the ≡-class of :math:`A` containing :math:`a`.

The set :math:`A/{≡}`, of all such equivalence classes is called the **quotient of** :math:`A` **modulo** ≡.  It is defined to be the set :math:`\{ a/{≡} ∣ a ∈ A \}`.

Equivalence captures a weak notion of equality: if two elements of :math:`A` are equivalent modulo ≡, they are not necessarily the same, but they differ only in ways that do not interest us.  

Here is a "real-world" example of a situation in which we would "mod out" certain irrelevant information.  In a study of image data for the purpose of facial recognition---specifically, the task of identifying a particular person from two photographs---the orientation of the face at the moment it is captured in the photos is unimportant.  Indeed, it would be silly to conclude that the individuals in the two photos must be different simply because the face is shown at different angles.

Equivalence classes collect similar objects together, unifying them into a single entity (e.g., the collection of all photographs of a single individual).  Thus :math:`A/{≡}` is a version of the set :math:`A` where similar elements have been compressed into a single element.

A simple example from mathematics is the equivalence relation on ℤ of **congruence modulo 5**, which partitions ℤ into five equivalence classes---namely, :math:`5ℤ`, :math:`1 + 5ℤ`, :math:`2+5ℤ`, :math:`3+5ℤ` and :math:`4+5ℤ`.  Here, :math:`5ℤ` is the set :math:`\{\dots, -10, -5, 0, 5, 10, 15, \dots\}` of multiples of 5, and :math:`2+5ℤ` is the set :math:`\{\dots, -8, -3, 2, 7, 12, \dots\}` of integers that differ from a multiple of 5 by 2.

-------------------------------------------------------------

.. index:: ! ordered tuples, !tuples
.. index:: ! unary relation, ! binary relation, ! ternary relation

Relations
---------

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

.. index:: ! function, ! inverse, ! function composition, ! restriction, ! image

Functions
---------

A **function** (or **mapping**) is a relation :math:`F` such that for each :math:`x` in :math:`\dom F` there is only one :math:`y` such that :math:`x \mathrel{F} y`.

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

    The image :math:`F[A]` can be characterized more simply when :math:`F` is a function and :math:`A ⊆ \dom F`; in this case :math:`F[A] = \{F(u) ∣ u ∈ A\}`.

    In each case we can easily apply a subset axiom to establish the existence of the desired set. Specifically,

    .. math:: F^{-1} ⊆ \ran F × \dom F, \quad  F ∘ G ⊆ \dom G × \ran F, \quad F ↾ A ⊆ F, \quad F[A] ⊆ \ran F.

    (A more detailed justification of the definition of :math:`F^{-1}` would go as follows: By a subset axiom there is a set :math:`B` such that for every :math:`x`,

    .. math:: x ∈ B \quad ⟺ \quad  x ∈ \ran F × \dom F \ ∧ \ ∃ u \ ∃ v \ (x = (u, v) \ ∧ \ (v, u) ∈ F).

    It then follows that

    .. math:: x ∈ B \quad ⟺ \quad ∃ u \ ∃ v \ (x = (u, v) \ ∧ \ (v, u) ∈ F).

    We denote this unique set :math:`B` by :math:`F^{-1}`.)

Let

.. math:: F = \{ (∅, a), (\{∅\}, b) \}.

Observe that :math:`F` is a function. We have :math:`F^{-1} = \{ (a, ∅), (b, \{∅\}) \}`. Thus, :math:`F^{-1}` is a function iff :math:`a ≠ b`.

The restriction of :math:`F` to :math:`∅` is :math:`∅`, but :math:`F ↾ \{∅\} = \{(0, a)\}`.

Consequently, :math:`F[\{∅\}] = \{a\}`, in contrast to the fact that :math:`F(\{∅\}) = b`.

.. proof:theorem::

   Assume that :math:`F: A → B`, and that :math:`A` is nonempty.

   #. There exists a function :math:`G: B → A` (a “left inverse”) such that :math:`G ∘ F` is the identity function :math:`\id_A` on :math:`A` iff :math:`F` is one-to-one.

   #. There exists a function :math:`H: B → A` (a “right inverse”) such that :math:`F ∘ H` is the identity function :math:`\id_B` on :math:`B` iff :math:`F` maps :math:`A` *onto* :math:`B`.

.. _axiom-of-choice-1:

.. proof:axiom:: Axiom of Choice 1

   For any relation :math:`R` there is a function :math:`H ⊆ R` with :math:`\dom H = \dom R`.

With this axiom we can prove the sufficiency direction of item 2 of the theorem above: take :math:`H` to be a function with :math:`H ⊆ F^{-1}` and :math:`\dom H = \dom F^{-1} = B`. Then :math:`H` does what we want: Given any :math:`y ∈ B`, we have :math:`(y,H(y)) ∈ F^{-1}` hence :math:`(H(y), y) ∈ F`, and so :math:`F(H(y)) = y`.

------------------------------

.. index:: ! join, ! upper bound, ! least upper bound, ! supremum
.. index:: ! meet, ! lower bound, ! greatest lower bound, !infimum

Joins and meets
-----------------

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

----------------------------


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

   To make clear why the term “projection” is reserved for the case when :math:`σ` is one-to-one, suppose :math:`k=4`, :math:`n=3`, and consider the 4-tuple :math:`σ = (1, 0, 1, 1)`. Then :math:`σ` is the function :math:`σ : \{0,1,2,3\} → \{0,1,2\}` given by :math:`σ(0) = 1`, :math:`σ(1) = 0`, :math:`σ(2) = 1`, :math:`σ(3) = 1`, and so :math:`a ↦ a ∘ σ` is the function that takes :math:`(a_0, a_1, a_2)∈ A_0 × A_1 × A_2` to :math:`(a_1, a_0, a_1, a_1) ∈ A_1 × A_0 × A_1 × A_1`. [2]_

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

.. index:: ! directed set, ! inductive set

.. _directed-sets-and-inductive-sets:

Directed sets and inductive sets
--------------------------------

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

-----------------------------------------

.. rubric:: Footnotes

.. [1]
   The relationship that a computer scientist has with equality, borne of necessity, is deeper than that of a mathematician, just as the relationship of an Eskimo to snow is deeper than that humans living in mild climates. (See `There really are 50 Eskimo words for snow <https://www.washingtonpost.com/national/health-science/there-really-are-50-eskimo-words-for-snow/2013/01/14/e0e3f4e0-59a0-11e2-beee-6e38f5215402_story.html>`_.)

.. [2]
   Note that even in the special case when :math:`\Proj_j ℝ = 𝔸_{σ(j)}` for each :math:`j<k` so that :math:`ℝ ≤_{\mathrm{sd}} ∏_{j<k} 𝔸_{σ(j)}`, we refrain from using :math:`\Proj_σ 𝔸` to denote :math:`∏_{j<k} 𝔸_{σ(j)}`  for the simple reason that σ might not be one-to-one.  For example, we could have :math:`𝔸 = 𝔸_0 × 𝔸_1` and :math:`σ = (1,0,1)`, in which case :math:`∏_{j<k} 𝔸_{σ(j)} = 𝔸_1 × 𝔸_0 × 𝔸_1` and this is not the "projection" of 𝔸 onto a subset of its factors.
   

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

.. Preliminaries
..   Preorders
..   Equivalence relations
..   Partial Order Relations
..     The poset induced by a preorder
..   Total and strict orderings
..   Equality
..   Relations of higher arity
..   Functions
..   Joins and meets
..   Projections
..   Directed sets and inductive sets
..   Completeness and cocompleteness
..   Closure systems

