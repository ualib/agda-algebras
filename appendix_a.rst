.. include:: _static/html_latex_macros.rst

.. _appendix-a:

==========================
Appendix A. Prerequisites
==========================

.. index:: ! binary relation, ! preorder, ! partial order, ! equivalence relation

.. _relations:

Relations
---------

A **binary relation** is a set of ordered pairs. Thus, if :math:`X` is a set, a binary relation on :math:`X` is simply a subset of the Cartesian product :math:`X \times X`.

For a binary relation :math:`R`, we sometimes write :math:`x \mathrel{R} y` in place of :math:`(x, y) ∈ R`. For example, in the case of the order relation :math:`≤` on the set of natural numbers, :math:`≤` is the set

.. math:: \{(x, y) ∈ ℕ × ℕ : x \text{ is less than or equal to } y}\},

and we usually write :math:`x ≤ y` instead of :math:`(x, y) ∈ ≤`.

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

#. If :math:`A = \R^2` then
   :math:`R = \{(a, b) \in \R^2\times \R^2 : a = (a_1, a_2), \; b = (b_1, b_2), \; a_1^2+ a_2^2 = b_1^2+ b_2^2 \}`
   is an equivalence relation on :math:`A`. The equivalence classes are
   circles centered at :math:`(0,0)`.

A **partition** of a set :math:`A` is a collection
:math:`\Pi = \{A_i : i\in I\}` of non-empty subsets of :math:`A` such
that

.. math::

   \bigcup_{i\in I} A_i = A \quad \text{ and } \quad  A_i \cap A_j = 
   \emptyset \text{ for all pairs $i\neq j$ in $I$.}

 The :math:`A_i` are called the “blocks” of the partition.

Every partition :math:`\Pi` determines an equivalence relation—namely,
the relation :math:`R` defined by :math:`a\rel{R} b` if and only if
:math:`a` and :math:`b` are in the same block of :math:`\Pi`.
Conversely, if :math:`R` is an equivalence relation on :math:`A`, we
denote the equivalence class of :math:`R` containing :math:`a` by
:math:`a/R := \{b\in A : a \rel{R} b\}` and the set
:math:`A/\theta := \{a/\theta : a\in A\}` of all :math:`\theta` classes
is a partition of :math:`A`.

Examples: preorders, partial orders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An **equivalence relation** on a set :math:`X` is a preorder that is
**symmetric**. That is, an equivalence relation is a binary relation
that is reflexive, symmetric, and transitive.

With any preorder :math:`X` we can associate a poset in a natural way.
Since a preorder is not antisymmetric in general, we may have distinct
elements :math:`x, y \in X` with :math:`x\leq y` and :math:`y\leq x`.
However, in this case we define the binary relation :math:`\cong` on
:math:`X` by: :math:`x\cong y` iff :math:`x\leq y` and :math:`y\leq x`.
(Some authors call the elements :math:`x` and :math:`y` **isomorphic**
in this case, but we prefer the term :math:`{\cong}`-equivalent.) The
relation :math:`\cong` so defined is an equivalence relation on
:math:`X` and if we simply equate all :math:`{\cong}`-equivalent pairs
:math:`x\cong y`, then we obtain a poset, denoted by :math:`X/{\cong}`.
The elements of :math:`X/{\cong}` are **:math:`\cong`-equivalence
classes**. These classes partition the set :math:`X` into disjoint
subsets, each subset consisting of elements that are pairwise
:math:`\cong`-equivalent. For :math:`x\in X`, the equivalence class
containing the element :math:`x`—which is sometimes denoted by
:math:`[x]` or :math:`[x]_{\cong}`—is given by the set
:math:`[x]=\{y\in X : x\cong y\}`. The relation :math:`\leq` defined by
:math:`[x] \leq [y]` iff :math:`x\leq y` is a partial order on the set
:math:`X/{\cong}:=\{[x] : x\in X\}` of equivalence classes. The poset
:math:`X/{\cong}` is sometimes called the **poset reflection** of the
preorder :math:`X`.

Let :math:`\< X, \leq\>` be a preorder, let :math:`A, B, C\subseteq X`
be subsets, and let :math:`x \in X`. If :math:`a\leq x` for all
:math:`a \in A`, then we write :math:`A\leq x` and we say that :math:`x`
is an **upper bound** for :math:`A` in :math:`X`. (Lower bounds are
defined dually.) A **join** of :math:`A` (when it exists) is a least
element in the set of all upper bounds of :math:`A` in :math:`X`. A join
is sometimes called a **least upper bound** or **supremum**. A **meet**
of :math:`A` (when it exists) is a greatest element in the set of all
lower bounds of :math:`A` in :math:`X`. A meet of :math:`A` is sometimes
called a **greatest lower bound** or **infimum**. It is easy to see that
joins and meets of preordered sets are determined uniquely up to
(:math:`\cong`)-equivalence. Indeed, if :math:`a` and :math:`a'` are two
least upper bounds of :math:`A`, then we clearly have :math:`a\leq a'`
and :math:`a'\leq a`; therefore, :math:`a\cong a'`. If a subset
:math:`A` has at least one join, then we will let :math:`{\Join}A`
denote a choice of one of the joins of :math:`A`. Similarly, if
:math:`A` has at least one meet, then we let :math:`{\Meet}A` denote a
choice of one of the meets of :math:`A`. To specify the preorder
:math:`X` with respect to which the join or meet is taken, we write
:math:`{\Join_X}A` and :math:`{\Meet_X}A`, respectively. Note that for
every :math:`x\in X` we have :math:`{\Join_X}A \leq x` iff
:math:`A \leq x`. Similarly, for meets, we have :math:`x\leq {\Meet_X}A`
iff :math:`x\leq A`.

Considering the empty subset :math:`\varnothing \subseteq X`, and in
light of the fact that for every :math:`x\in X` the implication
:math:`a\in \varnothing \longrightarrow a\leq x` holds *ex falso
quodlibet*, we see that the join of :math:`\varnothing`, if it exists,
must satisfy :math:`{\Join}\varnothing \leq x` for all :math:`x\in X`.
Therefore, :math:`\bot := {\Join}\varnothing` is the “bottom” of any
preorder in which :math:`{\Join}\varnothing` exists. Similarly,
:math:`a\in \varnothing \longrightarrow x\leq a` also holds vacuously,
so for all :math:`x\in X` we have :math:`{\Meet}\varnothing \leq x`, and
we let :math:`\top := {\Meet}\varnothing` be the “top” of any preorder
in which :math:`{\Meet}\varnothing` exists.

We call :math:`C\subseteq X` a **chain** if for all :math:`x, y \in C`
we have :math:`x\leq y` or :math:`y\leq x`. If, in addition, the
elements of :math:`C` can be indexed by the natural numbers, then we
call :math:`C` an :math:`\omega`\ **-chain**. A subset :math:`A` of a
preorder :math:`X` is called an **antichain** if for all
:math:`x, y \in A` we have :math:`x \leq y` implies :math:`y\leq x`.

.. _basic-type-theory:

Basic type theory
-----------------

This section presents some of the rudiments of *type theory*.  For more details, a nice and easy introduction to the basics is `Logic and Proof`_, and more advanced treatments are :cite:`MR3445957` and :cite:`HoTT`.

.. todo:: say something more about this

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

The simplest example of a Pi type is the Cartesian product :math:`B_0 × B_1` which, when viewed as the collection of functions that map :math:`i ∈ \{0, 1\}` to some element of :math:`B_i`, is the type :math:`\Pi_{i : \{0, 1\}} B_i`. [1]_

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

