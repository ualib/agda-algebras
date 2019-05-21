Relations and functions
=======================

Let :math:`\N` denote the set of natural numbers (including :math:`0`)
and :math:`\N^+` the positive natural numbers. Thus,
:math:`\N = \{0, 1, \dots \}` and :math:`\N^+ = \{1, 2, \dots \}`.

This section gives a brief review of some elementary definitions and
facts from set theory. See Enderton :raw-latex:`\cite{Enderton:1977}`
for more details.

Most of us probably have a good idea of what is meant by an “ordered
pair,” :math:`(x, y)`. It consists of two elements (or sets) :math:`x`
and :math:`y`, listed in a particular order. How to make this notion
mathematically precise is not quite so obvious. According
to :raw-latex:`\cite{Enderton:1977}`, in 1921 Kazimierz Kuratowski gave
us the definition in general use today: given two sets :math:`x` and
:math:`y`, the **ordered pair** :math:`(x, y)` is defined to be the set
:math:`\{\{x\}, \{x, y\}\}`. It is not too hard to prove that this
definition captures our intuitive idea of ordered pair—namely,
:math:`(x, y)` uniquely determines both what :math:`x` and :math:`y`
are, and the order in which they appear. Indeed, it is a theorem
(Theorem 3A of :raw-latex:`\cite{Enderton:1977}`) that
:math:`(u, v) = (x, y)` iff :math:`u =
x` and :math:`v = y`.

Binary relations
----------------

A **binary relation** is a set of ordered pairs. Thus, if :math:`X` is a
set, a binary relation :math:`\sR` on :math:`X` is simply a subset of
the Cartesian product :math:`X \times X`; that is,

.. math:: \sR \subseteq X\times X := \{(x_1, x_2) : x_1, x_2 \in X\}.

 For a binary relation :math:`\sR`, we sometimes write :math:`x \rsR y`
in place of :math:`(x, y) \in \sR`. For example, in the case of the
order relation :math:`\leq` on the set  of real numbers, :math:`\leq` is
defined to be the set

.. math:: \{(x, y) \in \R \times \R : \text{$x$ is less than or equal to $y$}\},

 and we usually write :math:`x \leq y` to mean that the pair
:math:`(x, y)` belongs to the relation :math:`\leq`. In fact, we could
write :math:`(x, y) \in \; \leq`, but the “infix” notation
:math:`x \leq y` is often preferred for binary relations.

For a relation :math:`R`, we define the **domain** of :math:`R`
(:math:`\dom R`) and the **range** of :math:`R` (:math:`\ran R`) by

.. math::

   \begin{aligned}
   x \in  \dom R \quad &\Longleftrightarrow \quad \exists y \; (x,y) \in R,\\
   x \in\ran R  \quad &\Longleftrightarrow \quad \exists t \; (t,x) \in R.\end{aligned}

Binary relations arise so often that we simply call them “relations,”
and only say “binary relation” when we want to highlight their arity and
distinguish them from relations of other arities. Some binary relations
have properties that make them especially useful in a vast array of
applications. Indeed, a binary relation :math:`R` may or may not satisfy
one or more of the following:

-  (*reflexivity*) :math:`\forall x`, :math:`x\relR x`;

-  (*symmetry*) :math:`\forall x\, \forall y`
   :math:`(x\relR y \;\rightarrow \;y \relR x)`;

-  (*antisymmetry*) :math:`\forall x\, \forall y`
   :math:`(x\relR y \mathrel{\meet} y\relR x \; \rightarrow \; x=y)`;

-  (*transitivity*) :math:`\forall x\, \forall y\, \forall z`
   :math:`(x\relR y \meet y\relR z \rightarrow x \relR z)`.

A **preorder** on a set :math:`X` is a binary relation
:math:`\sP \subseteq X \times X` that satisfies the following
conditions.

#. (*reflexivity*) :math:`\forall x`, :math:`x\rsP x`;

#. (*transitivity*) :math:`\forall x\, \forall y\, \forall z`
   :math:`(x\rsP y \meet y\rsP z \rightarrow x \rsP z)`.

In this case we refer to :math:`\<X, \sP \>` (or :math:`X`) as a
preordered set.

The `reachability
relation <http://en.wikipedia.org/wiki/Reachability>`__ in any `directed
graph <http://en.wikipedia.org/wiki/Directed_graph>`__ (possibly
containing cycles) gives rise to a preorder :math:`\sR`, where
:math:`x \rsR y` if and only if there is a path from :math:`x` to
:math:`y` in the directed graph. Conversely, every preorder :math:`\sR`
on a set :math:`X` is the reachability relation of a directed graph
(simply take elements of :math:`X` to be the vertices and draw an edge
from :math:`x` to :math:`y` whenever :math:`x \rsR y`).

The significance of preorders stems mainly from the fact that the two
most important classes of binary relations happen to be preorders. These
are partial orders and equivalence relations.

A *partial ordering* (or just “partial order”) is an anti-symmetric
preorder; precisely,

A **partial ordering** :math:`\sP` on a set :math:`X` is a relation
:math:`\sP \subseteq X \times X` satisfying,

#. (*reflexivity*) :math:`\forall x`, :math:`x\rsP x`;

#. (*antisymmetry*) :math:`\forall x\, \forall y`
   :math:`(x\rsP y \mathrel{\meet} y\rsP x \; \rightarrow \; x=y)`;

#. (*transitivity*) :math:`\forall x\, \forall y\, \forall z`
   :math:`(x\rsP y \meet y\rsP z \rightarrow x \rsP z)`.

A **partially ordered set** (or “poset”) :math:`\<X, \sP\>` is a set
:math:`X` along with a preorder :math:`\sP` defined on :math:`X` that,
in addition to being reflexive and transitive, is also antisymmetric;
that is, :math:`\forall x, y \in X`, if :math:`x\rsP y` and
:math:`y\rsP x`, then :math:`x = y`.

An *equivalence relation* is a symmetric preorder; that is,

An **equivalence relation** on a set :math:`X` is a binary relation
:math:`\sE\subseteq X \times X` satisfying,

#. (*reflexivity*) :math:`\forall x`, :math:`x\rel{\sE} x`;

#. (*symmetry*) :math:`\forall x\, \forall y`
   :math:`(x\rel{\sE} y \;\rightarrow \;y \rel{\sE} x)`;

#. (*transitivity*) :math:`\forall x\, \forall y\, \forall z`
   :math:`(x\rel{\sE} y \meet y\rel{\sE} z \rightarrow x \rel{\sE} z)`.

We denote the set of all equivalence relations on a set :math:`X` by
:math:`\Eq(X)`.

Here are a few concrete examples of binary relations that arise often.

#. If :math:`A = \Z` and :math:`R` is the usual :math:`\leq` relation,
   then :math:`R` is a partial order on :math:`A`. (In fact,
   :math:`\leq` is a total order on :math:`\Z` in this case.)

#. Let :math:`X` be any set and consider the collection
   :math:`A = \mathcal{P}(X)` of all subsets of :math:`X`. The subset
   relation :math:`y \subseteq z` (“:math:`y` is a subset of :math:`z`”)
   is a partial order on :math:`A`.

#. Let :math:`A = \R^2` and :math:`R =` “:math:`\leq` on each component”
   :math:`= \{(a, b) \in \R^2\times \R^2 : a_1 \leq b_1, \; a_2\leq b_2 \}`.
   Then :math:`R` is a partial order on :math:`A`.

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

Functions
---------

A **function** (or mapping) is a relation :math:`F` such that for each
:math:`x` in :math:`\dom F` there is only one :math:`y` such that
:math:`x \,F\, y`.

The following operations are most commonly applied to functions, are
sometimes applied to relations, but can actually be defined for
arbitrary sets :math:`A`, :math:`F`, and :math:`G`.

(a) The **inverse** of :math:`F` is the set

    .. math:: F^{-1}=\{(u, v) \mid v \,F \,u\}=\{(u, v) \mid (v,u) \in F \}.

(b) The **composition** of :math:`F` and :math:`G` is the set

    .. math::

       F \circ G = \{(u, v) \mid \exists t \,(u \,G \,t \;\&\; t\, F\, v)\}
       = \{(u, v) \mid \exists t \;((u,t)\in G\; \& \;(t,v) \in F)\}.

(c) The **restriction** of :math:`F` to :math:`A` is the set

    .. math::

       F \res A = \{(u, v) \mid u \, F \,v\; \& \; u \in A\}
       = \{(u, v) \mid (u,v)\in F \; \& \; u \in A\}.

     We often denote this restriction by :math:`\restr{F}{A}`.

(d) The **image** of :math:`A` under :math:`F` is the set

    .. math:: F\lb A\rb = \ran(F \res A)= \{v \mid (\exists u \in A)\; (u,v) \in F\}.

| :math:`F\lb A\rb` can be characterized more simply when :math:`F` is a
  function and :math:`A\subseteq \dom F`; in this case

  .. math:: F\lb A\rb = \{F(u) \mid u \in A\}.

   In each case we can easily apply a subset axiom to establish the
  existence of the desired set. Specifically,

  .. math::

     F^{-1} \subseteq \ran F \times \dom F, \quad 
     F \circ G \subseteq \dom G \times \ran F, \quad  
     F \res A \subseteq F, \quad 
     F\lb A\rb \subseteq \ran F.

   (A more detailed justification of the definition of :math:`F^{-1}`
  would go as follows: By a subset axiom there is a set :math:`B` such
  that for any :math:`x`,

  .. math::

     x\in B \quad \Longleftrightarrow \quad  x \in  \ran F \times \dom F \; \& \; 
     \exists u \; \exists v\; (x = (u, v) \; \&\; (v, u) \in F).

   It then follows that

  .. math:: x\in B \quad \Longleftrightarrow  \quad \exists u \; \exists v\; (x = (u, v) \; \&\; (v, u) \in F).

   This unique set :math:`B` we denote by :math:`F^{-1}`.)

Let

.. math:: F = \{ (\emptyset, a), (\{\emptyset\}, b) \}.

 Observe that :math:`F` is a function. We have
:math:`F^{-1} = \{ (a, \emptyset), (b, \{\emptyset\}) \}`. Thus,
:math:`F^{-1}` is a function iff :math:`a \neq b`. The restriction of
:math:`F` to :math:`\emptyset` is :math:`\emptyset`, but
:math:`F \res \{\emptyset\} = \{(0, a)\}`. Consequently,
:math:`F\lb \{\emptyset \}\rb = \{a\}`, in contrast to the fact that
:math:`F(\{\es\}) = b`.

Assume that :math:`F: A\rightarrow  B`, and that :math:`A` is nonempty.

(a) There exists a function :math:`G: B \rightarrow A` (a “left
    inverse”) such that :math:`G \circ F` is the identity function
    :math:`\id_{A}` on :math:`A` iff :math:`F` is one-to-one.

(b) There exists a function :math:`H: B \rightarrow A` (a “right
    inverse”) such that :math:`F \circ H` is the identity function
    :math:`\id_{B}` on :math:`B` iff :math:`F` maps :math:`A` *onto*
    :math:`B`.

**Axiom of Choice 1.** For any relation :math:`R` there is a function
:math:`H \subseteq R` with :math:`\dom H = \dom R`.

With this axiom we can prove the sufficiency direction of part (b) of
the Theorem above: take :math:`H` to be a function with
:math:`H \subseteq F^{-1}` and :math:`\dom H = \dom F^{-1} = B`. Then
:math:`H` does what we want: Given any :math:`y \in B`, we have
:math:`(y,H(y)) \in F^{-1}` hence :math:`(H(y), y) \in F`, and so
:math:`F(H(y)) = y`.

Higher order relations
~~~~~~~~~~~~~~~~~~~~~~

We can extend the definition of ordered pairs and define an *ordered
triple* recursively, as follows:

.. math:: (x, y, z) = ((x, y), z).

 Similarly we can form *ordered quadruples*:

.. math::

   (x_1, x_2, x_3, x_4) = ((x_1, x_2, x_3), x_4)
   = (((x_1,x_2),x_3),x_4).

 Inductively, for each :math:`n\in \N`, if we assume the notion of
ordered :math:`k`-tuple, :math:`(x_1, \dots, x_k)`, has been defined for
:math:`k < n`, we can form *ordered :math:`n`-tuples* as follows:

.. math:: (x_1, \dots, x_{n-1}, x_n) = ((x_1, \dots, x_{n-1}), x_n).

 It is convenient for reasons of uniformity to define also the 1-tuple
:math:`(x) = x`. We define an :math:`n`-ary relation on :math:`A` to be
a set of ordered :math:`n`-tuples with all components in :math:`A`. Thus
a binary (2-ary) relation on :math:`A` is just a subset of
:math:`A \times A`. And a ternary (3-ary) relation on :math:`A` is a
subset of :math:`(A \times A) \times A`. There is, however, a
terminological quirk here. If :math:`n > 1`, then any :math:`n`-ary
relation on :math:`A` is actually a binary relation, but a unary (1-ary)
relation on :math:`A` is just a subset of :math:`A`.

A **:math:`k`-ary relation** :math:`R` on a set :math:`A` is a subset of
the Cartesian product :math:`A^k`. We give some examples of relations
below. In these examples, :math:`\R` denotes the set of real numbers,
and letters :math:`a \in \R^2`, :math:`b \in \R^3` etc. denote tuples
:math:`(a_0, a_1)`, :math:`(b_0, b_1, b_2)`, etc.

(a) :math:`A = \R` and
    :math:`R = \{a\in \R^2: a = b\} = \{(a,a) : a \in \R\}`.

(b) :math:`A = \R^2` (the plane) and
    :math:`R = \{(a,b,c) \in \R^2\times \R^2\times
        \R^2: \text{$a$, $b$, $c$ lie on a line}\}`; i.e. triples of
    points which are *colinear*.

Note that a 1-ary or **unary relation** on a set :math:`A` is simply a
subset of :math:`A`, a **binary relation** is a subset of :math:`A^2`, a
**ternary relation** is a subset of :math:`A^3`, etc.

Projections
-----------

An operation :math:`f : A^n \rightarrow A` is called **idempotent**
provided :math:`f(a, a, \dots, a) = a` for all :math:`a \in A`. Examples
of idempotent operations are the projection functions and these will
play an important role in later sections, so we start by introducing a
sufficiently general and flexible notation for them.

Define the natural numbers as usual and denote them as follows:

.. math::

   \uzero := \emptyset, \quad
   \uone := \{0\}, \quad
   \utwo := \{0, 1\}, \dots,

.. math:: \dots, \nn := \{0, 1, 2, \dots, n-1\}, \dots.

 Given sets :math:`A_0, A_1, \dots, A_{n-1}`, denote their Cartesian
product by

.. math:: \Pi_{\nn} A_i := A_0 \times A_1 \times \cdots \times A_{n-1}.

 An element :math:`\ba \in \Pi_{\nn} A_i` is an ordered :math:`n`-tuple,
which may be specified by simply listing its values,
:math:`\ba = (\ba(0), \ba(1), \dots, \ba(n-1))`. [1]_ Thus, tuples are
functions defined on a finite (“index”) set, and we often view them this
way. This fact may be emphasized by writing

.. math:: \ba : \nn \to \bigcup_{i\in \nn} A_i; \;\; i\mapsto \ba(i) \in A_i.

 If :math:`\sigma: \kk \to \nn` is a :math:`k`-tuple of numbers in the
set :math:`\nn`, then we can compose an :math:`n`-tuple
:math:`\ba\in \Pi_{\nn} A_i` with :math:`\sigma` yielding
:math:`\ba\circ \sigma \in \Pi_{\kk}A_{\sigma(i)}`. The result is a
:math:`k`-tuple whose :math:`i`-th component is
:math:`(\ba\circ \sigma)(i) = \ba(\sigma(i))`. If :math:`\sigma` happens
to be one-to-one, then we call the following a **projection function**:

.. math::

   \label{eq:5}
   \Proj_\sigma: \Pi_{\nn}A_i \to \Pi_{\kk}A_{\sigma(i)};
   \;\; \ba \mapsto \ba\circ \sigma.

 That is, for :math:`\ba\in \Pi_{\nn}A_i` we define
:math:`\Proj_\sigma \ba := \ba\circ \sigma`. In later sections, we will
apply such projection functions to subsets
:math:`R\subseteq \Pi_{\nn}A_i`, in which case

.. math::

   \Proj_\sigma R := \{\br\circ \sigma \mid \br \in R\}\\
   = \{(\br_{\sigma(0)}, \br_{\sigma(1)}, \dots, \br_{\sigma(k-1)}) \mid r \in R\}.

 We will also make frequent use of the following shorthand:

.. math:: R_\sigma := \Proj_\sigma R.

To make clear why the term “projection” is reserved for the case when
:math:`\sigma` is one-to-one, suppose :math:`k=4`, :math:`n=3`, and
consider the 4-tuple :math:`\sigma = (1, 0, 1, 1)`. Then :math:`\sigma`
is the function :math:`\sigma: \{0,1,2,3\} \to \{0,1,2\}` given by
:math:`\sigma(0) = 1`, :math:`\sigma(1) = 0`, :math:`\sigma(2) = 1`,
:math:`\sigma(3) = 1`, and so :math:`a \mapsto a\circ \sigma` is the
function that takes :math:`(a_0, a_1, a_2)\in A_0 \times A_1 \times A_2`
to
:math:`(a_1, a_0, a_1, a_1) \in A_1 \times A_0 \times A_1 \times A_1`.

Let :math:`\uA = \prod_{\nn} A_i`, let
:math:`\sigma : \kk \rightarrow \nn` be one-to-one, and define the
projection :math:`\Proj_\sigma` as in ([eq:5]) above. Then the *kernel*
of :math:`\Proj_\sigma`, which we denote by :math:`\vzero_\sigma`, is
defined as follows:

.. math::

   \begin{aligned}
    \label{eq:6}
   \vzero_\sigma &:= \ker (\Proj_\sigma) 
   = \{(\ba,\ba') \in \uA^2 \mid \Proj_\sigma \ba = \Proj_\sigma \ba'\}\\
   &= \{(\ba,\ba') \in \uA^2 \mid \ba \circ \sigma = \ba' \circ \sigma \}
   = \{(\ba,\ba') \in \uA^2 \mid \forall j \in \im \sigma, \,\ba(j)= \ba'(j)  \}.\nonumber\end{aligned}

 It is obvious that :math:`\vzero_\sigma` is an equivalence relation on
the set :math:`\uA`.

More generally, if :math:`\theta` is an equivalence relation on the set
:math:`\Pi_{j\in \kk} A_{\sigma(j)}`—that is,
:math:`\theta \subseteq (\Pi_{j\in \kk} A_{\sigma(j)})^2` and
:math:`\theta` is reflexive, symmetric, and transitive—then we define
the equivalence relation :math:`\theta_\sigma` on the set
:math:`\uA = \Pi_{\nn} A_i` as follows:

.. math::

   \label{eq:17}
    \theta_\sigma := 
    \{(\ba, \ba') \in \uA^2 \mid (\ba\circ \sigma) \mathrel{\theta} (\ba' \circ \sigma)\}.

 In other words, :math:`\theta_\sigma` consists of all pairs in
:math:`\uA^2` that land in :math:`\theta` when projected onto the
coordinates in :math:`\im \sigma`.

(i)   Recall that :math:`\Proj_\sigma: \uA \to \Pi_{\kk} A_{\sigma(j)}`
      is the function that maps :math:`\ba` to :math:`\ba \circ \sigma`.
      Now, suppose we have a tuple
      :math:`(\ba_0, \ba_1, \dots, \ba_{p-1})\in \uA^p`, and suppose we
      intend to apply :math:`\Proj_\sigma` to each component,
      :math:`\ba_j`. To do so, we need to lift :math:`\Proj_\sigma` from
      type :math:`\uA \to \Pi_{\kk} A_{\sigma(j)}` to type
      :math:`\uA^p \to (\Pi_{\kk} A_{\sigma(j)})^p`, which is
      accomplished using a functor that often goes by the name
      :math:`\map`. For instance, if :math:`(\ba, \ba') \in \uA^2`, then
      :math:`\map(\Proj_\sigma)(\ba, \ba') =
          (\Proj_\sigma(\ba), \Proj_\sigma(\ba'))`. Therefore,

      .. math:: \theta_\sigma =\{(\ba, \ba') \in \uA^2 \mid \map(\Proj_\sigma)(\ba, \ba') \in \theta \},

       from which we see that
      :math:`\theta_\sigma = \map(\Proj_\sigma)^{-1}\theta`.

(ii)  If :math:`f: X \to A` and :math:`g: X \to B` are functions defined
      on the same domain :math:`X`, then :math:`(f,g): X \to A \times B`
      is the unique function that composes with the first projection to
      give :math:`f` and composes with the second projection to give
      :math:`g`. For example, in the last remark there appears the
      expression
      :math:`(\Proj_\sigma(\ba), \Proj_\sigma(\ba')) = (\ba \circ \sigma, \ba' \circ \sigma)`,
      which has type :math:`(\Pi_{\kk} A_{\sigma(j)})^2`.

(iii) [rem:notation-eta] In retrospect, a more appropriate name for
      :math:`\vzero_\sigma` might be :math:`\Delta_\sigma`, or even
      :math:`=_\sigma`, but this would surely annoy too many people who
      are used to seeing :math:`\eta` play the role of projection
      kernel.

If the domain of :math:`\sigma` is a singleton, :math:`\kk = \{0\}`,
then of course :math:`\sigma` is just a one-element list, say,
:math:`\sigma= (j)`. In such cases, we write :math:`\Proj_j` instead of
:math:`\Proj_{(j)}`. Similarly, we write and :math:`\vzero_j` and
:math:`\theta_j` instead of :math:`\vzero_{(j)}` and
:math:`\theta_{(j)}`. Thus, :math:`\Proj_j \ba = \ba(j)`, and
:math:`\vzero_j = \{(\ba, \ba') \in \uA^2 \mid \ba(j) = \ba'(j)\}`, and,
if :math:`\theta\in \Con \alg{A}_j`, then
:math:`\theta_j = \{(\ba, \ba') \in \uA^2 \mid \ba(j) \mathrel{\theta} \ba'(j)\}`.
Here are some obvious consequences of these definitions:

.. math::

   \bigvee_{j\in \nn}\vzero_j =\uA^2, \qquad
    \vzero_\sigma= \bigwedge_{j\in \sigma}\vzero_j, \qquad
    \vzero_{\nn} = \bigwedge_{j\in \nn}\vzero_j = 0_{\ubA}, \qquad
   \theta_\sigma = \bigwedge_{j\in \kk}\theta_{\sigma(j)},

 where :math:`0_{\uA}` denotes the least equivalence relation on , that
is, :math:`0_{\uA}:= \{(\ba, \ba') \in \uA^2 \mid \ba = \ba'\}`. As we
alluded to in Remark ([rem:notation-eta]) above, :math:`\eta_\sigma` is
shorthand for :math:`(0_{\uA})_\sigma`.

Compositions
------------

For a natural number :math:`n`, let
:math:`[n] = \{0, 1, \dots, n-1\}`. [2]_ Let :math:`A`, :math:`B`,
:math:`C` be sets, let :math:`f: B^n \to A` be a function. Let us
identify :math:`n`-tuples in :math:`B^n` with functions of type
:math:`[n] \to B`. That is, the tuple

.. math::

   \label{eq:3}
   (b(0), b(1), \dots, b(n-1)) \in B^n

 defines the function :math:`b` which, when applied to :math:`k`, gives
the value :math:`b(k)` appearing in the tuple presentation ([eq:3]).
Conversely, we can express a given function :math:`b` of type
:math:`[n] \to B` by listing the function values :math:`b(k)` in the
form of an :math:`n`-tuple, as in ([eq:3]). Thus, the set :math:`B^n` is
identified with the set of all functions of type :math:`[n]\to B`.
Therefore, a function :math:`f` of type :math:`B^n \to A` is the same as
a function of type :math:`([n] \to B) \to A`, where for each
:math:`b:[n]\to B`, we have
:math:`f b = f(b(0), b(1), \dots, b(n-1)) \in A`.

Let :math:`g(0), g(1), \dots, g(n-1)` be a list of :math:`n` functions
of type :math:`C \to B`. Then the :math:`n`-tuple
:math:`g = (g(0), g(1), \dots, g(n-1))` is a function of type
:math:`[n] \to (C \to B)`. That is, for each :math:`0\leq k < n` we have
:math:`g(k): C\to B`, and for each :math:`c \in C` we have
:math:`g(k)(c) \in B`.

Given a function :math:`f:([n] \to B) \to A` and a function
:math:`g:[n] \to (C \to B)`, we obtain a new function of type
:math:`C \to A` by an operation called the *general composition* of
:math:`f` with :math:`g`. This new function, which we denote by
:math:`f \circ g`, is defined for each :math:`c\in C` as follows:

.. math:: (f \circ g)(c) = f(g(0)(c), g(1)(c), \dots, g(n-1)(c))

.. math::

   f \circ (g_0, g_1, \dots, g_{n-1})(c) = f(g_0 (c), g_1 (c), 
   \dots, g_{n-1}(c)).

If :math:`n` and :math:`m` are natural numbers, and if we take
:math:`B = A` and :math:`C = A^m` in the foregoing definition, then
:math:`f \in \AAn`, and each :math:`g_i` is of type :math:`\AAm`
(:math:`m`-ary). Thus, the general composition of :math:`f` with
:math:`g_0, g_1,\dots, g_{n-1}` is given in this case by

.. math:: f \circ (g_0, g_1, \dots, g_{n-1})(\ba) = f(g_0 (\ba), g_1 (\ba), \dots, g_{n-1}(\ba)),

 for each :math:`\ba = (a_0, a_1 , \dots, a_{m-1})` in :math:`A^m`.

#. Unlike the ordinary composition of unary functions, the general
   composition exists only when the arities of the component functions
   match up correctly.

#. Just as the set of unary operations forms a monoid under the
   operation of unary composition, we can form a *partial algebra* whose
   elements are the members of :math:`\sansO_A` and with general
   composition as partial operation.

#. For the purpose of programming, it may be more convenient to write
   the composition function :math:`f \circ (g_0, g_1, \dots, g_{n-1})`
   as :math:`\sansComp(f)(g_0, g_1, \dots, g_{n-1})`. Then
   :math:`\sansComp` is a function with the following type signature:

   .. math:: \sansComp : (B^n \to A) \rightarrow (C\to B)^n \rightarrow (C\to A).

Generalities
============

Generalized projections
-----------------------

An operation :math:`f : A^n \rightarrow A` is called **idempotent**
provided :math:`f(a, a, \dots, a) = a` for all :math:`a \in A`. Examples
of idempotent operations are the projection functions and these will
play an important role in later sections, so we start by introducing a
sufficiently general and flexible notation for them.

Define the natural numbers as usual and denote them as follows:

.. math::

   \uzero := \emptyset, \quad
   \uone := \{0\}, \quad
   \utwo := \{0, 1\}, \dots,

.. math:: \dots, \nn := \{0, 1, 2, \dots, n-1\}, \dots.

 Given sets :math:`A_0, A_1, \dots, A_{n-1}`, denote their Cartesian
product by

.. math:: \Pi_{\nn} A_i := A_0 \times A_1 \times \cdots \times A_{n-1}.

 An element :math:`\ba \in \Pi_{\nn} A_i` is an ordered :math:`n`-tuple,
which may be specified by simply listing its values,
:math:`\ba = (\ba(0), \ba(1), \dots, \ba(n-1))`. (Tuples are more
commonly written with subscripts as in
:math:`(a_0, a_1, \dots, a_{n-1})`, and we will adopt this convention
when it is convenient, especially if the functional view is not
relevant.) Thus, tuples are functions defined on a finite (“index”) set,
and we often view them this way. This fact may be emphasized by writing

.. math:: \ba : \nn \to \bigcup_{i\in \nn} A_i; \;\; i\mapsto \ba(i) \in A_i.

 If :math:`\sigma: \kk \to \nn` is a :math:`k`-tuple of numbers in the
set :math:`\nn`, then we can compose an :math:`n`-tuple
:math:`\ba\in \Pi_{\nn} A_i` with :math:`\sigma` yielding
:math:`\ba\circ \sigma \in \Pi_{\kk}A_{\sigma(i)}`. The result is a
:math:`k`-tuple whose :math:`i`-th component is
:math:`(\ba\circ \sigma)(i) = \ba(\sigma(i))`. If :math:`\sigma` happens
to be one-to-one, then we call the following a **projection function**:

.. math::

   \label{eq:5}
   \Proj_\sigma: \Pi_{\nn}A_i \to \Pi_{\kk}A_{\sigma(i)};
   \;\; \ba \mapsto \ba\circ \sigma.

 That is, for :math:`\ba\in \Pi_{\nn}A_i` we define
:math:`\Proj_\sigma \ba := \ba\circ \sigma`. In later sections, we will
apply such projection functions to subsets
:math:`R\subseteq \Pi_{\nn}A_i`, in which case

.. math::

   \Proj_\sigma R := \{\br\circ \sigma \mid \br \in R\}\\
   = \{(\br_{\sigma(0)}, \br_{\sigma(1)}, \dots, \br_{\sigma(k-1)}) \mid r \in R\}.

 We will also make frequent use of the following shorthand:

.. math:: R_\sigma := \Proj_\sigma R.

To make clear why the term “projection” is reserved for the case when
:math:`\sigma` is one-to-one, suppose :math:`k=4`, :math:`n=3`, and
consider the 4-tuple :math:`\sigma = (1, 0, 1, 1)`. Then :math:`\sigma`
is the function :math:`\sigma: \{0,1,2,3\} \to \{0,1,2\}` given by
:math:`\sigma(0) = 1`, :math:`\sigma(1) = 0`, :math:`\sigma(2) = 1`,
:math:`\sigma(3) = 1`, and so :math:`a \mapsto a\circ \sigma` is the
function that takes :math:`(a_0, a_1, a_2)\in A_0 \times A_1 \times A_2`
to
:math:`(a_1, a_0, a_1, a_1) \in A_1 \times A_0 \times A_1 \times A_1`.

Let :math:`\uA = \prod_{\nn} A_i`, let
:math:`\sigma : \kk \rightarrow \nn` be one-to-one, and define the
projection :math:`\Proj_\sigma` as in ([eq:5]) above. Then the *kernel*
of :math:`\Proj_\sigma`, which we denote by :math:`\vzero_\sigma`, is
defined as follows:

.. math::

   \begin{aligned}
    \label{eq:600}
   \vzero_\sigma &:= \ker (\Proj_\sigma) 
   = \{(\ba,\ba') \in \uA^2 \mid \Proj_\sigma \ba = \Proj_\sigma \ba'\}\\
   &= \{(\ba,\ba') \in \uA^2 \mid \ba \circ \sigma = \ba' \circ \sigma \}
   = \{(\ba,\ba') \in \uA^2 \mid \forall j \in \im \sigma, \,\ba(j)= \ba'(j)  \}.\nonumber\end{aligned}

 It is obvious that :math:`\vzero_\sigma` is an equivalence relation on
the set :math:`\uA`.

More generally, if :math:`\theta` is an equivalence relation on the set
:math:`\Pi_{j\in \kk} A_{\sigma(j)}`—that is,
:math:`\theta \subseteq (\Pi_{j\in \kk} A_{\sigma(j)})^2` and
:math:`\theta` is reflexive, symmetric, and transitive—then we define
the equivalence relation :math:`\theta_\sigma` on the set
:math:`\uA = \Pi_{\nn} A_i` as follows:

.. math::

   \label{eq:1700}
     \theta_{\sigma} := 
     \{(\ba, \ba') \in \uA^2 \mid (\ba\circ \sigma) \mathrel{\theta} (\ba' \circ \sigma)\}.

In other words, :math:`\theta_\sigma` consists of all pairs in
:math:`\uA^2` that land in :math:`\theta` when projected onto the
coordinates in :math:`\im \sigma`.

#. Recall that :math:`\Proj_\sigma: \uA \to \Pi_{\kk} A_{\sigma(j)}` is
   the function that maps :math:`\ba` to :math:`\ba \circ \sigma`. Now,
   suppose we have a tuple
   :math:`(\ba_0, \ba_1, \dots, \ba_{p-1})\in \uA^p`, and suppose we
   intend to apply :math:`\Proj_\sigma` to each component,
   :math:`\ba_j`. To do so, we need to lift :math:`\Proj_\sigma` from
   type :math:`\uA \to \Pi_{\kk} A_{\sigma(j)}` to type
   :math:`\uA^p \to (\Pi_{\kk} A_{\sigma(j)})^p`, which is accomplished
   using a functor that often goes by the name :math:`\map`. For
   instance, if :math:`(\ba, \ba') \in \uA^2`, then
   :math:`\map(\Proj_\sigma)(\ba, \ba') =
       (\Proj_\sigma(\ba), \Proj_\sigma(\ba'))`. Therefore,

   .. math:: \theta_\sigma =\{(\ba, \ba') \in \uA^2 \mid \map(\Proj_\sigma)(\ba, \ba') \in \theta \},

    from which we see that
   :math:`\theta_\sigma = \map(\Proj_\sigma)^{-1}\theta`.

#. If :math:`f: X \to A` and :math:`g: X \to B` are functions defined on
   the same domain :math:`X`, then :math:`(f,g): X \to A \times B` is
   the unique function that composes with the first projection to give
   :math:`f` and composes with the second projection to give :math:`g`.
   For example, in the last remark there appears the expression
   :math:`(\Proj_\sigma(\ba), \Proj_\sigma(\ba')) = (\ba \circ \sigma, \ba' \circ \sigma)`,
   which has type :math:`(\Pi_{\kk} A_{\sigma(j)})^2`.

#. [rem:notation-eta] In retrospect, a more appropriate name for
   :math:`\vzero_\sigma` might be :math:`\Delta_\sigma`, or even
   :math:`=_\sigma`, but this would surely annoy too many people who are
   used to seeing :math:`\eta` play the role of projection kernel.

If the domain of :math:`\sigma` is a singleton, :math:`\kk = \{0\}`,
then of course :math:`\sigma` is just a one-element list, say,
:math:`\sigma= (j)`. In such cases, we write :math:`\Proj_j` instead of
:math:`\Proj_{(j)}`. Similarly, we write and :math:`\vzero_j` and
:math:`\theta_j` instead of :math:`\vzero_{(j)}` and
:math:`\theta_{(j)}`. Thus, :math:`\Proj_j \ba = \ba(j)`, and
:math:`\vzero_j = \{(\ba, \ba') \in \uA^2 \mid \ba(j) = \ba'(j)\}`, and,
if :math:`\theta\in \Con \alg{A}_j`, then
:math:`\theta_j = \{(\ba, \ba') \in \uA^2 \mid \ba(j) \mathrel{\theta} \ba'(j)\}`.
Here are some obvious consequences of these definitions:

.. math::

   \bigvee_{j\in \nn}\vzero_j =\uA^2, \qquad
    \vzero_\sigma= \bigwedge_{j\in \sigma}\vzero_j, \qquad
    \vzero_{\nn} = \bigwedge_{j\in \nn}\vzero_j = 0_{\ubA}, \qquad
   \theta_\sigma = \bigwedge_{j\in \kk}\theta_{\sigma(j)},

 where :math:`0_{\uA}` denotes the least equivalence relation on , that
is, :math:`0_{\uA}:= \{(\ba, \ba') \in \uA^2 \mid \ba = \ba'\}`. As we
alluded to in Remark ([rem:notation-eta]) above, :math:`\eta_\sigma` is
shorthand for :math:`(0_{\uA})_\sigma`.

Generalized projections and dependent types
-------------------------------------------

This is new material on a more general way of presenting projections and
partial application of functions. (The first draft of this section
initially appeared in the appendix of our absorption notes, but has
since been removed from those notes.)

Let :math:`\{\alg{A}_i : i \in \sI\}` be a collection of algebras of the
same signature (for some :math:`\sI \subseteq \N`) [3]_ and let
:math:`\underline{\alg{A}} = \prod_{i\in \sI} \alg{A}_i`. (Actually, for
now it suffices to think of the :math:`\alg{A}_i` and
:math:`\underline{\alg{A}}` as sets since the algebraic structure won’t
play a role in this section.) View the elements of
:math:`\underline{\alg{A}}` as functions:

.. math::

   \label{eq:7}
   \ba \in \prod_{i\in \sI} \alg{A}_i \quad \longleftrightarrow
   \quad 
   \begin{cases}
   \ba: \sI \rightarrow \bigcup_{i\in \sI} A_i, \text{ and }&\\
   \ba(i) \in A_i, \text{ for each $i\in \sI$.} &  
   \end{cases}

This correspondence simply records the fact that the product type (on
the left of the :math:`\longleftrightarrow` symbol) represents a special
kind of function type (depicted on the right of
:math:`\longleftrightarrow` using the usual :math:`\rightarrow` notation
for function types). In other words, ([eq:7]) says that an element of
the product type :math:`\prod_{i\in \sI} \alg{A}_i` is a function from
:math:`\sI` into :math:`\bigcup_{i\in \sI} A_i` whose codomain
:math:`A_i` *depends* on the input argument :math:`i`. Such a function
(or product) type is what computer scientists call a *dependent type*.

Now, given a subset :math:`J \subseteq \sI`, a function
:math:`\sigma: J \rightarrow \sI`, and an element
:math:`\ba \in \prod_{i\in \sI}A_i`, consider the composition
:math:`\ba \circ \sigma`. This is a function from :math:`J` to
:math:`\bigcup_{j\in J} A_{\sigma(j)}`, where
:math:`(\ba\circ \sigma)(j) \in A_{\sigma(j)}`. Again, we could express
this function type using the arrow notation,
“:math:`\ba \circ \sigma: J \rightarrow \bigcup_{j\in J} A_{\sigma(j)}`
where :math:`(\ba\circ \sigma)(j) \in A_{\sigma(j)}`,” but this
specification has a more compact description using a product type:

.. math:: \ba \circ \sigma \in \prod_{j\in J} A_{\sigma(j)}.

 Assume :math:`\sigma` is one-to-one and define the “projection”
function,

.. math:: \Proj(\sigma) : \prod_{i\in \sI} A_{i} \rightarrow \prod_{j\in J} A_{\sigma(j)}

 by :math:`\Proj(\sigma): \ba \mapsto (\ba \circ \sigma)`. That is,
:math:`\Proj(\sigma)(\ba) = \ba \circ \sigma`.

We could try to specify the type of :math:`\Proj` using the arrow
notation as follows:

.. math::

   \label{eq:8}
   \Proj: (J \rightarrow \sI)\rightarrow 
   \bigl(\sI \rightarrow \bigcup_{i\in \sI} A_{i}\bigr) \rightarrow 
   \bigl(J \rightarrow \bigcup_{i\in \sI} A_{i}\bigr),

 but the deficiencies of the arrow notation are now even more glaring.
The function type specification given in ([eq:8]) is not only imprecise,
but also misleading. The result of applying :math:`\Proj` first to some
:math:`\sigma: J \rightarrow \sI` and then
:math:`\ba:\sI \rightarrow \bigcup_{i\in \sI} A_{i}` is
:math:`\Proj (\sigma) (\ba)= \ba \circ \sigma`, and to say that this is
a function of type :math:`J \rightarrow \bigcup_{i\in \sI} A_{i}` is
ambiguous at best. Rather, the precise (correct!) type specification is,
“:math:`\Proj (\sigma) (\ba): J \rightarrow \bigcup_{j\in J} A_{\sigma(j)}`
where :math:`\Proj (\sigma) (\ba) (j) \in A_{\sigma(j)}`.” Here again we
can express this more concisely with a product type,
:math:`\Proj (\sigma)(\ba) \in \prod_{j\in J} A_{\sigma(j)}`. Thus, to
denote the type of :math:`\Proj`, we must add to ([eq:8]) the
constraints on codomains that depend on argument values. For specifying
the type of a “function of higher order” (a.k.a. a “functional”), the
arrow notation can be cumbersome.

The following is closer to what we want, but still imperfect:

.. math::

   \label{eq:9}
   \Proj: (J \rightarrow \sI)\rightarrow \prod_{i\in \sI} A_{i} \rightarrow 
   \prod_{j\in J} A_{\sigma(j)}.

 This says that :math:`\Proj` takes a function
:math:`\sigma : J \rightarrow \sI` and a function
:math:`\ba \in \prod_{i\in \sI} A_{i}` and returns the function
:math:`\ba \circ \sigma \in \prod_{j\in J} A_{\sigma(j)}`. Here again we
see that the arrow notation is not expressive enough because
:math:`\prod_{j\in J} A_{\sigma(j)}` depends on :math:`\sigma`, but no
:math:`\sigma` is available from earlier in the expression ([eq:9]).

The solution is again to denote the function type as a product. Product
types are more expresive and enable us to concisely specify dependent
types. Before demonstrating this, we make one more notational
adjustment. Instead of denoting set membership by :math:`a \in A`, we
will use the (type theoretic) notation :math:`a: A`, which expresses the
fact that :math:`a` is a “constant” of type :math:`A`. Thus, the full
(dependent) type specification of the projection operation is

.. math::

   \Proj: \prod_{\sigma :J \rightarrow \sI}\left( \prod_{i: \sI} A_{i} \rightarrow 
   \prod_{j: J} A_{\sigma(j)}\right).

Kernels of generalized projections
----------------------------------

Let :math:`\alg{A} = \prod_{i\in \sI} \alg{A}_i` be a product of
algebras of the same type, and suppose
:math:`\sigma : J \rightarrow \sI` is a one-to-one function, where
:math:`\emptyset \neq J \subseteq \sI \subseteq \N`. Define the *kernel
of the projection of* :math:`\alg{A}` *onto*
:math:`\prod_{j: J} A_{\sigma(j)}` as follows: [4]_

.. math::

   \Delta_\sigma = \{(a,a') \in \alg{A}^2 : a \circ \sigma = a' \circ \sigma \} 
   = \ker (\Proj \sigma)

 This is a congruence of :math:`\alg{A}`. More generally, if
:math:`\theta` is a congruence of :math:`\prod_{j: J} A_{\sigma(j)}`,
define :math:`\theta_\sigma \in \Con \alg{A}` as follows:

.. math::

   \theta_\sigma := (\Proj \sigma)^{-1}(\theta)  = 
   \{(a, a') \in \alg{A}^2 : (a\circ \sigma) \mathrel{\theta} (a' \circ \sigma)\}.

 This indicates the origin of the notation :math:`\Delta_\sigma`, where
:math:`\Delta` denotes the trivial (identity) relation on
:math:`\prod_{j: J} A_{\sigma(j)}`. If :math:`J = \{0\}` and
:math:`\sigma : \sI` is just a constant, say, :math:`\sigma(0) = k`,
then we write :math:`\theta_k` instead of :math:`\theta_{\{k\}}`, so

.. math:: \theta_k = \{(a, a') \in \alg{A}^2 : a(k) \mathrel{\theta} a'(k)\}.

 (Here, :math:`\theta` must be in :math:`\Con \alg{A}_k`.)

The symbols :math:`\N`, :math:`\omega`, and nat are used
interchangeably; they all denote the set of natural numbers. A
**signature** :math:`S = (F, \rho)` consists of a set :math:`F` of
operation symbols and a function :math:`\rho \colon F \to \N`. We call
:math:`\rho f` the **arity** of the symbol :math:`f`. If :math:`A` is a
set and :math:`f` is a :math:`\rho f`-ary operation on :math:`A`, then
we sometimes write :math:`f \colon A^{\rho f} \to A`. Since the natural
number :math:`\rho f` denotes the set
:math:`\{0, 1, \dots, \rho f -1\}`, a function
:math:`g \colon \rho f \to A` is simply a :math:`\rho f`-tuple of
elements from :math:`A`; that is for each :math:`i\in \rho f`,
:math:`g i \in A`.

By identifying the :math:`\rho f`-th power, :math:`A^{\rho f}`, of the
set :math:`A` with the type :math:`\rho f \to A` of functions from
:math:`\{0, 1, \dots, \rho f -1\}` to :math:`A`, we thus identify the
function type :math:`A^{\rho f} \to A` with the type
:math:`(\rho f \to A) \to A`. To say that :math:`f` inhabits the
function type :math:`A^{\rho f} \to A` and to write
:math:`f \colon A^{\rho f} \to A` is then equivalent to saying that
:math:`f` inhabits :math:`(\rho f \to A) \to A` and writing
:math:`f \colon (\rho f \to A) \to A`.

Fix :math:`m\in \N`. If :math:`a = (a_0, a_1, \dots, a_{m-1})` is an
:math:`m`-tuple of elements from :math:`A`, then (keeping in mind that
:math:`m` is the set :math:`\{0, 1, \dots, m-1\}`) it is useful to
understand that this tuple is a function :math:`a : m \to A`, where
:math:`a(i) = a_i`, for each :math:`i<m`. If :math:`h \colon A \to A`,
then :math:`h\circ a : m \to A` is the tuple
:math:`(h(a_0), h(a_1), \dots, h(a_{m-1}))\in A^m`, whose :math:`i`-th
coordinate is :math:`(h\circ a)(i) = h(a(i)) = h(a_i) \in A`. On the
other hand, if :math:`g \colon A^m \to A`—equivalently,
:math:`g \colon (m \to A) \to A`—then :math:`g a` is the element
:math:`g(a_0, a_1, \dots, a_{m-1}) \in A`. If
:math:`f \colon (\rho f \to B) \to B` is a :math:`\rho f`-ary operation
on :math:`B`, if :math:`a \colon \rho f \to A` is a :math:`\rho f`-tuple
on :math:`A`, and if :math:`h \colon A \to B`, then
:math:`h \circ a \colon \rho f \to B`, so
:math:`f (h \circ a) \colon B`.

Generalized composition
-----------------------

Suppose :math:`f \colon (\rho f \to A) \to A`, and suppose
:math:`g_i \colon A^m \to A` for each :math:`i <\rho f`. Let
:math:`g \colon \rho f \to (A^m \to A)` denote the function whose value
at :math:`i < \rho f` is :math:`g(i) = g_i`. We want to define a
*generalized composition* of :math:`f` with
:math:`g_0, g_1, \dots, g_{\rho f -1}`. We could obviously do this
component-wise, but that makes computing with such compositions
unweildy. Observe,

Apparently composition of :math:`f` with :math:`g` is impossible without
dropping down to coordinates since the types don’t line up properly.
However, this is easily fixed with an obvious isomorphism. Denote by
:math:`\uncurry{g} \colon (\rho f \times (m \to A)) \to A` the uncurried
version of :math:`g`, so that :math:`gib = \uncurry{g}(i,b)`. Swapping
the first and second coordinates of :math:`\uncurry{g}` yields
:math:`\swap{\uncurry{g}} \colon ((m\to A) \times \rho f) \to A`; that
is :math:`\swap{\uncurry{g}}(b,i) = \uncurry{g} (i,b)` for all
:math:`i \colon \rho f` and :math:`b \colon m \to A`. Now, if we let
:math:`\tilde{g} := \curry{\swap{\uncurry{g}}}`, then the types of
:math:`f` and :math:`\tilde{g}` are properly aligned for composition.
Indeed, we have

and for each :math:`b \colon m \to A`, the function
:math:`\tilde{g}b \colon \rho f \to A` is the tuple whose :math:`i`-th
coordinate is :math:`\tilde{g}b(i) = g_i(b_0, \dots, b_{m-1})`. Thus,

.. math:: f\tilde{g} b = f(g_0 (b_0, \dots, b_{m-1}), \dots, g_{\rho f -1}(b_0, \dots, b_{m-1})).

 This is called the **generalized composition** of :math:`f` with
:math:`g = (g_0, \dots, g_{\rho f -1})`.

Partial function application
----------------------------

Let :math:`\sI` be a nonempty set and let
:math:`\{\alg{A}_i \mid i : \sI\}` be a collection of sets (or algebras
of the same signature). [5]_ In applications, :math:`\sI` is often
:math:`\{0,1,\dots, n-1\}` for some :math:`n: \N`, and it helps to keep
this special case in mind. Elements of the product
:math:`\underline{\alg{A}} = \prod_{i: \sI} \alg{A}_i` are functions
:math:`\ba: \sI \to \bigcup_{i: \sI} A_{i}` such that for each :math:`i`
we have :math:`\ba(i): A_i`.

Let :math:`J\subseteq \sI` and let :math:`\sigma : J \to \sI` be
one-to-one. Then, as above,
:math:`\ba \circ \sigma: \prod_{j: J} A_{\sigma(j)}` gives the
projection of :math:`\ba` onto certain coordinates of the full product,
namely, the coordinates :math:`\im \sigma = \{\sigma(j) \mid j:J\}`.

Suppose :math:`f` is a self map of the set
:math:`\underline{A}:=\prod_{i: \sI} A_i`. That is,
:math:`f: \underline{A}\to \underline{A}`. If
:math:`\sI = \{0, 1, \dots, n-1\}`, then
:math:`\underline{A}=\prod_{i=0}^{n-1} A_i` and the (curried) type of
:math:`f` is

.. math:: f: A_0 \to (A_1 \to (A_2 \to \cdots \to (A_{n-3} \to (A_{n-2} \to A_{n-1}))\cdots ).

 For a given :math:`a_0: A_0`, the function :math:`f` partially applied
at the first coordinate has type

.. math:: f(a_0): A_1 \to (A_2 \to \cdots \to (A_{n-3} \to (A_{n-2} \to A_{n-1}))\cdots ).

 To ease notation we will sometimes write function application by
juxtaposition so that :math:`f a_0 := f(a_0)`, for example. For elements
:math:`a_0` and :math:`a_1` inhabiting types :math:`A_0` and :math:`A_1`
(resp.), the partial application of :math:`f` to these elements yields
the following function : type pair

.. math:: f a_0 a_1 : A_2 \to (A_3 \to \cdots \to (A_{n-3} \to (A_{n-2} \to A_{n-1}))\cdots ).

 In general, for :math:`a_i: A_i`, :math:`0\leq i<\ell`,

.. math:: f a_0 a_1\dots a_{\ell-1}: A_\ell \to (A_{\ell+1} \to \cdots \to (A_{n-3} \to (A_{n-2} \to A_{n-1}))\cdots ).

It would be useful to have a means of partial function application in
case the domain :math:`\sI` is not simply :math:`\{0, 1, \dots, n-1\}`,
or in case we wish to partially apply a function to an arbitrary subset
of its operands (coordinates of its domain). If we have, as above,

-  :math:`\underline{\alg{A}} = \prod_{i: \sI} A_i`,

-  :math:`\sigma : J \to \sI` (one-to-one),

-  :math:`\ba \circ \sigma: \prod_{j: J} A_{\sigma(j)}`, for each
   :math:`\ba: \prod_{i: \sI} A_i`,

Let :math:`f` have type
:math:`\prod_{i: \sI} A_i \to \prod_{i: \sI} A_i`, which means that if
we apply :math:`f` to an element :math:`\ba:\prod_{i: \sI} A_i` the
result has the same type, that is,
:math:`f \ba: \ba:\prod_{i: \sI} A_i`. We may wish to apply :math:`f` to
just a portion of :math:`\ba` but it may not be the case that
:math:`\sI` is a subset of :math:`\N`, or an ordered enumeration of some
other set, so there is no natural notion of “the first :math:`\ell`
operands.” Even if there was such a notion, we may wish to partially
apply :math:`f` to something other than the first :math:`\ell` operands.
Therefore, we define a more general notion of partial application as
follows: :math:`f` partially applied to the coordinates
:math:`\im \sigma = \{\sigma(j) \mid j:J\}` of the element :math:`\ba`
gives the function : type pair

.. math::

   f \circ (a \circ \sigma): 
   \prod_{\substack{i: \sI\\ i\notin \im \sigma}} A_i \to \prod_{i: \sI} A_i.

Projections and compositions in Lean
------------------------------------

Directed sets, closure systems, Galois connections
==================================================

Directed sets and inductive sets
--------------------------------

A subset :math:`D` of a preorder is called **directed** if every finite
subset of :math:`D` has an upper bound in :math:`D`. That is, if
:math:`F\subseteq D` and :math:`F` is finite, then there exists
:math:`d\in D` such that :math:`f\leq d` for all :math:`f \in F`. A
subset :math:`I` of a preorder :math:`X` is called **inductive** if
:math:`{\Join_X}D\in I` for every directed subset :math:`D\subseteq X`
contained in :math:`I`. That is, if :math:`D\subseteq I`, and if every
finite subset of :math:`D` has an upper bound in :math:`D`, then
:math:`D` as a least upper bound in :math:`I`.

(This example appears as Remark 1.2.10
in :raw-latex:`\cite{MR1275826}`.) Let
:math:`X = \{0, 1, 2, \dots, n, n+1, \dots, \infty, \top\}` be the chain
with order relation satisfying
:math:`0\leq 1\leq 2\leq \cdots \leq n\leq n+1 \leq \cdots \leq \infty \leq \top`.
Let :math:`A = X -\{\infty\}` and :math:`D = X -\{\infty, \top\}`. (See
Figure [fig:noninductive].) Then :math:`{\Join_A}D` exists and is equal
to :math:`\top`, since the join is taken in :math:`A`. However,
:math:`{\Join_X} D = \infty \notin A`, so :math:`A` is not an inductive
subset of :math:`X`.

(0) at (0,-1) :math:`D`; (1) at (0,0) :math:`1`; (2) at (0,1) :math:`2`;
(3) at (0,2) :math:`3`; (4) at (0,3) :math:`4`; (5) at (0,3.75)
:math:`\vdots`; (1) – (2) – (3) – (4);

(0) at (0,-1) :math:`A`; (1) at (0,0) :math:`1`; (2) at (0,1) :math:`2`;
(3) at (0,2) :math:`3`; (4) at (0,3) :math:`4`; (5) at (0,3.75)
:math:`\vdots`; (6) at (0,5) :math:`\top`; (1) – (2) – (3) – (4);

(0) at (0,-1) :math:`X`; (1) at (0,0) :math:`1`; (2) at (0,1) :math:`2`;
(3) at (0,2) :math:`3`; (4) at (0,3) :math:`4`; (5) at (0,3.75)
:math:`\vdots`; (6) at (0,4.25) :math:`\infty`; (7) at (0,5)
:math:`\top`; (1) – (2) – (3) – (4); (6) – (7);

Completeness and cocompleteness
-------------------------------

The existence of meets and joins for certain kinds of subsets of a
preorder is known as completeness and cocompleteness respectively.
Suppose :math:`X` is a preorder and let :math:`P` be a **property of
subsets** of :math:`X`. Given a subset :math:`A\subseteq X`, denote by
:math:`P A` the judgement “:math:`A` has property :math:`P`”. If the
meet :math:`\Meet A` exists for every subset :math:`A \subseteq X` for
which :math:`P A` holds, then we say that :math:`X` is
**:math:`P`-complete**. Dually, :math:`X` is called
**:math:`P`-cocomplete** if the join :math:`\Join A` exists for every
subset :math:`A` with property :math:`P`. To take an example that will
be especially important for the purposes of these notes, suppose
:math:`X` is a preorder in which the joins of all directed subsets
exist. Then :math:`X` is called a **directed-cocomplete preorder**. If,
in addition, :math:`X` happens to be a poset, then :math:`X` is a
**directed-cocomplete partial order** or **dcpo**. If :math:`X` has
joins of all :math:`\omega`-chains, then :math:`X` is said to be
**:math:`\omega`-chain cocomplete**. We will refer to an
**:math:`\omega`-chain cocomplete partial order** as a
:math:`\omega`-cpo. Finally, if all meets in :math:`X` exist, then we
say :math:`X` is **complete**, and if all joins exist, then :math:`X` is
called **cocomplete**.

It is easy to see that a preorder is complete if and only if it is
cocomplete. Indeed, this follows from the next pair of equations, which
are direct consequences of the defintions of :math:`\Meet` and
:math:`\Join`:

.. math::

   {\Meet} A = {\Join}\{x \in X : x \leq A\} \qquad
   {\Join} A = {\Meet}\{x \in X : A \leq x\}.

A homomorphism of dcpos :math:`X` and :math:`Y` is a function
:math:`f: X \to Y` that preserves the structure of :math:`X`, which is
to say :math:`f` is monotone and if :math:`D \subseteq X` is directed,
then :math:`f(\Join D) =\Join f(D)`. (The join on the right hand side
exists since :math:`f` is monotone.) A homomorphism of
:math:`\omega`-cpos is defined analogously. A homomorphism of dcpos
(:math:`\omega`-cpos) will also be referred to as a **continuous
(:math:`\omega`-continuous)** function. If :math:`X` and :math:`Y` have
least elements, both denoted by :math:`\bot`, then any function
:math:`f: X \to Y` is said to be strict if :math:`f(\bot) = \bot`. If
:math:`X` is a dcpo then the subset :math:`A\subseteq X` is a
**subdcpo** of :math:`X` if every directed subset :math:`D` of :math:`X`
contained in :math:`A` satisfies :math:`\Join_X D \in A`. Thus if
:math:`A` is a subdcpo of :math:`X` and :math:`A` is given the
restriction order from :math:`X`, then the inclusion :math:`i: A \to X`
is a continuous function. Note also that if :math:`A\subseteq X` are
dcpos and if :math:`i: A \to X` is continuous, then :math:`A` is a
subdcpo of :math:`X`.

If :math:`X` is a poset, :math:`D` a directed subset of :math:`X`, and
if the join of :math:`D` in :math:`X` exists, then we denote the join of
:math:`D` by :math:`\bigsqcup_X D` rather than :math:`\Join_X D`. Part
of the force of the judgement :math:`\bigsqcup_X D` is that the set
:math:`D` is directed.

Closure systems
---------------

Let :math:`\mathfrak{X}` be a set and let :math:`\power{\mathfrak{X}}`
denote the collection of all subsets of :math:`\mathfrak{X}`. A
**closure operator** on :math:`\mathfrak{X}` is a set function
:math:`\sansC : \power{\mathfrak{X}}\rightarrow \power{\mathfrak{X}}`
satisfying, for all :math:`X, Y \in \power{\mathfrak{X}}`, conditions,

#. :math:`X \subseteq  \sansC(X)`,

#. :math:`\sansC \sansC = \sansC`,

#. :math:`Y \subseteq X \Longrightarrow \sansC(Y) \subseteq \sansC(X)`.

If :math:`\mfA` is a collection of algebras of the same type, let
:math:`\sansS \mfA` and :math:`\sansR \mfA` denote, respectively, the
collection of all subalgebras and retracts of algebras in :math:`\mfA`.

:math:`\sansS` is a closure operator on sets of algebras of the same
type.

If the retraction is defined as in ([eq:2]) above, then retraction
operator :math:`\sansR` is not a closure operator on sets of algebras of
the same type. However, if we take our definition of **retraction of
:math:`\alg{A} = \<A, F\>` via :math:`p\in \Pol_1(\alg{A})`** to be

.. math:: p(\alg{A}) = \<p(A), \{p \restr{f}{p(A)} : f \in F\}\>,

 then :math:`\sansR` is a closure operator.

Galois connections
------------------

**Todo: fill in this section.**

.. [1]
   Tuples are more commonly written with subscripts as in
   :math:`(a_0, a_1, \dots, a_{n-1})`, and we will adopt this convention
   when it is convenient, especially if the functional view is not
   relevant.

.. [2]
   In set theory we define :math:`n` to be the set
   :math:`\{0, 1, \dots, n-1\}`, but the notation :math:`[n]` for this
   set is a standard crutch that can sometimes help to avoid confusion.

.. [3]
   Usually :math:`\sI` will simply be :math:`[n] := \{0,1,\dots, n-1\}`.

.. [4]
   Note that our :math:`\Delta_\sigma` is the same as Kearnes’
   :math:`\eta_\sigma`, in the paper, “Idempotent Simple Algebras.”

.. [5]
   Sets would do for now, but we continue to mention algebras to help
   smooth the transition to material in later sections.
