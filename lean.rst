.. include:: _static/math_macros.rst

======
 Lean
======
.. Contents of Preliminaries Chapter
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


We now describe how many of the concepts of sets and types discussed in the last two chapters are implemented in the Lean language.

Many of the implementations shown here also appear in the following files in the `Lean standard library <lean_src>`_ and the `Lean Mathlib <mathlib>`_:

+ set.lean_
+ basic.lean_
+ lattice.lean_

-----------------------------------------------

Sets in Lean
------------

If ``α`` is a type, then Lean provides the type ``set α``, which represents the type of **sets of elements of type** ``α``.

This is naturally implemented as a function type.  Indeed, the type ``set α`` is simply an alias for the type ``α → Prop``.

Thus, a set ``A`` of elements of type ``α`` would be denoted by ``A: set α``.

We say "``x`` belongs to ``A``", and write ``x ∈ A``, if and only if the proposition ``A x`` holds (i.e., has a proof, say, ``h: A x``).

.. _intersection-and-union:

Intersection and union
~~~~~~~~~~~~~~~~~~~~~~

Let ``S`` be a family of sets of type :math:`α`.

In lattice.lean_, the **intersection** of the sets in ``S`` is denoted by ``⋂₀ S``. [1]_

.. code-block:: lean

   import data.set
   variable S : set (set α)
   #check ⋂₀ S          -- answer: set α

Here is the formal definition from the file lattice.lean_.

.. code-block:: lean

    /-- Intersection of a set of sets. -/
    @[reducible]
    def sInter (S : set (set α)) : set α := Inf S

    prefix `⋂₀`:110 := sInter

The **union of sets** is implemented in lattice.lean_ similarly.

.. code-block:: lean

   @[reducible]
   def sUnion (s : set (set α)) : set α := {t | ∃ a ∈ s, t ∈ a}
   prefix `⋃₀`:110 := sUnion

-------------------------------------------

.. index:: relation, binary relation, preorder, partial order, equivalence relation
.. index:: domain, range

.. index:: equivalence relation, partial ordering
.. index:: pair: partially ordered set; poset

.. _relations-in-lean:

Relations in Lean
------------------

In the last chapter, we noted that set theorists think of a binary relation :math:`R` on a set :math:`A` as a set of ordered pairs, so that :math:`R(a, b)` really means :math:`(a, b) \in R`. An alternative is to think of :math:`R` as a function which, when applied to :math:`a` and :math:`B`, returns the proposition that :math:`R(a, b)` holds. This is the viewpoint adopted by Lean: a binary relation on a type ``A`` is a function ``A → A → Prop``. Remember that the arrows associate to the right, so ``A → A → Prop`` really means ``A → (A → Prop)``. So, given ``a : A``, ``R a`` is a predicate (the property of being related to ``A``), and given ``a b : A``, ``R a b`` is a proposition.

With first-order logic, we can say what it means for a relation to be reflexive, symmetric, transitive, and antisymmetric, as follows:

.. code-block:: lean

    namespace hidden

    variable {A : Type}

    def reflexive (R : A → A → Prop) : Prop :=
    ∀ x, R x x

    def symmetric (R : A → A → Prop) : Prop :=
    ∀ x y, R x y → R y x

    def transitive (R : A → A → Prop) : Prop :=
    ∀ x y z, R x y → R y z → R x z

    def antisymmetric (R : A → A → Prop) : Prop :=
    ∀ x y, R x y → R y x → x = y

    end hidden

We can then use the notions freely. Notice that Lean will unfold the definitions when necessary, for example, treating ``reflexive R`` as ``∀ x, R x x``.

.. code-block:: lean

    namespace hidden
    variable {A : Type}
    def reflexive (R : A → A → Prop) : Prop := ∀ x, R x x
    def symmetric (R : A → A → Prop) : Prop := ∀ x y, R x y → R y x
    def transitive (R : A → A → Prop) : Prop := ∀ x y z, R x y → R y z → R x z
    def antisymmetric (R : A → A → Prop) : Prop := ∀ x y, R x y → R y x → x = y

    -- BEGIN
    variable R : A → A → Prop

    example (h : reflexive R) (x : A) : R x x := h x

    example (h : symmetric R) (x y : A) (h1 : R x y) : R y x :=
    h x y h1

    example (h : transitive R) (x y z : A) 
    (h1 : R x y) (h2 : R y z) : R x z :=
    h x y z h1 h2

    example (h : antisymmetric R) (x y : A) 
    (h1 : R x y) (h2 : R y x) : x = y :=
    h x y h1 h2
    -- END

    end hidden

.. index:: implicit argument

In the command ``variable {A : Type}``, we put curly braces around ``A`` to indicate that it is an **implicit argument**, which is to say that you don't have to write it explicitly; Lean can infer it from the argument ``R``. That is why we can write ``reflexive R`` rather than ``reflexive A R``: since ``R`` is a binary relation on ``A``, Lean_ can infer that ``reflexive R`` refers to reflexivity of a binary relation ``R`` on ``A``.

Given ``h : transitive R``, ``h1 : R x y``, and ``h2 : R y z``, it is annoying to have to write ``h x y z h1 h2`` to prove ``R x z``. After all, Lean should be able to use the fact that ``h1`` is ``R x y`` and ``h2`` is ``R y z`` to infer that we are talking about transitivity at ``x``, ``y``, and ``z``. Indeed it can and as a result we can replace that information by underscores.

.. code-block:: lean

    namespace hidden
    variable {A : Type}
    def transitive (R : A → A → Prop) : Prop := ∀ x y z, R x y → R y z → R x z

    -- BEGIN
    variable R : A → A → Prop

    example (h : transitive R) (x y z : A)
    (h1 : R x y) (h2 : R y z) : R x z :=
    h _ _ _ h1 h2
    -- END

    end hidden

But typing underscores is annoying, too. The best solution is to declare the arguments ``x y z`` to a transitivity hypothesis to be implicit as well:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    variable {A : Type}

    def transitive (R : A → A → Prop) : Prop :=
    ∀ {x y z}, R x y → R y z → R x z

    variable R : A → A → Prop

    example (h : transitive R) (x y z : A)
    (h1 : R x y) (h2 : R y z) : R x z :=
    h h1 h2

    -- END

    end hidden

In fact, the notions ``reflexive``, ``symmetric``, ``transitive``, and ``antisymmetric`` are defined in Lean's core library in exactly this way, so we are free to use them without defining them. (That is why we put our temporary definitions of in a namespace ``hidden``; that means that the full name of our version of ``reflexive`` is ``hidden.reflexive``, which, therefore, doesn't conflict with the one defined in the library.)

Preorders and equivalences in Lean
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In :numref:`equivalence-relation` we saw that an *equivalence relation* is a symmetric preorder; that is, a reflexive, symmetric, and transitive binary relation. We will define such a relation in Lean shortly, but first let's define preorder and use this definition to define equivalence relation.

Recall, a **preorder** is a reflexive and transitive binary relation.

.. code-block:: lean

    namespace hidden

    variable {A : Type}

    def preorder (R : A → A → Prop) : Prop :=
    reflexive R ∧ transitive R

    end hidden

Lean's library provides a different formulation of preorders, so, in order to use the same name, we have to put it in the ``hidden`` namespace. Lean's library defines other properties of relations, such as these:

.. code-block:: lean

    namespace hidden

    variables {A : Type} (R : A → A → Prop)

    def equivalence := reflexive R ∧ symmetric R ∧ transitive R

    def total := ∀ x y, R x y ∨ R y x

    def irreflexive := ∀ x, ¬ R x x

    def antisymmetric := ∀ ⦃x y⦄, R x y → R y x → x = y

    end hidden

You can ask Lean to print their definitions:

.. code-block:: lean

    #print equivalence
    #print total
    #print irreflexive
    #print anti_symmetric

Building on our previous definition of a preorder, we can describe a partial order as an antisymmetric preorder, and show that an equivalence relation as a symmetric preorder.

.. code-block:: lean

    namespace hidden
    variable {A : Type}

    def preorder (R : A → A → Prop) : Prop :=
    reflexive R ∧ transitive R

    def partial_order (R : A → A → Prop) : Prop :=
    preorder R ∧ anti_symmetric R

    example (R : A → A → Prop):
      equivalence R ↔ preorder R ∧ symmetric R :=
    iff.intro
      (assume h1 : equivalence R,
        have h2 : reflexive R, from and.left h1,
        have h3 : symmetric R, from and.left (and.right h1),
        have h4 : transitive R, from and.right (and.right h1),
        show preorder R ∧ symmetric R,
          from and.intro (and.intro h2 h4) h3)
      (assume h1 : preorder R ∧ symmetric R,
        have h2 : preorder R, from and.left h1,
        show equivalence R,
          from and.intro (and.left h2)
                 (and.intro (and.right h1) (and.right h2)))

    end hidden

We previously claimed that another way to define *equivalence relation* is as a binary relation satisfying

  #. :math:`\forall a \ (a ≡ a)`, and
  #. :math:`\forall a, b, c \ (a ≡ b ∧ c ≡ b \ → \ a ≡ c)`.

Let's prove this now. Remember that the ``parameters`` and ``local infix`` commands fix a relation ``R`` and introduce the symbol ``≈`` to denote it. 

(``≈`` is typed ``\~~`` or ``\approx``.) In the assumptions ``reflexive (≈)`` and ``symmetric (≈)``, the notation ``(≈)`` denotes ``R``.

.. code-block:: lean

    namespace hidden

    def preorder {A : Type} (R : A → A → Prop) : Prop :=
    reflexive R ∧ transitive R

    -- BEGIN
    section
    parameters {A : Type} (R : A → A → Prop)
    local infix ≈ := R

    variable (h1 : reflexive (≈))
    variable (h2 : ∀ {a b c}, a ≈ b ∧ c ≈ b → a ≈ c)

    example : symmetric (≈) :=
    assume a b (h : a ≈ b),
    have b ≈ b ∧ a ≈ b, from and.intro (h1 b) h,
    show b ≈ a, from h2 this

    example : transitive (≈) :=
    assume a b c (h3 : a ≈ b) (h4 : b ≈ c),
    have c ≈ b, from h2 (and.intro (h1 c) h4),
    have a ≈ b ∧ c ≈ b, from and.intro h3 this,
    show a ≈ c, from h2 this

    end
    -- END

    end hidden

Partial orders in Lean
~~~~~~~~~~~~~~~~~~~~~~

.. todo:: insert Lean definition

The poset induced by a preorder
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

..     The poset induced by a preorder

Total and strict orders in Lean
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

..   Equality
..   Relations of higher arity
..   Functions
..   Joins and meets
..   Projections
..   Directed sets and inductive sets
..   Completeness and cocompleteness
..   Closure systems

In :numref:`total-and-strict-ordering` we showed that a strict partial order---that is, a transitive and irreflexive binary relation. Here is a proof of that fact in Lean.

.. code-block:: lean

    variable A : Type
    variable R : A → A → Prop

    example (h1 : irreflexive R) (h2 : transitive R) :
      ∀ x y, R x y → ¬ R y x :=
    assume x y,
    assume h3 : R x y,
    assume h4 : R y x,
    have h5 : R x x, from h2 h3 h4,
    have h6 : ¬ R x x, from h1 x, 
    show false, from h6 h5

In mathematics, it is common to use infix notation and a symbol like ``≤`` to denote a partial order. Lean supports this practice:
 
.. code-block:: lean

    section
    parameter A : Type
    parameter R : A → A → Prop

    local infix ≤ := R

    example (h1 : irreflexive R) (h2 : transitive R) : 
      ∀ x y, x ≤ y → ¬ y ≤ x :=
    assume x y,
    assume h3 : x ≤ y,
    assume h4 : y ≤ x,
    have h5 : x ≤ x, from h2 h3 h4,
    have h6 : ¬ x ≤ x, from h1 x, 
    show false, from h6 h5

    end

The ``parameter`` and ``parameters`` commands are similar to the ``variable`` and ``variables`` commands, except that parameters are fixed within a section. In other words, if you prove a theorem about ``R`` in the section above, you cannot apply that theorem to another relation, ``S``, without closing the section. Since the parameter ``R`` is fixed, Lean allows us to define notation for ``R`` to be used locally in the section.

In the example below, having fixed a partial order, ``R``, we define the corresponding strict partial order and prove that it is, indeed, a strict order.

.. code-block:: lean

    section
    parameters {A : Type} (R : A → A → Prop)
    parameter (reflR : reflexive R)
    parameter (transR : transitive R)
    parameter (antisymmR : ∀ {a b : A}, R a b → R b a → a = b)

    local infix ≤ := R

    definition R' (a b : A) : Prop := a ≤ b ∧ a ≠ b

    local infix < := R'

    theorem irreflR (a : A) : ¬ a < a :=
    assume : a < a,
    have a ≠ a, from and.right this,
    have a = a, from rfl,
    show false, from ‹a ≠ a› ‹a = a›

    theorem transR {a b c : A} (h₁ : a < b) (h₂ : b < c) : a < c :=
    have a ≤ b, from and.left h₁,
    have a ≠ b, from and.right h₁,
    have b ≤ c, from and.left h₂,
    have b ≠ c, from and.right h₂,
    have a ≤ c, from transR ‹a ≤ b› ‹b ≤ c›,
    have a ≠ c, from
        assume : a = c,
        have c ≤ b, from eq.subst ‹a = c› ‹a ≤ b›,
        have b = c, from antisymmR ‹b ≤ c› ‹c ≤ b›,
        show false, from ‹b ≠ c› ‹b = c›,
    show a < c, from and.intro ‹a ≤ c› ‹a ≠ c›
    end

Notice that we have used suggestive names ``reflR``, ``transR``, ``antisymmR`` instead of ``h1``, ``h2``, ``h3`` to help remember which hypothesis is which. The proof also uses anonymous ``have`` and ``assume``, referring back to them with the French quotes, ``\f<`` anf ``\f>``. Remember also that ``eq.subst ‹a = c› ‹a ≤ b›`` is a proof of the fact that amounts for substituting ``c`` for ``a`` in ``a ≤ b``. You can also use the equivalent notation ``‹a = c› ▸ ‹a ≤ b›``, where the triangle is written ``\t``.

Here is one more example. Suppose ``R`` is a binary relation on a type ``A``, and we define ``S x y`` to mean that both ``R x y`` and ``R y x`` holds. Below we show that the resulting relation is reflexive and symmetric.

.. code-block:: lean

    section
    parameter A : Type
    parameter R : A → A → Prop

    variable h1 : transitive R
    variable h2 : reflexive R

    def S (x y : A) := R x y ∧ R y x

    example : reflexive S :=
    assume x,
    have R x x, from h2 x,
    show S x x, from and.intro this this

    example : symmetric S :=
    assume x y,
    assume h : S x y,
    have h1 : R x y, from h.left,
    have h2 : R y x, from h.right,
    show S y x, from ⟨h.right, h.left⟩

    end

As an exercise, the reader should prove in Lean that ``S`` is transitive as well.

In the first example, we use the anonymous ``assume`` and ``have``, and then refer back to the ``have`` with the keyword ``this``. In the second example, we abbreviate ``and.left h`` and ``and.right h`` as ``h.left`` and ``h.right``, respectively. We also abbreviate ``and.intro h.right h.left`` with an anonymous constructor, writing ``⟨h.right, h.left⟩``. Lean figures out that we are trying to prove a conjunction, and figures out that ``and.intro`` is the relevant introduction principle. You can type the corner brackets with ``\<`` and ``\>``, respectively.




.. .. index:: ! ordered tuples, !tuples
.. .. index:: ! unary relation, ! binary relation, ! ternary relation

.. Orderings on numbers
.. ~~~~~~~~~~~~~~~~~~~~

.. Conveniently, Lean has the normal orderings on the natural numbers, integers, and so on defined already.

.. .. code-block:: lean

..     open nat
..     variables n m : ℕ

..     #check 0 ≤ n
..     #check n < n + 1

..     example : 0 ≤ n := zero_le n
..     example : n < n + 1 := lt_succ_self n

..     example (h : n + 1 ≤ m) : n < m + 1 :=
..     have h1 : n < n + 1, from lt_succ_self n,
..     have h2 : n < m, from lt_of_lt_of_le h1 h,
..     have h3 : m < m + 1, from lt_succ_self m,
..     show n < m + 1, from lt.trans h2 h3

.. There are many theorems in Lean that are useful for proving facts about inequality relations. We list some common ones here.

.. .. code-block:: lean

..     variables (A : Type) [partial_order A]
..     variables a b c : A

..     #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
..     #check (lt_trans : a < b → b < c → a < c)
..     #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
..     #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
..     #check (le_of_lt : a < b → a ≤ b)

.. Here the declaration at the top says that ``A`` has the structure of a partial order. There are also properties that are specific to some domains, like the natural numbers:

.. .. code-block:: lean

..     variable n : ℕ

..     #check (nat.zero_le : ∀ n : ℕ, 0 ≤ n)
..     #check (nat.lt_succ_self : ∀ n : ℕ, n < n + 1)
..     #check (nat.le_succ : ∀ n : ℕ, n ≤ n + 1)

Relations of higher arity
~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

---------------------------------

.. index:: function, inverse, function composition, restriction, image

Functions in Lean
------------------

.. todo:: complete this section

.. index:: projection, idempotent operation

.. _projections-in-lean:

Projections
~~~~~~~~~~~

.. todo:: complete this section

.. index:: generalized projection

Generalized projection
~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section

.. index:: kernel

Kernel
~~~~~~

.. todo:: complete this section

-------------------------------------

.. index:: join, upper bound, least upper bound, supremum
.. index:: meet, lower bound, greatest lower bound, infimum

Joins and meets
---------------

.. todo:: complete this section

------------------------------

.. .. index:: product

.. .. _products-in-lean:

.. Products in Lean
.. -----------------

.. Recall, the **Cartesian product** of two sets :math:`A_0` and :math:`A_1`, denoted :math:`A_0 × A_1`, is the set of all ordered pairs :math:`(a_0, a_1)` such that :math:`a_0 ∈ A_0` and :math:`a_1 ∈ A_1`. That is, :math:`A_0 × A_1 := \{(a_0, a_1) ∣ a_0 ∈ A_0, a_1 ∈ A_1\}`.

.. More generally, :math:`A_0 × \cdots × A_{n-1}` is the set of sequences of length :math:`n` with :math:`i`-th element in :math:`A_i`. That is,

.. .. math:: A_0 × \cdots × A_{n-1} := \{(a_0, \dots,  a_{n-1}) ∣ a_0 ∈ A_0, \dots, a_{n-1} ∈ A_{n-1}\}.

.. Another way to view :math:`A_0 × \cdots × A_{n-1}` is as the set of all functions with domain :math:`\{0, 1, \dots, n-1\}` and range :math:`⋃_{i<n} A_i`. More generally still, the **Cartesian product** of an indexed family of sets, :math:`\{A_i : i ∈ I\}`, is the set of all functions with domain :math:`I` and range :math:`⋃_{i ∈ I} A_i` such that :math:`f(i) ∈ A_i`. That is,

.. .. math:: ∏_{i∈I} A_i := \{f: I → ⋃_{i∈I} A_i | f(i) ∈ A_i\}.

.. When :math:`A_0 = A_1 = \cdots = A`, we write :math:`A^2 := A × A` and :math:`A^n := A × \cdots × A` (:math:`n` factors), and refer to these as **Cartesian powers** of
.. :math:`A`.

.. .. proof:question::

..    How do you know :math:`∏_{i∈I} A_i ≠ ∅`, even supposing :math:`I ≠ ∅` and :math:`A_i ≠ ∅` for all :math:`i ∈ I`? [2]_

.. .. todo:: complete this section, adding Lean code

.. -------------------------------------------------

.. index:: dependent types

.. _dependent-types-in-lean:

Dependent types in Lean
------------------------

.. todo:: complete this section

.. index:: type of; dependent functions (Pi type)

.. _pi-type:

Pi Type
~~~~~~~

The **Pi type** ``Π(x:A),B x``, also known as the **dependent function type**, generalizes the function type ``A → B`` and is called a *dependent type* because the codomain ``B x`` may depend on the value ``x: A``.

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
    { f | ∀ a ∈ i, f a ∈ s a }

.. index:: type of; dependent pairs (Sigma type)

.. _sigma-type:

Sigma Type
~~~~~~~~~~~

The **Sigma type** ``Σ(x:A),B x``, also known as the **dependent pair type**, generalizes the Cartesian product ``A × B`` by allowing the type ``B x`` of the second argument of the ordered pair to depend on the value ``x`` of the first.

.. code-block:: lean

    structure sigma {α : Type u} (β : α → Type v) :=
    mk :: (fst : α) (snd : β fst)

    structure psigma {α : Sort u} (β : α → Sort v) :=
    mk :: (fst : α) (snd : β fst)

------------------------------

.. index:: dependent type theory, inductive type, universes

.. _inductive-types-in-lean:

Inductive types in Lean
------------------------

.. todo:: complete this section

----------------------------------

.. rubric:: Footnotes

.. [1]
   The symbol ``⋂`` is produced by typing ``\bigcap``, and the ``0`` subscript is obtained by typing ``\0``.

.. .. [2]
..    **Answer**. Each :math:`f` "chooses" an element from each :math:`A_i`, but when the :math:`A_i` are distinct and :math:`I` is infinite, we may not be able to do this. The :ref:`Axiom of Choice <axiom-of-choice-1>` ("Choice") says you can. Gödel proved that Choice is consistent with the other axioms of set theory. Cohen proved that the negation of Choice is also consistent.

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


