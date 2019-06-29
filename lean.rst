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

Many of the implementations shown here also appear in the following files in the `Lean Standard Library`_ (:term:`LSL`) and the `Lean Mathlib <mathlib>`_:

+ set.lean_
+ basic.lean_
+ lattice.lean_

-----------------------------------------------

.. _sets-in-lean:

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
   variables (α : Type) (S : set (set α))

   #check ⋂₀ S          -- answer: set α

Here is the formal definition of ``sInter`` from the file lattice.lean_.

::

   @[reducible]
   def sInter (S: set (set α)): set α := Inf S

   prefix `⋂₀`:110 := sInter

The **union of sets** is implemented in lattice.lean_ similarly.

::

   @[reducible]
   def sUnion (s: set (set α)): set α := {t | ∃ a ∈ s, t ∈ a}

   prefix `⋃₀`:110 := sUnion

-------------------------------------------

.. index:: relation, binary relation, preorder
.. index:: domain, range

Relations in Lean
------------------

.. _binary-relations-in-lean:

Binary relations
~~~~~~~~~~~~~~~~

In the last chapter, we noted that set theorists think of a binary relation :math:`R` on a set :math:`A` as a set of ordered pairs, so that :math:`R(a, b)` really means :math:`(a, b) \in R`. An alternative is to think of :math:`R` as a function which, when applied to :math:`a` and :math:`B`, returns the proposition that :math:`R(a, b)` holds. This is the viewpoint adopted by Lean: a binary relation on a type ``A`` is a function ``A → A → Prop``. Remember that the arrows associate to the right, so ``A → A → Prop`` really means ``A → (A → Prop)``. So, given ``a: A``, ``R a`` is a predicate (the property of being related to ``A``), and given ``a b: A``, ``R a b`` is a proposition.

With first-order logic, we can say what it means for a relation to be reflexive, symmetric, transitive, and antisymmetric, as follows:

.. highlight:: lean

::

   namespace prelim
     section
       parameters {A: Type} (R: A → A → Prop)

       def reflexive: Prop := ∀ x, R x x

       def symmetric: Prop := ∀ x y, R x y → R y x

       def transitive: Prop := ∀ x y z, R x y → R y z → R x z

       def antisymmetric: Prop := ∀ x y, R x y → R y x → x = y
     end
   end prelim

We can then use the notions freely. Notice that Lean will unfold the definitions when necessary, for example, treating ``reflexive R`` as ``∀ x, R x x``.
Also, in ``parameters {A: Type}``, we use curly braces to indicate that ``A`` is an **implicit argument**, thus you don't have to write it explicitly.

Lean can infer from the argument ``R``, which is a binary relation on ``A``, that ``reflexive R`` really means ``reflexive A R``.

::

  namespace prelim
    section
      parameters {A: Type} (R: A → A → Prop)
      def reflexive: Prop := ∀ x, R x x
      def symmetric: Prop := ∀ x y, R x y → R y x
      def transitive: Prop := ∀ x y z, R x y → R y z → R x z
      def antisymmetric: Prop := ∀ x y, R x y → R y x → x = y

  -- BEGIN
  example (h: reflexive R) (x: A): R x x := h x

  example (h: symmetric R) (x y: A)
  (h₁: R x y): R y x := h x y h₁

  example (h: transitive R) (x y z: A)
  (h₁: R x y) (h₂: R y z): R x z :=
  h x y z h₁ h₂

  example (h: antisymmetric R) (x y: A)
  (h₁: R x y) (h₂: R y x): x = y:=
  h x y h₁ h₂
  -- END
    end

   end prelim

.. index:: implicit argument

In one of these examples we show ``R x z`` follows from the assumptions ``h: transitive R`` and ``h₁: R x y`` and ``h₂: R y z``. This is done using the proof term ``h x y z h₁ h₂``. But Lean_ could use the fact that ``h₁`` is ``R x y`` and ``h₂`` is ``R y z`` to infer that we are talking about transitivity at ``x``, ``y`` and ``z``, so we should not need to mention these variable names explicitly.  Indeed, we can replace them with underscores.

::

  namespace prelim

    def transitive {A: Type} (R: A → A → Prop): Prop :=
    ∀ x y z, R x y → R y z → R x z

    example {A: Type} (R: A → A → Prop)
    (h: transitive R) (x y z: A) (h₁: R x y) (h₂: R y z): R x z :=
    h _ _ _ h₁ h₂

  end prelim

But typing underscores is annoying; we should make ``x y z`` implicit arguments so that the underscores are unnecessary.

::

  namespace prelim

    def transitive {A: Type} (R: A → A → Prop): Prop :=
    ∀ {x y z}, R x y → R y z → R x z

    example {A: Type} (R: A → A → Prop) (h: transitive R) (x y z: A)
    (h₁: R x y) (h₂: R y z): R x z := h h₁ h₂

  end prelim

In fact, the notions ``reflexive``, ``symmetric``, ``transitive``, and ``antisymmetric`` are defined in Lean's core library in exactly this way, so we are free to use them without defining them and we can (must) leave off the implicit parameters.

It is possible to provide the implicit parameters explicitly, but then the ``@`` prefix must be used, as follows:

::

  example {A : Type} (R: A → A → Prop)
  (h: transitive R) (x y z: A) (h₁: R x y) (h₂: R y z): R x z :=
  @h x y z h₁ h₂


.. index:: preorder, equivalence relation, total order relation, irreflexive relation, antisymmetric relation

.. _preorders-and-equivalences-in-lean:

Preorders and equivalences
~~~~~~~~~~~~~~~~~~~~~~~~~~

In :numref:`equivalence-relation` we learned that an *equivalence relation* is a symmetric preorder, or, equivalently, a reflexive, symmetric, and transitive binary relation. We will define such a relation in Lean shortly, but first let's define preorder.

Recall, a *preorder* is a reflexive and transitive binary relation.

::

  namespace prelim

    def preorder {A: Type} (R: A → A → Prop): Prop :=
    reflexive R ∧ transitive R

  end prelim

Lean's library provides a different formulation of preorders, so, in order to use the same name, we have to put it in the ``prelim`` namespace. The Lean library also defines other properties of relations, such as these:

::

  namespace prelim

    def equivalence {A: Type} (R: A → A → Prop) :=
    reflexive R ∧ symmetric R ∧ transitive R

    def total {A: Type} (R: A → A → Prop) :=
    ∀ x y, R x y ∨ R y x

    def irreflexive {A: Type} (R: A → A → Prop) :=
    ∀ x, ¬ R x x

    def antisymmetric {A: Type} (R: A → A → Prop) :=
    ∀ ⦃x y⦄, R x y → R y x → x = y

  end prelim

(In the standard library, the latter is actually named ``anti_symmetric``.)

Lean will print the definitions of these (as defined in the standard library) if given the commands

::

  #print equivalence
  #print total
  #print irreflexive
  #print anti_symmetric

An equivalent way to define **equivalence relation** is as a binary relation on :math:`A` satisfying,

  #. :math:`∀ a ∈ A \ (a ≡ a)`, and
  #. :math:`∀ a, b, c ∈ A \ (a ≡ b ∧ c ≡ b \ → \ a ≡ c)`.

Let's prove this now. First recall that the commands

::

  parameters {A: Type} (R: A → A → Prop)
  local infix ≈ := R

fix a relation ``R`` and introduce the symbol ``≈`` to denote it. Thus, in the assumptions ``reflexive (≈)`` and ``symmetric (≈)``, the notation ``(≈)`` denotes ``R``.

(The symbol ``≈`` is produced by typing ``\~~`` or ``\approx``; see :numref:`symbols`.)

::

  namespace prelim

    def preorder {A: Type} (R: A → A → Prop): Prop :=
    reflexive R ∧ transitive R

    section
      parameters {A: Type} (R: A → A → Prop)
      local infix ≈ := R

      variable (h₁: reflexive (≈))
      variable (h₂: ∀ {a b c}, a ≈ b ∧ c ≈ b → a ≈ c)

      -- We will show that a relation satisfying h₁ and
      -- h₂ must also be symmetric and transitive, hence,
      -- an equivalence relation.

      example: symmetric (≈) :=
      assume a b (h: a ≈ b),
      have b ≈ b ∧ a ≈ b, from and.intro (h₁ b) h,
      show b ≈ a, from h₂ this

      example: transitive (≈) :=
      assume a b c (h₃: a ≈ b) (h₄: b ≈ c),
      have c ≈ b, from h₂ (and.intro (h₁ c) h₄),
      have a ≈ b ∧ c ≈ b, from and.intro h₃ this,
      show a ≈ c, from h₂ this
    end

  end prelim

Finally, we prove that an equivalence relation (defined as a reflexive, symmetric, transitive, binary relation) is a symmetric preorder, as claimed above.

::

  namespace prelim

    def preorder {A: Type} (R: A → A → Prop): Prop :=
    reflexive R ∧ transitive R

    example {A: Type} (R: A → A → Prop):
    equivalence R ↔ preorder R ∧ symmetric R :=
    iff.intro
      (assume h₁: equivalence R,
        have h₂: reflexive R, from and.left h₁,
        have h₃: symmetric R, from and.left (and.right h₁),
        have h₄: transitive R, from and.right (and.right h₁),
        show preorder R ∧ symmetric R,
          from and.intro (and.intro h₂ h₄) h₃)
      (assume h₁: preorder R ∧ symmetric R,
        have h₂: preorder R, from and.left h₁,
        show equivalence R,
          from and.intro (and.left h₂)
                 (and.intro (and.right h₁) (and.right h₂)))

  end prelim

.. _quotients-in-lean:

Quotients
~~~~~~~~~~

.. todo:: add section on quotients in Lean

.. _partial-orders-in-lean:

Partial orders
~~~~~~~~~~~~~~

Building on our Lean definition of :term:`preorder`, we can define a :term:`partial order` in Lean as an antisymmetric preorder.

::

  namespace prelim

    def preorder {A : Type} (R : A → A → Prop) : Prop :=
    reflexive R ∧ transitive R

    def partial_order {A : Type} (R : A → A → Prop) : Prop :=
    preorder R ∧ anti_symmetric R

  end prelim

.. _the-poset-induced-by-a-preorder-in-lean:

The poset induced by a preorder
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: complete this section after completing :numref:`quotients-in-lean`.

..     The poset induced by a preorder

.. _total-and-strict-orders-in-lean:

Total and strict orders
~~~~~~~~~~~~~~~~~~~~~~~

In :numref:`total-and-strict-ordering` we showed that a strict partial order---that is, a transitive and irreflexive binary relation. Here is a proof of that fact in Lean.

::

  example {A: Type} (R: A → A → Prop) 
  (h₁: irreflexive R) (h₂: transitive R):
  ∀ x y, R x y → ¬ R y x :=
  assume x y (h₃: R x y) (h₄: R y x),
  have h₅: R x x, from h₂ h₃ h₄,
  have h₆: ¬ R x x, from h₁ x,
  show false, from h₆ h₅

In mathematics, it is common to use infix notation and a symbol like ``≤`` to denote a partial order. Lean supports this practice:

::

  section
    parameters {A : Type} (R : A → A → Prop)

    local infix ≤ := R

    example (h₁: irreflexive ≤) (h₂: transitive ≤):
    ∀ x y, x ≤ y → ¬ y ≤ x :=
    assume x y (h₃: x ≤ y) (h₄: y ≤ x),
    have h₅: x ≤ x, from h₂ h₃ h₄,
    have h₆: ¬ x ≤ x, from h₁ x,
    show false, from h₆ h₅
  end

The ``parameter`` and ``parameters`` commands are similar to the ``variable`` and ``variables`` commands, except that parameters are fixed within a section. In other words, if you prove a theorem about ``R`` in the section above, you cannot apply that theorem to another relation, ``S``, without closing the section. Since the parameter ``R`` is fixed, Lean allows us to define notation for ``R`` to be used locally in the section.

In the example below, having fixed a partial order, ``R``, we define the corresponding strict partial order and prove that it is, indeed, a strict order.

::

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

Notice that we have used suggestive names ``reflR``, ``transR``, ``antisymmR`` to help remember which hypothesis is which.

The proof also uses anonymous ``have`` and ``assume``, referring back to them with the French quotes (produced by typing ``\f<`` and ``\f>``; see :numref:`symbols`).

Remember also that ``eq.subst ‹a = c› ‹a ≤ b›`` is a proof of the fact that amounts for substituting ``c`` for ``a`` in ``a ≤ b``. You can also use the equivalent notation ``‹a = c› ▸ ‹a ≤ b›``, where the triangle is written ``\t``.

Here is one more example. Suppose ``R`` is a binary relation on a type ``A``, and we define ``S x y`` to mean that both ``R x y`` and ``R y x`` holds. Below we show that the resulting relation is reflexive and symmetric.

::

  section
    parameters {A: Type} (R: A → A → Prop)

    variable h₁: transitive R
    variable h₂: reflexive R

    def S (x y: A) := R x y ∧ R y x

    example: reflexive S :=
    assume x,
    have R x x, from h₂ x,
    show S x x, from and.intro this this

    example: symmetric S :=
    assume x y,
    assume h: S x y,
    have h₁: R x y, from h.left,
    have h₂: R y x, from h.right,
    show S y x, from ⟨h.right, h.left⟩
  end

As an exercise, the reader should prove in Lean that ``S`` is transitive as well.

In the first example, we use the anonymous ``assume`` and ``have``, and then refer back to the ``have`` with the keyword ``this``.

In the second example, we abbreviate ``and.left h`` and ``and.right h`` as ``h.left`` and ``h.right``, respectively. We also abbreviate ``and.intro h.right h.left`` with an anonymous constructor, writing ``⟨h.right, h.left⟩``. Lean figures out that we are trying to prove a conjunction, and figures out that ``and.intro`` is the relevant introduction principle.

(You can produce angled brackets by typing ``\<`` and ``\>``; see :numref:`symbols`.)

.. _equality-in-lean:

Equality
~~~~~~~~

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
..     have h\_1 : n < n + 1, from lt_succ_self n,
..     have h\_2 : n < m, from lt_of_lt_of_le h\_1 h,
..     have h\_3 : m < m + 1, from lt_succ_self m,
..     show n < m + 1, from lt.trans h\_2 h\_3

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

.. index:: join, upper bound, least upper bound, supremum
.. index:: meet, lower bound, greatest lower bound, infimum

Joins and meets
~~~~~~~~~~~~~~~~

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

.. _Lean Standard Library: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/


