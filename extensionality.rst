.. _extensionality:

.. index:: ! extensionality

.. highlight:: lean

Extensionality
==============

Attribution
-----------

This chapter takes as its starting point the `Axioms and Computation`_ section of the `Theorem Proving in Lean`_ tutorial.  Some material from that tutorial is repeated here for clarity and self-containment.

-------------------------------------------------

.. index:: proposition extensionality, function extensionality, law of the excluded middle, Choice
.. index:: extensional equality of; propositions
.. index:: extensional equality of; functions
.. index:: extensional equality of; sets

Classical and constructive reasoning
------------------------------------

The version of the :term:`Calculus of Inductive Constructions` (CiC) implemented in Lean includes :term:`dependent function types <dependent function type>`, :term:`inductive types <inductive type>`, and a hierarchy of :term:`universes` that starts with an :term:`impredicative` ``Prop`` type at the bottom.

Lean extends :term:`CiC` with additional axioms and rules in order to make proof construction easier and more versatile by making the language more expressive.

Adding axioms to a foundational system can have negative consequences, beyond concerns about correctness and consistency. In particular, whether or not our theorems and proofs have computational content depends on whether we abstain from the use of certain classical axioms, as we now discuss.

Lean is designed to support **classical reasoning** as well as **computational**, or **constructive reasoning**.

By adhering to a "computationally pure" fragment of logic, we enjoy guarantees that closed expressions in the system evaluate to :term:`canonical normal forms <canonical normal form>`. For example, any closed :term:`computationally pure` expression of type ℕ will reduce to a number.

The `Lean Standard Library`_ (:term:`LSL`) defines an additional axiom, :term:`proposition extensionality`, and a :term:`quotient` construction. These in turn imply the principle of :term:`function extensionality`.  These extensions are used to develop theories of sets and finite sets, but as we will see,

  *using such axiomatic extensions can block evaluation in Lean's kernel*

so that closed terms of type ℕ may no longer evaluate to numbers.

On the other hand,

  *Lean erases types and propositional information when compiling definitions to* :term:`bytecode` *for its virtual machine evaluator*,

and since these axioms only add new propositions, they admit a computational interpretation.

The :term:`LSL` supports the classical :term:`law of the excluded middle` (em) as an optional axiom.  We can invoke it if we explicitly open the classical fragment of the library with the line ``open classical``, and then we can write proofs that argue by case analysis on the two possible cases for a given proposition ``P``---either ``P`` or ``¬ P``.

.. proof:example::

   In classical logic, for all propositions ``P`` and ``Q`` the implication ``P → Q`` is equivalent to the disjunction ``¬ P ∨ Q``.  The left-to-right direction of this equivalence is proved in Lean using ``em``, as follows:

::

  open classical

  example (P Q: Prop) (f: P → Q): ¬ P ∨ Q :=
  or.elim (em P)
    (assume h: P, or.inr (f h))
    (assume h: ¬ P, or.inl h)

(Here's a brief dissection of the line ``or.elim (em P)`` from the last example, for the benefit of any Lean novices who are puzzled by it:
``or.elim`` means "apply the disjunction elimination rule" [1]_ to the disjunction ``em P``; the latter is ``P ∨ ¬ P`` and the final two lines handles each disjunct in turn.)

Like proposition extensionality, the use of :term:`em` may block evaluation in the Lean kernel, yet admit a computational interpretation after compilation to :term:`bytecode`.

The `Lean Standard Library`_ also defines a :term:`Choice` principle, but this principle is entirely antithetical to a computational interpretation since it magically produces "data" from a proposition that asserts the existence of Choice.

Use of :term:`Choice` is essential to some classical constructions and it can be imported in Lean when needed. However,

  *expressions that use Choice to produce data do not have any computational interpretation*.

Therefore, in Lean we must mark such definitions ``noncomputable``.

.. Diaconescu's theorem
.. ~~~~~~~~~~~~~~~~~~~~
.. A famous theorem of Diaconescu uses :term:`proposition extensionality`, :term:`function extensionality` and :term:`Choice` to derive the :term:`law of the excluded middle`. However, as noted above, use of :term:`em` is still compatible with :term:`bytecode` compilation and :term:`code extraction`, as are other classical principles, *as long as they are not used to manufacture data*.

To summarize, on top of the framework of :term:`universes`, :term:`dependent function types <dependent function type>`, and :term:`inductive types <inductive type>`, the :term:`LSL` adds three (optional) components:

+ the axiom of :term:`proposition extensionality`
+ a :term:`quotient` construction, which implies :term:`function extensionality`
+ a :term:`Choice` principle, which produces data from an existential proposition.

The first two of these are compatible with :term:`bytecode` evaluation, despite blocking normalization within Lean, whereas the third does not admit computational interpretations.

----------------------------------

Philosophical context
---------------------

It is widely accepted that computational considerations are important to mathematics, but there are different views about the best means of addressing these computational concerns.

+ *Constructively*, mathematics are not separate from their computational roots and every meaningful mathematical theorem should have a direct computational interpretation.

+ *Classically*, it is more fruitful to maintain a separation of mathematical and computational concerns. One (constructive) language may useful for *writing* computer programs, while nonconstructive theories and methods may be more useful when *reasoning* about such programs.

Lean is designed to support both of these approaches. Core parts of the library are developed constructively, but the system also provides support for carrying out classical mathematical reasoning.

  *Computationally, the purest part of dependent type theory avoids the use of the* ``Prop`` *type entirely*.

Introducing a proof-irrelevant ``Prop`` type and marking theorems irreducible represents a first step towards separation of concerns.

  *Inhabitants (i.e., proofs) of a proposition* ``p:Prop`` *should play no role in computation*,

and so the particular construction of a term (i.e., proof) ``t:p`` is "irrelevant" in that sense.

One can still define computational objects that incorporate elements of type ``Prop``, which can help us reason about the effects of the computation, but can be ignored when we extract "code" from the term.

Elements of type ``Prop`` are not entirely innocuous, however. They include equations ``s = t:α`` for any type ``α``, and such equations can be used as casts, to type check terms. Below, we will see examples of how such casts can block computation in the system.

However, computation is still possible under an evaluation scheme that

  1. erases propositional content,
  2. ignores intermediate typing constraints, and
  3. reduces terms until they reach a normal form.

This is precisely what Lean's virtual machine does.

If we adopt a proof-irrelevant ``Prop``, then we might consider it legitimate to use, for example, the :term:`law of the excluded middle` (em), ``∀ p:Prop, p ∨ ¬p``.  This can block computation in :term:`CiC`, but will not block :term:`bytecode` evaluation.

It is only the :term:`Choice` principle, discussed in more detail `here <https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#choice>`_, that completely erases the distinction between the :term:`proof-irrelevant` and :term:`data-relevant` parts of the theory.

--------------------------------------------

.. index:: ! proposition extensionality
.. index:: extensional equality of; propositions

.. _proposition-extensionality:

Proposition extensionality
~~~~~~~~~~~~~~~~~~~~~~~~~~

An extensionality axiom is an equivalence relation that represents some notion of equality.

The **proposition extensionality** axiom is a relation on propositions according to which two propositions are related (or extensionally equal) iff each implies the other.

This axiom is useful when reasoning about classes of :term:`logically equivalent` propositions, treating such classes as a single unit, rather than reasoning about each individual propositions.

::

  namespace extensionality
    -- BEGIN
    -- "proposition extensionality"
    axiom propext {a b: Prop}: (a ↔ b) → a = b
    -- END
  end extensionality

This principle is consistent with set-theoretic interpretations in which an element ``a:Prop`` is either empty or a singleton.  The axiom also has the consequence that equivalent propositions can be substituted for one another in every context.

::

  section
    variables a b c d e: Prop
    variable p: Prop → Prop

    example (h: a ↔ b): (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    example (h: a ↔ b) (h₁: p a): p b :=
    propext h ▸ h₁
  end

The first example could be proved without ``propext`` using the fact that the propositional connectives respect propositional equivalence.

The second example represents a more essential use of ``propext``. In fact, it is equivalent to ``propext`` itself. (Exercise!)

Given a definition or theorem in Lean, ``#print axioms`` will display the axioms on which it depends.

::

  variables a b c d e: Prop
  variable p: Prop → Prop

  theorem thm (h: a ↔ b): (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ iff.refl _

  #print axioms thm  -- propext

-----------------------------------

.. index:: ! function extensionality
.. index:: ! extensional equality of; functions
.. index:: intensional equality

.. _function-extensionality:

Function extensionality
~~~~~~~~~~~~~~~~~~~~~~~

The **function extensionality** axiom is the equivalence relation on functions according to which two functions of type ``Π(x:α), β x`` are extensionally equal if they agree on all inputs.

::

  #check @funext  -- ∀ {α: Sort u_1} {β: α → Sort u_2}
                  -- {f₁ f₂: Π (x: α), β x},
                  -- (∀ (x: α), f₁ x = f₂ x) → f₁ = f₂)

This is sometimes called "Leibniz equality" and it is usually taken for granted in the context of set theory and classical logic.

From a constructive perspective, a function is given by an algorithm, or computer program, that implements a specification of the function in a particular way.  Of course, two programs (i.e., functions) may output the same answer for every input, even if the syntax and performance characteristics of the programs are quite different.

In contrast to extensional equality, an :term:`intensional` view of functions does *not* identify two functions solely on the basis input/output behavior.

The reader may wish to think about notions of equality of functions that seem reasonable or natural.  Should two programs be considered "equal" provided they always return the same output when given the same input.  What if they eventually produce the same output but one takes milliseconds to complete, while the other takes a lifetime?

Evidently, there are a number of distinct notions of equality, and each may have its place.

-------------------------------------

.. index:: ! characteristic function, ! extensional equality (of sets)
.. index:: quotient

Extensionality in Lean
----------------------

Function extensionality follows from the existence of *quotients* (discussed in the next section) and in the :term:`LSL` the theorem ``funext`` is proved in the file `funext.lean <https://github.com/leanprover/lean/blob/master/library/init/funext.lean>`_ using the quotient construction.

Let ``α:Type`` and let ``set α := α → Prop`` represent the type of sets containing elements of type ``α`` (identifying subsets with predicates; see :numref:`Section %s <sets-in-lean>`).  In other terms, ``A: set α`` represents the **characteristic function** of the set ``A`` defined for all ``x:α`` by

.. math:: \mathsf{A\ x} = \begin{cases} \mathsf{true},& \text{ if $\mathsf x$ belongs to $\mathsf A$,}\\
                              \mathsf{false},& \text{ otherwise.}
                              \end{cases}

Thus, if we combine ``funext`` and ``propext``, we obtain an *extensional theory of subsets*, or **set extensionality**.  This means that two sets are equal when then contain the same elements, that is, when their characteristic functions are (extensionally) equal.

More precisely, ``A B: set α`` are (extensionally) equal iff their characteristic functions are (extensionally) equal iff for each ``x:α``, the propositions ``A x`` and ``B x`` are (extensionally) equal.

::

   namespace extensionality

     -- BEGIN
     universe u

     def set (α: Type u) := α → Prop

     def mem {α: Type u} (x: α) (a: set α) := a x
     notation e ∈ a := mem e a

     theorem setext {α: Type u} {a b: set α}
     (h: ∀ x, x ∈ a ↔ x ∈ b): a = b :=
     funext (assume x, propext (h x))

     -- END
   end extensionality


We can then define the empty set, ∅, as well as set intersection, union, etc. and then prove some set identities.

::

  namespace extensionality

    universe u

    def set (α: Type u) := α → Prop

    def mem {α: Type u} (x: α) (a: set α) := a x

    local notation e ∈ a := mem e a

    theorem setext {α: Type u} {a b: set α}
    (h: ∀ x, x ∈ a ↔ x ∈ b): a = b :=
    funext (assume x, propext (h x))

    -- BEGIN
    def empty {α: Type u} : set α := λ x, false

    local notation `∅` := empty

    def inter {α: Type u} (a b: set α): set α := λ x, x ∈ a ∧ x ∈ b

    local notation a ∩ b := inter a b

    theorem inter_self {α: Type u} (a: set α): a ∩ a = a :=
    setext (assume x, and_self _)

    theorem inter_empty {α: Type u} (a: set α): a ∩ ∅ = ∅ :=
    setext (assume x, and_false _)

    theorem empty_inter {α: Type u} (a: set α): ∅ ∩ a = ∅ :=
    setext (assume x, false_and _)

    theorem inter.comm {α: Type u} (a b : set α) : a ∩ b = b ∩ a :=
    setext (assume x, and_comm _ _)
    -- END

  end extensionality

The following is an example of how function extensionality can block computation in the Lean kernel. [2]_

::

  def f₁ (x: ℕ) := x
  def f₂ (x: ℕ) := 0 + x

  -- f₁ and f₂ are extensionally equal
  theorem feq: f₁ = f₂ := funext (assume x, (zero_add x).symm)

  -- cast 0: ℕ by replacing f₁ with f₂ in the type
  def val: ℕ := eq.rec_on feq (0: ℕ)

  -- complicated!
  #reduce val

  -- evaluates to 0
  #eval val

Of course, the cast is vacuous, because ``ℕ`` does not depend on ``f₁``. Nonetheless, under Lean's computational rules, the code above produces a closed term of type ``ℕ`` that does not reduce to a numeral.

In such cases, it's tempting to reduce the expression to ``0``, but in nontrivial examples

  *eliminating cast changes the type of the term*,

which might give an expression that is not of the expected type, but the virtual machine has no trouble evaluating it to ``0``.

The next example shows how ``propext`` can also block the kernel.

.. proof:example

   ::

     theorem tteq: (true ∧ true) = true := propext (and_true true)

     def val: ℕ := eq.rec_on tteq 0

     -- complicated!
     #reduce val

     -- evaluates to 0
     #eval val

Current research aims to extend type theory to permit reductions for casts involving function extensionality, quotients, and more. However, the solutions are not so obvious, and Lean's underlying calculus does not allow such reductions.

  *In a sense, a cast does not change the meaning of an expression. Rather, it is a mechanism to reason about the expression's type*.

Given an appropriate semantics, it makes sense to reduce terms in ways that preserve their meaning, ignoring the intermediate bookkeeping needed to make the reductions type check. Thus, adding new axioms in ``Prop`` does not matter; by proof irrelevance, an expression in ``Prop`` carries no information, and can be safely ignored by the reduction procedures.

-------------------------------------

.. rubric:: Footnotes

.. [1]
   :math:`∨\mathrm E`; see `Section 24 of Logic and Proof <https://leanprover.github.io/logic_and_proof/nd_quickref.html>`_.

.. [2]
   Like some of the other material in this chapter, this example is borrowed from the `Axioms and Computation`_ section of the `Theorem Proving in Lean`_ tutorial.

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

.. _Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/index.html

.. _Axioms and Computation: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#
