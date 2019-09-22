.. include:: _static/math_macros.rst

.. highlight:: lean

.. _lean-basics:

========================
Appendix. Lean Basics
========================

In this appendix we describe the various features and aspects of Lean_ on which the lean-ualib_ depends.

Some of the topics discussed here will come from the Lean_ standard library.  Others will be from the mathlib_ Lean community project, and possible other projects.

Some good references for this material are

  + `Lean Tutorial <https://leanprover.github.io/tutorial/>`_
  + `Theorem Proving in Lean`_
  + `Lean Reference Manual`_
  + `Logic and Proof`_

------------------------------------------------

.. _leans-type-hierarchy:

Lean's type hierarchy
----------------------

(See also the section of the `Lean Tutorial`_ called `Universe Levels <http://leanprover.github.io/tutorial/06_Inductive_Types.html>`_.)

Like its more mature cousins Coq and Agda, Lean_ takes for its logical foundations *dependent type theory* with *inductive types* and a countable hierarchy of *universes*. However, unlike Coq or Agda, Lean's universes are *non-cumulative*. This is not a problem since, in places where we might exploit universe cumulativity in Coq, we can instead use :term:`universe polymorphism` and lifting constructions.

Sort and Type
~~~~~~~~~~~~~

The following excerpt from the `Lean Reference Manual`_ explains the correspondence between ``Sort`` and ``Type``.

  Every type in Lean is, by definition, an expression of type ``Sort u`` for some universe level ``u``. A universe level is one of the following:

  + a natural number, ``n``
  + a universe variable, ``u`` (declared with the command universe or universes)
  + an expression ``u + n``, where ``u`` is a universe level and ``n`` is a natural number
  + an expression ``max u v``, where ``u`` and ``v`` are universes
  + an expression ``imax u v``, where ``u`` and ``v`` are universe levels

  The last one denotes the universe level 0 if ``v`` is 0, and ``max u v`` otherwise.

  .. code-block:: lean

     universes u v                    -- Lean Output
                                      -- -----------
     #check Sort u                    -- Sort u : Type u
     #check Sort 5                    -- Type 4 : Type 5
     #check Sort (u + 1)              -- Type u : Type (u+1)
     #check Sort (u + 3)              -- Type (u+2) : Type (u+3)
     #check Sort (max u v)            -- Sort (max u v) : Type (max u v)
     #check Sort (max (u + 3) v)      -- Sort (max (u+3) v) : Type (max (u+3) v)
     #check Sort (imax (u + 3) v)     -- Sort (imax (u+3) v) : Type (imax (u+3) v)
     #check Prop                      -- Prop : Type
     #check Type                      -- Type : Type 1

.. index:: keyword: Type, Type 0, Type 1, ...

Lean_ has a hierarchy of :math:`\omega`-many type universe levels. We want some operations to be *polymorphic* over type universes.

For example, ``list α`` should make sense for any type ``α``, no matter which universe ``α`` lives in. This explains why ``list`` has the following type signature:

.. code-block:: lean

   #check @list    -- answer: Type u → Type u

Here ``u`` is a variable ranging over type levels.

Think of ``Type 0`` as a universe of "small" or "ordinary" types. ``Type 1`` is then a larger universe of types that contains ``Type 0`` as an *element*, and ``Type 2`` is an even larger universe of types, that contains ``Type 1`` as an element. The list is indefinite, so that there is a ``Type n`` for every natural number ``n``. ``Type`` is an abbreviation for ``Type 0``.

.. index:: ! predicative, ! ramified, ! impredicative
.. index:: keyword: Prop

The upshot of this **ramified** arrangement is that the types described in the last paragraph are :term:`predicative`, which means that their definitions are not self-referential. By avoiding self-referential definitions, we avoid Russel's paradox. However, in certain specific situations we *do* want to employ a self-referential type, so Lean_ supplies us with exactly one. It is the type ``Prop`` of propositions, and it is :term:`impredicative` (self-referential).

------------------

.. _implicit-arguments:

Implicit arguments
------------------

Lean's support of implicit arguments and type-inference is quite powerful and extremely helpful. The `TPL`_ sections on `Implicit Arguments`_ and `More on Implicit Arguments`_ explain this topic in detail.  In the present section we merely collect a few fine points and technicalities that come up in `lean-ualib`_.

By default, Lean inserts, and eagerly tries to infer the type of, the implicit argument.  For example,

::

  -- Aggressive type inference.

  definition id₁ {α: Type} (x: α): α := x

  #check id₁    -- ℕ → ℕ

In this case, Lean seems a bit presumptuous since the type ``α`` is not known, so there's no evidence for the typing judgments ``x: ℕ`` nor ``id₁: ℕ → ℕ``.

If we instead use double curly braces ``{{ … }}``, or their unicode equivalents ``⦃ … ⦄``, this tells the parser to be more conservative about inserting the argument and inferring its type. [2]_

::

  -- Conservative type inference.

  definition id₂ ⦃α: Type⦄ (x: α): α := x

  #check id₂     -- Π ⦃α: Type⦄, α → α

------------------------------------------------

.. _pattern-matching:

Pattern matching
----------------

.. todo:: complete this section

------------------------------------------------

.. _the-elaboration-engine:

Elaboration engine
------------------

On top of the Lean_ kernel there is a powerful *elaboration engine* that can

#. infer implicit universe variables;

#. infer implicit arguments, using higher order unification;

#. support overloaded notation or declarations;

#. insert coercions;

#. infer implicit arguments using type classes;

#. convert readable proofs to proof terms

#. construct terms using tactics

Lean_ does most of these things simultaneously. For example, the term constructed by type classes can be used to find out implicit arguments for functions.

(For a nice overview of the elaboration engine, see this `2015 post by Floris van Doorn`_.)

----------------------------------------------------------

.. _type-classes:

Type Classes
-------------

The `chapter on Type Classes <https://leanprover.github.io/theorem_proving_in_lean/type_classes.html>`_ in `TPL`_ provides a nice explanation of **type classes**.  Here we excerpt a few highlights from that chapter.

"Any family of types can be marked as a type class. We can then declare particular elements of a type class to be instances. These provide hints to the elaborator: any time the elaborator is looking for an element of a type class, it can consult a table of declared instances to find a suitable element.

"More precisely, there are three steps involved:

+ First, we declare a family of inductive types to be a type class.
+ Second, we declare instances of the type class.
+ Finally, we mark some implicit arguments with square brackets instead of curly brackets, to inform the elaborator that these arguments should be inferred by the type class mechanism."

See the `chapter on Type Classes <https://leanprover.github.io/theorem_proving_in_lean/type_classes.html>`_ in `TPL`_ for more details.

----------------------------------------------------------

.. _coercion:

Coercion
--------

**References**. `Coercions`_ and `Coercions using Type Classes`_ sections of `TPL`_

A very nice feature of Lean, called coercion, enables us to identify two objects that we think of as "the same" but that are of different types. This kind of thing happens implicitly in virtually all informal mathematical arguments.

Here's a simple example. Suppose we have an integer :math:`z : ℤ` and a natural number :math:`n : ℕ`.  Most people would not hesitate to form the sum :math:`z + n`.  Of course, this doesn't make sense since (in type theory as well as set theory), natural numbers are not integers!  That is, :math:`ℕ ⊈ ℤ`, despite what your highschool math teacher told you.

However, it is true that the set of natural numbers can be embedded in ℤ in a natural way, and Lean_ allows us to express this embedding using coercions.

Here's how the example just discussed is handled in Lean_.

.. code-block:: lean

   variable n : ℕ
   variable z : ℤ
   #check z + n      -- z + ↑n : ℤ

Indeed, the addition is handled automatically in this case.  But notice the coercion symbol ``↑`` that appears in the output of ``#check``. The up arrow is notation for the Lean_ function ``coe``; it can be typed with ``\u``, but ``coe`` could be used instead.

In fact, an explicit ``↑`` must appear in certain cases, in particular when Lean_ is not aware in advance that a coercion is needed.

If we change the order of the arguments of ``#check`` in the example above, we get an error unless we tell Lean_ about the required coercion.

.. code-block:: lean

   -- #check n + z        -- error!
   #check ↑n + z          -- ↑n + z : ℤ

Lean_ allows various kinds of coercions using type classes; for details, see the `Coercions using Type Classes`_ section of `TPL`_.

In our ``algebra`` type, we used ``has_coe_to_sort`` and ``has_coe_to_fun``. The definitions of these in the Lean_ library are as follows:

.. code-block:: lean

   class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
   (S : Sort v) (coe : a → S)

   class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
   (F : a → Sort v) (coe : Π x, F x)


----------------------------------------------------------

.. _metaprogramming:

Metaprogramming
---------------

Lean_ is easy to extend via **metaprogramming**. Briefly, a :term:`metaprogram` is a program whose purpose is to modify the behavior of other programs. :term:`Proof tactics <proof tactic>` form an important class of metaprograms.

An nice feature of Lean_ is that *metaprograms can be written in the Lean language* itself, rather that in the lower level language (C/C++) that was used to create Lean. Thus the metaprogramming language is the same logical language that we use to express specifications, propositions, and proofs.

--------------------------

Comparison of ITPs
------------------

The following popular :term:`ITPs <ITP>` are all based on some flavor of :term:`dependent type` theory.  One may distinguish them by the philosophical and foundational assumptions on which they are based. Two basic criterion along these lines are whether they are :term:`intensional` or :term:`extensional` and whether they are :term:`predicative` or :term:`impredicative`.  All four of these languages support :term:`dependent types <dependent type>`.

Agda_ is an :term:`intensional`, :term:`predicative` :term:`ITP` developed at Chalmers University in (Göteborg).  It is based on Martin Lof :term:`type theory`.

.. ; url: https://wiki.portal.chalmers.se/agda/pmwiki.php .

Coq_ is an :term:`intensional`, :term:`impredicative` :term:`ITP` developed at INRIA in France.  It is based on :term:`CiC`.

.. ; url: http://coq.inria.fr .

NuPRL_ is an :term:`extensional`, :term:`predicative` :term:`ITP` developed at Cornell University in Ithaca (USA).  It is based on Martin Lof :term:`type theory`.

.. ; url: http://www.nuprl.org/

Lean_ is an :term:`extensional`, :term:`impredicative` :term:`ITP` developed at Microsoft Research and Carnegie Mellon University (USA). It is based on :term:`CiC`.

.. ; url: https://leanprover.github.io/

.. + NuPRL_ . :term:`extensional`, :term:`predicative`
.. + Coq_ .  :term:`intensional`, :term:`impredicative`
.. + Agda_ . :term:`intensional`, :term:`predicative`
.. + Lean_  :term:`extensional`, :term:`impredicative`


-------------------------------------------------

.. index:: dependent type

.. _dependent-types-in-lean:

Dependent types
---------------

.. todo:: complete this section

.. index:: ! type of; dependent functions (Pi type)

.. _pi-type:

Pi Type
~~~~~~~

The **Pi type**

  ``Π(x:A),B x``

is called a **dependent function type**. It generalizes the (nondependent) function type ``A → B``.

To see why ``Π(x:A),B x`` is a *dependent type*, consider the following example: a function ``f: Π(x:A),B x`` implies for each ``a:A`` the typing judgment ``f a: B a``, where the type ``B a`` *depends* on the value ``a``.

::

  variables {α : Type*} {π : α → Type*}

  def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
  { f | ∀ a ∈ i, f a ∈ s a }

.. index:: ! type of; dependent pairs (Sigma type)

.. _sigma-type:

Sigma Type
~~~~~~~~~~~

The **Sigma type**

  ``Σ(x:A),B x``

is called a **dependent pair type**.  It generalizes the Cartesian product ``A × B``.

To see why ``Σ(x:A),B x`` is a *dependent type*, consider the following example: a pair ``(a,b): Σ(x:A),B x`` implies the typing judgments ``a:A`` and ``b: B a``, where the type ``B a`` *depends* on the value ``a``.

::

  structure sigma {α : Type u} (β : α → Type v) :=
  mk :: (fst : α) (snd : β fst)

  structure psigma {α : Sort u} (β : α → Sort v) :=
  mk :: (fst : α) (snd : β fst)

------------------------------

.. index:: dependent type theory, inductive type, universes

.. _inductive-types-in-lean:

Inductive types
---------------

.. todo:: complete this section

----------------------------------

.. index:: ! extensionality

.. _extensionality:

Extensionality
---------------

This section takes as its starting point the `Axioms and Computation`_ section of the `Theorem Proving in Lean`_ tutorial.  Some material from that tutorial is repeated here for clarity and to keep this section self-contained.

.. index:: proposition extensionality, function extensionality, law of the excluded middle, Choice
.. index:: extensional equality of; propositions
.. index:: extensional equality of; functions
.. index:: extensional equality of; sets

Classical and constructive reasoning
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The version of the :term:`Calculus of Inductive Constructions` (CiC) implemented in Lean includes :term:`dependent function types <dependent function type>`, :term:`inductive types <inductive type>`, and a countable hierarchy of universes that starts with the :term:`impredicative` ``Prop`` type at the bottom. (See :numref:`leans-type-hierarchy` for more details about Lean's type hierarchy.)

Lean extends the :term:`CiC` with additional axioms and rules in order to make the language more expressive and versatile so that the statements of theorems and the constructions of proofs are simpler and more elegant.

Adding axioms to a foundational system can have negative consequences, beyond concerns about correctness and consistency. In particular, whether the theorems and proofs expressed in the extended system have computational content depends on whether we abstain from the use of certain classical axioms.

Lean is designed to support **classical reasoning** as well as **computational** (or **constructive**) **reasoning**.

By adhering to a "computationally pure" fragment of logic, we enjoy guarantees that closed expressions in the system evaluate to :term:`canonical normal forms <canonical normal form>`. For example, every closed computationally pure expression of type ℕ will reduce to a number.

Two axioms that the `Lean Standard Library`_ (:term:`LSTL`) adds to :term:`CiC` are :term:`proposition extensionality` and a :term:`quotient` construction, which in turn imply the principle of :term:`function extensionality`.  These extensions are used to develop theories of sets and finite sets, but as we will see,

  *using such axiomatic extensions can block evaluation in Lean's kernel*

so that closed terms of type ℕ may no longer evaluate to numbers.

On the other hand,

  *Lean erases types and propositional information when compiling definitions to* :term:`byte-code` *for its virtual machine evaluator*,

and since these axioms only add new propositions, they admit a computational interpretation.

The :term:`LSTL` supports the classical :term:`law of the excluded middle` (em) as an optional axiom that the user can assume when necessary.  We can invoke ``em`` if we explicitly open the classical fragment of the library with the directive ``open classical``, and then we can write proofs that argue by case analysis on the two possible cases for a given proposition ``P``, that is, either ``P`` or ``¬ P``.

.. proof:example::

   In classical logic, for all propositions ``P`` and ``Q`` the implication ``P → Q`` is equivalent to the disjunction ``¬ P ∨ Q``.  The left-to-right direction of this equivalence is proved in Lean using ``em``, as we now show.

.. index:: elimination rule; (for disjunction)

::

  open classical

  example (P Q: Prop): (P → Q) → ¬ P ∨ Q :=
  assume f: P → Q,
  or.elim (em P)
    (assume h: P, or.inr (f h))
    (assume h: ¬ P, or.inl h)

(Here's a brief dissection of the line ``or.elim (em P)`` from the last example, for the benefit of Lean novices who might be puzzled by it: ``or.elim`` means "apply the **disjunction elimination** rule", :math:`∨\mathrm E`.  [4]_  In this case, we apply :math:`∨\mathrm E` to the disjunction ``em P``, that is, ``P ∨ ¬ P``, and the final two lines handle each disjunct in turn.)

.. proof:example::

   On the other hand, the converse of the example above---that is, ``¬ P ∨ Q → (P → Q)``---can be proved without the help of classical axioms, so the code below need not be preceded by ``open classical``.

::

  example (P Q: Prop): ¬ P ∨ Q → (P → Q) :=
  assume (h: ¬ P ∨ Q) (p: P), show Q, from
  or.elim h
    (assume np: ¬ P, false.elim (np p))
    (assume q : Q, q)


Like proposition extensionality, the use of :term:`em` may block evaluation in the Lean kernel, yet admit a computational interpretation after compilation to :term:`byte-code`.

The `Lean Standard Library`_ also defines a :term:`Choice` principle, but this principle is entirely antithetical to a computational interpretation since it magically produces "data" from a proposition that asserts the existence of Choice.

Use of :term:`Choice` is essential to some classical constructions and it can be imported in Lean when needed. However,

  *expressions that use Choice to produce data do not have any computational interpretation*.

Therefore, in Lean we must mark such definitions ``noncomputable``.

.. Diaconescu's theorem
.. ~~~~~~~~~~~~~~~~~~~~
.. A famous theorem of Diaconescu uses :term:`proposition extensionality`, :term:`function extensionality` and :term:`Choice` to derive the :term:`law of the excluded middle`. However, as noted above, use of :term:`em` is still compatible with :term:`bytecode` compilation and :term:`code extraction`, as are other classical principles, *as long as they are not used to manufacture data*.

To summarize, on top of the framework of universes, :term:`dependent function types <dependent function type>`, and :term:`inductive types <inductive type>`, the :term:`LSTL` adds three (optional) components:

+ the axiom of :term:`proposition extensionality`
+ a :term:`quotient` construction, which implies :term:`function extensionality`
+ a :term:`Choice` principle, which produces data from an existential proposition.

The first two of these are compatible with :term:`byte-code` evaluation, despite blocking normalization within Lean, whereas the third does not admit computational interpretations.

Philosophical context
~~~~~~~~~~~~~~~~~~~~~~~~

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

If we adopt a proof-irrelevant ``Prop``, then we might consider it legitimate to use, for example, the :term:`law of the excluded middle` (em), ``∀ p:Prop, p ∨ ¬p``.  This can block computation in :term:`CiC`, but will not block :term:`byte-code` evaluation.

It is only the :term:`Choice` principle, discussed in more detail `here <https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#choice>`_, that completely erases the distinction between the :term:`proof-irrelevant` and :term:`data-relevant` parts of the theory.

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
    -- proposition extensionality
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

This is sometimes called :term:`Leibniz equality <Leibniz equal>` and it is usually taken for granted in the context of set theory and classical logic.

From a constructive perspective, a function is given by an algorithm, or computer program, that implements a specification of the function in a particular way.  Of course, two programs (i.e., functions) may output the same answer for every input, even if the syntax and performance characteristics of the programs are quite different.

In contrast to extensional equality, an :term:`intensional` view of functions does *not* identify two functions solely on the basis input/output behavior.

The reader may wish to think about notions of equality of functions that seem reasonable or natural.  Should two programs be considered "equal" provided they always return the same output when given the same input.  What if they eventually produce the same output but one takes milliseconds to complete, while the other takes a lifetime?

Evidently, there are a number of distinct notions of equality, and each may have its place.

To gain some familiarity with function extensionality in Lean, we will dissect the `funext.lean <https://github.com/leanprover/lean/blob/master/library/init/funext.lean>`_ program of the `Lean Standard Library`_, including the proof of the ``funext`` theorem, which states that function extensionality *is* equality of functions in Lean; in other words, two functions are equal iff they are :term:`Leibniz equal` (i.e., they give the same output for each input).

To do this requires that we understand *quotients* and *setoids*---two concepts that we cover in the next chapter---so we postpone our dissection of the ``funext`` program until :numref:`proof-of-funext`.

.. index:: ! characteristic function, ! extensional equality (of sets)
.. index:: quotient

Extensionality in Lean
~~~~~~~~~~~~~~~~~~~~~~~

Function extensionality follows from the existence of *quotients* (discussed in detail in :numref:`quotients`) and in the :term:`LSTL` the theorem ``funext`` is proved in the file `funext.lean <https://github.com/leanprover/lean/blob/master/library/init/funext.lean>`_ using the quotient construction.  (We will dissect the `funext.lean`_ program in :numref:`proof-of-funext` below.)

Let ``α:Type`` and let ``set α := α → Prop`` represent the type of sets containing elements of type ``α`` (identifying subsets with predicates; see :numref:`Section %s <sets-in-lean>`).

In other terms, ``A: set α`` represents the **characteristic function** of the set ``A`` defined for all ``x:α`` by

.. math:: \mathsf{A\ x} = \begin{cases} \mathsf{true},& \text{ if $\mathsf x$ belongs to $\mathsf A$,}\\
                              \mathsf{false},& \text{ otherwise.}
                              \end{cases}

Thus, if we combine ``funext`` and ``propext``, we obtain an *extensional theory of subsets*, or **set extensionality**.  This means that two sets are equal when then contain the same elements, that is, when their characteristic functions are (extensionally) equal.

More precisely, ``A B: set α`` are equal iff their characteristic functions are equal iff for each ``x:α``, the propositions ``A x`` and ``B x`` are equal.  (Here, each occurrence of "equal" is understood to mean "extensionally equal".)

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

The following is an example of how function extensionality can block computation in the Lean kernel. [3]_

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

-----------------------------------

.. rubric:: Footnotes

.. [2]
   On some systems, typing ``\{{`` and hitting the spacebar produces both left and right double curly braces---i.e., ``⦃ ⦄``.   On other systems, perhaps the ``\}}`` is needed for the closing ``⦄`` symbol. If neither works, the ascii symbols ``{{`` and ``}}`` may be used instead.

.. [3]
   The symbol ``⋂`` is produced by typing ``\bigcap``, and the ``0`` subscript is obtained by typing ``\0``.

.. [4]
   see, e.g., `Section 24 of Logic and Proof <https://leanprover.github.io/logic_and_proof/nd_quickref.html>`_.


.. .. [2]
..    **Answer**. Each :math:`f` "chooses" an element from each :math:`A_i`, but when the :math:`A_i` are distinct and :math:`I` is infinite, we may not be able to do this. The :ref:`Axiom of Choice <axiom-of-choice-1>` ("Choice") says you can. Gödel proved that Choice is consistent with the other axioms of set theory. Cohen proved that the negation of Choice is also consistent.

.. include:: hyperlink_references.rst





