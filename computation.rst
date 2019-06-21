.. _axioms_and_computation:

Computation
===========

References and attributions
----------------------------

In this chapter, we take as a starting point the chapter `Axioms and Computation`_ from the book `Theorem Proving in Lean`_.  Some of the background material from that chapter is repeated here to keep our presentation self-contained.

-------------------------------------------------

.. index:: proposition extensionality, quotient, function extensionality, law of the excluded middle, Choice

Classical and constructive reasoning
------------------------------------

The version of the :term:`Calculus of Inductive Constructions` (CiC) implemented in Lean includes :term:`dependent function types <dependent function type>`, :term:`inductive types <inductive type>`, and a hierarchy of :term:`universes` that starts with an :term:`impredicative` ``Prop`` type at the bottom.

Lean extends :term:`CiC` with additional axioms and rules in order to make proof construction easier and more versatile by making the language more expressive.

Adding axioms to a foundational system can have negative consequences, beyond concerns about correctness and consistency. In particular, whether or not our theorems and proofs have computational content depends on whether we abstain from the use of certain classical axioms, as we now discuss.

Lean is designed to support **classical reasoning** as well as **computational**, or **constructive reasoning**.

By adhering to a "computationally pure" fragment of logic, we enjoy guarantees that closed expressions in the system evaluate to :term:`canonical normal forms <canonical normal form>`. For example, any closed :term:`computationally pure` expression of type ℕ will reduce to a number.

`Lean's standard library <lean_src>`_ defines an additional axiom, :term:`proposition extensionality`, and a :term:`quotient` construction. These in turn imply the principle of :term:`function extensionality`.  These extensions are used to develop theories of sets and finite sets, but as we will see,

  *using such axiomatic extensions can block evaluation in Lean's kernel*

so that closed terms of type ℕ may no longer evaluate to numbers.

On the other hand, 

  *Lean erases types and propositional information when compiling definitions to :term:`bytecode` for its virtual machine evaluator*, 

and since these axioms only add new propositions, they admit a computational interpretation.

One may also assume a classical axiom called the :term:`law of the excluded middle` (em).  Like extensionality, :term:`em` may block evaluation in the Lean kernel, yet admit a computational interpretation after compilation to :term:`bytecode`.

The `standard library <lean_src>`_ also defines a :term:`Choice` principle, but this principle is entirely antithetical to a computational interpretation since it magically produces "data" from a proposition that asserts the existence of Choice.

Use of :term:`Choice` is essential to some classical constructions and it can be imported in Lean when needed. However,

  *expressions that use Choice to produce data do not have any computational interpretation*.

Therefore, in Lean we must mark such definitions ``noncomputable``.

.. Diaconescu's theorem
.. ~~~~~~~~~~~~~~~~~~~~
.. A famous theorem of Diaconescu uses :term:`proposition extensionality`, :term:`function extensionality` and :term:`Choice` to derive the :term:`law of the excluded middle`. However, as noted above, use of :term:`em` is still compatible with :term:`bytecode` compilation and :term:`code extraction`, as are other classical principles, *as long as they are not used to manufacture data*.

To summarize, on top of the framework of :term:`universes`, :term:`dependent function types <dependent function type>`, and :term:`inductive types <inductive type>`, the `standard library <lean_src>`_ adds three (optional) components:

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

  *Computationally, the purest part of dependent type theory avoids the use of the ``Prop`` type entirely*.

Introducing a proof-irrelevant ``Prop`` type and marking theorems irreducible represents a first step towards separation of concerns.

  *Inhabitants (i.e., proofs) of a proposition ``p : Prop`` should play no role in computation*,

and so the particular construction of a term (i.e., proof) ``t : p`` is "irrelevant" in that sense.

One can still define computational objects that incorporate elements of type ``Prop``, which can help us reason about the effects of the computation, but can be ignored when we extract "code" from the term.

Elements of type ``Prop`` are not entirely innocuous, however. They include equations ``s = t : α`` for any type ``α``, and such equations can be used as casts, to type check terms. Below, we will see examples of how such casts can block computation in the system.

However, computation is still possible under an evaluation scheme that

  1. erases propositional content, 
  2. ignores intermediate typing constraints, and 
  3. reduces terms until they reach a normal form.

This is precisely what Lean's virtual machine does.

If we adopt a proof-irrelevant ``Prop``, then we might consider it legitimate to use, for example, the :term:`law of the excluded middle` (em), ``∀ p: Prop, p ∨ ¬p``.  This can block computation in :term:`CiC`, but will not block :term:`bytecode` evaluation.

It is only the :term:`Choice` principle, discussed in more detail `here <https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#choice>`_, that completely erases the distinction between the :term:`proof-irrelevant` and :term:`data-relevant` parts of the theory.

--------------------------------------------

.. index:: ! proposition extensionality

Proposition extensionality
--------------------------

The **proposition extensionality** axiom is a relation that identifies propositions that mutually imply each other.  Thus, proposition extensionality is a principle we use when we wish to reason about classes of such "logically equivalent" propositions, rather than considering each individual proposition separately.

.. highlight:: lean

::

  namespace propext
    -- BEGIN
    -- Proposition extensionality
    axiom propext {a b: Prop}: (a ↔ b) → a = b
    -- END
  end propext

This principle is consistent with set-theoretic interpretations in which an element ``a: Prop`` is either empty or a singleton.  The axiom also has the consequence that equivalent propositions can be substituted for one another in every context.

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

.. code-block:: lean

    variables a b c d e : Prop
    variable p : Prop → Prop

    theorem thm (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    #print axioms thm  -- propext

-----------------------------------

Function extensionality
-----------------------

The **function extensionality** principle is an equivalence relation on functions that equates two functions of type ``Π(x:α), β x`` that agree on all inputs.

.. code-block:: lean

    universes u₁ u₂

    #check (@funext : ∀ {α : Type u₁} {β : α → Type u₂} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂)

This :term:`extensional` view of equality of functions is sometimes called "Leibniz equality" and it is usually taken for granted in the context of set theory and classical logic.  From a constructive perspective, however, it is more natural to think of a function as an algorithm, or computer programs, that is presented in some explicit (constructive) way.

It is certainly the case that two computer programs can compute the same answer for every input despite the fact that their syntax and performance characteristics may be quite different.  Are these computer programs really "equal?"

A view of functions that does not force us to identify two functions with the same input/output behavior is known as an :term:`intensional` view of functions.


-------------------------------------

Extensionality in Lean
----------------------

Function extensionality follows from the existence of *quotients*, as describe in the next section. In the `standard library <lean_src>`_, therefore, ``funext`` is `proved from the quotient construction <https://github.com/leanprover/lean/blob/master/library/init/funext.lean>`__.

Let ``α: Type`` and define ``set α := α → Prop`` to denote the type of subsets of ``α`` (identifying subsets with predicates).

By combining ``funext`` and ``propext``, we obtain an extensional theory of subsets.

.. code-block:: lean

    namespace hidden

    -- BEGIN
    universe u

    def set (α : Type u) := α → Prop

    namespace set

    variable {α : Type u}

    definition mem (x : α) (a : set α) := a x
    notation e ∈ a := mem e a

    theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
    funext (assume x, propext (h x))

    end set
    -- END
    end hidden

We can then proceed to define the empty set, set intersection, etc. and then prove some set identities.

::

  namespace computation

    universe u
    definition set (α : Type u) := α → Prop

    namespace set

      variable {α : Type u}

      def mem (x : α) (a : set α) := a x

      instance has_mem_set (α : Type u) : has_mem α (set α) := ⟨mem⟩

      theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
      funext (assume x, propext (h x))

      definition empty : set α := λ x, false
      local notation `∅` := empty

      definition inter (a b : set α) : set α := λ x, x ∈ a ∧ x ∈ b

      notation a ∩ b := inter a b

      theorem inter_self (a : set α) : a ∩ a = a :=
      setext (assume x, and_self _)

      theorem inter_empty (a : set α) : a ∩ ∅ = ∅ :=
      setext (assume x, and_false _)

      theorem empty_inter (a : set α) : ∅ ∩ a = ∅ :=
      setext (assume x, false_and _)

      theorem inter.comm (a b : set α) : a ∩ b = b ∩ a :=
      setext (assume x, and_comm _ _)

    end set
    end computation

The following is an example of how function extensionality blocks computation inside the Lean kernel.

.. code-block:: lean

    def f₁  (x : ℕ) := x
    def f₂ (x : ℕ) := 0 + x

    theorem feq : f₁ = f₂ := funext (assume x, (zero_add x).symm)

    def val : ℕ := eq.rec_on feq (0 : ℕ)

    -- complicated!
    #reduce val

    -- evaluates to 0
    #eval val

First, we show that the two functions ``f₁`` and ``f₂`` are equal using function extensionality, and then we cast ``0`` of type ``ℕ`` by replacing ``f₁`` by ``f₂`` in the type. Of course, the cast is vacuous, because ``ℕ`` does not depend on ``f₁``. But that is enough to do the damage: under the computational rules of the system, we now have a closed term of ``ℕ`` that does not reduce to a numeral. In this case, we may be tempted to reduce the expression to ``0``. But in nontrivial examples, eliminating cast changes the type of the term, which might make an ambient expression type incorrect. The virtual machine, however, has no trouble evaluating the expression to ``0``. Here is a similarly contrived example that shows how ``propext`` can get in the way.

.. code-block:: lean

    theorem tteq : (true ∧ true) = true := propext (and_true true)

    def val : ℕ := eq.rec_on tteq 0

    -- complicated!
    #reduce val

    -- evaluates to 0
    #eval val

Current research programs, including work on *observational type theory* and *cubical type theory*, aim to extend type theory in ways that permit reductions for casts involving function extensionality, quotients, and more. But the solutions are not so clear cut, and the rules of Lean's underlying calculus do not sanction such reductions.

In a sense, however, a cast does not change the meaning of an expression. Rather, it is a mechanism to reason about the expression's type. Given an appropriate semantics, it then makes sense to reduce terms in ways that preserve their meaning, ignoring the intermediate bookkeeping needed to make the reductions type correct. In that case, adding new axioms in ``Prop`` does not matter; by proof irrelevance, an expression in ``Prop`` carries no information, and can be safely ignored by the reduction procedures.

Quotients
---------

Let ``α`` be any type, and let ``r`` be an equivalence relation on ``α``. It is mathematically common to form the "quotient" ``α / r``, that is, the type of elements of ``α`` "modulo" ``r``. Set theoretically, one can view ``α / r`` as the set of equivalence classes of ``α`` modulo ``r``. If ``f : α → β`` is any function that respects the equivalence relation in the sense that for every ``x y : α``, ``r x y`` implies ``f x = f y``, then ``f`` "lifts" to a function ``f' : α / r → β`` defined on each equivalence class ``⟦x⟧`` by ``f' ⟦x⟧ = f x``. Lean's standard library extends the Calculus of Constructions with additional constants that perform exactly these constructions, and installs this last equation as a definitional reduction rule.

In its most basic form, the quotient construction does not even require ``r`` to be an equivalence relation. The following constants are built into Lean:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    universes u v

    constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
    
    constant quot.mk : 
      Π {α : Sort u} (r : α → α → Prop), α → quot r

    axiom quot.ind : 
      ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
        (∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

    constant quot.lift : 
      Π {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
        (∀ a b, r a b → f a = f b) → quot r → β

    -- END
    end hidden

The first one forms a type ``quot r`` given a type ``α`` by any binary relation ``r`` on ``α``. The second maps ``α`` to ``quot α``, so that if ``r : α → α → Prop`` and ``a : α``, then ``quot.mk r a`` is an element of ``quot r``. The third principle, ``quot.ind``, says that every element of ``quot.mk r a`` is of this form.  As for ``quot.lift``, given a function ``f : α → β``, if ``h`` is a proof that ``f`` respects the relation ``r``, then ``quot.lift f h`` is the corresponding function on ``quot r``. The idea is that for each element ``a`` in ``α``, the function ``quot.lift f h`` maps ``quot.mk r a`` (the ``r``-class containing ``a``) to ``f a``, wherein ``h`` shows that this function is well defined. In fact, the computation principle is declared as a reduction rule, as the proof below makes clear.

.. code-block:: lean

    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α

    -- the quotient type
    #check (quot r : Type)

    -- the class of a
    #check (quot.mk r a : quot r)

    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂ 

    -- the corresponding function on quot r
    #check (quot.lift f h : quot r → β)

    -- the computation principle
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl

The four constants, ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` in and of themselves are not very strong. You can check that the ``quot.ind`` is satisfied if we take ``quot r`` to be simply ``α``, and take ``quot.lift`` to be the identity function (ignoring ``h``). For that reason, these four constants are not viewed as additional axioms:

.. code-block:: lean

    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α
    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂ 
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl

    -- BEGIN
    #print axioms thm   -- no axioms
    -- END

They are, like inductively defined types and the associated constructors and recursors, viewed as part of the logical framework.

What makes the ``quot`` construction into a bona fide quotient is the following additional axiom:

.. code-block:: lean

    namespace hidden
    universe u

    -- BEGIN
    axiom quot.sound : 
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → quot.mk r a = quot.mk r b
    -- END
    end hidden

This is the axiom that asserts that any two elements of ``α`` that are related by ``r`` become identified in the quotient. If a theorem or definition makes use of ``quot.sound``, it will show up in the ``#print axioms`` command.

Of course, the quotient construction is most commonly used in situations when ``r`` is an equivalence relation. Given ``r`` as above, if we define `r'` according to the rule `r' a b` iff `quot.mk r a = quot.mk r b`, then it's clear that `r'` is an equivalence relation. Indeed, `r'` is the *kernel* of the function ``a ↦ quot.mk r a``.  The axiom ``quot.sound`` says that ``r a b`` implies ``r' a b``. Using ``quot.lift`` and ``quot.ind``, we can show that ``r'`` is the smallest equivalence relation containing ``r``, in the sense that if ``r''`` is any equivalence relation containing ``r``, then ``r' a b`` implies ``r'' a b``. In particular, if ``r`` was an equivalence relation to start with, then for all ``a`` and ``b`` we have ``r a b`` iff ``r' a b``.

To support this common use case, the standard library defines the notion of a *setoid*, which is simply a type with an associated equivalence relation:

.. code-block:: lean

    universe u
    namespace hidden

    -- BEGIN
    class setoid (α : Type u) :=
    (r : α → α → Prop) (iseqv : equivalence r)

    namespace setoid
      infix `≈` := setoid.r

      variable {α : Type u}
      variable [s : setoid α]
      include s

      theorem refl (a : α) : a ≈ a :=
      (@setoid.iseqv α s).left a

      theorem symm {a b : α} : a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
    -- END

    end hidden

Given a type ``α``, a relation ``r`` on ``α``, and a proof ``p`` that ``r`` is an equivalence relation, we can define ``setoid.mk p`` as an instance of the setoid class.

.. code-block:: lean

    universe u
    namespace hidden

    -- BEGIN
    def quotient {α : Type u} (s : setoid α) :=
    @quot α setoid.r
    -- END

    end hidden

The constants ``quotient.mk``, ``quotient.ind``, ``quotient.lift``, and ``quotient.sound`` are nothing more than the specializations of the corresponding elements of ``quot``. The fact that type class inference can find the setoid associated to a type ``α`` brings a number of benefits. First, we can use the notation ``a ≈ b`` (entered with ``\eq`` in Emacs) for ``setoid.r a b``, where the instance of ``setoid`` is implicit in the notation ``setoid.r``. We can use the generic theorems ``setoid.refl``, ``setoid.symm``, ``setoid.trans`` to reason about the relation. Specifically with quotients we can use the generic notation ``⟦a⟧`` for ``quot.mk setoid.r`` where the instance of ``setoid`` is implicit in the notation ``setoid.r``, as well as the theorem ``quotient.exact``:

.. code-block:: lean

    universe u

    -- BEGIN
    #check (@quotient.exact : 
      ∀ {α : Type u} [setoid α] {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈ b)
    -- END

Together with ``quotient.sound``, this implies that the elements of the quotient correspond exactly to the equivalence classes of elements in ``α``.

Recall that in the standard library, ``α × β`` represents the Cartesian product of the types ``α`` and ``β``. To illustrate the use of quotients, let us define the type of *unordered* pairs of elements of a type ``α`` as a quotient of the type ``α × α``. First, we define the relevant equivalence relation:

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    infix `~` := eqv

The next step is to prove that ``eqv`` is in fact an equivalence relation, which is to say, it is reflexive, symmetric and transitive. We can prove these three facts in a convenient and readable way by using dependent pattern matching to perform case-analysis and break the hypotheses into pieces that are then reassembled to produce the conclusion.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    -- BEGIN
    open or

    private theorem eqv.refl {α : Type u} : 
      ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : 
      ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := 
        inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := 
        inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : 
      ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : 
      equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) 
      (@eqv.trans α)
    -- END

We open the namespaces ``or`` and ``eq`` to be able to use ``or.inl``, ``or.inr``, and ``eq.trans`` more conveniently.

Now that we have proved that ``eqv`` is an equivalence relation, we can construct a ``setoid (α × α)``, and use it to define the type ``uprod α`` of unordered pairs.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    open or

    private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

    -- BEGIN
    instance uprod.setoid (α : Type u) : setoid (α × α) :=
    setoid.mk (@eqv α) (is_equivalence α)

    definition uprod (α : Type u) : Type u :=
    quotient (uprod.setoid α)

    namespace uprod
      definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
      ⟦(a₁, a₂)⟧

      local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂ 
    end uprod
    -- END

Notice that we locally define the notation ``{a₁, a₂}`` for ordered pairs as ``⟦(a₁, a₂)⟧``. This is useful for illustrative purposes, but it is not a good idea in general, since the notation will shadow other uses of curly brackets, such as for records and sets.

We can easily prove that ``{a₁, a₂} = {a₂, a₁}`` using ``quot.sound``, since we have ``(a₁, a₂) ~ (a₂, a₁)``.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    open or

    private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

    instance uprod.setoid (α : Type u) : setoid (α × α) :=
    setoid.mk (@eqv α) (is_equivalence α)

    definition uprod (α : Type u) : Type u :=
    quotient (uprod.setoid α)

    namespace uprod
      definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
      ⟦(a₁, a₂)⟧

      local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂  

    -- BEGIN
      theorem mk_eq_mk {α : Type} (a₁ a₂ : α) : 
        {a₁, a₂} = {a₂, a₁} :=
      quot.sound (inr ⟨rfl, rfl⟩)
    -- END
    end uprod

To complete the example, given ``a : α`` and ``u : uprod α``, we define the proposition ``a ∈ u`` which should hold if ``a`` is one of the elements of the unordered pair ``u``. First, we define a similar proposition ``mem_fn a u`` on (ordered) pairs; then we show that ``mem_fn`` respects the equivalence relation ``eqv`` with the lemma ``mem_respects``. This is an idiom that is used extensively in the Lean standard library.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    open or

    private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

    instance uprod.setoid (α : Type u) : setoid (α × α) :=
    setoid.mk (@eqv α) (is_equivalence α)

    definition uprod (α : Type u) : Type u :=
    quotient (uprod.setoid α)

    namespace uprod
      definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
      ⟦(a₁, a₂)⟧

      local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂  

      theorem mk_eq_mk {α : Type} (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
      quot.sound (inr ⟨rfl, rfl⟩)

    -- BEGIN
      private definition mem_fn {α : Type} (a : α) : 
        α × α → Prop
      | (a₁, a₂) := a = a₁ ∨ a = a₂

      -- auxiliary lemma for proving mem_respects
      private lemma mem_swap {α : Type} {a : α} : 
        ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
      | (a₁, a₂) := propext (iff.intro
          (λ l : a = a₁ ∨ a = a₂, 
            or.elim l (λ h₁, inr h₁) (λ h₂, inl h₂))
          (λ r : a = a₂ ∨ a = a₁, 
            or.elim r (λ h₁, inr h₁) (λ h₂, inl h₂)))

      private lemma mem_respects {α : Type} : 
        ∀ {p₁ p₂ : α × α} (a : α), 
          p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
      | (a₁, a₂) (b₁, b₂) a (inl ⟨a₁b₁, a₂b₂⟩) :=
        by { dsimp at a₁b₁, dsimp at a₂b₂, rw [a₁b₁, a₂b₂] }
      | (a₁, a₂) (b₁, b₂) a (inr ⟨a₁b₂, a₂b₁⟩) :=
        by { dsimp at a₁b₂, dsimp at a₂b₁, rw [a₁b₂, a₂b₁], 
              apply mem_swap }

      def mem {α : Type} (a : α) (u : uprod α) : Prop :=
      quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_respects a e)

      local infix `∈` := mem

      theorem mem_mk_left {α : Type} (a b : α) : a ∈ {a, b} :=
      inl rfl

      theorem mem_mk_right {α : Type} (a b : α) : b ∈ {a, b} :=
      inr rfl

      theorem mem_or_mem_of_mem_mk {α : Type} {a b c : α} : 
        c ∈ {a, b} → c = a ∨ c = b :=
      λ h, h
    -- END
    end uprod

For convenience, the standard library also defines ``quotient.lift₂`` for lifting binary functions, and ``quotient.ind₂`` for induction on two variables.

We close this section with some hints as to why the quotient construction implies function extenionality. It is not hard to show that extensional equality on the ``Π x : α, β x`` is an equivalence relation, and so we can consider the type ``extfun α β`` of functions "up to equivalence." Of course, application respects that equivalence in the sense that if ``f₁`` is equivalent to ``f₂``, then ``f₁ a`` is equal to ``f₂ a``. Thus application gives rise to a function ``extfun_app : extfun α β → Π x : α, β x``. But for every ``f``, ``extfun_app ⟦f⟧`` is definitionally equal to ``λ x, f x``, which is in turn definitionally equal to ``f``. So, when ``f₁`` and ``f₂`` are extensionally equal, we have the following chain of equalities:

.. code-block:: text

    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂

As a result, ``f₁`` is equal to ``f₂``.

-------------------------------------

.. rubric:: Footnotes

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

.. _Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/index.html

.. _Axioms and Computation: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#
