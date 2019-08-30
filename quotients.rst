.. highlight:: lean

.. index:: equivalence class, ! quotient

.. _quotients:

Quotients
=========

(Parts of this chapter are borrowed from the `Axioms and Computation`_ section of the excellent `Theorem Proving in Lean`_ tutorial.)

Here we document the code in the quotients.lean file and discuss some of the theory underpinning that code.

Given an :term:`equivalence relation` on :math:`A`, there is an important mathematical construction known as forming the *quotient* of :math:`A` modulo the given equivalence relation.

As in :numref:`equivalence-relation`, for each :math:`a ∈ A`, we denote by :math:`a/{≡}` the set of elements in :math:`A` that are **equivalent to** :math:`a` **modulo** ≡, that is,

.. math:: a/{≡} = \{ b ∈ A ∣ b ≡ a \}.

We call :math:`a/{≡}` the ≡-class of :math:`A` containing :math:`a`, and the collection :math:`\{ a/{≡} ∣ a ∈ A \}` of all such equivalence classes is denoted by :math:`A/{≡}`, called the **quotient of** :math:`A` **modulo** ≡.

Equivalence captures a rather weak notion of equality. If two elements of :math:`A` are equivalent modulo ≡, they are not necessarily the same, but the way in which they differ may be uninteresting or irrelevant for all intents and purposes.

.. proof:example::

   Consider the following "real-world" situation in which it is useful to "mod out"---i.e., ignore by forming a quotient---irrelevant information.

   In a study of image data for the purpose of face recognition---specifically, the task of identifying a particular person in different photographs---the orientation of a person's face is unimportant, and it would be silly to infer that faces in multiple photos belong to different people solely because they are orientated differently with respect to the camera's field of view.

   In this application it is reasonable to collect into a single group (equivalence class) those face images that differ only with respect to the spacial orientation of the face.  We might call two faces from the same class "equivalent modulo orientation."

Thus, equivalence classes collect similar objects together, unifying them into a single entity (e.g., the collection of all images of the face of a single individual).  Thus :math:`A/{≡}` is a version of :math:`A` where similar elements are compressed into a single element, so irrelevant distinctions can be ignored.

.. proof:example::

   The equivalence relation of **congruence modulo 5** on the set of integers partitions ℤ into five equivalence classes---namely, :math:`5ℤ`, :math:`1 + 5ℤ`, :math:`2+5ℤ`, :math:`3+5ℤ` and :math:`4+5ℤ`.  Here, :math:`5ℤ` is the set :math:`\{\dots, -10, -5, 0, 5, 10, 15, \dots\}` of multiples of 5, and :math:`2+5ℤ` is the set :math:`\{\dots, -8, -3, 2, 7, 12, \dots\}` of integers that differ from a multiple of 5 by 2.

--------------------------------------------

.. index:: quotient

.. index:: ! type of; (quotients)

.. index:: ! lift of; (functions)

.. _lifts-of-functions:

Lifts of functions
------------------

Let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.

Define the **quotient** :math:`α/R` (read, "alpha modulo :math:`R`") to be the collection of :math:`R`-classes in :math:`α`. That is, for each :math:`x:α`, there is a class :math:`x/R ⊆ α` consisting of all :math:`y:α` such that :math:`x \mathrel R y`, that is, 

.. math:: x/R = \{y : α ∣  x \mathrel R y\}.

The type of the class :math:`x/R` is a **quotient type**, denoted in this case by :math:`α/R`, and the main goal of this chapter is to see how such quotient types can be defined in Lean.

.. index:: lift; of a function, reduction rule

Let :math:`f: α → β` be a function. We say that :math:`f` **lifts** from :math:`α` to :math:`α/R` provided the implication

.. math:: (x, y) ∈ R \ → \ f x = f y
   :label: lift

holds for all :math:`x` and :math:`y` of type :math:`α`.

Evidently, implication :eq:`lift` holds iff :math:`R` is contained in the **kernel** of :math:`f`; that is,

.. math:: R ⊆ \ker f := \{(x, y) ∈ α × α ∣ f x = f y\}.

Let :math:`f[R] := \{(f x, f y) ∈ β × β ∣ (x, y) ∈ R\}` and let :math:`0_α := \{(x, y) ∈ α × α ∣ x = y\}` be the identity relation on :math:`α`. Then :math:`f` :term:`lifts` from :math:`α` to :math:`α/R` if and only if :math:`f[R] ⊆ 0_α` if and only if :math:`R ⊆ \ker f`.

If :math:`f` :term:`lifts` from :math:`α` to :math:`α/R`, then there is a function :math:`fₗ : α/R → β` defined by :math:`fₗ (x/R) = f x`, for each :math:`x/R: α/R`. We call this function the **lift** of :math:`f` from :math:`α` to :math:`α/R`.

The `Lean Standard Library`_ (:term:`LSTL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation :math:`fₗ(x/R) = f x` available as a definitional reduction rule. [1]_

Four such constants that are defined in the :term:`LSTL` are also defined in the `lean-ualib`_, as follows:

.. index:: keyword: quot, quot.mk, quot.ind
.. index:: keyword: quot.lift
.. index:: keyword: quotient

::

  import basic 
  import data.fintype

  -- Universes u, v, w.
  -- Generally we will use these for, respectively,
  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib

    -- The quotient type former
    constant quot:
    Π {α: Type u}, (α → α → Prop) → Type u

    -- So quot takes a type α and a relation R ⊆ α × α
    -- and forms the collection α/R of R-classes.

    -- Given α and R ⊆ α × α, map each a:α to its R-class
    constant quot.mk:
    Π {α: Type u} (a : α) (R: α → α → Prop),
    quot R

    -- So, if R: α → α → Prop and a:α, then quot.mk R a is the
    -- R-class a/R containing a, which has type quot R.

    -- Let us define some syntactic sugar that reflects this fact.
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R

    -- The quot.ind axioms asserts that each element of
    -- ``quot R`` is an R-class of the form ``quot.mk R a``.
    axiom quot.ind:
    ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    -- Defines what it means for a function to respect a relation
    -- in a certain sense.
    def funresp {α: Type u} {β: Type v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    infix `⫢`:50 := funresp       -- ``\vDdash``

    -- Take a function f: α → β and a proof h : f ⫢ R, and
    -- return the lift of f to quot R.
    constant quot.lift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β),
    (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

  end ualib

The first constant, ``quot``, takes a type ``α`` and a binary relation ``R`` on ``α`` and forms the type ``quot R`` (or ``@quot α R``, if we wish to make the first parameter explicit). Thus, for each ``α: Sort u``, the function type ``@quot α`` takes a binary relation ``R: α → α → Prop`` and returns the quotient type ``quot R``, each element of which is an equivalence class, say, ``a/R``, where ``a:α``.

The second constant, ``quot.mk``, takes ``α`` and ``R: α → α → Prop`` and forms the function that maps each ``a:α`` to its ``R``-class, ``quot.mk R a``, of type ``quot R``.

Third is the axiom ``quot.ind``, which asserts that every element of ``quot R`` is of the form ``quot.mk R a``.

Before considering the final constant, ``quot.lift``, observe the syntactic sugar we defined for the "respects" relation, which allows us to simply write ``f ⫢ R`` whenever we wish to assert that ``∀ a b, R a b → f a = f b``. (Type ``\vDdash`` to produce the symbol ⫢.)

The constant ``quot.lift`` takes a function ``f: α → β`` and, if ``h`` is a proof that ``f`` respects ``R`` (in the sense of the last sentence; i.e., ``f ⫢ R``), then ``quot.lift f h`` is the corresponding function on ``quot R``, that is, the lift of ``f`` to ``quot R``.

The idea is for each ``a:α``, the function ``quot.lift f h`` maps the ``R``-class ``quot.mk R a`` to ``f a``, where ``h`` is a proof that this function is well defined.

.. In fact, this computation principle is declared as a reduction rule in Lean, so it is built into the logical framework and is applied automatically (which explains why the computation principle below can be proved with just ``rfl``).


The constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` are not very strong.  (Indeed, ``quot.ind`` is satisfied if ``quot R`` is just ``α``, and ``quot.lift`` is the identity function.)  For that reason, the :term:`LSTL` does not even take these four constants to be "axioms." (This can be verified by asking Lean to ``#print`` the axioms used by ``lift_comp_principle`` and observing that Lean responds with "``no axioms``.")

::

  variables (α β: Type) (R: α → α → Prop)
  variables (a: α) (f: α → β) (h: ∀ a₁ a₂, R a₁ a₂ → f a₁ = f a₂)

  theorem lift_comp_principle: quot.lift f h (quot.mk R a) = f a :=
  rfl

  -- BEGIN
  #print axioms lift_comp_principle  -- no axioms
  -- END

What makes ``quot`` into a bona fide quotient is the ``quot.sound`` axiom which asserts that if two elements of ``α`` are related by ``R``, then they are identified in the quotient ``α/R``.

.. index:: keyword: quot.sound

::

  variables (α β: Type) (R: α → α → Prop) (a: α)

  -- the quotient type
  #check (quot R: Type)

  -- the class of a
  #check (quot.mk R a: quot R)

  variable f: α → β
  variable h: ∀ a₁ a₂, R a₁ a₂ → f a₁ = f a₂

  -- the corresponding function on quot R
  #check quot.lift f h      -- quot R → β

  -- the computation principle
  theorem lift_comp_principle: quot.lift f h (quot.mk R a) = f a :=
  rfl

  -- BEGIN
  axiom quot.sound {α: Type u} {R: α → α → Prop}:
  ∀ (a b: α), R a b → a/R = b/R
  -- END

If a theorem or definition makes use of ``quot.sound``, it will show up in the ``#print axioms`` command.

Like inductively defined types and their associated constructors and recursors, the constants ``quot``, ``quot.mk``, ``quot.ind``, ``quot.lift`` defined in the :term:`LSTL` are viewed as part of the logical framework.

In contrast, the other lifting constructions that we defined in the next section, which are important for universal algebra, are not native to Lean and, therefore, their computation principles cannot be proved as theorems, so we will define them as axioms.

------------------------

.. index:: pair: respect; preserve

Lifts of operations
-------------------

The last section explain the quotient construction that is built into Lean and that is useful for lifting a function :math:`f: α → β` to a function :math:`f': α/R → β` for some relation :math:`R ⊆ α × α` "respected" by :math:`f` (in the sense denoted above by ``f ⫢ R``).  In this section, we generalize this lifting construction to a lift that is more common in universal algebra.  Namely, we wish to take an operation of type :math:`(β → α) → α` and lift it to an operation of type :math:`(β → α/R) → α/R`.

Respecting relations
~~~~~~~~~~~~~~~~~~~~

Recall, an :math:`n`-**ary operation** on :math:`α` is a function with domain :math:`α^n` and codomain :math:`α`.  Recall also that we represent such an operation as a function of type :math:`(n → α) → α` (instead of :math:`α^n → α`).

Given a unary operation :math:`f: α → α`, we say that :math:`f` **respects** (or **preserves**) the binary relation :math:`R ⊆ α × α`, and we write :math:`f ⊧ R`, just in case :math:`∀ x, y :α \ (x \mathrel R y \ → \ f x \mathrel R f y)`.

Generalizing to operations of higher arity, suppose :math:`f: (ρf → α) → α` is an operation on :math:`α` (of arity :math:`ρf`), and let :math:`τ: ρf → (α × α)` be a :math:`ρf`-tuple of pairs of elements of type :math:`α`; that is, to each :math:`i : ρ f` corresponds a pair :math:`τ \ i : α × α`.

If :math:`π_i^k` denotes the :math:`k`-ary function that projects onto the :math:`i`-th coordinate, then :math:`π_1^{ρf} ∘ τ` is the :math:`ρf`-tuple of all first coordinates of the pairs in the range of :math:`τ`; similarly, :math:`π_2^{ρf} ∘ τ` is the :math:`ρf`-tuple of all second coordinates.

For example, if the :math:`i`-th pair in the range of :math:`τ` is :math:`τ\ i = (a_1, a_2)`, then the first coordinate of the :math:`i`-th pair is :math:`(π_1^{ρf} ∘ τ)(i) = π_1^2 (τ \ i) = a_1`.

(From now on, when the arity :math:`k` is clear from the context, we will write :math:`π_i` instead of :math:`π_i^k`.)

Thus, :math:`f (π_1 ∘ τ)` denotes :math:`f` evaluated at the :math:`ρf`-tuple of all first coordinates of :math:`τ`. Similarly, :math:`f (π_2 ∘ τ)` is :math:`f` evaluated at all second coordinates of :math:`τ`.

If :math:`R ⊆ α × α` is a binary relation on :math:`α`, then we say that :math:`τ: ρf → (α × α)` **belongs to** :math:`R` provided the pair :math:`τ\ i` belongs to :math:`R` for every :math:`i : ρf`.

We say that :math:`f` **respects** :math:`R`, and we write :math:`f ⊧ R`, just in case the following implication holds for all :math:`τ: ρf → (α × α)`:

  if :math:`τ` belongs to :math:`R`, then :math:`(f (π_1 ∘ τ), f (π_2 ∘ τ))` belongs to :math:`R`.

Type ``\models`` to produce the symbol ``⊧``. (Note that ``\vDash`` produces ⊨, which is not ⊧.)

.. proof:example::

   Readers who do not find the foregoing explanation perfectly clear are invited to consider this simple, concrete example.

   Let :math:`f : (\{0,1,2\} → α) → α` be a ternary operation on :math:`α`, let :math:`R ⊆ α × α`, and suppose that for every triple :math:`(a_1, b_1), (a_2, b_2), (a_3, b_3)` of pairs from :math:`R`, the pair :math:`(f(a_1, a_2, a_3), f(b_1, b_2, b_3))` also belongs to :math:`R`. Then :math:`f ⊧ R`.

.. index:: ! quotient tuple
.. index:: ! lift; of tuples
.. index:: ! lift; of operations

.. _lifts-of-tuples-and-operations:

Lifts of tuples and operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let :math:`α` and :math:`β` be types, let :math:`R ⊆ α × α` be a binary relation and :math:`g : (β → α) → α` a :math:`β`-ary operation. Recall that the function type :math:`β → α` may be viewed as the type of :math:`β`-tuples of elements from :math:`α`.

Define a **lift of tuples** :math:`[\ ]: (β → α) → β → α/R` as follows: for each tuple :math:`τ: β → α`, let :math:`[τ] : β → α/R` be the :math:`β`-tuple that takes each :math:`i: β` to the :math:`R`-class containing :math:`τ\ i`; that is,

.. math:: [τ]\ i = (τ\ i)/R.

We would like to define a **lift of operations** as follows: for each :math:`β`-ary operation :math:`g: (β → α) → α`, let the lift of :math:`g` be the function of type :math:`(β → α/R) → α/R` that takes each (lifted) tuple :math:`[τ]: β → α/R` to the :math:`R`-class containing :math:`g τ`.

Note, however, that this function is well-defined if and only if :math:`g` :term:`respects` :math:`R`, so we must supply a proof that :math:`g ⊧ R` whenever we wish to consider the lift of :math:`g` from :math:`(β → α) → α` to :math:`(β → α/R) → α/R`.

Below, when we implement lifts of tuples and operations in Lean, we will introduce the symbol ``ℒ`` to denote the lift of operations, with the following typing judgment:

  ``ℒ : Π {R: α → α → Prop} (g: (β → α) → α), (g ⊧ R) → (β → α/R) → α/R``.

As such, ``ℒ`` takes a relation ``R: α → α → Prop``, an operation ``g: (β → α) → α``, and a proof ``p: g ⊧ R``, and constructs the operation ``g ℒ p: (β → α/R) → α/R``, defined as follows: for each ``τ: β → α``,

  ``(g ℒ p) [τ]  := (g τ) / R``.

----------------------

Lifts of Operations in Lean
----------------------------

The definitions of lifts of tuples and operations in :numref:`lifts-of-tuples-and-operations` are fundamentally different from that of the *lift of a function* given in :numref:`lifts-of-functions` and defined in the :term:`LSTL`. To account for this, we must introduce new lifting constants.

The next section of code begins by redefining the constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` and then defines three new lift constants, ``quot.colift``, ``quot.tlift``, and ``quot.oplift``.

By redefining the standard ``quot`` constants, the ``ualib`` namespace puts all quotient constants on the same "level" in the sense that all are now "user-defined" and thus none is a built-in part of Lean's logical framework.  As such, their associated computation principles will be added as axioms rather than proved as theorems.

::

  import basic 
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot:
    Π {α: Type u}, (α → α → Prop) → Type u

    constant quot.mk:
    Π {α: Type u} (a : α) (R: α → α → Prop),
    quot R

    infix `/` := quot.mk

    axiom quot.ind:
    ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    def funresp {α: Type u} {β: Type v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    infix `⫢`:50 := funresp

    constant quot.lift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β),
    (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift 

  -- BEGIN

  -- quot.colift
  -- lift to a function with quotient codomain (instead of domain)
  constant quot.colift:
  Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β),
  α → quot R

  -- LIFT OF A TUPLE ------------------------------------------
  -- quot.tlift
  -- lift tuple of α's to a tuple of quotients α/R's
  -- (same as colift, except for order of arguments)
  constant quot.tlift:
  Π {α: Type u} {R: α → α → Prop} {β: Type v} (t: β → α),
  β → quot R

  notation `[` t `]` := quot.tlift t -- lift of a tuple

  -- LIFT OF RELATIONS AND OPERATIONS --------------------------
  def liftrel {α: Type u} {β: Type v}:
  (α → α → Prop) → (β → α) → (β → α) → Prop :=
  λ R a b, ∀ i, R (a i) (b i)

  def respects {α: Type u} {β: Type v}:
  ((β → α) → α) → (α → α → Prop) → Prop :=
  λ f R, ∀ (a b: β → α), (liftrel R) a b → R (f a) (f b)

  infix `⊧`:50 := respects              -- ``\models``

  constant quot.oplift {α: Type u} {β: Type v}:
  Π {R: α → α → Prop} (f: op β α),
  (f ⊧ R) → (β → quot R) → quot R

  infix `ℒ`:50 := quot.oplift

  -- uncurrying a relation (from α → α → Prop to set (α × α))
  def uncurry {α: Type u} (R: α → α → Prop):
  set (α × α) := λ a, R a.fst a.snd

  notation R`̃ ` := uncurry R            -- type: ``R\tilde``

  def ker {α: Type u} {β: Type v} (f : α → β):
  set (α × α) := {a | f a.fst = f a.snd}

  -- END
  end ualib

Notice the alternative syntax we added for this notion of "respects".

Now is a good time to pause and summarize the shorthand notation defined thus far.

.. (Recall we defined ``⫢`` earlier as notation for the notion of "respects" that agrees with the one used in the :term:`LSTL`).

+ ``f ⫢ R`` means ``∀ a b, R a b → f a = f b``,

+ ``f ⊧ R`` means

    ``∀ (a b: β → α), ((∀ i, R (a i) (b i)) → R (f a) (f b))``,

+ ``f ℒ h`` means ``quot.oplift f h``, and

+ ``R̃`` means ``uncurry R``.

.. We also made use of the ``operation`` type which will be formally introduced in :numref:`algebras-in-lean`.

Now let's check some types associated with these newly defined constants, test the new notation, and prove that the notion of a function ``f`` respecting a relation ``R``, as defined in the :term:`LSTL`, is equivalent to the assertion that ``R`` is a subset of the kernel of ``f``.

.. ::

..   variables (α β: Type) (R: α → α → Prop) (a: α)

..   -- the quotient type
..   #check (quot R: Type)

..   -- the class of a
..   #check (quot.mk R a: quot R)

..   variable f: α → β
..   variable h: ∀ a₁ a₂, R a₁ a₂ → f a₁ = f a₂

..   -- the corresponding function on quot R
..   #check quot.lift f h      -- quot R → β

..   -- the computation principle
..   theorem lift_comp_principle: quot.lift f h (quot.mk R a) = f a :=
..   rfl

::

  import basic 
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot:
    Π {α: Type u}, (α → α → Prop) → Type u

    constant quot.mk:
    Π {α: Type u} (a : α) (R: α → α → Prop),
    quot R

    infix `/` := quot.mk  -- notation: a/R := quot.mk a R

    axiom quot.ind:
    ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    def funresp {α: Type u} {β: Type v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    infix `⫢`:50 := funresp

    constant quot.lift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β),
    (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

    constant quot.colift:
    Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β),
    α → quot R

    constant quot.tlift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (t: β → α),
    β → quot R

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    def liftrel {α: Type u} {β: Type v}:
    (α → α → Prop) → (β → α) → (β → α) → Prop :=
    λ R a b, ∀ i, R (a i) (b i)

    notation `⟨` R `⟩` := liftrel R       -- ``\<R\>``

    def respects {α: Type u} {β: Type v}:
    ((β → α) → α) → (α → α → Prop) → Prop :=
    λ f R, ∀ (a b: β → α), ⟨R⟩ a b → R (f a) (f b)

    infix `⊧`:50 := respects              -- ``\models``

    constant quot.oplift {α: Type u} {β: Type v}:
    Π {R: α → α → Prop} (f: op β α),
    (f ⊧ R) → (β → quot R) → quot R

    infix `ℒ`:50 := quot.oplift

    def uncurry {α: Type u} (R: α → α → Prop):
    set (α × α) := λ a, R a.fst a.snd

    notation R`̃ ` := uncurry R            -- type: ``R\tilde``

    def ker {α: Type u} {β: Type v} (f : α → β):
    set (α × α) := {a | f a.fst = f a.snd}

  -- BEGIN

  section examples

    parameter α : Type u
    parameter β : Type v

    variable R: α → α → Prop -- A binary relation on α,
    variable f: α → β        -- A function...
    variable h₀: f ⫢ R       -- ...that respects R.

    variable (t: β → α)        -- A tuple.
    variable (g: op β α)       -- An operation...
    variable (h₁: g ⊧ R)       -- ...that respects R

    -- test notation for lift of a relation --
    #check liftrel R      -- (?M_1 → α) → (?M_1 → α) → Prop)
    #check @liftrel α β R -- (β → α) → (β → α) → Prop)
    #check (R: α → α → Prop)

    -- test notation for lift of a function --
    #check (quot.lift f h₀: quot (λ (a b: α), R a b) → β)
    #check (f ℓ h₀: quot R → β)

    -- test notation for lift of a tuple --
    #check quot.tlift t  -- β → quot ?M_1
    #check [t]           -- β → quot ?M_1

    -- test notation for lift of an operation
    #check (quot.oplift g h₁ : (β → quot R) → quot R)
    #check g ℒ h₁           -- (β → quot R) → quot R

    -- test notation for uncurrying a relation --
    #check (uncurry R : set (α × α))
    #check (R̃ : set (α × α) )

    -- Theorem. The function f: α → β respects R: α → α → Prop
    --          iff uncurry R ⊆ ker f
    --          iff R̃ ⊆ ker f
    theorem kernel_resp
    {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β):
    (f ⫢ R)  ↔  (R̃ ⊆ ker f) :=
    iff.intro
    ( assume h: f ⫢ R, show R̃ ⊆ ker f, from
        λ p, h p.fst p.snd
    )
    ( assume h: R̃ ⊆ ker f, show f ⫢ R, from
        assume a₁ a₂ (h₁: R a₁ a₂),
        have h₂: (a₁ , a₂) ∈ (R̃), from h₁,
        h h₂
    )

  end examples

  -- END

  end ualib

Finally, let us assert some computation principles for these new lift operators. [2]_

::

  import basic 
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot:
    Π {α: Type u}, (α → α → Prop) → Type u

    constant quot.mk:
    Π {α: Type u} (a : α) (R: α → α → Prop),
    quot R

    infix `/` := quot.mk  -- notation: a/R := quot.mk a R

    axiom quot.ind:
    ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    def funresp {α: Type u} {β: Type v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    infix `⫢`:50 := funresp

    constant quot.lift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β),
    (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

    constant quot.colift:
    Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β),
    α → quot R

    constant quot.tlift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (t: β → α),
    β → quot R

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    def liftrel {α: Type u} {β: Type v}:
    (α → α → Prop) → (β → α) → (β → α) → Prop :=
    λ R a b, ∀ i, R (a i) (b i)

    notation `⟨` R `⟩` := liftrel R       -- ``\<R\>``

    def respects {α: Type u} {β: Type v}:
    ((β → α) → α) → (α → α → Prop) → Prop :=
    λ f R, ∀ (a b: β → α), ⟨R⟩ a b → R (f a) (f b)

    infix `⊧`:50 := respects              -- ``\models``

    constant quot.oplift {α: Type u} {β: Type v}:
    Π {R: α → α → Prop} (f: op β α),
    (f ⊧ R) → (β → quot R) → quot R

    infix `ℒ`:50 := quot.oplift

    def uncurry {α: Type u} (R: α → α → Prop):
    set (α × α) := λ a, R a.fst a.snd

    notation R`̃ ` := uncurry R            -- type: ``R\tilde``

    def ker {α: Type u} {β: Type v} (f : α → β):
    set (α × α) := {a | f a.fst = f a.snd}

  theorem kernel_resp
  {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β): 
  (f ⫢ R)  ↔  (R̃ ⊆ ker f) :=
  iff.intro
  ( assume h: f ⫢ R, show R̃ ⊆ ker f, from
      λ p, h p.fst p.snd
  )
  ( assume h: R̃ ⊆ ker f, show f ⫢ R, from
      assume a₁ a₂ (h₁: R a₁ a₂), 
      have h₂: (a₁ , a₂) ∈ (R̃), from h₁,
      h h₂
  )

  -- BEGIN

  -- computation principle for function lift
  axiom flift_comp_principle
  {α: Type u} {R: α → α → Prop} {β : Type v}
  (f: α → β) (h: f ⫢ R):
  ∀ (a: α), (f ℓ h) (a/R) = f a

  -- The same flift principle, assuming instead that (uncurry) R 
  -- belongs to the kernel of f and applying the kernel_resp theorem.
  axiom flift_comp_principle'
  {α : Type u} {R: α → α → Prop} {β: Type v}
  (f: α → β) (h: R̃ ⊆ ker f): ∀ (a: α),
  (f ℓ (iff.elim_right (kernel_resp f) h)) (a/R) = f a

  -- computation principle for colift
  axiom colift_comp_principle
  {α: Type u} {β: Type v} {R: β → β → Prop}
  (f: α → β): ∀ (a: α), 
  (quot.colift f) a = (f a)/R

  -- computation principle for tuple lift
  axiom tlift_comp_principle
  {α: Type u} {R: α → α → Prop} {β: Type v}
  (τ: β → α): ∀ (b : β), [τ] b = (τ b)/R

  -- computation principle for operation lift
  axiom olift_comp_principle
  {α: Type u} {R: α → α → Prop} {β: Type v}
  (g: (β → α) → α) (h : g ⊧ R): ∀ (τ : β → α),
  (g ℒ h) [τ] = (g τ)/R

  axiom quot.sound
  {α: Type u} {R: α → α → Prop}:
  ∀ (a b: α), R a b → a/R = b/R
  -- END

  end ualib

-------------------------------------

.. rubric:: Footnotes

.. [1]
   The issue here is whether we can define :math:`fₗ (x/R)` without invoking some form of the axiom of :term:`Choice` axiom.  Indeed, :math:`x/R` is a class of inhabitants of type :math:`α` and, if :math:`fₗ(x/R)` is taken to be the value returned when :math:`f` is evaluated at some member of this class, then we must have a way to choose one such member.  Note that we use :math:`x/R` to denote the :math:`R`-class containing :math:`x`, while the notation defined in the :term:`LSTL` for this :math:`R`-class is :math:`⟦x⟧`.

.. [2]
   The definitions inside the ``quotient`` namespace are not part of Lean's built-in logical framework, so the computation principles we would like these definitions to satisfy must be assumed (as an ``axiom``), rather than proved (as a ``theorem``). If we had stuck with the ``quot`` constants defined in the `Lean Standard Library`_ (instead of defining our own versions of these constants), we could have *proved* the the ``flift_comp_principle``,  since this principle is taken as part of the logical framework of the :term:`LSTL`.


-------------------------------------

.. include:: hyperlink_references.rst
