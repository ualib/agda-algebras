.. highlight:: lean

.. index:: equivalence class, ! quotient

.. _quotients:

Quotients [1]_
===============

Given an :term:`equivalence relation` on :math:`A`, there is an important mathematical construction known as forming the *quotient* of :math:`A` modulo the given equivalence relation.

As in :numref:`equivalence-relation`, for each :math:`a ∈ A`, we let :math:`a/{≡}` denote the set :math:`\{ b ∈ A ∣ b ≡ a \}` of elements in :math:`A` that are equivalent to :math:`a` modulo ≡. We call :math:`a/{≡}` the ≡-class of :math:`A` containing :math:`a`.

.. Below we will sometimes use the notation :math:`a/{≡}` to denote the class :math:`⟦a⟧`

The collection :math:`\{ a/{≡} ∣ a ∈ A \}` of all such equivalence classes is denoted by :math:`A/{≡}` and called the **quotient** :math:`A` modulo ≡.

Equivalence captures a weak notion of equality. If two elements of :math:`A` are equivalent modulo ≡, they are not necessarily the same, rather, the way in which they do differ is not relevant to us.

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

Define the **quotient** :math:`α/R` (read, "alpha modulo :math:`R`") to be the collection of :math:`R`-classes in :math:`α`. That is, for each :math:`x:α`, there is a class :math:`x/R ⊆ α` consisting of all :math:`y:α` such that :math:`(x,y) ∈ R`.

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

The `Lean Standard Library`_ (:term:`LSL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation :math:`fₗ(x/R) = f x` available as a definitional reduction rule. [2]_

Here are four such constants from the :term:`LSL`.

.. index:: keyword: quot, quot.mk, quot.ind
.. index:: keyword: quot.lift
.. index:: keyword: ualib_quotient

::

  namespace ualib_quotient

    -- BEGIN
    universes u v

    -- The quotient type former.
    constant quot: Π {α: Sort u}, (α → α → Prop) → Sort u

    -- So quot takes a type α and a relation R ⊆ α × α
    -- and forms the collection α/R of R-classes.

    -- Given α and R ⊆ α × α, map each a:α to its R-class.
    constant quot.mk: Π {α: Sort u} (R: α → α → Prop), α → quot R

    -- So, if R: α → α → Prop and a:α, then quot.mk R a is the
    -- R-class a/R containing a, which has type quot R.

    -- Each element of quot R is a R-class of the form quot.mk R a.
    axiom quot.ind:
    ∀ {α: Sort u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (quot.mk R a)) → ∀ (q: quot R), β q

    -- Given a function f: α → β and a proof of R ⊆ ker f,
    -- return the lift of f to quot R.
    constant quot.lift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (f: α → β),
    (∀ a b, R a b → f a = f b) → quot R → β

    -- END
  end ualib_quotient

The first of these takes a type ``α`` and a binary relation ``R`` on ``α`` and forms the type ``quot R`` (or ``@quot α R``, if we wish to make the first parameter explicit).

That is, for each ``α: Sort u``, we form the function type ``@quot α`` which takes a binary relation ``R: α → α → Prop`` and returns the quotient type ``quot R``, each element of which is an equivalence class, say, ``a/R``, where ``a:α``.

The second constant, ``quot.mk``, takes ``α`` and ``R: α → α → Prop`` and forms the function that maps each ``a:α`` to its ``R``-class ``quot.mk R a``, which is of type ``quot R``.

The third, ``quot.ind``, is the axiom asserting that every element of ``quot R`` is of the form ``quot.mk R a``.

Finally, ``quot.lift`` takes a function ``f: α → β`` and, if ``h`` is a proof that ``f`` respects ``R`` (i.e., ``f ⊧ R``), then ``quot.lift f h`` is the corresponding function on ``quot R``, that is, the lift of ``f`` to ``quot R``.

The idea is for each ``a:α``, the function ``quot.lift f h`` maps the ``R``-class ``quot.mk R a`` to ``f a``, where ``h`` is a proof that this function is well defined.

In fact, this computation principle is declared as a reduction rule in Lean, so it is built into the logical framework and is applied automatically (which explains why the computation principle below can be proved with just ``rfl``).

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

The constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` are not very strong.  (Indeed, ``quot.ind`` is satisfied if ``quot R`` is just ``α``, and ``quot.lift`` is the identity function.)

For that reason, the `Lean Standard Library`_ does not take these four constants to be "axioms." This can be verified by asking Lean to ``#print`` the axioms used by ``lift_comp_principle``; observe that Lean responds, "``no axioms``."

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

Like inductively defined types and their associated constructors and recursors, the constants ``quot``, ``quot.mk``, ``quot.ind``, ``quot.lift`` are viewed as part of the logical framework.

By contrast, other lifting constructions that are defined in the next section (and are important in universal algebra) are not native to Lean. Therefore, their computation principles cannot be proved as theorems and will have to be added as axioms.

------------------------

.. index:: pair: respect; preserve

Lifts of operations
-------------------

The last section explain the quotient construction that is built into Lean and that is useful for lifting a function :math:`f: α → β` to a function :math:`f': α/R → β` for some relation :math:`R ⊆ α × α` respected by :math:`f`.  In this section, we generalize this lifting construction to a lift that is more common in universal algebra.  Namely, we wish to take an operation of type :math:`(β → α) → α` and lift it to an operation of type :math:`(β → α/R) → α/R`.

Respecting relations
~~~~~~~~~~~~~~~~~~~~

Recall, an :math:`n`-**ary operation** on :math:`α` is a function with domain :math:`α^n` and codomain :math:`α`.  Recall also that we can represent the function type not by :math:`α^n → α`, but by :math:`(n → α) → α`.

Given a unary operation :math:`f: α → α`, we say that :math:`f` **respects** (or **preserves**) the binary relation :math:`R ⊆ α × α`, and we write :math:`f ⊧ R`, just in case :math:`∀ x, y :α \ (x \mathrel R y \ → \ f x \mathrel R f y)`.

Let us now generalize this notion to operations of higher arity.

Suppose :math:`f: (ρf → α) → α` is an operation (of arity :math:`ρf`) and let :math:`τ: ρf → (α × α)` be a :math:`ρf`-tuple of pairs of elements of type :math:`α`; that is, to each :math:`i : ρ f` corresponds a pair :math:`τ \ i : α × α`.

If :math:`π_i^k` denotes the :math:`k`-ary function that projects onto the :math:`i`-th coordinate, then :math:`π_1^{ρf} ∘ τ` is the :math:`ρf`-tuple of all first coordinates of the pairs in the range of :math:`τ`; similarly, :math:`π_2^{ρf} ∘ τ` is the :math:`ρf`-tuple of all second coordinates.

For example, if the :math:`i`-th pair in the range of :math:`τ` is :math:`τ\ i = (a_1, a_2)`, then the first coordinate of the :math:`i`-th pair is :math:`(π_1^{ρf} ∘ τ)(i) = π_1^2 (τ \ i) = a_1`.

(From now on, when the arity :math:`k` is clear from the context, we will write :math:`π_i` instead of :math:`π_i^k`.)

Thus, :math:`f (π_1 ∘ τ)` denotes :math:`f` evaluated at the :math:`ρf`-tuple of all first coordinates of :math:`τ`. Similarly, :math:`f (π_2 ∘ τ)` is :math:`f` evaluated at all second coordinates of :math:`τ`.

If :math:`R ⊆ α × α` is a binary relation on :math:`α`, then we say that :math:`τ: ρf → (α × α)` **belongs to** :math:`R` provided the pair :math:`τ\ i` belongs to :math:`R` for every :math:`i : ρf`.

We say that :math:`f` **respects** :math:`R`, and we write :math:`f ⊧ R`, just in case the following implication holds for all :math:`τ: ρf → (α × α)`:

  if :math:`τ` belongs to :math:`R`, then :math:`(f (π_1 ∘ τ), f (π_2 ∘ τ))` belongs to :math:`R`.

.. proof:example::

   Readers who do not find the foregoing explanation perfectly clear are invited to consider this simple, concrete example.

   Let :math:`f : (\{0,1,2\} → α) → α` be a ternary operation on :math:`α`, let :math:`R ⊆ α × α`, and suppose that for every triple :math:`(a_1, b_1), (a_2, b_2), (a_3, b_3)` of pairs from :math:`R`, the pair :math:`(f(a_1, a_2, a_3), f(b_1, b_2, b_3))` also belongs to :math:`R`. Then :math:`f ⊧ R`.

.. index:: ! quotient tuple
.. index:: ! lift; of tuples
.. index:: ! lift; of operations

.. _lifts-of-tuples-and-operations:

Lifts of tuples and operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let :math:`α` and :math:`β` be types, let :math:`R ⊆ α × α` be a binary relation on :math:`α`, and let :math:`g : (β → α) → α` be a :math:`β`-ary operation on :math:`α`.

Recall, we view the function type :math:`β → α` as the type of :math:`β`-tuples of elements from :math:`α`.

We define a **lift of tuples** :math:`[\ ]: (β → α) → β → α/R` as follows: for each tuple :math:`τ: β → α`, we take :math:`[τ] : β → α/R` to be the :math:`β`-tuple that takes each :math:`i: β` to the :math:`R`-class containing :math:`τ\ i`; that is,

.. math:: [τ]\ i = (τ\ i)/R.

We define a **lift of operations** as follows: for each :math:`β`-ary operation :math:`g: (β → α) → α`, we would like the lift of :math:`g` to have type :math:`(β → α/R) → α/R` and take each lifted tuple :math:`[τ]: β → α/R` to the :math:`R`-class containing :math:`g τ`.

However, such a lift is not well-defined unless :math:`g` :term:`respects` :math:`R`.  Therefore, we must provide a proof that :math:`g` respects :math:`R` in order to guarantee the well-definedness of the lift from :math:`(β → α) → α` to :math:`(β → α/R) → α/R`.

Below, when we implement lifts of tuples and operations in Lean, we will introduce the symbol ``ℒ`` to denote the lift of operations, with the following typing judgment:

  ``ℒ : Π {R: α → α → Prop} (g: (β → α) → α), (g ⊧ R) → (β → α/R) → α/R``.

As such, ``ℒ`` takes a relation ``R: α → α → Prop``, an operation ``g: (β → α) → α``, and a proof ``p: g ⊧ R``, and constructs the operaiton ``g ℒ p: (β → α/R) → α/R``, defined as follows: for each tuple ``τ: β → α``,

  ``(g ℒ p) [τ]  := (g τ) / R``.

----------------------

Lifts of Operations in Lean
----------------------------

The definitions of lifts of tuples and operations in :numref:`lifts-of-tuples-and-operations` are fundamentally different from that of the *lift of a function* given in :numref:`lifts-of-functions` and defined in the :term:`LSL`. To account for this, we must introduce new lifting constants.

The next section of code begins by redefining the constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` and then defines three new lift constants, ``quot.colift``, ``quot.tlift``, and ``quot.oplift``.  By redefining the standard ``quot`` constants, the ``ualib_quotient`` namespace puts all of the quotient constants on the same "level" in the sense that all are now "user-defined" and thus none is a built-in part of Lean's logical framework.  As such, their associated computation principles will be added as axioms rather than proved as theorems.

::

  namespace ualib_quotient

    universes u v

    -- (Already defined in std lib)
    -- The quotient type former.
    constant quot: Π {α: Sort u}, (α → α → Prop) → Sort u

    -- So quot takes a type α and a relation R ⊆ α × α
    -- and forms the collection α/R of R-classes.

    -- (Already defined in std lib)
    -- Given α and R ⊆ α × α, map each a:α to its R-class.
    constant quot.mk: Π {α: Sort u} (a : α) (R: α → α → Prop),
    quot R

    -- So, if R: α → α → Prop and a:α, then quot.mk R a is the
    -- R-class a/R containing a, which has type quot R.

    -- Let us define some syntactic sugar that reflects this fact.
    infix `/` := quot.mk        -- (notation: a/R := quot.mk a R)

    -- (Already defined in std lib)
    -- Each element of quot R is a R-class of the form quot.mk R a.
    axiom quot.ind:
    ∀ {α: Sort u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    -- true if the function f "respects" R.
    def funresp {α: Sort u} {β: Sort v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    -- notation f ⫢ R := funresp f R
    infix `⫢`:50 := funresp          -- type: ``f \vDdash R``
 
    -- (Already defined in std lib)
    -- Take a function f: α → β and a proof h : f ⫢ R, and
    -- return the lift of f to quot R.
    constant quot.lift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (f: α → β),
    (f ⫢ R) → quot R → β

    -- notation: f ℓ h := quot.mk f h
    infix `ℓ`:50 := quot.lift        -- type: ``f \ell R``

    -- new lift constants

    -- quot.colift
    -- lift to a fun with quot codomain (instead of quot domain)
    constant quot.colift:
    Π {α: Sort u} {β: Sort u} {R: β → β → Prop} (f: α → β),
    (α → quot R)

    -- LIFT OF A TUPLE ----------------------------------------
    -- quot.tlift
    -- lift tuple of α's to a tuple of quotients α/R's
    -- (same as colift, except for order of arguments)
    constant quot.tlift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (t: β → α),
    (β → quot R)

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    -- LIFT OF RELATIONS AND OPERATIONS -----------------------
    -- operation type
    def op (β : Sort v) (α : Sort u) := (β → α) → α
    variables {α β : Type}
    def liftrel: (α → α → Prop) → (β → α) → (β → α) → Prop :=
    λ R a b, ∀ i, R (a i) (b i)

    notation `⟨` R `⟩` := liftrel R       -- ``\<R\>``

    def respects: ((β → α) → α) → (α → α → Prop) → Prop :=
    λ f R, ∀ (a b: β → α), ⟨R⟩ a b → R (f a) (f b)

    infix `⊧`:50 := respects              -- ``\models``

    constant quot.oplift :
    Π {R: α → α → Prop} (f: op β α),
    (f ⊧ R) → (β → quot R) → quot R

    infix `ℒ`:50 := quot.oplift          -- ``\mscrL``

    -- uncurrying a relation (from α → α → Prop to set (α × α))
    def uncurry {α: Type} (R: α → α → Prop): set (α × α) :=
    λ a, R a.fst a.snd

    notation R`̃ ` := uncurry R            -- ``R\tilde``

    def ker (f: α → β): set (α × α) := { a | f a.fst = f a.snd}

  end ualib_quotient

Notice the syntactic sugar we added for the "respects" relation, so that now we can simply write

+ ``f ⫢ R`` in place of ``∀ a b, R a b → f a = f b``,

+ ``f ⊧ R`` in place of

    ``∀ (a b: β → α), ((∀ i, R (a i) (b i)) → R (f a) (f b))``,

+ ``f ℒ h`` in place of ``quot.oplift f h``, and

+ ``R̃`` in place of ``uncurry R``.

We also made use of the ``operation`` type which will be formally introduced in :numref:`algebras-in-lean`.

Now let's check the types of some of these newly defined constants, test the new notation, and prove that the notion of a function ``f`` respecting a relation ``R``, as defined in the :term:`LSL`, is equivalent to the assertion that ``R`` is a subset of the kernel of ``f``.

::

  namespace ualib_quotient

    universes u v
    constant quot: Π {α: Sort u}, (α → α → Prop) → Sort u
    constant quot.mk: Π {α: Sort u} (a : α) (R: α → α → Prop), quot R

    infix `/` := quot.mk  -- notation: a/R := quot.mk a R

    axiom quot.ind:
    ∀ {α: Sort u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    def funresp {α: Sort u} {β: Sort v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    infix `⫢`:50 := funresp       -- ``\vDdash``
 
    constant quot.lift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (f: α → β),
    (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

    constant quot.colift:
    Π {α: Sort u} {β: Sort u} {R: β → β → Prop} (f: α → β), (α → quot R)

    constant quot.tlift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (t: β → α), (β → quot R)

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    def op (β : Sort v) (α : Sort u) := (β → α) → α
    variables {α β : Type}
    def liftrel: (α → α → Prop) → (β → α) → (β → α) → Prop :=
    λ R a b, ∀ i, R (a i) (b i)

    notation `⟨` R `⟩` := liftrel R       -- ``\<R\>``

    def respects: ((β → α) → α) → (α → α → Prop) → Prop :=
    λ f R, ∀ (a b: β → α), ⟨R⟩ a b → R (f a) (f b)

    infix `⊧`:50 := respects              -- ``\models``

    constant quot.oplift :
    Π {R: α → α → Prop} (f: op β α), (f ⊧ R) → (β → quot R) → quot R

    infix `ℒ`:50 := quot.oplift

    def uncurry {α : Type} (R : α → α → Prop) : set (α × α) := λ a, R a.fst a.snd

    notation R`̃ ` := uncurry R            -- ``R\tilde``

    def ker (f : α → β) : set (α × α) := { a | f a.fst = f a.snd}

    -- BEGIN
    -- TEST NEW DEFINITIONS AND NOTATIONS --

    variable {R: α → α → Prop} -- A binary relation on α.
    variable (f: α → β)        -- A function,
    variable (f ⫢ R)           -- that respects R.

    variable (t: β → α)        -- A tuple.
    variable (g: op β α)       -- An operation,
    variable (h₁: g ⊧ R)       -- that respects R

    -- lift of a relation --
    #check liftrel R      -- (?M_1 → α) → (?M_1 → α) → Prop)
    #check ⟨R⟩            -- (?M_1 → α) → (?M_1 → α) → Prop

    -- uncurried relation --
    #check (uncurry R : set (α × α))
    #check R̃         -- set (α × α)

    -- lift of a function --
    #check (quot.lift f h₀: quot (λ (a b: α), R a b) → β)
    #check f ℓ h₀        -- quot (λ (a b: α), R a b) → β

    -- lift of a tuple --
    #check quot.tlift t  -- β → quot ?M_1)
    #check [t]           -- β → quot ?M_1

    -- lift of an operation
    #check (quot.oplift g h₁ : (β → quot R) → quot R)
    #check g ℒ h₁           -- (β → quot R) → quot R

    -- Theorem. The function f: α → β respects R: α → α → Prop
    --          iff  R̃ ⊆ ker f.
    theorem kernel_resp
    {α : Type} {R: α → α → Prop} {β : Type} (f: α → β):
    (f ⫢ R) ↔ (R̃ ⊆ ker f) :=
    iff.intro
    ( assume h: f ⫢ R, show R̃ ⊆ ker f, from
        λ p, h p.fst p.snd
    )
    ( assume h: R̃ ⊆ ker f,
      show f ⫢ R, from
        assume a₁ a₂ (h1 : R a₁ a₂),
        have h2 : (a₁ , a₂) ∈ (R̃), from h1,
        h h2
    )
    -- END
  end ualib_quotient

Finally, let us assert the computation principles for these new lift operators. [3]_

::

  namespace ualib_quotient

    universes u v
    constant quot: Π {α: Sort u}, (α → α → Prop) → Sort u
    constant quot.mk: Π {α: Sort u} (a : α) (R: α → α → Prop), quot R
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R
    axiom quot.ind:
    ∀ {α: Sort u} {R: α → α → Prop} {β: quot R → Prop},
    (∀ a, β (a/R)) → ∀ (q: quot R), β q

    def funresp {α: Sort u} {β: Sort v}
    (f: α → β) (R: α → α → Prop): Prop :=
    ∀ a b, R a b → f a = f b

    infix `⫢`:50 := funresp       -- ``\vDdash``
 
    constant quot.lift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (f: α → β),
    (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

    constant quot.colift:
    Π {α: Sort u} {β: Sort u} {R: β → β → Prop} (f: α → β), (α → quot R)

    constant quot.tlift:
    Π {α: Sort u} {R: α → α → Prop} {β: Sort u} (t: β → α), (β → quot R)

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    def op (β : Sort v) (α : Sort u) := (β → α) → α
    variables {α β : Type}
    def liftrel: (α → α → Prop) → (β → α) → (β → α) → Prop :=
    λ R a b, ∀ i, R (a i) (b i)

    notation `⟨` R `⟩` := liftrel R       -- ``\<R\>``

    def respects: ((β → α) → α) → (α → α → Prop) → Prop :=
    λ f R, ∀ (a b: β → α), ⟨R⟩ a b → R (f a) (f b)

    infix `⊧`:50 := respects              -- ``\models``

    constant quot.oplift :
    Π {R: α → α → Prop} (f: op β α), (f ⊧ R) → (β → quot R) → quot R

    infix `ℒ`:50 := quot.oplift

    def uncurry {α : Type} (R : α → α → Prop) : set (α × α) := λ a, R a.fst a.snd
    notation R`̃ ` := uncurry R            -- type: ``R\tilde``

    def ker (f : α → β) : set (α × α) := { a | f a.fst = f a.snd}

    theorem kernel_resp {α : Type} {R: α → α → Prop} {β : Type} (f: α → β):
    (f ⫢ R) ↔ (R̃ ⊆ ker f) := iff.intro
    ( assume h: f ⫢ R, show R̃ ⊆ ker f, from
        λ p, h p.fst p.snd
    )
    ( assume h: R̃ ⊆ ker f, show f ⫢ R, from
        assume a₁ a₂ (h1 : R a₁ a₂),
        have h2 : (a₁ , a₂) ∈ (R̃), from h1,
        h h2
    )

    -- BEGIN
    -- computation principle for function lift
    axiom flift_comp_principle
    {α : Type} {R: α → α → Prop} {β : Type} (f: α → β) (h: f ⫢ R):
    ∀ (a : α), (f ℓ h) (a/R) = f a

    -- The same flift principle, assuming instead that (uncurry) R
    -- belongs to kernel of f and applying the kernel_resp theorem.
    axiom flift_comp_principle' {α : Type} {R: α → α → Prop}
    {β : Type} (f: α → β) (h: R̃ ⊆ ker f): ∀ (a : α),
    (f ℓ (iff.elim_right (kernel_resp f) h)) (a/R) = f a

    -- computation principle for colift
    axiom colift_comp_principle {α : Type} {β : Type}
    {R: β → β → Prop} (f: α → β): ∀ (a : α),
    (quot.colift f) a = (f a)/R

    -- computation principle for tuple lift
    axiom tlift_comp_principle {α : Type} {R: α → α → Prop}
    {β : Type} (τ: β → α): ∀ (b : β), [τ] b = (τ b)/R

    -- computation principle for operation lift
    axiom olift_comp_principle {R : α → α → Prop}
    (g: (β → α) → α) (h : g ⊧ R): ∀ (τ : β → α),
    (g ℒ h) [τ] = (g τ)/R
    -- END

  end ualib_quotient

----------------------------------------

.. _setoids:

.. index:: ! setoid, kernel

Setoids
-------

In a quotient construction ``α/R``, the relation ``R`` is typically an *equivalence relation*.  If not, we can extend it to one.  Indeed, given a binary relation ``R``, we define ``R'`` according to the rule

  ``R' a b`` :math:`\quad` iff :math:`\quad` ``a/R = b/R``.

Then ``R'`` is an equivalence relation---namely, the **kernel** of the function ``a ↦ a/R``.

The axiom ``quot.sound`` given at the end of the last section asserts that ``R a b`` implies ``R' a b``.

Using ``quot.lift`` and ``quot.ind``, we can show that ``R'`` is the smallest equivalence relation containing ``R``. In particular, if ``R`` is already an equivalence relation, then we have ``R = R'``.

::

  import ualib_quotient

  namespace ualib_setoid

    universe u

    class setoid (α: Type u) :=
    (R: α → α → Prop) (iseqv: equivalence R)

    namespace setoid

      open setoid
      infix `≈` := setoid.R

      variable (α: Type u)
      variable [s: setoid α]
      include s

      theorem refl (a: α): a ≈ a :=
      (@setoid.iseqv α s).left a

      theorem symm {a b: α}: a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂

    end setoid

  end ualib_setoid

Given a type ``α``, a relation ``r`` on ``α``, and a proof ``p`` that ``r`` is an equivalence relation, we can define ``setoid.mk p`` as an instance of the setoid class.

::

  import ualib_quotient
  namespace ualib_setoid
    universe u
    class setoid (α: Type u) :=
    (R: α → α → Prop) (iseqv: equivalence R)
    namespace setoid
      open setoid
      infix `≈` := setoid.R
      variable (α: Type u)
      variable [s: setoid α]
      include s
      theorem refl (a: α): a ≈ a :=
      (@setoid.iseqv α s).left a
      theorem symm {a b: α}: a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h
      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid

    -- BEGIN
    variables (α : Type u) (r : α → α → Prop) (p: equivalence r)

    #check setoid.mk r p -- {R := r, iseqv := p} : setoid
    -- END
  end ualib_setoid

Now let us define some syntactic sugar to make it a little easier to work with quotients.

::

  import ualib_quotient
  namespace ualib_setoid
    universe u
    class setoid (α: Type u) :=
    (R: α → α → Prop) (iseqv: equivalence R)
    namespace setoid
      open setoid
      infix `≈` := setoid.R
      variable (α: Type u)
      variable [s: setoid α]
      include s
      theorem refl (a: α): a ≈ a := (@setoid.iseqv α s).left a
      theorem symm {a b: α}: a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h
      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c := λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
  end ualib_setoid

  -- BEGIN
  namespace ualib_setoid
    universe u

    def quotient (α : Type u) (s : setoid α) := @quot α setoid.R
    variable (α : Type u)

  end ualib_setoid
  -- END

The constants ``quotient.mk``, ``quotient.ind``, ``quotient.lift``, and ``quotient.sound`` are simply specializations of the corresponding elements of ``quot``.

The fact that type class inference can find the setoid associated to a type ``α`` has the following benefits:

First, we can use the notation ``a ≈ b`` for ``setoid.R a b``, where the instance of ``setoid`` is implicit in the notation ``setoid.R``.  (The ≈ symbol is produced by typing ``\app`` or ``\approx``.)

We can use the generic theorems ``setoid.refl``, ``setoid.symm``, ``setoid.trans`` to reason about the relation. Specifically with quotients we can use the generic notation ``⟦a⟧`` for ``quot.mk setoid.R`` where the instance of ``setoid`` is implicit in the notation ``setoid.R``, as well as the theorem ``quotient.exact``:

::

  import ualib_quotient
  namespace ualib_setoid
    universe u
    class setoid (α: Type u) :=
    (R: α → α → Prop) (iseqv: equivalence R)
    namespace setoid
      open setoid
      infix `≈` := setoid.R
      variable (α: Type u)
      variable [s: setoid α]
      include s
      theorem refl (a: α): a ≈ a := (@setoid.iseqv α s).left a
      theorem symm {a b: α}: a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h
      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c := λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
  end ualib_setoid

  namespace ualib_setoid
    universe u

    def quotient (α : Type u) (s : setoid α) := @quot α setoid.R
    variable (α : Type u)

    -- BEGIN
    axiom quotient.exact: ∀ {α : Type u} [setoid α] {a b: α},
    (a/setoid.R = b/setoid.R → a ≈ b)
    -- END

  end ualib_setoid

Together with ``quotient.sound``, this implies that the elements of the quotient correspond exactly to the equivalence classes of elements in ``α``.

Here is the full listing of the `ualib_setoid.lean <https://gitlab.com/ualib/lean-ualib/blob/dev_wjd/src/ualib_setoid.lean>`_ file.  We dissect this program below.

::

  import ualib_quotient

  namespace ualib_setoid

    universe u

    class setoid (α: Type u) :=
    (R: α → α → Prop) (iseqv: equivalence R)

    namespace setoid

      infix `≈` := setoid.R

      variable (α: Type u)
      variable [s: setoid α]
      include s

      theorem refl (a: α): a ≈ a :=
      (@setoid.iseqv α s).left a

      theorem symm {a b: α}: a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂

    end setoid

    variables (α: Type u) (r : α → α → Prop) (p: equivalence r)

    #check setoid.mk r p -- {R := r, iseqv := p} : setoid

    def quotient (α: Type u) (s: setoid α) := @quot α setoid.R
    axiom quotient.exact: ∀ {α: Type u} [setoid α] {a b: α},
    (a/setoid.R = b/setoid.R → a ≈ b)

    variables {Q: α → α → Prop} (a: α) (q: equivalence Q)
    -- test notation for quotient --
    #check @ualib_quotient.quot.mk α a Q  -- ualib_quotient.quot Q
    #check a/Q  -- ualib_quotient.quot Q

    #check @ualib_quotient.quot.ind α Q
    -- ∀ {β: ualib_quotient.quot Q → Prop},
    -- (∀ (a: α), β (a/Q)) → ∀ (q: ualib_quotient.quot Q), β q

    variable β : ualib_quotient.quot Q → Prop
    variable h: ∀ (a: α), β (a/Q)

    #check @ualib_quotient.quot.ind α Q β h
    -- ∀ (q: ualib_quotient.quot Q), β q

    #check @ualib_quotient.quot.lift α Q
    -- Π {β: Type u} (f: α → β), f ⫢ Q → ualib_quotient.quot Q → β

    #check @ualib_quotient.quot.sound α Q
    -- ∀ (a b: α), Q a b → a/Q = b/Q

    #check @ualib_setoid.quotient.exact α
    -- a/setoid.R = b/setoid.R → a ≈ b

    def Qeq: α → α → Prop := λ (a b: α),
    ualib_quotient.quot.mk a Q = ualib_quotient.quot.mk b Q

    theorem reflQ {a: α}: @Qeq α Q a a :=
    have h: ualib_quotient.quot.mk a Q = ualib_quotient.quot.mk a Q,
    from sorry,
    sorry

    theorem symmQ {a b: α}: @Qeq α Q a b → @Qeq α Q b a := eq.symm

    theorem transQ {a b c: α}:
    @Qeq α Q a b → @Qeq α Q b c → @Qeq α Q a c :=
    λ h₁ h₂, eq.trans h₁ h₂

  end ualib_setoid

.. Recall that in the `Lean Standard Library`_, ``α × β`` represents the Cartesian product of the types ``α`` and ``β``. To illustrate the use of quotients, let us define the type of **unordered pairs** of elements of a type ``α`` as a quotient of the type ``α × α``.

.. First, we define the relevant equivalence relation:

.. ::

..   universe u

..   private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
..   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

..   infix `~` := eqv

.. The next step is to prove that ``eqv`` is in fact an equivalence relation, which is to say, it is reflexive, symmetric and transitive. We can prove these three facts in a convenient and readable way by using dependent pattern matching to perform case-analysis and break the hypotheses into pieces that are then reassembled to produce the conclusion.

.. ::

..   universe u

..   private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
..   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

..   local infix `~` := eqv

..   -- BEGIN
..   open or

..   private theorem eqv.refl {α : Type u}:
..   ∀ p: α × α, p ~ p := assume p, inl ⟨rfl, rfl⟩

..   private theorem eqv.symm {α: Type u}:
..   ∀ p₁ p₂: α × α, p₁ ~ p₂ → p₂ ~ p₁
..   | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩):=
..     inl ⟨symm a₁b₁, symm a₂b₂⟩
..   | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩):=
..     inr ⟨symm a₂b₁, symm a₁b₂⟩

..   private theorem eqv.trans {α: Type u}:
..   ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩):=
..     inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩):=
..     inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩):=
..     inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩):=
..     inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

..   private theorem is_equivalence (α: Type u):
..   equivalence (@eqv α):= mk_equivalence (@eqv α)
..   (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)
..   -- END

.. We open the namespaces ``or`` and ``eq`` to be able to use ``or.inl``, ``or.inr``, and ``eq.trans`` more conveniently.

.. Now that we have proved that ``eqv`` is an equivalence relation, we can construct a ``setoid (α × α)``, and use it to define the type ``uprod α`` of unordered pairs.

.. ::

..   universe u

..   private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
..   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

..   local infix `~` := eqv

..   open or

..   private theorem eqv.refl {α: Type u} : ∀ p: α × α, p ~ p :=
..   assume p, inl ⟨rfl, rfl⟩

..   private theorem eqv.symm {α: Type u} : ∀ p₁ p₂: α × α, p₁ ~ p₂ → p₂ ~ p₁
..   | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
..   | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

..   private theorem eqv.trans {α: Type u} : ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
..     inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
..     inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
..     inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
..     inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

..   private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
..   mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

..   -- BEGIN
..   instance uprod.setoid (α: Type u): setoid (α × α) :=
..   setoid.mk (@eqv α) (is_equivalence α)

..   definition uprod (α: Type u): Type u :=
..   quotient (uprod.setoid α)

..   namespace uprod
..     definition mk {α: Type u} (a₁ a₂: α): uprod α:=
..     ⟦(a₁, a₂)⟧

..     local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂
..   end uprod
..   -- END

.. Notice that we locally define the notation ``{a₁, a₂}`` for ordered pairs as ``⟦(a₁, a₂)⟧``. This is useful for illustrative purposes, but it is not a good idea in general, since the notation will shadow other uses of curly brackets, such as for records and sets.

.. We can easily prove that ``{a₁, a₂} = {a₂, a₁}`` using ``quot.sound``, since we have ``(a₁, a₂) ~ (a₂, a₁)``.

.. ::

..   universe u

..   private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
..   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

..   local infix `~` := eqv

..   open or

..   private theorem eqv.refl {α: Type u}: ∀ p: α × α, p ~ p :=
..   assume p, inl ⟨rfl, rfl⟩

..   private theorem eqv.symm {α: Type u}: ∀ p₁ p₂: α × α, p₁ ~ p₂ → p₂ ~ p₁
..   | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
..   | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

..   private theorem eqv.trans {α: Type u}:
..   ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
..     (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
..     inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
..     inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
..     inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂)
..     (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
..     inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

..   private theorem is_equivalence (α: Type u):
..   equivalence (@eqv α) := mk_equivalence (@eqv α)
..   (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

..   instance uprod.setoid (α: Type u): setoid (α × α) :=
..   setoid.mk (@eqv α) (is_equivalence α)

..   definition uprod (α: Type u): Type u :=
..   quotient (uprod.setoid α)

..   namespace uprod
..     definition mk {α: Type u} (a₁ a₂: α): uprod α :=
..     ⟦(a₁, a₂)⟧

..     local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂

..     -- BEGIN
..     theorem mk_eq_mk {α: Type} (a₁ a₂: α):
..     {a₁, a₂} = {a₂, a₁} := quot.sound (inr ⟨rfl, rfl⟩)
..     -- END
..   end uprod

.. To complete the example, given ``a:α`` and ``u: uprod α``, we define the proposition ``a ∈ u`` which should hold if ``a`` is one of the elements of the unordered pair ``u``. First, we define a similar proposition ``mem_fn a u`` on (ordered) pairs; then we show that ``mem_fn`` respects the equivalence relation ``eqv`` with the lemma ``mem_respects``. This is an idiom that is used extensively in the Lean `standard library <lean_src>`_.

.. ::

..   universe u

..   private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
..   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

..   local infix `~` := eqv

..   open or

..   private theorem eqv.refl {α: Type u}: ∀ p: α × α, p ~ p :=
..   assume p, inl ⟨rfl, rfl⟩

..   private theorem eqv.symm {α: Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
..   | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
..   | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

..   private theorem eqv.trans {α: Type u} : ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
..     inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
..     inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
..     inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
..   | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
..     inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

..   private theorem is_equivalence (α: Type u): equivalence (@eqv α) :=
..   mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

..   instance uprod.setoid (α: Type u): setoid (α × α) :=
..   setoid.mk (@eqv α) (is_equivalence α)

..   definition uprod (α: Type u): Type u :=
..   quotient (uprod.setoid α)

..   namespace uprod
..     definition mk {α: Type u} (a₁ a₂: α): uprod α :=
..     ⟦(a₁, a₂)⟧

..     local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂

..     theorem mk_eq_mk {α: Type} (a₁ a₂: α): {a₁, a₂} = {a₂, a₁} :=
..     quot.sound (inr ⟨rfl, rfl⟩)

..     -- BEGIN
..     private definition mem_fn {α: Type} (a: α):
..       α × α → Prop
..     | (a₁, a₂) := a = a₁ ∨ a = a₂

..     -- auxiliary lemma for proving mem_respects
..     private lemma mem_swap {α: Type} {a: α}:
..       ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
..     | (a₁, a₂) := propext (iff.intro
..         (λ l: a = a₁ ∨ a = a₂,
..           or.elim l (λ h₁, inr h₁) (λ h₂, inl h₂))
..         (λ r: a = a₂ ∨ a = a₁,
..           or.elim r (λ h₁, inr h₁) (λ h₂, inl h₂)))

..     private lemma mem_respects {α: Type}:
..       ∀ {p₁ p₂: α × α} (a: α),
..         p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
..     | (a₁, a₂) (b₁, b₂) a (inl ⟨a₁b₁, a₂b₂⟩) :=
..       by { dsimp at a₁b₁, dsimp at a₂b₂, rw [a₁b₁, a₂b₂] }
..     | (a₁, a₂) (b₁, b₂) a (inr ⟨a₁b₂, a₂b₁⟩) :=
..       by { dsimp at a₁b₂, dsimp at a₂b₁, rw [a₁b₂, a₂b₁],
..             apply mem_swap }

..     def mem {α: Type} (a: α) (u: uprod α): Prop :=
..     quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_respects a e)

..     local infix `∈` := mem

..     theorem mem_mk_left {α: Type} (a b: α): a ∈ {a, b} :=
..     inl rfl

..     theorem mem_mk_right {α: Type} (a b: α): b ∈ {a, b} :=
..     inr rfl

..     theorem mem_or_mem_of_mem_mk {α: Type} {a b c: α}:
..       c ∈ {a, b} → c = a ∨ c = b :=
..     λ h, h
..     -- END
..   end uprod

.. For convenience, the `standard library <lean_src>`_ also defines ``quotient.lift₂`` for lifting binary functions, and ``quotient.ind₂`` for induction on two variables.

.. We close this section with some hints as to why the quotient construction implies function extenionality. It is not hard to show that extensional equality on the ``Π(x:α), β x`` is an equivalence relation, and so we can consider the type ``extfun α β`` of functions "up to equivalence." Of course, application respects that equivalence in the sense that if ``f₁`` is equivalent to ``f₂``, then ``f₁ a`` is equal to ``f₂ a``. Thus application gives rise to a function ``extfun_app: extfun α β → Π(x:α), β x``. But for every ``f``, ``extfun_app ⟦f⟧`` is definitionally equal to ``λ x, f x``, which is in turn definitionally equal to ``f``. So, when ``f₁`` and ``f₂`` are extensionally equal, we have the following chain of equalities:

.. ::

..   f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂

.. As a result, ``f₁`` is equal to ``f₂``.


-------------------------------------

.. index:: !Leibniz equal, function extionsionality
.. index:: keyword: funext

.. _proof-of-funext:

Proof of funext
---------------

To gain some more familiarity with extensionality in Lean, we will dissect the definition of function extensionality in the `Lean Standard Library`_, as well as the proof of the ``funext`` theorem, which states that the function extensionality principle *is* equality of functions in Lean; in other words, two functions are equal iff they are :term:`Leibniz equal` (i.e., they give the same output for each input).

We start with the full listing of the `funext.lean <https://github.com/leanprover/lean/blob/master/library/init/funext.lean>`_, which resides in the ``library/init`` directory of the `Lean Standard Library`_.

::

  /-
  Copyright (c) 2015 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file
  LICENSE.

  Author: Jeremy Avigad

  Extensional equality for functions, and a proof of
  function extensionality from quotients.
  -/
  prelude
  import init.data.quot init.logic

  universes u v

  namespace function
    variables {α : Sort u} {β : α → Sort v}

    protected def equiv (f₁ f₂: Π x:α, β x): Prop :=
    ∀ x, f₁ x = f₂ x

    local infix `~` := function.equiv

    protected theorem equiv.refl (f: Π x:α, β x):
    f ~ f := assume x, rfl

    protected theorem equiv.symm {f₁ f₂: Π x:α, β x}:
    f₁ ~ f₂ → f₂ ~ f₁ := λ h x, eq.symm (h x)

    protected theorem equiv.trans {f₁ f₂ f₃: Π x:α, β x}:
    f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ :=
    λ h₁ h₂ x, eq.trans (h₁ x) (h₂ x)

    protected theorem equiv.is_equivalence
    (α: Sort u) (β: α → Sort v):
    equivalence (@function.equiv α β) :=
    mk_equivalence (@function.equiv α β)
    (@equiv.refl α β) (@equiv.symm α β) (@equiv.trans α β)
  end function

  section

    open quotient
    variables {α: Sort u} {β: α → Sort v}

    @[instance]
    private def fun_setoid (α: Sort u) (β: α → Sort v):
    setoid (Π x:α, β x) :=
    setoid.mk (@function.equiv α β)
              (function.equiv.is_equivalence α β)

    private def extfun (α : Sort u) (β : α → Sort v):
    Sort (imax u v) := quotient (fun_setoid α β)

    private def fun_to_extfun (f: Π x:α, β x):
    extfun α β := ⟦f⟧
    private def extfun_app (f : extfun α β) : Π x : α, β x :=
    assume x,
    quot.lift_on f
      (λ f : Π x : α, β x, f x)
      (λ f₁ f₂ h, h x)

    theorem funext {f₁ f₂: Π x:α, β x} (h: ∀ x, f₁ x = f₂ x):
    f₁ = f₂ := show extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧, from
      congr_arg extfun_app (sound h)

  end

  attribute [intro!] funext

  local infix `~` := function.equiv

  instance pi.subsingleton {α : Sort u} {β : α → Sort v}
  [∀ a, subsingleton (β a)]: subsingleton (Π a, β a) :=
  ⟨λ f₁ f₂, funext (λ a, subsingleton.elim (f₁ a) (f₂ a))⟩

The first section of the program, inside the ``function`` namespace, is simply a formalization of the easy proof that extensional equality of functions is an equivalence relation.

The more interesting part appears in between the ``section`` and ``end`` delimiters.

First, the ``open quotient`` directive makes the contents of the ``quotient`` namespace available.  (We reproduce that namespace in Appendix :numref:`the-standard-librarys-quotient-namespace` for easy reference.)

Next, some implicit variables are defined, namely, for universes ``u`` and ``v``, we have ``α: Sort u`` and ``β: α → Sort v``.

This is followed by four definitions,

::

  prelude
  import init.data.quot init.logic
  universes u v
  namespace function
    variables {α : Sort u} {β : α → Sort v}
    protected def equiv (f₁ f₂: Π x:α, β x): Prop := ∀ x, f₁ x = f₂ x
    local infix `~` := function.equiv
    protected theorem equiv.refl (f: Π x:α, β x): f ~ f := assume x, rfl
    protected theorem equiv.symm {f₁ f₂: Π x:α, β x}: f₁ ~ f₂ → f₂ ~ f₁ := λ h x, eq.symm (h x)
    protected theorem equiv.trans {f₁ f₂ f₃: Π x:α, β x}: f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ := λ h₁ h₂ x, eq.trans (h₁ x) (h₂ x)
    protected theorem equiv.is_equivalence (α: Sort u) (β: α → Sort v): equivalence (@function.equiv α β) := mk_equivalence (@function.equiv α β) (@equiv.refl α β) (@equiv.symm α β) (@equiv.trans α β)
  end function
  section
    open quotient
    variables {α: Sort u} {β: α → Sort v}

    -- BEGIN
    @[instance]
    private def fun_setoid (α: Sort u) (β: α → Sort v):
    setoid (Π x:α, β x) :=
    setoid.mk (@function.equiv α β)
              (function.equiv.is_equivalence α β)

    private def extfun (α: Sort u) (β: α → Sort v):
    Sort (imax u v) := quotient (fun_setoid α β)

    private def fun_to_extfun (f: Π x:α, β x):
    extfun α β := ⟦f⟧
    private def extfun_app (f: extfun α β): Π x:α, β x :=
    assume x, 
    quot.lift_on f (λ f: Π x:α, β x, f x) (λ f₁ f₂ h, h x)
    -- END

    theorem funext {f₁ f₂: Π x:α, β x} (h: ∀ x, f₁ x = f₂ x):
    f₁ = f₂ := show extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧, from
      congr_arg extfun_app (sound h)

  end

The first of these creates a setoid consisting of functions of type ``Π x:α, β x`` along with the relation ``function.equiv`` (which was just proved, in the ``function`` namespace, to be an equivalence relation).

The second takes this ``fun_setoid`` and uses it to define the quotient consisting of the ``function.equiv``-classes of functions of type ``Π x:α, β x``, where functions within a single class are :term:`Leibniz equal`.

The third, ``fun_to_extfun``, simply maps each function ``f: Π x:α, β x`` to its equivalence class ``⟦f⟧: extfun α β``.

As for ``extfun_app``, this function lifts each class ``⟦f⟧: extfun α β`` of functions back up to an actual function of type ``Π x:α, β x``.

Finally, the ``funext`` theorem asserts that function extensionality *is* function equality.

::

  prelude
  import init.data.quot init.logic
  universes u v
  namespace function
    variables {α : Sort u} {β : α → Sort v}
    protected def equiv (f₁ f₂: Π x:α, β x): Prop := ∀ x, f₁ x = f₂ x
    local infix `~` := function.equiv
    protected theorem equiv.refl (f: Π x:α, β x): f ~ f := assume x, rfl
    protected theorem equiv.symm {f₁ f₂: Π x:α, β x}: f₁ ~ f₂ → f₂ ~ f₁ := λ h x, eq.symm (h x)
    protected theorem equiv.trans {f₁ f₂ f₃: Π x:α, β x}: f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ := λ h₁ h₂ x, eq.trans (h₁ x) (h₂ x)
    protected theorem equiv.is_equivalence (α: Sort u) (β: α → Sort v): equivalence (@function.equiv α β) := mk_equivalence (@function.equiv α β) (@equiv.refl α β) (@equiv.symm α β) (@equiv.trans α β)
  end function
  section
    open quotient
    variables {α: Sort u} {β: α → Sort v}
    @[instance]
    private def fun_setoid (α: Sort u) (β: α → Sort v): setoid (Π x:α, β x) := setoid.mk (@function.equiv α β) (function.equiv.is_equivalence α β)
    private def extfun (α : Sort u) (β : α → Sort v): Sort (imax u v) := quotient (fun_setoid α β)
    private def fun_to_extfun (f: Π x:α, β x): extfun α β := ⟦f⟧
    private def extfun_app (f : extfun α β) : Π x : α, β x := assume x,
    quot.lift_on f (λ f : Π x : α, β x, f x) (λ f₁ f₂ h, h x)

    -- BEGIN
    theorem funext {f₁ f₂: Π x:α, β x} (h: ∀ x, f₁ x = f₂ x):
    f₁ = f₂ := show extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧, from
      congr_arg extfun_app (sound h)
    -- END

  end

-------------------------------------

.. rubric:: Footnotes

.. [1]
   Some material in this chapter is borrowed from the `Axioms and Computation`_ section of the `Theorem Proving in Lean`_ tutorial.

.. [2]
   The issue here is whether we can define :math:`fₗ (x/R)` without invoking some form of the axiom of :term:`Choice` axiom.  Indeed, :math:`x/R` is a class of inhabitants of type :math:`α` and, if :math:`fₗ(x/R)` is taken to be the value returned when :math:`f` is evaluated at some member of this class, then we must have a way to choose one such member.  Note that we use :math:`x/R` to denote the :math:`R`-class containing :math:`x`, while the notation defined in the :term:`LSL` for this :math:`R`-class is :math:`⟦x⟧`.

.. [3]
   The definitions inside the ``ualib_quotient`` namespace are not part of Lean's built-in logical framework, so the computation principles we would like these definitions to satisfy must be assumed (as an ``axiom``), rather than proved (as a ``theorem``). If we had stuck with the ``quot`` constants defined in the `Lean Standard Library`_ (instead of defining our own versions of these constants), we could have *proved* the the ``flift_comp_principle``,  since this principle is taken as part of the logical framework of the :term:`LSL`.



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

.. _Lean Standard Library: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/

.. _Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/index.html

.. _Axioms and Computation: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#



