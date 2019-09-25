.. highlight:: lean

.. index:: equivalence class, ! quotient

.. _quotients:

Quotients
=========

Background
-----------

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

----------------------

.. index:: type of; quotients

Quotient in Lean
-----------------

.. index:: keyword: quot, quot.mk, quot.ind

Let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.

Define the **quotient** :math:`α/R` (read, "alpha modulo :math:`R`") to be the collection of :math:`R`-classes in :math:`α`. That is, for each :math:`x:α`, there is a class :math:`x/R ⊆ α` consisting of all :math:`y:α` such that :math:`x \mathrel R y`, that is,

.. math:: x/R = \{y : α ∣  x \mathrel R y\}.

The type of the class :math:`x/R` is a **quotient type**, denoted in this case by :math:`α/R`.

The `Lean Standard Library`_ (:term:`LSTL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation :math:`fₗ(x/R) = f x` available as a definitional reduction rule. [1]_

Four such constants that are defined in the :term:`LSTL` are also defined in the `lean-ualib`_, as follows:

.. index:: lift of; a function
.. index:: reduction rule

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

    axiom quot.sound
    {α: Type u} {R: α → α → Prop}:
    ∀ (a b: α), R a b → a/R = b/R

  end ualib

The first constant, ``quot``, takes a type ``α`` and a binary relation ``R`` on ``α`` and forms the type ``quot R`` (or ``@quot α R``, if we wish to make the first parameter explicit). Thus, for each ``α: Sort u``, the function type ``@quot α`` takes a binary relation ``R: α → α → Prop`` and returns the quotient type ``quot R``, each element of which is an equivalence class, say, ``a/R``, where ``a:α``.

The second constant, ``quot.mk``, takes ``α`` and ``R: α → α → Prop`` and forms the function that maps each ``a:α`` to its ``R``-class, ``quot.mk R a``, of type ``quot R``.

Third is the axiom ``quot.ind``, which asserts that every element of ``quot R`` is of the form ``quot.mk R a``.

What makes ``quot`` into a bona fide quotient is the ``quot.sound`` axiom which asserts that if two elements of ``α`` are related by ``R``, then they are identified in the quotient ``α/R``.

Finally, note the syntactic sugar we defined for the "respects" relation, which allows us to simply write ``f ⫢ R`` whenever we wish to assert that ``∀ a b, R a b → f a = f b``. (Type ``\vDdash`` to produce the symbol ⫢.)

Let us now look at a few basic examples.

::

  import basic
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib

    constant quot: Π {α: Type u}, (α → α → Prop) → Type u
    constant quot.mk: Π {α: Type u} (a : α) (R: α → α → Prop), quot R
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R
    axiom quot.ind: ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop}, (∀ a, β (a/R)) → ∀ (q: quot R), β q
    def funresp {α: Type u} {β: Type v} (f: α → β) (R: α → α → Prop): Prop := ∀ a b, R a b → f a = f b
    infix `⫢`:50 := funresp
    axiom quot.sound {α: Type u} {R: α → α → Prop}: ∀ (a b: α), R a b → a/R = b/R

  -- BEGIN
  section examples
    #print quot.mk
    -- Π {α: Type u}, α → Π (R: α → α → Prop), quot R

    parameters {α: Type u} {r : α → α → Prop}
    variables {Q: α → α → Prop} (a: α) (q: equivalence Q)

    #check quot Q          -- quot Q: Type u
    #check @quot.mk α a Q  -- a/Q: quot Q
    #check quot.mk a Q     -- a/Q: quot Q
    #check a/Q             -- a/Q: quot Q

    #check @quot.ind α Q
    -- ∀ {β: quot Q → Prop},
    -- (∀ (a: α), β (a/Q)) → ∀ (q: quot Q), β q

    variables (β : quot Q → Prop) (h: ∀ (a: α), β (a/Q))

    #check @quot.ind α Q β h -- ∀ (q: quot Q), β q
  end examples
  -- END
  end ualib

The constants ``quot``, ``quot.mk``, and ``quot.ind``, are not very strong. Indeed, ``quot.ind`` is satisfied if ``quot R`` is just ``α``. For that reason, the :term:`LSTL` does not even take these constants to be “axioms.”  (We'll come back to this point in a moment.)

What makes ``quot`` into a bona fide quotient is the axiom ``quot.sound`` appearing at the end of the code listing above.  This axiom asserts that if two elements of ``α`` are related by ``R``, then they are identified in the quotient ``α/R``.

If ``foo`` is a theorem or definition that makes use of the ``quot.sound`` axiom, then that axiom will show up in the output of ``#print axioms foo``.

Like inductively defined types and their associated constructors and recursors, the :term:`LSTL` versions of the constants quot, quot.mk, and quot.ind are viewed as part of the logical framework.

In contrast, the analogous constants defined in the `lean-ualib`_ are not native to Lean and, therefore, their computation principles cannot be proved as theorems, so we define them as axioms.

--------------------------------------------

.. index:: quotient

.. index:: ! type of; quotients

.. index:: ! lift of; a function

.. _lift-of-a-function:

Lift of a function
--------------------

Let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.


Let :math:`f: α → β` be a function. We say that :math:`f` **lifts** from :math:`α` to :math:`α/R` provided the implication

.. math:: (x, y) ∈ R \ → \ f x = f y
   :label: lift

holds for all :math:`x` and :math:`y` of type :math:`α`.

Evidently, implication :eq:`lift` holds iff :math:`R` is contained in the **kernel** of :math:`f`; that is,

.. math:: R ⊆ \ker f := \{(x, y) ∈ α × α ∣ f x = f y\}.

Let :math:`f[R] := \{(f x, f y) ∈ β × β ∣ (x, y) ∈ R\}` and let :math:`0_α := \{(x, y) ∈ α × α ∣ x = y\}` be the identity relation on :math:`α`. Then :math:`f` :term:`lifts <lifts (v)>` from :math:`α` to :math:`α/R` if and only if :math:`f[R] ⊆ 0_α` if and only if :math:`R ⊆ \ker f`.

If :math:`f` :term:`lifts <lifts (v)>` from :math:`α` to :math:`α/R`, then there is a function :math:`fₗ : α/R → β` defined by :math:`fₗ (x/R) = f x`, for each :math:`x/R: α/R`. We call this function the :term:`lift <lift (n)>` of :math:`f` from :math:`α` to :math:`α/R`.

The `Lean Standard Library`_ (:term:`LSTL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation :math:`fₗ(x/R) = f x` available as a definitional reduction rule. [1]_

.. index:: keyword: quot.lift

::

  import basic
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot: Π {α: Type u}, (α → α → Prop) → Type u
    constant quot.mk: Π {α: Type u} (a : α) (R: α → α → Prop), quot R
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R
    axiom quot.ind: ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop}, (∀ a, β (a/R)) → ∀ (q: quot R), β q
    def funresp {α: Type u} {β: Type v} (f: α → β) (R: α → α → Prop): Prop := ∀ a b, R a b → f a = f b
    infix `⫢`:50 := funresp       -- ``\vDdash``
    axiom quot.sound {α: Type u} {R: α → α → Prop}: ∀ (a b: α), R a b → a/R = b/R

    -- BEGIN
    -- Take a function f: α → β and a proof h : f ⫢ R, and
    -- return the lift of f to quot R. (dup)
    constant quot.lift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v}
    (f: α → β), (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

    -- quot.colift
    -- lift to a function with quotient codomain (instead of domain)
    constant quot.colift:
    Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β),
    α → quot R
    -- END

    -- quot.tlift
    -- lift tuple of α's to a tuple of quotients α/R's
    -- (same as colift, except for order of arguments)
    constant quot.tlift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (t: β → α),
    β → quot R

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    -- LIFT OF RELATIONS AND OPERATIONS
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

  end ualib

The constant ``quot.lift`` takes a function ``f: α → β`` and, if ``h`` is a proof that ``f`` respects ``R`` (in the sense of the last sentence; i.e., ``f ⫢ R``), then ``quot.lift f h`` is the corresponding function on ``quot R``, that is, the lift of ``f`` to ``quot R``.

The idea is for each ``a:α``, the function ``quot.lift f h`` maps the ``R``-class ``quot.mk R a`` to ``f a``, where ``h`` is a proof that this function is well defined.

.. In fact, this computation principle is declared as a reduction rule in Lean, so it is built into the logical framework and is applied automatically (which explains why the computation principle below can be proved with just ``rfl``).

Let us see some examples.

::

  import basic
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot: Π {α: Type u}, (α → α → Prop) → Type u
    constant quot.mk: Π {α: Type u} (a : α) (R: α → α → Prop), quot R
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R
    axiom quot.ind: ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop}, (∀ a, β (a/R)) → ∀ (q: quot R), β q
    def funresp {α: Type u} {β: Type v} (f: α → β) (R: α → α → Prop): Prop := ∀ a b, R a b → f a = f b
    infix `⫢`:50 := funresp       -- ``\vDdash``
    axiom quot.sound {α: Type u} {R: α → α → Prop}: ∀ (a b: α), R a b → a/R = b/R

    -- Take a function f: α → β and a proof h : f ⫢ R, and
    -- return the lift of f to quot R. (dup)
    constant quot.lift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v}
    (f: α → β), (f ⫢ R) → quot R → β

    infix `ℓ`:50 := quot.lift

    -- quot.colift
    -- lift to a function with quotient codomain (instead of domain)
    constant quot.colift:
    Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β),
    α → quot R

  -- BEGIN
  section examples

    parameters {α: Type u} {β : Type v} {r : α → α → Prop}

    -- Name some binary relations on α.
    variables (R: α → α → Prop) (Q: α → α → Prop)
    variable a: α

    #check @quot.lift α Q
    -- Π {β: Type u} (f: α → β), f ⫢ Q → ualib_quotient.quot Q → β

    #check @quot.sound α Q   -- ∀ (a b: α), Q a b → a/Q = b/Q
    #check quot.lift Q       -- Q ⫢ ?M_1 → quot ?M_1 → α → Prop

    -- Name a function and assume it respects R.
    variables (f: α → β) (h₀: f ⫢ R)

    #check (quot.lift f h₀: quot (λ (a b: α), R a b) → β)
    #check (f ℓ h₀: quot R → β)

  end examples
  -- END

  end ualib


------------------------

.. index:: pair: respect; preserve
.. index:: ! quotient tuple
.. index:: ! lift of; a tuple
.. index:: ! lift of; an operation

.. _lift-of-an-operation:

Lift of an operation
---------------------

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

(Type ``\models`` to produce the symbol ``⊧``; note that ``\vDash`` produces ⊨, which is not the same as ⊧.)

.. proof:example::

   Readers who do not find the foregoing explanation perfectly clear are invited to consider this simple, concrete example.

   Let :math:`f : (\{0,1,2\} → α) → α` be a ternary operation on :math:`α`, let :math:`R ⊆ α × α`, and suppose that for every triple :math:`(a_1, b_1), (a_2, b_2), (a_3, b_3)` of pairs from :math:`R`, the pair :math:`(f(a_1, a_2, a_3), f(b_1, b_2, b_3))` also belongs to :math:`R`. Then :math:`f ⊧ R`.

Let :math:`α` and :math:`β` be types, let :math:`R ⊆ α × α` be a binary relation and :math:`g : (β → α) → α` a :math:`β`-ary operation. Recall that the function type :math:`β → α` may be viewed as the type of :math:`β`-tuples of elements from :math:`α`.

Define a **lift of tuples** :math:`[\ ]: (β → α) → β → α/R` as follows: for each tuple :math:`τ: β → α`, let :math:`[τ] : β → α/R` be the :math:`β`-tuple that takes each :math:`i: β` to the :math:`R`-class containing :math:`τ\ i`; that is,

.. math:: [τ]\ i = (τ\ i)/R.

We would like to define a **lift of operations** as follows: for each :math:`β`-ary operation :math:`g: (β → α) → α`, let the lift of :math:`g` be the function of type :math:`(β → α/R) → α/R` that takes each (lifted) tuple :math:`[τ]: β → α/R` to the :math:`R`-class containing :math:`g τ`.

Note, however, that this function is well-defined if and only if :math:`g` :term:`respects` :math:`R`, so we must supply a proof that :math:`g ⊧ R` whenever we wish to consider the lift of :math:`g` from :math:`(β → α) → α` to :math:`(β → α/R) → α/R`.

Below, when we implement lifts of tuples and operations in Lean, we will introduce the symbol ``ℒ`` to denote the lift of operations, with the following typing judgment:

  ``ℒ : Π {R: α → α → Prop} (g: (β → α) → α), (g ⊧ R) → (β → α/R) → α/R``.

As such, ``ℒ`` takes a relation ``R: α → α → Prop``, an operation ``g: (β → α) → α``, and a proof ``p: g ⊧ R``, and constructs the operation ``g ℒ p: (β → α/R) → α/R``, defined as follows: for each ``τ: β → α``,

  ``(g ℒ p) [τ]  := (g τ) / R``.


The definitions of lifts of tuples and operations in :numref:`lift-of-an-operation` are fundamentally different from that of the *lift of a function* given in :numref:`lift-of-a-function` and defined in the :term:`LSTL`. To account for this, we must introduce new lifting constants.

The next section of code begins by redefining the constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` and then defines three new lift constants, ``quot.colift``, ``quot.tlift``, and ``quot.oplift``.

By redefining the standard ``quot`` constants, the ``ualib`` namespace puts all quotient constants on the same "level" in the sense that each is now "user-defined" and none is a built-in part of Lean's logical framework.  As such, their associated computation principles will be added as axioms rather than proved as theorems.

::

  import basic
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot: Π {α: Type u}, (α → α → Prop) → Type u
    constant quot.mk: Π {α: Type u} (a : α) (R: α → α → Prop), quot R
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R
    axiom quot.ind: ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop}, (∀ a, β (a/R)) → ∀ (q: quot R), β q
    def funresp {α: Type u} {β: Type v} (f: α → β) (R: α → α → Prop): Prop := ∀ a b, R a b → f a = f b
    infix `⫢`:50 := funresp       -- ``\vDdash``
    axiom quot.sound {α: Type u} {R: α → α → Prop}: ∀ (a b: α), R a b → a/R = b/R
    constant quot.lift: Π {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β), (f ⫢ R) → quot R → β
    infix `ℓ`:50 := quot.lift
    constant quot.colift: Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β), α → quot R

    -- BEGIN
    -- The lift of a tuple.
    -- quot.tlift: lifts a tuple of α's to a tuple of classes α/R's
    -- (same as colift, except for order of arguments)
    constant quot.tlift:
    Π {α: Type u} {R: α → α → Prop} {β: Type v} (t: β → α),
    β → quot R

    notation `[` t `]` := quot.tlift t -- lift of a tuple

    -- The lift of a relation.
    def liftrel {α: Type u} {β: Type v}:
    (α → α → Prop) → (β → α) → (β → α) → Prop :=
    λ R a b, ∀ i, R (a i) (b i)

    def respects {α: Type u} {β: Type v}:
    ((β → α) → α) → (α → α → Prop) → Prop :=
    λ f R, ∀ (a b: β → α), (liftrel R) a b → R (f a) (f b)

    infix `⊧`:50 := respects              -- ``\models``

    -- The lift of an operation.
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
    section examples
      parameters {α: Type u} {β : Type v}

      -- Name some binary relations on α.
      variables (R: α → α → Prop)

      -- Lift of a tuple.
      variable t: β → α        -- A tuple.
      #check quot.tlift t  -- β → quot ?M_1
      #check [t]           -- β → quot ?M_1

      -- Lift of an operation.
      -- Name an operation and assume it respects R.
      variables (g: op β α) (h₁: g ⊧ R)
      #check (quot.oplift g h₁ : (β → quot R) → quot R)
      #check g ℒ h₁           -- (β → quot R) → quot R

      -- Uncurry notation.
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

  end ualib

Note the weaker sense in which a function may respect a relation; also note that we use the symbol ⊧ (typed with ``\models``) to denote this alternative notion of the "respects" relation.

Now is a good time to pause to summarize the shorthand notation defined thus far.

.. (Recall we defined ``⫢`` earlier as notation for the notion of "respects" that agrees with the one used in the :term:`LSTL`).

+ ``f ⫢ R`` means ``∀ a b, R a b → f a = f b``,

+ ``f ⊧ R`` means

    ``∀ (a b: β → α), ((∀ i, R (a i) (b i)) → R (f a) (f b))``,

+ ``f ℒ h`` means ``quot.oplift f h``, and

+ ``R̃`` means ``uncurry R``.

----------------------

Computation principles
----------------------

Finally, let us assert some computation principles for the lifts defined above. [2]_

::

  import basic
  import data.fintype

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib
    constant quot: Π {α: Type u}, (α → α → Prop) → Type u
    constant quot.mk: Π {α: Type u} (a : α) (R: α → α → Prop), quot R
    infix `/` := quot.mk  -- notation: a/R := quot.mk a R
    axiom quot.ind: ∀ {α: Type u} {R: α → α → Prop} {β: quot R → Prop}, (∀ a, β (a/R)) → ∀ (q: quot R), β q
    def funresp {α: Type u} {β: Type v} (f: α → β) (R: α → α → Prop): Prop := ∀ a b, R a b → f a = f b
    infix `⫢`:50 := funresp       -- ``\vDdash``
    axiom quot.sound {α: Type u} {R: α → α → Prop}: ∀ (a b: α), R a b → a/R = b/R
    constant quot.lift: Π {α: Type u} {R: α → α → Prop} {β: Type v} (f: α → β), (f ⫢ R) → quot R → β
    infix `ℓ`:50 := quot.lift
    constant quot.colift: Π {α: Type u} {β: Type v} {R: β → β → Prop} (f: α → β), α → quot R
    constant quot.tlift: Π {α: Type u} {R: α → α → Prop} {β: Type v} (t: β → α), β → quot R
    notation `[` t `]` := quot.tlift t -- lift of a tuple
    def liftrel {α: Type u} {β: Type v}: (α → α → Prop) → (β → α) → (β → α) → Prop := λ R a b, ∀ i, R (a i) (b i)
    def respects {α: Type u} {β: Type v}: ((β → α) → α) → (α → α → Prop) → Prop := λ f R, ∀ (a b: β → α), (liftrel R) a b → R (f a) (f b)
    infix `⊧`:50 := respects
    constant quot.oplift {α: Type u} {β: Type v}: Π {R: α → α → Prop} (f: op β α), (f ⊧ R) → (β → quot R) → quot R
    infix `ℒ`:50 := quot.oplift
    def uncurry {α: Type u} (R: α → α → Prop): set (α × α) := λ a, R a.fst a.snd
    notation R`̃ ` := uncurry R
    def ker {α: Type u} {β: Type v} (f : α → β): set (α × α) := {a | f a.fst = f a.snd}
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
    -- END

  end ualib

-------------------------------

.. index:: ! setoid, kernel

.. _setoids:

Setoids
-------

This section documents the 
In a quotient construction ``α/R``, the relation ``R`` is typically an *equivalence relation*.  If not, we can extend it to one.  Indeed, given a binary relation ``R``, define ``R'`` according to the rule

  ``R' a b`` :math:`\quad` iff :math:`\quad` ``a/R = b/R``.

Then ``R'`` is an equivalence relation---namely, the :term:`kernel` of the function ``a ↦ a/R``.

The axiom ``quot.sound`` given at the end of the last section asserts that ``R a b`` implies ``R' a b``.

Using ``quot.lift`` and ``quot.ind``, we can show that ``R'`` is the smallest equivalence relation containing ``R``. In particular, if ``R`` is already an equivalence relation, then we have ``R = R'``.

Here is the beginning of the ``setoid`` namespace in `lean-ualib`_ from the source file `setoid.lean`_.

::

  import quotient

  -- Universes u, v, w.
  -- Generally we will use these for, respectively,
  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib

    section setoid

      class setoid (α: Type u) :=
      (R: α → α → Prop) (iseqv: equivalence R)

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

    def quotient (α: Type u) (s: setoid α) := @quot α setoid.R

    axiom quotient.exact: ∀ {α: Type u} [setoid α] {a b: α},
    (a/setoid.R = b/setoid.R → a ≈ b)

  end ualib

Given a type ``α``, a relation ``r`` on ``α``, and a proof ``p`` that ``r`` is an equivalence relation, we can define ``setoid.mk p`` as an instance of the setoid class.

::

  import quotient

  universe u   -- carrier (universe) types,          (α)
  universe v   -- type of operation symbols,         (β)
  universe w   -- arity types.                       (γ)

  namespace ualib

    section setoid

      class setoid (α: Type u) := (R: α → α → Prop) (iseqv: equivalence R)

      infix `≈` := setoid.R

      variable α: Type u
      variable [s: setoid α]
      include s

      theorem refl (a: α): a ≈ a := (@setoid.iseqv α s).left a

      theorem symm {a b: α}: a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c := λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂

    end setoid

  -- BEGIN

  section examples

    parameters {α: Type u} {r : α → α → Prop} {p: equivalence r}
    #check setoid.mk r p -- {R := r, iseqv := p} : setoid α

    variables {Q: α → α → Prop} (a: α) (q: equivalence Q)
    -- test notation for quotient --
    #check quot Q          -- quot Q: Type u
    #check @quot.mk α a Q  -- a/Q: quot Q
    #check quot.mk a Q     -- a/Q: quot Q
    #check a/Q             -- a/Q: quot Q

    #check @quot.ind α Q
    -- ∀ {β: quot Q → Prop},
    -- (∀ (a: α), β (a/Q)) → ∀ (q: quot Q), β q

    variables (β : quot Q → Prop) (h: ∀ (a: α), β (a/Q))

    #check @quot.ind α Q β h -- ∀ (q: quot Q), β q

    #check quot.lift Q  -- Q ⫢ ?M_1 → quot ?M_1 → α → Prop

    #check @quot.lift α Q
    -- Π {β: Type u} (f: α → β), f ⫢ Q → ualib_quotient.quot Q → β

    #check @quot.sound α Q   -- ∀ (a b: α), Q a b → a/Q = b/Q

  end examples
  -- END


Now let us define a ``quotient`` type which will make it a little easier to work with quotients.

::

  import quotient
  namespace setoid
    universes u v
    class setoid (α: Sort u) :=(R: α → α → Prop) (iseqv: equivalence R)
    namespace setoid
      infix ` ≈ ` := setoid.R
      variable (α: Sort u)
      variable [s: setoid α]
      include s
      theorem refl (a: α): a ≈ a := (@setoid.iseqv α s).left a
      theorem symm {a b: α}: a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h
      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c := λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid

    -- BEGIN
    def quotient (α: Sort u) (s: setoid α) := @quot α setoid.R

    constant setoid.quotient.exact:
    ∀ {α: Sort u} [setoid α] {a b: α},
    a/setoid.R = b/setoid.R → a ≈ b

    #check @quotient.exact α
    -- ∀ [s: setoid α] {a b: α}, ⟦a⟧ = ⟦b⟧ → a ≈ b

    #check @setoid.quotient.exact α (setoid.mk r p)
    -- ∀ {a b: α}, a/setoid.R = b/setoid.R → a ≈ b
    -- END

  end setoid

The resulting constants ``quotient.mk``, ``quotient.ind``, ``quotient.lift``, and ``quotient.sound`` are available and are simply specializations of the corresponding elements of ``quot``.

The fact that type class inference can find the setoid associated to a type ``α`` has the following benefits:

First, we can use the notation ``a ≈ b`` for ``setoid.R a b``, where the instance of ``setoid`` is implicit in the notation ``setoid.R``.  (The ≈ symbol is produced by typing ``\app`` or ``\approx``.)

We can use the generic theorems ``setoid.refl``, ``setoid.symm``, ``setoid.trans`` to reason about the relation. Specifically with quotients we can use the generic notation ``a/setoid.R`` for ``quot.mk setoid.R a`` where the instance of ``setoid`` is implicit in the notation ``setoid.R``, as well as the theorem ``quotient.exact``.

::

  import quotient
  namespace setoid
    universes u v
    class setoid (α: Sort u) :=(R: α → α → Prop) (iseqv: equivalence R)
    namespace setoid
      infix ` ≈ ` := setoid.R
      variable (α: Sort u)
      variable [s: setoid α]
      include s
      theorem refl (a: α): a ≈ a := (@setoid.iseqv α s).left a
      theorem symm {a b: α}: a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h
      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c := λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid

    def quotient (α: Sort u) (s: setoid α) := @quot α setoid.R

    constant setoid.quotient.exact: ∀ {α: Sort u} [setoid α] {a b: α},
    a/setoid.R = b/setoid.R → a ≈ b

    variables (α: Type u) (r : α → α → Prop) (p: equivalence r)
    variables (a: α) (Q: α → α → Prop)

    -- BEGIN
    variables (β : Type v) [setoid β] (b: β)
    variable B : quotient.quot Q → Prop
    variable h: ∀ (a: α), B (a/Q)

    #check b/setoid.R             -- quotient.quot setoid.R

    #check @quotient.quot.ind α Q
    -- quotient.quot.ind:
    -- ∀ {β: quotient.quot Q → Prop},
    --   (∀ (a: α), β (a/Q)) → ∀ (q: quotient.quot Q), β q

    #check @quotient.quot.ind α Q B h
    -- quotient.quot.ind h:
    -- ∀ (q: quotient.quot Q), B q

    #check @quotient.quot.lift α Q
    -- quotient.quot.lift:
    -- Π {β: Sort u} (f: α → β), f ⫢ Q → quotient.quot Q → β

    #check @quotient.quot.sound α Q
    -- quotient.quot.sound:
    -- ∀ {a b: α}, Q a b → a/Q = b/Q

    #check @setoid.quotient.exact α (setoid.mk r p)
    -- ∀ {a b: α}, a/setoid.R = b/setoid.R → a ≈ b
    -- END

  end setoid

Together with ``quotient.sound``, this implies that the elements of the quotient correspond exactly to the equivalence classes of elements in ``α``.

::

  import quotient
  namespace setoid
    universes u v
    class setoid (α: Sort u) :=(R: α → α → Prop) (iseqv: equivalence R)
    namespace setoid
      infix ` ≈ ` := setoid.R
      variable (α: Sort u)
      variable [s: setoid α]
      include s
      theorem refl (a: α): a ≈ a := (@setoid.iseqv α s).left a
      theorem symm {a b: α}: a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h
      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c := λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
    def quotient (α: Sort u) (s: setoid α) := @quot α setoid.R
    constant setoid.quotient.exact: ∀ {α: Sort u} [setoid α] {a b: α}, a/setoid.R = b/setoid.R → a ≈ b
    variables (α: Type u) (r : α → α → Prop) (p: equivalence r)
    variables (a: α) (Q: α → α → Prop)
    variables (β : Type v) [setoid β] (b: β)
    variable B : quotient.quot Q → Prop
    variable h: ∀ (a: α), B (a/Q)

    -- BEGIN
    def Qeq : α → α → Prop := λ (a b : α), a/Q = b/Q

    theorem reflQ {a: α} : @Qeq α Q a a :=
    have a/Q = a/Q, from rfl, this

    theorem symmQ {a b: α}: @Qeq α Q a b → @Qeq α Q b a := eq.symm

    theorem transQ {a b c: α}:
    @Qeq α Q a b → @Qeq α Q b c → @Qeq α Q a c := eq.trans
    -- END

  end setoid

-------------------------------------

.. rubric:: Footnotes

.. [1]
   The issue here is whether we can define :math:`fₗ (x/R)` without invoking some :term:`Choice` axiom.  Indeed, :math:`x/R` is a class of inhabitants of type :math:`α` and, if :math:`fₗ(x/R)` is taken to be the value returned when :math:`f` is evaluated at some member of this class, then we must have a way to choose one such member.  Note that we use :math:`x/R` to denote the :math:`R`-class containing :math:`x`, while the notation defined in the :term:`LSTL` for this :math:`R`-class is :math:`⟦x⟧`.

.. [2]
   Definitions in the ``ualib`` namespace are not part of Lean's built-in logical framework, so the computation principles we would like these definitions to satisfy must be assumed (as an ``axiom``), rather than proved (as a ``theorem``). If we had stuck with the ``quot`` constants defined in the `Lean Standard Library`_ (instead of defining our own versions of these constants), we could have *proved* the the ``flift_comp_principle``,  since this principle is taken as part of the logical framework of the :term:`LSTL`.

.. include:: hyperlink_references.rst


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

