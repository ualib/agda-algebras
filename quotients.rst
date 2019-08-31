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

Quotient in Lean
-----------------

.. index:: keyword: quot, quot.mk, quot.ind

Let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.

Define the **quotient** :math:`α/R` (read, "alpha modulo :math:`R`") to be the collection of :math:`R`-classes in :math:`α`. That is, for each :math:`x:α`, there is a class :math:`x/R ⊆ α` consisting of all :math:`y:α` such that :math:`x \mathrel R y`, that is,

.. math:: x/R = \{y : α ∣  x \mathrel R y\}.

The type of the class :math:`x/R` is a **quotient type**, denoted in this case by :math:`α/R`.

The `Lean Standard Library`_ (:term:`LSTL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation :math:`fₗ(x/R) = f x` available as a definitional reduction rule. [1]_

Four such constants that are defined in the :term:`LSTL` are also defined in the `lean-ualib`_, as follows:

.. index:: lift; of a function, reduction rule

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

.. index:: ! type of; (quotients)

.. index:: ! lift of; (functions)

.. _lifts-of-functions:

Lifts of functions
------------------

Let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.


Let :math:`f: α → β` be a function. We say that :math:`f` **lifts** from :math:`α` to :math:`α/R` provided the implication

.. math:: (x, y) ∈ R \ → \ f x = f y
   :label: lift

holds for all :math:`x` and :math:`y` of type :math:`α`.

Evidently, implication :eq:`lift` holds iff :math:`R` is contained in the **kernel** of :math:`f`; that is,

.. math:: R ⊆ \ker f := \{(x, y) ∈ α × α ∣ f x = f y\}.

Let :math:`f[R] := \{(f x, f y) ∈ β × β ∣ (x, y) ∈ R\}` and let :math:`0_α := \{(x, y) ∈ α × α ∣ x = y\}` be the identity relation on :math:`α`. Then :math:`f` :term:`lifts` from :math:`α` to :math:`α/R` if and only if :math:`f[R] ⊆ 0_α` if and only if :math:`R ⊆ \ker f`.

If :math:`f` :term:`lifts` from :math:`α` to :math:`α/R`, then there is a function :math:`fₗ : α/R → β` defined by :math:`fₗ (x/R) = f x`, for each :math:`x/R: α/R`. We call this function the **lift** of :math:`f` from :math:`α` to :math:`α/R`.

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

.. _lifts-of-operations:

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

Let :math:`α` and :math:`β` be types, let :math:`R ⊆ α × α` be a binary relation and :math:`g : (β → α) → α` a :math:`β`-ary operation. Recall that the function type :math:`β → α` may be viewed as the type of :math:`β`-tuples of elements from :math:`α`.

Define a **lift of tuples** :math:`[\ ]: (β → α) → β → α/R` as follows: for each tuple :math:`τ: β → α`, let :math:`[τ] : β → α/R` be the :math:`β`-tuple that takes each :math:`i: β` to the :math:`R`-class containing :math:`τ\ i`; that is,

.. math:: [τ]\ i = (τ\ i)/R.

We would like to define a **lift of operations** as follows: for each :math:`β`-ary operation :math:`g: (β → α) → α`, let the lift of :math:`g` be the function of type :math:`(β → α/R) → α/R` that takes each (lifted) tuple :math:`[τ]: β → α/R` to the :math:`R`-class containing :math:`g τ`.

Note, however, that this function is well-defined if and only if :math:`g` :term:`respects` :math:`R`, so we must supply a proof that :math:`g ⊧ R` whenever we wish to consider the lift of :math:`g` from :math:`(β → α) → α` to :math:`(β → α/R) → α/R`.

Below, when we implement lifts of tuples and operations in Lean, we will introduce the symbol ``ℒ`` to denote the lift of operations, with the following typing judgment:

  ``ℒ : Π {R: α → α → Prop} (g: (β → α) → α), (g ⊧ R) → (β → α/R) → α/R``.

As such, ``ℒ`` takes a relation ``R: α → α → Prop``, an operation ``g: (β → α) → α``, and a proof ``p: g ⊧ R``, and constructs the operation ``g ℒ p: (β → α/R) → α/R``, defined as follows: for each ``τ: β → α``,

  ``(g ℒ p) [τ]  := (g τ) / R``.


The definitions of lifts of tuples and operations in :numref:`lifts-of-operations` are fundamentally different from that of the *lift of a function* given in :numref:`lifts-of-functions` and defined in the :term:`LSTL`. To account for this, we must introduce new lifting constants.

The next section of code begins by redefining the constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` and then defines three new lift constants, ``quot.colift``, ``quot.tlift``, and ``quot.oplift``.

By redefining the standard ``quot`` constants, the ``ualib`` namespace puts all quotient constants on the same "level" in the sense that all are now "user-defined" and thus none is a built-in part of Lean's logical framework.  As such, their associated computation principles will be added as axioms rather than proved as theorems.

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

Finally, let us assert some computation principles for these lift operators defined above. [2]_

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

-------------------------------------

.. rubric:: Footnotes

.. [1]
   The issue here is whether we can define :math:`fₗ (x/R)` without invoking some form of the axiom of :term:`Choice` axiom.  Indeed, :math:`x/R` is a class of inhabitants of type :math:`α` and, if :math:`fₗ(x/R)` is taken to be the value returned when :math:`f` is evaluated at some member of this class, then we must have a way to choose one such member.  Note that we use :math:`x/R` to denote the :math:`R`-class containing :math:`x`, while the notation defined in the :term:`LSTL` for this :math:`R`-class is :math:`⟦x⟧`.

.. [2]
   Definitions in the ``ualib`` namespace are not part of Lean's built-in logical framework, so the computation principles we would like these definitions to satisfy must be assumed (as an ``axiom``), rather than proved (as a ``theorem``). If we had stuck with the ``quot`` constants defined in the `Lean Standard Library`_ (instead of defining our own versions of these constants), we could have *proved* the the ``flift_comp_principle``,  since this principle is taken as part of the logical framework of the :term:`LSTL`.


-------------------------------------

.. include:: hyperlink_references.rst
