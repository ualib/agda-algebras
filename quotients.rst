.. _quotients:

.. highlight:: lean

.. index:: equivalence class, ! quotient

Quotients [1]_
===============

Given an :term:`equivalence relation` on :math:`A`, there is an important mathematical construction known as forming the *quotient* of :math:`A` modulo the given equivalence relation.

As in :numref:`equivalence-relation`, for each :math:`a ∈ A`, we let :math:`a/{≡}` denote the set :math:`\{ b ∈ A ∣ b ≡ a \}` of elements in :math:`A` that are equivalent to :math:`a` modulo ≡. We call :math:`a/{≡}` the ≡-class of :math:`A` containing :math:`a`.  Below we will sometimes use the notation :math:`a/{≡}` to denote the class :math:`a/{≡}`.

The collection :math:`\{ a/{≡} ∣ a ∈ A \}` of all such equivalence classes is denoted by :math:`A/{≡}` and called the **quotient of** :math:`A` **modulo** ≡.

Equivalence captures a weak notion of equality. If two elements of :math:`A` are equivalent modulo ≡, they are not necessarily the same, rather, the way in which they do differ is not relevant to us.

.. proof:example::

   Consider this "real-world" example in which it is useful to "mod out"---i.e., ignore by forming a quotient---irrelevant information.

   In a study of image data for the purpose of facial recognition---specifically, the task of identifying a particular person in different photographs---the orientation of a person's face is unimportant.  Indeed, it would be silly to infer that faces in multiple photos belong to different people on the basis that the faces are orientated differently with respect to the camera's field of view.

   In this application it seems reasonable to collect in a single group (equivalence class) those faces that differ only with respect to their spacial orientations.  We might call two faces from the same class "equivalent modulo orientation."

As we have seen, equivalence classes collect similar objects together, unifying them into a single entity (e.g., the collection of all images of the face of a particular individual).  Thus :math:`A/{≡}` is a version of :math:`A` where similar elements are compressed into a single element, so irrelevant distinctions can be ignored.

.. proof:example::

   The equivalence relation of **congruence modulo 5** on the set of integers partitions ℤ into five equivalence classes---namely, :math:`5ℤ`, :math:`1 + 5ℤ`, :math:`2+5ℤ`, :math:`3+5ℤ` and :math:`4+5ℤ`.  Here, :math:`5ℤ` is the set :math:`\{\dots, -10, -5, 0, 5, 10, 15, \dots\}` of multiples of 5, and :math:`2+5ℤ` is the set :math:`\{\dots, -8, -3, 2, 7, 12, \dots\}` of integers that differ from a multiple of 5 by 2.

.. index:: pair: respect; preserve

Lifting functions
-----------------

Let ``α`` be a type and ``ρ`` a binary relation on ``α``.  Define the **quotient** ``α/ρ`` (read, "alpha modulo rho") to be the collection of ``ρ``-classes of ``α``.

That is, for each ``a:α``, there is a class ``a/ρ`` consisting of all ``b:α`` such that ``ρ a b`` (i.e., ``(a,b) ∈ ρ``). Moreover, each class ``a/ρ`` has type ``α/ρ``.

.. index:: lift; of a function, reduction rule

Let ``f: α → β`` be a function. We say that ``f`` **lifts** from ``α`` to ``α/ρ`` provided the implication

  ``ρ x y  →  f x = f y``
  
holds for all ``x`` and ``y`` of type ``α``.

(**Notation**. If ``f`` :term:`lifts` from ``α`` to ``α/ρ`` we write ``f ⊧ ρ``; the symbol ⊧ is produced by typing ``\models``.)

If ``f ⊧ ρ``, then there is a function ``fₗ : α/ρ → β`` defined by ``fₗ ⟦x⟧ = f x``, for each ``⟦x⟧: α/ρ`` .

We call this ``fₗ`` the **lift** of ``f`` from ``α`` to ``α/ρ``.  (The symbol ``fₗ`` is produced by typing ``f\_l``.)

The `Lean Standard Library`_ (:term:`LSL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation ``fₗ ⟦x⟧ = f x`` available as a definitional reduction rule. [2]_

Here are four such constants from the :term:`LSL`.

::

  namespace quotient

    -- BEGIN
    universes u v

    -- The quotient type former.
    constant quot: Π {α: Sort u}, (α → α → Prop) → Sort u

    -- So quot takes a type α and a relation ρ ⊆ α × α
    -- and forms the collection α/ρ of ρ-classes.

    -- Given α and ρ ⊆ α × α, map each a:α to its ρ-class.
    constant quot.mk: Π {α: Sort u} (ρ: α → α → Prop), α → quot ρ

    -- So, if ρ: α → α → Prop and a:α, then quot.mk ρ a is the
    -- ρ-class a/ρ containing a, which has type quot ρ.

    -- Assume each element of quot ρ is a ρ-class, like quot.mk ρ a.
    axiom quot.ind:
    ∀ {α: Sort u} {ρ: α → α → Prop} {β: quot ρ → Prop},
    (∀ a, β (quot.mk ρ a)) → ∀ (q: quot ρ), β q

    -- Take a function f: α → β and a proof h : f ⊧ ρ, and
    -- return the lift of f to quot ρ.
    constant quot.lift:
    Π {α: Sort u} {ρ: α → α → Prop} {β: Sort u} (f: α → β),
    (∀ a b, ρ a b → f a = f b) → quot ρ → β

    -- END
  end quotient

The first of these takes a type ``α`` and a binary relation ``ρ`` on ``α`` and forms the type ``quot ρ`` (or ``@quot α ρ``, if we wish to make the first parameter explicit).

That is, for each ``α: Sort u``, we form the function type ``@quot α`` which takes a binary relation ``ρ: α → α → Prop`` and returns the quotient type ``quot ρ``, each element of which is an equivalence class, say, ``a/ρ``, where ``a:α``.

The second constant, ``quot.mk``, takes ``α`` and ``ρ: α → α → Prop`` and forms the function that maps each ``a:α`` to its ρ-class ``quot.mk ρ a``, of type ``quot ρ``.

The third, ``quot.ind``, is the axiom asserting that every element of ``quot ρ`` is of the form ``quot.mk ρ a``.

Finally, ``quot.lift`` takes a function ``f: α → β`` and, if ``h`` is a proof that ``f`` respects ``ρ`` (i.e., ``f ⊧ ρ``), then ``quot.lift f h`` is the corresponding function on ``quot ρ``, that is, the lift of ``f`` to ``quot ρ``.

The idea is that for each ``a:α``, the function ``quot.lift f h`` maps each ``quot.mk ρ a`` (the ``ρ``-class containing ``a``) to ``f a``, where ``h`` shows that this function is well defined.

In fact, this computation principle is declared as a reduction rule, as the proof of the theorem at the end of this code block makes clear.

::

  variables (α β: Type) (ρ: α → α → Prop) (a: α)

  -- the quotient type
  #check (quot ρ: Type)

  -- the class of a
  #check (quot.mk ρ a: quot ρ)

  variable f: α → β
  variable h: ∀ a₁ a₂, ρ a₁ a₂ → f a₁ = f a₂

  -- the corresponding function on quot r
  #check (quot.lift f h: quot ρ → β)

  -- the computation principle
  theorem thm: quot.lift f h (quot.mk ρ a) = f a := rfl

Here's an example that includes a bit of syntactic sugar.

::

   namespace quotient
    universes u v
    constant quot: Π {α: Sort u}, (α → α → Prop) → Sort u
    constant quot.mk: Π {α: Sort u} (ρ: α → α → Prop), α → quot ρ

    axiom quot.ind:
    ∀ {α: Sort u} {ρ: α → α → Prop} {β: quot ρ → Prop},
    (∀ a, β (quot.mk ρ a)) → ∀ (q: quot ρ), β q

    constant quot.lift:
    Π {α: Sort u} {ρ: α → α → Prop} {β: Sort u} (f: α → β),
    (∀ a b, ρ a b → f a = f b) → quot ρ → β

    -- BEGIN
    variables (α β : Type) (f : α → β) (ρ : α → α → Prop)

    -- notation for "f respects ρ"
    notation f `⊧` ρ := ∀ a b, ρ a b → f a = f b

    variable h: f ⊧ ρ

    local notation `fₗ` := quot.lift f h

    #check f ⊧ ρ                 -- Prop
    #check quot.lift f h         -- quot (λ (a b : α), ρ a b) → β
    #check fₗ                    -- quot (λ (a b : α), ρ a b) → β
    -- END

  end quotient

The constants ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` are not very strong.  (Indeed, ``quot.ind`` is satisfied if ``quot ρ`` is just ``α``, and ``quot.lift`` is the identity function.)

For that reason, these four constants are not considered "axioms," as is verified in the following code segment which asks Lean to ``#print`` the axioms used by ``thm``. (Lean responds, "``no axioms``.")

::

  variables (α β: Type) (ρ: α → α → Prop)
  variables (a: α) (f: α → β)

  theorem thm (h: ∀ a₁ a₂, ρ a₁ a₂ → f a₁ = f a₂):
  quot.lift f h (quot.mk ρ a) = f a := rfl

  #print axioms thm   -- no axioms

Like inductively defined types and their associated constructors and recursors, the four constants above are viewed as part of the logical framework.

What makes ``quot`` into a bona fide quotient is the ``quot.sound`` axiom which asserts that if two elements of ``α`` are related by ``ρ``, then they are identified in the quotient ``α/ρ``.

::

  namespace quotient
    universe u

    -- BEGIN
    axiom quot.sound: ∀ {α: Type u} {ρ: α → α → Prop} {a b: α},
    ρ a b → quot.mk ρ a = quot.mk ρ b
    -- END
  end quotient

------------------------

Operations of higher arity
~~~~~~~~~~~~~~~~~~~~~~~~~~

Let ``f: (ρf → α) → α`` be an operation of arity ``ρf`` and let ``τ: ρf → (α × α)`` be a ``ρf``-tuple of pairs that belong to the relation ``r ⊆ α × α``.

To say that ``f`` respects ``r ⊆ α × α`` means the following

  For every ``ρf``-tuple of pairs from ``r``, the pair ``(f (fst ∘ τ), f (snd ∘ τ))`` also belongs to ``r``.

In other words, if we evaluate ``f`` at all the first coordinates of ``τ``, obtaining ``f (fst ∘ τ)``, and then at all second coordinates of ``τ``, obtaining ``f (snd ∘ τ)``, then the result is a pair that also belongs to ``r``.

Of course, if ``τ: ρf → (α × α)``, then ``(fst ∘ τ) : ρf → α`` and so ``f (fst ∘ τ)`` makes sense and has type ``α``.

----------------------------------------

.. _setoids:

.. index:: ! setoid, kernel

Setoids
-------

In a quotient construction α/ρ, the relation ρ is typically an *equivalence relation*.  If not, we can extend it to one.  Indeed, given a binary relation ``ρ``, we define ``ρ'`` according to the rule

  ``ρ' a b`` :math:`\quad` iff :math:`\quad` ``quot.mk ρ a = quot.mk ρ b``.
  
Then ``ρ'`` is an equivalence relation---namely, the **kernel** of the function ``a ↦ quot.mk ρ a``.

The axiom ``quot.sound`` given at the end of the last section asserts that ``ρ a b`` implies ``ρ' a b``.

Using ``quot.lift`` and ``quot.ind``, we can show that ``ρ'`` is the smallest equivalence relation containing ``ρ``. In particular, if ``ρ`` is already an equivalence relation, then we have ``ρ = ρ'``.

To support this common use case, the :term:`LSL` defines a **setoid**, which is simply a pair consisting of a type along with an associated equivalence relation.

::

  universe u
  namespace quotient

    -- BEGIN
    class setoid (α: Type u) :=
    (ρ: α → α → Prop) (iseqv: equivalence ρ)

    namespace setoid
      infix `≈` := setoid.ρ

      variable {α: Type u}
      variable [s: setoid α]
      include s

      theorem refl (a: α) : a ≈ a :=
      (@setoid.iseqv α s).left a

      theorem symm {a b: α}: a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
    -- END

  end quotient

Given a type ``α``, a relation ``ρ`` on ``α``, and a proof ``p`` that ``ρ`` is an equivalence relation, we can define ``setoid.mk p`` as an instance of the setoid class.

::

  universe u
  namespace quotients

    -- BEGIN
    def quotient {α: Type u} (s: setoid α) :=
    @quot α setoid.r
    -- END

  end quotients

The constants ``quotient.mk``, ``quotient.ind``, ``quotient.lift``, and ``quotient.sound`` are nothing more than the specializations of the corresponding elements of ``quot``. The fact that type class inference can find the setoid associated to a type ``α`` brings a number of benefits.

First, we can use the notation ``a ≈ b`` (entered with ``\eq`` in Emacs) for ``setoid.r a b``, where the instance of ``setoid`` is implicit in the notation ``setoid.r``. We can use the generic theorems ``setoid.refl``, ``setoid.symm``, ``setoid.trans`` to reason about the relation. Specifically with quotients we can use the generic notation ``⟦a⟧`` for ``quot.mk setoid.r`` where the instance of ``setoid`` is implicit in the notation ``setoid.r``, as well as the theorem ``quotient.exact``:

::

  universe u

  -- BEGIN
  #check (@quotient.exact: 
         ∀ {α: Type u} [setoid α] {a b: α}, 
         ⟦a⟧ = ⟦b⟧ → a ≈ b)
  -- END

Together with ``quotient.sound``, this implies that the elements of the quotient correspond exactly to the equivalence classes of elements in ``α``.

Recall that in the `standard library <lean_src>`_, ``α × β`` represents the Cartesian product of the types ``α`` and ``β``. To illustrate the use of quotients, let us define the type of **unordered pairs** of elements of a type ``α`` as a quotient of the type ``α × α``.

First, we define the relevant equivalence relation:

::

  universe u

  private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

  infix `~` := eqv

The next step is to prove that ``eqv`` is in fact an equivalence relation, which is to say, it is reflexive, symmetric and transitive. We can prove these three facts in a convenient and readable way by using dependent pattern matching to perform case-analysis and break the hypotheses into pieces that are then reassembled to produce the conclusion.

::

  universe u

  private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

  local infix `~` := eqv

  -- BEGIN
  open or

  private theorem eqv.refl {α : Type u}:
  ∀ p: α × α, p ~ p := assume p, inl ⟨rfl, rfl⟩

  private theorem eqv.symm {α: Type u}:
  ∀ p₁ p₂: α × α, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩):=
    inl ⟨symm a₁b₁, symm a₂b₂⟩
  | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩):=
    inr ⟨symm a₂b₁, symm a₁b₂⟩

  private theorem eqv.trans {α: Type u}:
  ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩):=
    inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
  | (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩):=
    inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
  | (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩):=
    inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
  | (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩):=
    inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

  private theorem is_equivalence (α: Type u):
  equivalence (@eqv α):= mk_equivalence (@eqv α)
  (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)
  -- END

We open the namespaces ``or`` and ``eq`` to be able to use ``or.inl``, ``or.inr``, and ``eq.trans`` more conveniently.

Now that we have proved that ``eqv`` is an equivalence relation, we can construct a ``setoid (α × α)``, and use it to define the type ``uprod α`` of unordered pairs.

::

  universe u

  private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

  local infix `~` := eqv

  open or

  private theorem eqv.refl {α: Type u} : ∀ p: α × α, p ~ p :=
  assume p, inl ⟨rfl, rfl⟩

  private theorem eqv.symm {α: Type u} : ∀ p₁ p₂: α × α, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
  | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

  private theorem eqv.trans {α: Type u} : ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
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
  instance uprod.setoid (α: Type u): setoid (α × α) :=
  setoid.mk (@eqv α) (is_equivalence α)

  definition uprod (α: Type u): Type u :=
  quotient (uprod.setoid α)

  namespace uprod
    definition mk {α: Type u} (a₁ a₂: α): uprod α:=
    ⟦(a₁, a₂)⟧

    local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂
  end uprod
  -- END

Notice that we locally define the notation ``{a₁, a₂}`` for ordered pairs as ``⟦(a₁, a₂)⟧``. This is useful for illustrative purposes, but it is not a good idea in general, since the notation will shadow other uses of curly brackets, such as for records and sets.

We can easily prove that ``{a₁, a₂} = {a₂, a₁}`` using ``quot.sound``, since we have ``(a₁, a₂) ~ (a₂, a₁)``.

::

  universe u

  private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

  local infix `~` := eqv

  open or

  private theorem eqv.refl {α: Type u}: ∀ p: α × α, p ~ p :=
  assume p, inl ⟨rfl, rfl⟩

  private theorem eqv.symm {α: Type u}: ∀ p₁ p₂: α × α, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
  | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

  private theorem eqv.trans {α: Type u}:
  ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
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

  private theorem is_equivalence (α: Type u):
  equivalence (@eqv α) := mk_equivalence (@eqv α)
  (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

  instance uprod.setoid (α: Type u): setoid (α × α) :=
  setoid.mk (@eqv α) (is_equivalence α)

  definition uprod (α: Type u): Type u :=
  quotient (uprod.setoid α)

  namespace uprod
    definition mk {α: Type u} (a₁ a₂: α): uprod α :=
    ⟦(a₁, a₂)⟧

    local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂

    -- BEGIN
    theorem mk_eq_mk {α: Type} (a₁ a₂: α):
    {a₁, a₂} = {a₂, a₁} := quot.sound (inr ⟨rfl, rfl⟩)
    -- END
  end uprod

To complete the example, given ``a:α`` and ``u: uprod α``, we define the proposition ``a ∈ u`` which should hold if ``a`` is one of the elements of the unordered pair ``u``. First, we define a similar proposition ``mem_fn a u`` on (ordered) pairs; then we show that ``mem_fn`` respects the equivalence relation ``eqv`` with the lemma ``mem_respects``. This is an idiom that is used extensively in the Lean `standard library <lean_src>`_.

::

  universe u

  private definition eqv {α: Type u} (p₁ p₂: α × α): Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

  local infix `~` := eqv

  open or

  private theorem eqv.refl {α: Type u}: ∀ p: α × α, p ~ p :=
  assume p, inl ⟨rfl, rfl⟩

  private theorem eqv.symm {α: Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
  | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

  private theorem eqv.trans {α: Type u} : ∀ p₁ p₂ p₃: α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
    inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
  | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
    inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
  | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
    inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
  | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
    inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

  private theorem is_equivalence (α: Type u): equivalence (@eqv α) :=
  mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

  instance uprod.setoid (α: Type u): setoid (α × α) :=
  setoid.mk (@eqv α) (is_equivalence α)

  definition uprod (α: Type u): Type u :=
  quotient (uprod.setoid α)

  namespace uprod
    definition mk {α: Type u} (a₁ a₂: α): uprod α :=
    ⟦(a₁, a₂)⟧

    local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂

    theorem mk_eq_mk {α: Type} (a₁ a₂: α): {a₁, a₂} = {a₂, a₁} :=
    quot.sound (inr ⟨rfl, rfl⟩)

    -- BEGIN
    private definition mem_fn {α: Type} (a: α):
      α × α → Prop
    | (a₁, a₂) := a = a₁ ∨ a = a₂

    -- auxiliary lemma for proving mem_respects
    private lemma mem_swap {α: Type} {a: α}:
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
    | (a₁, a₂) := propext (iff.intro
        (λ l: a = a₁ ∨ a = a₂,
          or.elim l (λ h₁, inr h₁) (λ h₂, inl h₂))
        (λ r: a = a₂ ∨ a = a₁,
          or.elim r (λ h₁, inr h₁) (λ h₂, inl h₂)))

    private lemma mem_respects {α: Type}:
      ∀ {p₁ p₂: α × α} (a: α),
        p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
    | (a₁, a₂) (b₁, b₂) a (inl ⟨a₁b₁, a₂b₂⟩) :=
      by { dsimp at a₁b₁, dsimp at a₂b₂, rw [a₁b₁, a₂b₂] }
    | (a₁, a₂) (b₁, b₂) a (inr ⟨a₁b₂, a₂b₁⟩) :=
      by { dsimp at a₁b₂, dsimp at a₂b₁, rw [a₁b₂, a₂b₁],
            apply mem_swap }

    def mem {α: Type} (a: α) (u: uprod α): Prop :=
    quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_respects a e)

    local infix `∈` := mem

    theorem mem_mk_left {α: Type} (a b: α): a ∈ {a, b} :=
    inl rfl

    theorem mem_mk_right {α: Type} (a b: α): b ∈ {a, b} :=
    inr rfl

    theorem mem_or_mem_of_mem_mk {α: Type} {a b c: α}:
      c ∈ {a, b} → c = a ∨ c = b :=
    λ h, h
    -- END
  end uprod

For convenience, the `standard library <lean_src>`_ also defines ``quotient.lift₂`` for lifting binary functions, and ``quotient.ind₂`` for induction on two variables.

We close this section with some hints as to why the quotient construction implies function extenionality. It is not hard to show that extensional equality on the ``Π(x:α), β x`` is an equivalence relation, and so we can consider the type ``extfun α β`` of functions "up to equivalence." Of course, application respects that equivalence in the sense that if ``f₁`` is equivalent to ``f₂``, then ``f₁ a`` is equal to ``f₂ a``. Thus application gives rise to a function ``extfun_app: extfun α β → Π(x:α), β x``. But for every ``f``, ``extfun_app ⟦f⟧`` is definitionally equal to ``λ x, f x``, which is in turn definitionally equal to ``f``. So, when ``f₁`` and ``f₂`` are extensionally equal, we have the following chain of equalities:

::

  f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂

As a result, ``f₁`` is equal to ``f₂``.

-------------------------------------

.. rubric:: Footnotes

.. [1]
   Some material in this chapter is borrowed from the `Axioms and Computation`_ section of the `Theorem Proving in Lean`_ tutorial.


.. [2]
   At issue here is the question of whether we can define ``fₗ ⟦x⟧`` without invoking some :term:`Choice` axiom.  Indeed, ``⟦x⟧`` is a class of inhabitants of type ``α`` and, if ``fₗ ⟦x⟧`` is taken to be the value returned when ``f`` is evaluated at some member of this class, then we must have a way to choose one such member.

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
