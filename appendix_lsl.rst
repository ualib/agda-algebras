.. include:: _static/math_macros.rst

.. highlight:: lean

.. _the-stl:

=======================
Appendix. The Lean STL
=======================

We first collect for easy reference some links to some of the basic components of the `Lean Standard Library`_ (:term:`LSTL`).  Thereafter, we dissect some of these components that are crucial for using Lean to do universal algebra.

Some basic components
---------------------

While Lean doesn't have a formal API, per se, you can browse the source code of the core Lean library to see what built-in types, definitions, and theorems are available in the :term:`LSTL`.

For example, some of the most important of these objects are implemented in the files listed below. These (and many more) can be found in (or under) the `lean/library/init`_ directory of the official `Lean github repository`_.

+ In `lean/library/init`_

  + `classical.lean`_
  + `core.lean`_
  + `function.lean`_
  + `logic.lean`_
  + `wf.lean`_

+ In `lean/library/init/data`_

  + `nat (dir)`_
  + `prod.lean`_
  + `quot.lean`_
  + `set.lean`_
  + `setoid.lean`_
  + `sigma (dir)`_

+ In `lean/library/init/algebra`_

  + `classes.lean`_
  + `functions.lean`_
  + `order.lean`_

----------------------------------------------------------

.. _quotients-in-the-LSTL:

Quotients
---------

To gain a better understanding of the implementation of quotients in the `Lean Standard Library`_, we will dissect the code in the file `quot.lean`_, which resides in the `lean/library/init/data`_ directory of the :term:`LSTL`.

We will divide the `quot.lean`_ file into three parts and dissect each part separately below, but first we note that at the top of the file `quot.lean`_ are some ``import`` statements which import some components of the :term:`LSTL`---namely,

+ `sigma/basic.lean`_
+ `logic.lean`_
+ `propext.lean`_
+ `setoid.lean`_

Here is the code containing these imports and a few other preliminaries.

::

  prelude

  /- We import propext here, otherwise we would need a quot.lift for propositions. -/
  import init.data.sigma.basic init.logic init.propext init.data.setoid

  universes u v

  -- iff can now be used to do substitutions in a calculation
  attribute [subst]
  lemma iff_subst {a b : Prop} {p : Prop → Prop}
  (h₁ : a ↔ b) (h₂ : p a) : p b := eq.subst (propext h₁) h₂

After this comes the ``quot`` namespace. Before analyzing the code in that namespace, however, we pause to note that in `core.lean`_ the directive ``init_quotient`` initializes the "quotient module" and is preceded by the following informative comment:

::

  /-
  Initialize the quotient module, which effectively adds
  the following definitions:

  constant quot {α: Sort u} (r: α → α → Prop) : Sort u

  constant quot.mk {α: Sort u} (r: α → α → Prop) (a: α) : quot r

  constant quot.lift
  {α: Sort u} {r: α → α → Prop} {β: Sort v} (f: α → β) :
  (∀ a b: α, r a b → eq (f a) (f b)) → quot r → β

  constant quot.ind
  {α: Sort u} {r: α → α → Prop} {β: quot r → Prop} :
  (∀ a: α, β (quot.mk r a)) → ∀ q: quot r, β q
  -/

Thus, inside the ``quot`` namespace of `quot.lean`_, these four constants---``quot``, ``mk``, ``lift``, and ``ind``---will be available, as can be easily verified with the ``#check`` directive.

::

  namespace quot

    #check @quot -- Π {α: Sort u_1}, (α → α → Prop) → Sort u_1

    #check @mk   -- Π {α: Sort u_1} (r: α → α → Prop), α → quot r

    #check @lift
    -- Π {α: Sort u_1} {r: α → α → Prop} {β: Sort u_2} (f: α → β),
    --   (∀ (a b: α), r a b → f a = f b) → quot r → β

    #check @ind
    -- (∀ {α: Sort u_1} {r: α → α → Prop} {β: quot r → Prop},
    --   (∀ (a: α), β (mk r a)) → ∀ (q: quot r), β q

  end quot

The constant ``lift`` takes as arguments,

+ a relation ``r: α → α → Prop``,
+ a function ``f: α → β``, and
+ a proof that ``f`` respects ``r``,

and returns a function of type ``quot r → β``, called the "lift" of ``f``.

The constant ``ind`` takes as arguments,

+ a relation ``r: α → α → Prop``,
+ a set ``β`` of ``r``-classes (of type ``quot r``), and
+ a proof that every ``r``-class of the form ``mk r a`` belongs to ``β``,

and returns a proof of the assertion that *every* ``r``-class belongs to ``β``.

.. _the-quot-namespace:

The quot namespace
~~~~~~~~~~~~~~~~~~

Without further ado, here is the ``quot`` namespace, which we dissect below.

::

  namespace quot

    constant sound : Π {α : Sort u} {r : α → α → Prop} {a b : α},
    r a b → quot.mk r a = quot.mk r b

    attribute [elab_as_eliminator] lift ind

    protected lemma lift_beta
    {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (c : ∀ a b, r a b → f a = f b) (a : α):
    lift f c (quot.mk r a) = f a := rfl

    protected lemma ind_beta
    {α : Sort u} {r : α → α → Prop} {β : quot r → Prop}
    (p : ∀ a, β (quot.mk r a)) (a : α) :
    (ind p (quot.mk r a) : β (quot.mk r a)) = p a := rfl

    attribute [reducible, elab_as_eliminator]
    protected def lift_on
    {α : Sort u} {β : Sort v} {r : α → α → Prop}
    (q : quot r) (f : α → β) (c : ∀ a b, r a b → f a = f b): β :=
    lift f c q

    attribute [elab_as_eliminator]
    protected lemma induction_on
    {α : Sort u} {r : α → α → Prop} {β : quot r → Prop}
    (q : quot r) (h : ∀ a, β (quot.mk r a)) : β q :=
    ind h q

    lemma exists_rep
    {α : Sort u} {r : α → α → Prop} (q : quot r) :
    ∃ a : α, (quot.mk r a) = q :=
    quot.induction_on q (λ a, ⟨a, rfl⟩)

    section
      variable {α : Sort u}
      variable {r : α → α → Prop}
      variable {β : quot r → Sort v}

      local notation `⟦`:max a `⟧` := quot.mk r a

      attribute [reducible]
      protected def indep (f : Π a, β ⟦a⟧) (a : α) : psigma β :=
      ⟨⟦a⟧, f a⟩

      protected lemma indep_coherent
      (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b),
      (eq.rec (f a) (sound p) : β ⟦b⟧) = f b):
      ∀ a b, r a b → quot.indep f a = quot.indep f b :=
      λ a b e, psigma.eq (sound e) (h a b e)

      protected lemma lift_indep_pr1
      ( f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b),
        (eq.rec (f a) (sound p) : β ⟦b⟧) = f b )
      (q : quot r):
      ( lift (quot.indep f) (quot.indep_coherent f h) q ).1 = q :=
      quot.ind (λ (a : α), eq.refl (quot.indep f a).1) q

      attribute [reducible, elab_as_eliminator]
      protected def rec
      (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b),
      (eq.rec (f a) (sound p) : β ⟦b⟧) = f b) (q : quot r) : β q :=
      eq.rec_on (quot.lift_indep_pr1 f h q)
      ((lift (quot.indep f) (quot.indep_coherent f h) q).2)

      attribute [reducible, elab_as_eliminator]
      protected def rec_on
      (q : quot r) (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b),
      (eq.rec (f a) (sound p) : β ⟦b⟧) = f b): β q :=
      quot.rec f h q

      attribute [reducible, elab_as_eliminator]
      protected def rec_on_subsingleton
      [h: ∀ a, subsingleton (β ⟦a⟧)]
      (q: quot r) (f: Π a, β ⟦a⟧): β q :=
      quot.rec f (λ a b h, subsingleton.elim _ (f b)) q

      attribute [reducible, elab_as_eliminator]
      protected def hrec_on (q: quot r) (f: Π a, β ⟦a⟧)
      (c: ∀ (a b: α) (p: r a b), f a == f b): β q :=
      quot.rec_on q f
      (λ a b p, eq_of_heq
      ( calc
        ( eq.rec (f a) (sound p): β ⟦b⟧)
              == f a: eq_rec_heq (sound p) (f a)
          ... == f b: c a b p
        )
      )
    end

  end quot

We examine each definition in turn.

.. index:: keyword: elab_as_eliminator
.. index:: keyword: reducible

+ ``constant sound``

  | If ``(a, b)`` belongs to the relation ``r``, then the ``r``-classes of ``a`` and ``b`` are the same; that is, ``quot.mk r a = quot.mk r b``.

+ ``attribute [elab_as_eliminator] lift ind``

  | This tells the elaborator that, in the function application of ``lift`` and ``ind``, the arguments should be elaborated as if ``lift`` and ``ind`` were eliminators.

+ ``protected lemma lift_beta``

  | If ``r`` is a relation on ``α``, if ``f: α → β`` is a function, and if we have a proof ``c`` that ``f`` respects ``r``, then the lift of ``f`` to ``quot.r`` is well defined by ``lift f c (quot.mk r a) = f a`` for each ``a:α``.

+ ``protected lemma ind_beta``

  | Given a relation ``r`` on ``α``, a "set" ``β: quot r → Prop`` of ``r``-classes, and a proof that ``β`` contains every ``r``-class of the form ``quot.mk r a``, it holds that ``β`` contains *every* ``r``-class.

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def lift_on``

  | takes a relation ``r`` on ``α``, a function ``f : α → β``, a proof that ``f`` respects ``r`` and an ``r``-class, ``q``, and returns the lift of ``f`` evaluated at ``q`` (which should be equal to ``f`` evaluated at any representative of the ``r``-class ``q``).

+ | ``attribute [elab_as_eliminator] protected``
  | ``lemma induction_on``

  If

    + ``r`` is a relation on ``α``,
    + ``β: quot r → Prop`` is a "set" of ``r``-classes,
    + all ``r``-classes  of the form ``quot.mk r a`` belong to ``β``,
    + ``q`` is an arbitrary ``r``-class,

  | then ``q`` belongs to ``β``.

+ | ``lemma exists_rep``

  | Given a relation ``r`` on ``α`` and an ``r``-class ``q``, there exists a representative ``a`` of the class ``q``; that is ``∃ a, (quot.mk r a) = q``.

Next is a ``section`` directive (which is actually unnecessary, since only variables---not parameters---are declared)inside of which we assume the following typing judgments:

  | ``α: Sort u``,
  | ``r: α → α → Prop``, and
  | ``β: quot r → Sort v``.

Then notation is defined so that ``⟦a⟧`` denotes ``quot.mk r a`` whenever ``a:α``.

+ | ``attribute [reducible] protected``
  | ``def indep``

  Before dissecting the definition of ``indep``, recall that if ``α:Sort u`` and ``β:α → Sort v``, then ``psigma β`` is the dependent pair type, ``∑(a:α),β a``, each inhabitant of which has the form ``⟨a, b⟩`` for some ``a:α`` and ``b:β a``.

  In particular, if ``r: α → α → Prop`` is a relation on ``α``, and ``β: quot r → Sort v``, then ``psigma β`` is the dependent pair type ``∑ (q:quot r), β q``, each inhabitant of which has the form ``⟨q, b⟩`` for some ``q: quot r`` and ``b: β q``, and of course ``⟨q, b⟩ = ⟨⟦a⟧, b⟩`` for some ``a:α`` and ``b: β ⟦a⟧``

  Thus, if ``β: quot r → Sort v`` and ``f: Π (a:α), β ⟦a⟧``, then ``indep f`` yields a function of type ``psigma β = ∑ (q: quot r), β q`` that maps each ``r``-class ``q`` to the pair ``⟨q, b⟩ = ⟨⟦a⟧, f a⟩``. (Here we explicitly mention a particular representative ``a:α`` of the class ``q`` for clarity.)

To dissect the next lemma, we must first make sense of the ``eq.rec`` function.

The inductive type ``eq`` is defined in the file `core.lean`_ as follows:

::

  namespace hidden
  -- BEGIN
  inductive eq {α: Sort u} (a: α): α → Prop
  | refl: eq a

  #check @eq.rec
  -- Π {α: Sort u_2} {a:α} {C: α → Sort u_1},
  --   C a → Π {b:α}, a = b → C b
  -- END
  end hidden

Thus ``eq.rec`` is the function that takes an inhabitant of ``C a: Sort u_1`` and produces a function of type ``Π {b:α}, a = b → C b``, which in turn maps ``b:α``, along with a proof of ``a = b``, to an inhabitant (or proof) of ``C b``.

Now, if ``β: quot r → Sort v``, then ``β (quot.mk r): α → Sort v``, so ``β (quot.mk r)`` has the same shape as the function ``C: α → Sort u_1``. Thus, it will come as no surprise when an inhabitant of ``β (quot.mk r a)`` (``= β ⟦a⟧``) shows up later in place of an element of type ``C a``.

The function ``eq.rec`` will appear in the following hypothesis:

  | ``h: ∀ (a b: α) (p: r a b),``
  | ``( eq.rec (f a) (sound p): β ⟦b⟧ ) = f b``

Here, ``f a`` has type ``β ⟦a⟧``, so ``eq.rec (f a)`` produces a function of type

  ``Π {⟦b⟧: quot r}, ⟦a⟧ = ⟦b⟧ → β ⟦b⟧``,

to which is passed a proof of ``⟦a⟧ = ⟦b⟧``---namely, ``sound p``.

(To see that ``sound p`` is a proof of ``⟦a⟧ = ⟦b⟧``, recall that ``sound`` has type

  | ``Π {α: Sort u} {r: α → α → Prop} {a b: α},``
  | ``r a b → quot.mk r a = quot.mk r b``

so, ``p: r a b`` implies ``sound p`` has type ``⟦a⟧ = ⟦b⟧``.)

Thus, ``eq.rec (f a) (sound p)`` evaluates to something of type ``β ⟦b⟧``, as desired.

The assumption ``h`` given above asserts that the "something" is, in fact, ``f b``.

Here is a pair of lemmas in which this application of ``eq.rec`` appears.

.. protected lemma indep_coherent (f : Π a, β ⟦a⟧)
..                      (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
..                      : ∀ a b, r a b → quot.indep f a = quot.indep f b  :=
.. λ a b e, psigma.eq (sound e) (h a b e)
.. ``quot.indep f a = quot.indep f b``, that is,

+ ``protected lemma indep_coherent``.

  Suppose a function ``f: Π (a:α), β ⟦a⟧`` respects a relation ``r: α → α → Prop`` in the following sense:

    ``∀ (a b: α), r a b → f a = f b``

  Then the function ``quot.indep f`` takes a relation ``r`` on ``α``, a function ``f: Π a, β ⟦a⟧``, and a proof that

    ``( eq.rec (f a) (sound p): β ⟦b⟧ ) = f b``

  holds for all ``(a, b)`` in ``r``, and constructs a proof of

  | ``∀ (a, b) (p: r a b), ⟨⟦a⟧, f a⟩ = ⟨⟦b⟧, f b⟩``.

.. protected lemma lift_indep_pr1
..   (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
..   (q : quot r) : (lift (quot.indep f) (quot.indep_coherent f h) q).1 = q  :=
.. quot.ind (λ (a : α), eq.refl (quot.indep f a).1) q

+ ``protected lemma lift_indep_pr1``

  This lemma takes the same hypotheses as those in ``indep_coherent``, plus an ``r``-class ``q``, and constructs a proof of the following: if the function ``quot.indep f: α → psigma β``---taking each ``a:α`` to ``⟨⟦a⟧, f a⟩``---respects ``r`` in the sense that ``r a b`` implies ``⟨⟦a⟧, f a⟩ = ⟨⟦b⟧, f b⟩``, then the composition consisting of the map ``⟦a⟧ ↦ ⟨⟦a⟧, f a⟩`` followed by the first projection is the identity function on ``quot r`` (as one would hope).

  Indeed, from the stated assumptions, ``lift_indep_pr1`` constructs a proof of

    ``( lift (quot.indep f) (quot.indep_coherent f h) q ).1 = q``.

  Here, ``quot.indep_coherent f h`` is a proof that the function

    ``quot.indep f: α → psigma β``

  respects the relation ``r``; this and the function ``quot.indep f`` are passed to ``lift``, which returns a function, say, ``φ``, of type ``quot r → psigma β``.

  From these data, ``lift_indep_pr1`` constructs a proof that the first component of ``φ q`` is, in fact, ``q``.

  This may seem to be making something out of nothing, but an important thing to take away from the proof of ``lift_indep_pr1`` is that one can refer to elements of the quotient ``quot r`` without ever referencing a particular element (say, ``a:α``) of the base type.

  | Here is a pair of definitions in which the same application of ``eq.rec`` (as described above) appears yet again.

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def rec``

  This function takes ``f: Π a, β ⟦a⟧``, the assumption ``h`` above (see ``indep_coherent``), and an ``r``-class ``q``, and returns

    | ``eq.rec_on (quot.lift_indep_pr1 f h q)``
    | ``( (lift (quot.indep f) (quot.indep_coherent f h) q).2 )``

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def rec_on``

  This function takes an ``r``-class ``q``, a function ``f: Π a, β ⟦a⟧``, and the assumption ``h`` above (see ``indep_coherent``), and returns ``quot.rec f h q``.

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def rec_on_subsingleton``

  Assuming ``[h: ∀ a, subsingleton (β ⟦a⟧)]``, this function takes an ``r``-class ``q``, and a function ``f: Π a, β ⟦a⟧``, and returns ``quot.rec f (λ a b h, subsingleton.elim _ (f b)) q``.

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def hrec_on``

  This function takes an ``r``-class ``q``, a function ``f: Π a, β ⟦a⟧``, and a proof ``c`` of ``∀ (a b: α) (p: r a b), f a == f b``, and returns the following inhabitant of ``β q``:

    | ``quot.rec_on q f``
    | ``( λ a b p, eq_of_heq``

      | ``( calc``

        | ``( eq.rec (f a) (sound p) : β ⟦b⟧ )``

            | ``== f a : eq_rec_heq (sound p) (f a)``

          | ``... == f b : c a b p``

      | ``)``

    | ``)``

.. todo:: dissect more of quot namespace

.. _the-quotient-namespace:

The quotient namespace
~~~~~~~~~~~~~~~~~~~~~~

In the second part of `quot.lean`_ is the ``quotient`` namespace.

::

  def quotient {α: Sort u} (s: setoid α) := @quot α setoid.r

  namespace quotient

    protected def mk {α: Sort u} [s: setoid α]
    (a: α): quotient s := quot.mk setoid.r a

    notation `⟦`:max a `⟧`:0 := quotient.mk a

    def sound {α: Sort u} [s: setoid α] {a b: α}:
    a ≈ b → ⟦a⟧ = ⟦b⟧ := quot.sound

    attribute [reducible, elab_as_eliminator]
    protected def lift {α: Sort u} {β: Sort v}
    [s: setoid α] (f: α → β):
    (∀ a b, a ≈ b → f a = f b) → quotient s → β :=
    quot.lift f

    attribute [elab_as_eliminator]
    protected lemma ind {α: Sort u} [s: setoid α]
    {β: quotient s → Prop}: (∀ a, β ⟦a⟧) → ∀ q, β q :=
    quot.ind

    attribute [reducible, elab_as_eliminator]
    protected def lift_on {α : Sort u} {β : Sort v}
    [s : setoid α] (q : quotient s) (f : α → β)
    (c : ∀ a b, a ≈ b → f a = f b) : β :=
    quot.lift_on q f c

    attribute [elab_as_eliminator]
    protected lemma induction_on {α : Sort u} [s : setoid α]
    {β : quotient s → Prop} (q : quotient s)
    (h : ∀ a, β ⟦a⟧) : β q := quot.induction_on q h

    lemma exists_rep {α : Sort u} [s : setoid α]
    (q : quotient s) : ∃ a : α, ⟦a⟧ = q :=
    quot.exists_rep q

    section

      variable {α : Sort u}
      variable [s : setoid α]
      variable {β : quotient s → Sort v}

      protected def rec
      (f: Π a, β ⟦a⟧) (h: ∀ (a b: α) (p: a ≈ b),
      (eq.rec (f a) (quotient.sound p) : β ⟦b⟧) = f b)
      (q : quotient s) : β q :=
      quot.rec f h q

      attribute [reducible, elab_as_eliminator]
      protected def rec_on
      (q: quotient s) (f: Π a, β ⟦a⟧)
      ( h: ∀ (a b : α) (p: a ≈ b),
        ( eq.rec (f a) (quotient.sound p): β ⟦b⟧ ) = f b
      ): β q := quot.rec_on q f h

      attribute [reducible, elab_as_eliminator]
      protected def rec_on_subsingleton
      [h: ∀ a, subsingleton (β ⟦a⟧)]
      (q: quotient s) (f: Π a, β ⟦a⟧): β q :=
      @quot.rec_on_subsingleton _ _ _ h q f

      attribute [reducible, elab_as_eliminator]
      protected def hrec_on (q: quotient s) (f: Π a, β ⟦a⟧)
      (c: ∀ (a b: α) (p: a ≈ b), f a == f b) : β q :=
      quot.hrec_on q f c

    end

    section

      universes u_a u_b u_c
      variables {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}
      variables [s₁ : setoid α] [s₂ : setoid β]
      include s₁ s₂

      attribute [reducible, elab_as_eliminator]
      protected def lift₂ (f: α → β → φ)
      (c: ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
      (q₁: quotient s₁) (q₂: quotient s₂): φ :=
      quotient.lift
      ( λ (a₁: α),
        quotient.lift (f a₁) (λ (a b: β),
        c a₁ a a₁ b (setoid.refl a₁)) q₂
      )
      ( λ (a b : α) (h : a ≈ b),
        @quotient.ind β s₂
        ( λ (a_1 : quotient s₂),
          ( quotient.lift (f a)
            ( λ (a_1 b : β),
              c a a_1 a b (setoid.refl a)
            ) a_1
          ) =
          ( quotient.lift (f b)
            ( λ (a b_1 : β),
              c b a b b_1 (setoid.refl b)
            ) a_1
          )
        )
        ( λ (a' : β),
          c a a' b a' h (setoid.refl a')
        ) q₂
      ) q₁

      attribute [reducible, elab_as_eliminator]
      protected def lift_on₂
      (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → φ)
      ( c: ∀ a₁ a₂ b₁ b₂,
        a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂
      ) : φ := quotient.lift₂ f c q₁ q₂

      attribute [elab_as_eliminator]
      protected lemma ind₂ {φ : quotient s₁ → quotient s₂ → Prop}
      ( h: ∀ a b,
        φ ⟦a⟧ ⟦b⟧) (q₁: quotient s₁) (q₂: quotient s₂): φ q₁ q₂ :=
        quotient.ind (λ a₁, quotient.ind (λ a₂, h a₁ a₂) q₂
      ) q₁

      attribute [elab_as_eliminator]
      protected lemma induction_on₂
      {φ : quotient s₁ → quotient s₂ → Prop}
      (q₁: quotient s₁) (q₂: quotient s₂)
      (h: ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
      quotient.ind (λ a₁, quotient.ind (λ a₂, h a₁ a₂) q₂) q₁

      attribute [elab_as_eliminator]
      protected lemma induction_on₃ [s₃ : setoid φ]
      {δ : quotient s₁ → quotient s₂ → quotient s₃ → Prop}
      (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃)
      (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧) : δ q₁ q₂ q₃ :=
      quotient.ind (λ a₁, quotient.ind
      (λ a₂, quotient.ind (λ a₃, h a₁ a₂ a₃) q₃) q₂) q₁

    end

    section exact
      variable   {α : Sort u}
      variable   [s : setoid α]
      include s

      private def rel (q₁ q₂ : quotient s) : Prop :=
      quotient.lift_on₂ q₁ q₂ (λ a₁ a₂, a₁ ≈ a₂)
      ( λ a₁ a₂ b₁ b₂ a₁b₁ a₂b₂,
        propext
        ( iff.intro
          ( λ a₁a₂,
            setoid.trans (setoid.symm a₁b₁) (setoid.trans a₁a₂ a₂b₂)
          )
          ( λ b₁b₂,
            setoid.trans a₁b₁ (setoid.trans b₁b₂ (setoid.symm a₂b₂))
          )
        )
      )

      local infix `~` := rel

      private lemma rel.refl : ∀ q : quotient s, q ~ q :=
      λ q, quot.induction_on q (λ a, setoid.refl a)

      private lemma eq_imp_rel
      {q₁ q₂: quotient s}: q₁ = q₂ → q₁ ~ q₂ :=
      assume h, eq.rec_on h (rel.refl q₁)

      lemma exact {a b: α}: ⟦a⟧ = ⟦b⟧ → a ≈ b :=
      assume h, eq_imp_rel h
    end exact

    section
      universes u_a u_b u_c
      variables {α : Sort u_a} {β : Sort u_b}
      variables [s₁ : setoid α] [s₂ : setoid β]
      include s₁ s₂

      attribute [reducible, elab_as_eliminator]
      protected def rec_on_subsingleton₂
      {φ : quotient s₁ → quotient s₂ → Sort u_c}
      [h : ∀ a b, subsingleton (φ ⟦a⟧ ⟦b⟧)]
      (q₁ : quotient s₁) (q₂ : quotient s₂)
      (f : Π a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂:=
      @quotient.rec_on_subsingleton _ s₁
      (λ q, φ q q₂) (λ a, quotient.ind (λ b, h a b) q₂) q₁
      (λ a, quotient.rec_on_subsingleton q₂ (λ b, f a b))
    end

  end quotient

.. todo:: dissect quotient namespace

.. _quotient-theorems:

Quotient theorems
~~~~~~~~~~~~~~~~~

The third and final part of the `quot.lean`_ file proves some theorems about the quotient types defined above.

::

  section
    variable {α : Type u}
    variable (r : α → α → Prop)

    inductive eqv_gen : α → α → Prop
    | rel {} : Π x y, r x y → eqv_gen x y
    | refl {} : Π x, eqv_gen x x
    | symm {} : Π x y, eqv_gen x y → eqv_gen y x
    | trans {} : Π x y z, eqv_gen x y → eqv_gen y z → eqv_gen x z

    theorem eqv_gen.is_equivalence : equivalence (@eqv_gen α r) :=
    mk_equivalence _ eqv_gen.refl eqv_gen.symm eqv_gen.trans

    def eqv_gen.setoid : setoid α :=
    setoid.mk _ (eqv_gen.is_equivalence r)

    theorem quot.exact {a b : α}
    (H : quot.mk r a = quot.mk r b) : eqv_gen r a b :=
    @quotient.exact _ (eqv_gen.setoid r) a b
      ( @congr_arg _ _ _ _
        ( quot.lift (@quotient.mk _ (eqv_gen.setoid r))
          ( λx y h, quot.sound (eqv_gen.rel x y h) )
        ) H
      )

    theorem quot.eqv_gen_sound {r : α → α → Prop} {a b : α}
    (H : eqv_gen r a b) : quot.mk r a = quot.mk r b :=
    eqv_gen.rec_on H
      (λ x y h, quot.sound h)
      (λ x, rfl)
      (λ x y _ IH, eq.symm IH)
      (λ x y z _ _ IH₁ IH₂, eq.trans IH₁ IH₂)
  end

  open decidable
  instance {α: Sort u} {s: setoid α}
  [d: ∀ a b: α, decidable (a ≈ b)]: decidable_eq (quotient s) :=
  λ q₁ q₂: quotient s,
  quotient.rec_on_subsingleton₂ q₁ q₂
    ( λ a₁ a₂,
      match (d a₁ a₂) with
      | (is_true h₁)  := is_true (quotient.sound h₁)
      | (is_false h₂) := is_false (λ h, absurd (quotient.exact h) h₂)
      end
    )

.. todo:: dissect quot theorems

-------------------------------------

.. _extensionality-in-the-lstl:

Extensionality
--------------

.. index:: !Leibniz equal, function extionsionality
.. index:: keyword: funext

.. _proof-of-funext:

Proof of funext
~~~~~~~~~~~~~~~~

Here we dissect the definition of function extensionality in the `Lean Standard Library`_, as well as the proof of the ``funext`` theorem, which states that the function extensionality principle *is* equality of functions in Lean; in other words, two functions are equal iff they are :term:`Leibniz equal` (i.e., they give the same output for each input).

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

First, the ``open quotient`` directive makes the contents of the ``quotient`` namespace available.  (See :numref:`the-quotient-namespace`.)

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

.. todo:: finish dissecting funext proof


.. _Agda: https://wiki.portal.chalmers.se/agda/pmwiki.php

.. _Coq: http://coq.inria.fr

.. _NuPRL: http://www.nuprl.org/

.. _Lean: https://leanprover.github.io/

.. _vscode: https://code.visualstudio.com/

.. _Lean github repository:  https://github.com/leanprover/lean/

.. _Logic and Proof: https://leanprover.github.io/logic_and_proof/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _mathlib: https://github.com/leanprover-community/mathlib/

.. _Lean Standard Library: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/

.. _TPL: https://leanprover.github.io/theorem_proving_in_lean/

.. _Coercions: https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#coercions

.. _Coercions using Type Classes: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

.. _Lean Tutorial: https://leanprover.github.io/tutorial/

.. _Lean Reference Manual: https://leanprover.github.io/reference/

.. _`lean/library/init`: https://github.com/leanprover/lean/tree/master/library/init

.. _classical.lean: https://github.com/leanprover/lean/blob/master/library/init/classical.lean
.. _core.lean: https://github.com/leanprover/lean/blob/master/library/init/core.lean
.. _function.lean: https://github.com/leanprover/lean/blob/master/library/init/function.lean
.. _logic.lean: https://github.com/leanprover/lean/blob/master/library/init/logic.lean
.. _wf.lean: https://github.com/leanprover/lean/blob/master/library/init/wf.lean
.. _`lean/library/init/data`: https://github.com/leanprover/lean/tree/master/library/init/data
.. _nat (dir): https://github.com/leanprover/lean/blob/master/library/init/data/nat
.. _prod.lean: https://github.com/leanprover/lean/blob/master/library/init/data/prod.lean
.. _propext.lean: https://github.com/leanprover/lean/blob/master/library/init/propext.lean
.. _quot.lean: https://github.com/leanprover/lean/blob/master/library/init/data/quot.lean
.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean
.. _`lean/library/init/algebra`: https://github.com/leanprover/lean/blob/master/library/init/algebra
.. _classes.lean: https://github.com/leanprover/lean/blob/master/library/init/algebra/classes.lean
.. _functions.lean: https://github.com/leanprover/lean/blob/master/library/init/algebra/functions.lean
.. _order.lean: https://github.com/leanprover/lean/blob/master/library/init/algebra/order.lean

.. _sigma (dir): https://github.com/leanprover/lean/blob/master/library/init/data/sigma/
.. _`sigma/basic.lean`: https://github.com/leanprover/lean/blob/master/library/init/data/sigma/basic.lean
.. _setoid.lean: https://github.com/leanprover/lean/blob/master/library/init/data/setoid.lean
