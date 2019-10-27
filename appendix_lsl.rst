.. File: appendix_lsl.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 11 Oct 2019
.. Updated: 27 Oct 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. highlight:: lean

.. _the-lean-stl:

The Lean STL
-------------

We first collect for easy reference some links to some of the basic components of the `Lean Standard Library`_ (:term:`LSTL`).  Thereafter, we dissect some of these components that are crucial for using Lean to do universal algebra.

Some basic components
~~~~~~~~~~~~~~~~~~~~~~~~~

While Lean doesn't have a formal API, per se, you can browse the source code of the core Lean library to see what built-in types, definitions, and theorems are available in the :term:`LSTL`.

For example, some of the most important of these objects are implemented in the files listed below. These (and many more) can be found in (or under) the `lean/library/init`_ directory of the official `Lean github repository`_.

+ In `lean/library/init`_

  + `classical.lean`_
  + `core.lean`_
  + `function.lean`_
  + `logic.lean`_
  + `wf.lean`_

+ In `lean/library/init/data`_

  + `nat/`_
  + `prod.lean`_
  + `quot.lean`_
  + `set.lean`_
  + `setoid.lean`_
  + `sigma/`_

+ In `lean/library/init/algebra`_

  + `classes.lean`_
  + `functions.lean`_
  + `order.lean`_


.. _extensionality-in-the-lstl:

Extensionality
~~~~~~~~~~~~~~~~~

.. index:: !Leibniz equal, function extensionality
.. index:: keyword: funext

.. _proof-of-funext:

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

First, the ``open quotient`` directive makes the contents of the ``quotient`` namespace available.  (See the :ref:`appendix section on the quotient namespace <the-quotient-namespace>`.)

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

.. _subsingleton-type-class:

Subsingleton type class
~~~~~~~~~~~~~~~~~~~~~~~~~

The ``subsingleton`` type class is used in the definition of ``quotient.rec_on_subsingleton`` and related theorems. Any type inhabited by a single element is a subsingleton type. Here is the definition.

::

  class inductive subsingleton (α: Sort u): Prop
  | intro (h: ∀ a b: α, a = b): subsingleton

  protected def subsingleton.elim {α: Sort u}
  [h: subsingleton α]: ∀ (a b: α), a = b :=
  subsingleton.rec (λ p, p) h

  protected def subsingleton.helim {α β: Sort u}
  [h: subsingleton α] (h: α = β): ∀ (a: α) (b: β), a == b :=
  eq.rec_on h (λ a b: α, heq_of_eq (subsingleton.elim a b))

  instance subsingleton_prop (p: Prop): subsingleton p :=
  ⟨λ a b, proof_irrel a b⟩

  instance (p: Prop): subsingleton (decidable p) :=
  subsingleton.intro
  ( λ d₁,
    match d₁ with
    | (is_true t₁)  :=
      ( λ d₂,
        match d₂ with
        | (is_true t₂)  := eq.rec_on (proof_irrel t₁ t₂) rfl
        | (is_false f₂) := absurd t₁ f₂
        end
      )
    | (is_false f₁) :=
      ( λ d₂,
        match d₂ with
        | (is_true t₂)  := absurd t₂ f₁
        | (is_false f₂) := eq.rec_on (proof_irrel f₁ f₂) rfl
        end
      )
  end)

  protected lemma rec_subsingleton {p: Prop} [h: decidable p]
  {h₁: p → Sort u} {h₂: ¬p → Sort u}
  [h₃: Π (h: p), subsingleton (h₁ h)]
  [h₄: Π (h: ¬p), subsingleton (h₂ h)]:
  subsingleton (decidable.rec_on h h₂ h₁) :=
  match h with
  | (is_true h)  := h₃ h
  | (is_false h) := h₄ h
  end


.. _sets-in-lean:

Sets in Lean
~~~~~~~~~~~~~~~

We now describe how some basic mathematical concepts are represented in the Lean language.

Many of the implementations shown here also appear in the following files in the `Lean Standard Library`_ (:term:`LSTL`) and the `Lean Mathlib <mathlib>`_:

+ set.lean_
+ basic.lean_
+ lattice.lean_


If ``α`` is a type, then Lean provides the type ``set α``, which represents the type of **sets of elements of type** ``α``.

This is naturally implemented as a function type.  Indeed, the type ``set α`` is simply an alias for the type ``α → Prop``.

Thus, a set ``A`` of elements of type ``α`` would be denoted by ``A: set α``.

We say "``x`` belongs to ``A``", and write ``x ∈ A``, if and only if the proposition ``A x`` holds (i.e., has a proof, say, ``h: A x``).

.. _intersection-and-union:

Intersection and union
~~~~~~~~~~~~~~~~~~~~~~

Let ``S`` be a family of sets of type :math:`α`.

In lattice.lean_, the **intersection** of the sets in ``S`` is denoted by ``⋂₀ S``.

::

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


.. index:: relation, binary relation, preorder
.. index:: domain, range

Relations in Lean
~~~~~~~~~~~~~~~~~~~~~

In the last chapter, we noted that set theorists think of a binary relation :math:`R` on a set :math:`A` as a set of ordered pairs, so that :math:`R(a, b)` really means :math:`(a, b) \in R`. An alternative is to think of :math:`R` as a function which, when applied to :math:`a` and :math:`B`, returns the proposition that :math:`R(a, b)` holds. This is the viewpoint adopted by Lean: a binary relation on a type ``A`` is a function ``A → A → Prop``. Remember that the arrows associate to the right, so ``A → A → Prop`` really means ``A → (A → Prop)``. So, given ``a: A``, ``R a`` is a predicate (the property of being related to ``A``), and given ``a b: A``, ``R a b`` is a proposition.

With first-order logic, we can say what it means for a relation to be reflexive, symmetric, transitive, and antisymmetric, as follows:

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the :ref:`appendix section on equivalence relations <equivalence-relations>` we learned that an equivalence relation is a symmetric preorder---equivalently, a reflexive, symmetric, and transitive binary relation. We will define such a relation in Lean shortly, but first let's define preorder.

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

(The symbol ``≈`` is produced by typing ``\~~`` or ``\approx``; see the :ref:`symbol appendix <symbols>`.)

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

.. todo:: complete this section after completing the :ref:`appendix section on quotients in the lstl <quotients-in-the-lstl>`.

..     The poset induced by a preorder

.. _total-and-strict-orders-in-lean:

Total and strict orders
~~~~~~~~~~~~~~~~~~~~~~~

In the :ref:`appendix section on orderings <total-and-strict-orderings>` we showed that a strict partial order---that is, a transitive and irreflexive binary relation. Here is a proof of that fact in Lean.

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

The proof also uses anonymous ``have`` and ``assume``, referring back to them with the French quotes (produced by typing ``\f<`` and ``\f>``; see the :ref:`symbol appendix <symbols>`).

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

(You can produce angled brackets by typing ``\<`` and ``\>`` or by typing ``\langle`` and ``\rangle``; see the :ref:`symbol appendix <symbols>`.)

.. .. _equality-in-lean:

.. Equality
.. ~~~~~~~~

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

.. .. index:: product

.. .. _products-in-lean:


.. _quotients-in-the-LSTL:

Quotients in the LSTL
~~~~~~~~~~~~~~~~~~~~~~~~

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

Without further ado, here is the ``quot`` namespace as defined in the :term:`LSTL`.  We will dissect this code below.

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


Let's examine each definition in turn.

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

  We repeat the definition of this function here because of its importance.

    | ``attribute [reducible] protected``
    | ``def indep (f: Π a, β ⟦a⟧) (a: α): psigma β := ⟨⟦a⟧, f a⟩``

  Before dissecting this definition, recall that if ``α:Sort u`` and ``β:α → Sort v``, then ``psigma β`` is the dependent pair type, ``∑(a:α),β a``, each inhabitant of which has the form ``⟨a, b⟩`` for some ``a:α`` and ``b: β a``.

  In particular, if ``r: α → α → Prop`` is a relation on ``α``, and ``β: quot r → Sort v``, then ``psigma β`` is the dependent pair type ``∑ (q:quot r), β q``, each inhabitant of which has the form ``⟨q, b⟩ = ⟨⟦a⟧, b⟩`` for some ``a:α`` and ``b: β ⟦a⟧``.

  Thus, if ``β: quot r → Sort v`` and ``f: Π (a:α), β ⟦a⟧``, then ``indep f`` is a function that maps ``a:α`` to the pair ``⟨⟦a⟧, f a⟩`` in ``psigma β``; that is, we have the following typing judgment:

    ``quot.indep f: α → psigma β``.

  Let us pause to check this, as well as the types of ``quot.mk`` and ``quot.sound``, in Lean.

  ::

    universes u v
    variable {α : Sort u}
    variable {r : α → α → Prop}
    variable {β : quot r → Sort v}
    variables (f: Π a, β (quot.mk r a)) (a:α)

    #check quot.indep f      -- α → psigma β

    #check @quot.mk
    -- Π {α: Sort u_1} (r: α → α → Prop), α → quot r

    #check @quot.sound
    -- ∀ {α: Sort u_1} {r: α → α → Prop} {a b: α},
    -- r a b → mk r a = mk r b

Before dissecting the next lemma, consider the ``eq.rec`` function. The inductive type ``eq`` is defined in the file `core.lean`_ as follows:

::

  namespace hidden
  -- BEGIN
  inductive eq {α: Sort u} (a: α): α → Prop
  | refl: eq a
  -- END
  end hidden

Each inductively defined type ``T`` (see :numref:`inductively-defined-types`) comes with an elimination principle that manifests in Lean as the two :term:`recursors <recursor>` called ``T.rec`` and ``T.rec_on``. Lean automatically generates such :term:`recursors <recursor>` whenever an inductive type is defined.

Let's check the types of the recursors associated with the inductively defined type ``eq``.

::

  namespace hidden
  inductive eq {α: Sort u} (a: α): α → Prop
  | refl: eq a

  -- BEGIN
  #check @eq.rec
  -- Π {α: Sort u} {a:α} {C: α → Sort v},
  --   C a → Π {b:α}, a = b → C b

  #check @eq.rec_on
  -- Π {α: Sort u} {a:α} {C: α → Sort v} {b:α},
  --   a = b → C a → C b
  -- END
  end hidden

Thus ``eq.rec`` takes an inhabitant of ``C a: Sort u_1`` and produces a function of type

  ``Π {b:α}, a = b → C b``.

The latter evidently takes ``b:α`` and proof of ``a = b`` and constructs an inhabitant (proof) of ``C b``.

Recall that ``mk r: α → quot r``, so if ``β: quot r → Sort v``, then ``β (mk r): α → Sort v``. Therefore, ``β (mk r)`` has the same shape as the function ``C: α → Sort u_1``, so it will come as no surprise when an element of type ``β (mk r a)`` (``= β ⟦a⟧``) shows up later where an inhabitant of ``C a`` is called for.

The function ``eq.rec`` will be used below in hypotheses like the following:

  | ``h: ∀ (a b: α) (p: r a b)                        (‡)``
  | ``( eq.rec (f a) (sound p): β ⟦b⟧ ) = f b``

Here, ``f a`` has type ``β ⟦a⟧``, so ``eq.rec (f a)`` produces a function of type

  ``Π {⟦b⟧: quot r}, ⟦a⟧ = ⟦b⟧ → β ⟦b⟧``.

If a proof of ``⟦a⟧ = ⟦b⟧`` is passed to such a function, the result has type ``β ⟦b⟧``.

Observe that ``(sound p)`` is a proof of ``⟦a⟧ = ⟦b⟧``, since ``sound`` has type

  | ``Π {α: Sort u} {r: α → α → Prop} {a b: α},``
  | ``r a b → quot.mk r a = quot.mk r b``

so, ``p: r a b`` implies ``sound p: ⟦a⟧ = ⟦b⟧``.

Thus, ``eq.rec (f a) (sound p)`` evaluates to something of type ``β ⟦b⟧``.

The hypothesis ``h`` above asserts that this something is ``f b``.

To see this in action, let's look at the next pair of lemmas from the `quot.lean`_ file.

.. protected lemma indep_coherent (f : Π a, β ⟦a⟧)
..                      (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
..                      : ∀ a b, r a b → quot.indep f a = quot.indep f b  :=
.. λ a b e, psigma.eq (sound e) (h a b e)
.. ``quot.indep f a = quot.indep f b``, that is,

+ ``protected lemma indep_coherent``.

  This lemma takes a function ``f: Π (a:α), β ⟦a⟧`` and the hypothesis ``(‡)`` and constructs a proof of

  ``∀ (a, b) (p: r a b), quot.indep f a = quot.indep f b``,

  | equivalently, ``∀ (a, b) (p: r a b), ⟨⟦a⟧, f a⟩ = ⟨⟦b⟧, f b⟩``.

.. (Recall, ``quot.indep f a`` is the pair ``⟨⟦a⟧, f a⟩``.)

.. protected lemma lift_indep_pr1
..   (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
..   (q : quot r) : (lift (quot.indep f) (quot.indep_coherent f h) q).1 = q  :=
.. quot.ind (λ (a : α), eq.refl (quot.indep f a).1) q

+ ``protected lemma lift_indep_pr1``

  This lemma takes a function ``f: Π (a:α), β ⟦a⟧``, the hypothesis ``(‡)``, and an ``r``-class ``q``, and constructs a proof of the following:

    If the function ``quot.indep f: α → psigma β`` (which takes each ``a:α`` to ``⟨⟦a⟧, f a⟩``) respects ``r`` in the sense that ``r a b`` implies ``⟨⟦a⟧, f a⟩ = ⟨⟦b⟧, f b⟩``, then the composition consisting of the map ``⟦a⟧ ↦ ⟨⟦a⟧, f a⟩`` followed by the first projection is the identity function on ``quot r`` (as one would hope).

  Indeed, from the stated assumptions, ``lift_indep_pr1`` constructs a proof of

    ``( lift (quot.indep f) (quot.indep_coherent f h) q ).1 = q``.

  Here, ``quot.indep_coherent f h`` is a proof that the function

    ``quot.indep f: α → psigma β``

  respects the relation ``r``; this and the function ``quot.indep f`` are passed to ``lift``, which returns a function, say, ``φ``, of type ``quot r → psigma β``, and defined for each ``q: quot r`` by

    ``φ q = ⟨q, y⟩   ( = ⟨⟦a⟧,f a⟩  ``, for some ``a:α).         (★)``

  From these data, ``lift_indep_pr1`` constructs a proof that the first component of ``φ q`` is ``q``.

  This may seem to be making something out of nothing, but an important take-away is that it's possible to refer to an arbitrary inhabitant (say, ``quot r``) of the quotient type in a computable way, without relying on the :term:`Axiom of Choice <Choice>` to guarantee that we can choose a particular representative (say, ``a:α``) of ``quot r``.

  | Here is a pair of definitions that also demonstrate the application of ``eq.rec`` described above.

.. attribute [reducible, elab_as_eliminator]
.. protected def rec
..    (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
..    (q : quot r) : β q :=
.. eq.rec_on (quot.lift_indep_pr1 f h q) ((lift (quot.indep f) (quot.indep_coherent f h) q).2)

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def rec``

  This is the recursor for ``quot``. Its type is shown in the output of ``#check @quot.rec``:

  ::

    Π{α: Sort u} {r: α → α → Prop} {β: quot r → Sort v}
    (f: Π (a: α), β (mk r a)),
    ( ∀ (a b: α) (p: r a b),
      eq.rec (f a) _ = f b ) → Π (q: quot r), β q

  For universe ``v`` and ``β: quot r → Sort v``, ``quot.rec`` takes the function ``f: Π a, β ⟦a⟧`` and hypothesis ``h = (‡)`` (defined above) and returns a function of type ``Π (q: quot r), β q``, namely, the function that maps each ``q`` to the following inhabitant of ``β q``:

    | ``eq.rec_on (quot.lift_indep_pr1 f h q)                       (ℓ₁)``
    | ``( (lift (quot.indep f) (quot.indep_coherent f h) q).2 )     (ℓ₂)``

  To dissect this return value, recall that ``quot.indep f`` maps each ``a`` to ``⟨⟦a⟧, f a⟩``, and

    ``quot.indep_coherent f h``

  is a proof that ``quot.indep f`` respects the relation ``r`` in the following sense:

    ``∀ (a b: α), r a b → ⟨⟦a⟧, f a⟩ = ⟨⟦b⟧, f b⟩``.

  This is exactly what is required in order to lift ``quot.indep f`` from domain ``α`` to domain ``quot r``.  Therefore,

    ``lift (quot.indep f) (quot.indep_coherent f h)``

  is the function ``φ: quot r → psigma β`` which takes each ``r``-class ``q`` to the pair ``⟨q, y⟩ = ⟨⟦a⟧, f a⟩``, where ``a`` is any inhabitant of ``α`` satisfying ``⟦a⟧ = q``.

  Thus, line ``(ℓ₂)`` gives the second projection of ``⟨q, y⟩ = ⟨⟦a⟧, f a⟩``, which is evidently ``y`` (or ``f a``).

  As for line ``(ℓ₁)``, recall ``quot.lift_indep_pr1 f h q`` is a proof that the first projection of ``φ`` is the identity function on ``quot r``.

.. Let ``A := (λ ⟨x, y⟩, x) ∘ (λ q, ⟨q, y⟩)`` and let ``B := id`` be the identity function on ``quot r``.
.. Then ``A`` and ``B`` have type ``quot r → quot r`` and ``quot.lift_indep_pr1 f h q`` is a proof that ``A = B``.

  As the directive ``#check @eq.rec_on`` shows, the type of ``eq.rec_on`` is

    ``Π {α: Sort u} {a:α} {C: α → Sort v} {b:α}, a = b → C a → C b``.

..  In the present case, we have ``γ := quot r → quot r``, and ``C: (quot r → quot r) → Sort v``.
.. All told, the function ``quot.rec`` yields a proof of ``C B`` when given the following data:
..   + two functions ``A B: quot r → quot r``,
..   + a proof of ``A = B``, and
..   + a proof of ``C A``

  All told, the function ``quot.rec`` yields a proof of ``C b`` when given the following data:

    + ``a b: α``,
    + a proof of ``a = b``, and
    + a proof of ``C a``.

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def rec_on``

  This function simply takes the (ordered) list of arguments

    1. ``q: quot r``,
    2. ``f: Π a, β ⟦a⟧``,
    3. ``h = (‡)`` (defined above),

  and returns ``quot.rec f h q``.

+ | ``attribute [reducible, elab_as_eliminator] protected``
  | ``def rec_on_subsingleton``

  If we ``#check`` it, we see the type of this definition is

  ::

    Π {α: Sort u} {r: α → α → Prop} {β: quot r → Sort v}
    [h: ∀ (a:α), subsingleton (β (mk r a))] (q: quot r),
    (Π (a: α), β (mk r a)) → β q

  First note the square brackets around the hypothesis ``h: ∀ a, subsingleton (β ⟦a⟧)``.  Brackets indicate implicit arguments and, when the brackets are square, this tells the elaborator that the given argument should be inferred using the type class mechanism.  (See the `chapter on Type Classes <https://leanprover.github.io/theorem_proving_in_lean/type_classes.html>`_ in the `TPL`_ tutorial for more details about this.)

  Thus (assuming ``[h: ∀ (a:α), subsingleton (β (mk r a))]`` is inferrable from the current context) the function ``rec_on_subsingleton`` takes an ``r``-class ``q`` and a function ``f: Π a, β ⟦a⟧``, and returns the following inhabitant of ``β q``:

    ``quot.rec f (λ a b h, subsingleton.elim _ (f b)) q``.

  A ``subsingleton`` type is inhabited by exactly one element.  See the :ref:`appendix section on the subsingleton type class <subsingleton-type-class>` for the definition.

  The ``subsingleton.elim`` function takes evidence that ``α`` is a subsingleton type and provides a proof of ``∀ (a b: α), a = b``.


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

---------------------

.. include:: hyperlink_references.rst

