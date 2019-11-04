.. File: type_classes.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 1 Nov 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. highlight:: lean

.. _type-classes:

Type classes
============

In this chapter we explain *type classes* and *coercions*, and we show how these two concepts play an important role in our Lean_ implementation of algebras and varieties.

**References**. The `chapter on Type Classes <https://leanprover.github.io/theorem_proving_in_lean/type_classes.html>`_ in TPL_ provides further background, and the `Coercions using Type Classes`_ section of TPL_ is also helpful.

-----------------------

.. _type-classes-and-coercions:

Type classes and coercions
-----------------------------

Type classes
~~~~~~~~~~~~~

A **type class** is a family of types; each type in the family is called an **instance** of the type class.

To have Lean infer an implicit argument using the type class mechanism, the argument in question should appear inside square brackets (instead of curly braces) in the declaration.

Type classes are used to provide hints to the elaborator when searching for an element of a certain type class.  The elaborator consults a table of declared instances of a particular type.

Before diving into examples of type classes, we must first explain what a type *coersion* is. That is the subject of the next subsection.

.. index:: coercion

.. _coercions:

Coercions
~~~~~~~~~~

A very nice feature of Lean that is useful for, among other things, bridging the gap between informal and formal mathematics is called type **coercion**.

In mathematics, we often think of distinct objects as the same, or "equal" in some sense.  In fact, identifying distinct objects is so common in mathematics that we often don't even mention it explicitly.  Of course, when formalizing mathematics in a computer language, precision is crucial and equality assertions require more care.  Certainly our understanding of equality must be made explicit and precise at some stage in the development.

.. proof:example::

   Suppose :math:`z: ℤ` is an integer and :math:`n: ℕ` a natural number. We may consider wish to compute the sum :math:`z + n`, but technically this doesn't make sense since (in type theory as well as set theory),natural numbers are not integers; indeed, :math:`ℕ ⊈ ℤ`, despite claims to the contrary by some otherwise intelligent people.

   What *is* true is that :math:`ℕ` can be embedded in :math:`ℤ`, and we can express this in Lean using a type coercion; e.g.,

   ::

     variable n : ℕ
     variable z : ℤ
     #check z + n   -- results in  z + ↑n : ℤ

   The addition is handled automatically in this case, but notice the coercion symbol ``↑`` that appears in the output of ``#check``.

   The up arrow is Lean notation for the function ``coe``, which could be used instead of ``↑``.  (Type ``↑`` with ``\u``.)

   In certain cases, an explicit ``coe`` or ``↑`` *must* appear.  This is true when Lean can't tell that a coercion is needed.

   For example, changing the order of the arguments of ``#check`` above results in the following error:

   ::

     #check n + z
     -- error:
     -- type mismatch at application
     --   n + z
     -- term
     --   z
     -- has type
     --   ℤ
     -- but is expected to have type
     --   ℕ

   but we can tell Lean to use coercion, like so:

   ::

     #check ↑n + z   -- ↑n + z : ℤ

----------------------------

.. index:: ! type class, ! instance

.. _type-classes-and-coersions-in-lean:

Type classes and coercions in Lean
-----------------------------------

Lean allows various kinds of coercions using type classes.

We will discuss this along with some examples, but for more details the reader is encouraged to study the `Coercions using Type Classes`_ section of `TPL`_.

Using a type class involves three main steps.

#. Declare a family of inductive types to be a type class.
#. Declare instances of the type class.
#. Define a function that infers an instance and puts it to use.

Let's consider examples demonstrating each step in turn.

#. **Declare a family of inductive types**.

   ::

     class inhabited (α: Type _) := (default: α)

     --...is shorthand for:
     --@[class] structure inhabited (α: Type _) := (default: α)

   An element of ``inhabited α`` has the form ``inhabited.mk a`` for some ``a:α``.

   The projection ``inhabited.default`` extracts an element of ``α`` from an element of ``inhabited α``.


#. **Populate the class with some instances**.

   ::

     namespace ualib

       class inhabited (α: Type _) := (default: α)

       instance Prop_inhabited: inhabited Prop:= inhabited.mk true
       instance bool_inhabited: inhabited bool:= inhabited.mk tt
       instance nat_inhabited: inhabited nat:= inhabited.mk 0
       instance unit_inhabited: inhabited unit:= inhabited.mk ()

       --Alternatively, we could use the anonymous constructor,
       instance Prop_inhabited': inhabited Prop := ⟨true⟩
       -- ...etc...

     end ualib

   The declarations above record the definitions of ``Prop_inhabited``, ``bool_inhabited``, ``nat_inhabited``, and ``unit_inhabited`` in a *list of instances* so that when the elaborator looks for a value to assign to an argument ``?M`` of type ``inhabited α``, it checks the list for a suitable instance.

   For example, when looking for an instance of ``inhabited Prop``, it finds ``Prop_inhabited``.

#. **Define a function that infers an instance and puts it to use**.

   In this step, we mark implicit arguments to the function with square brackets (``[ ]``) which prompts the elaborator to use the type class inference mechanism to infer this argument.

   In the next example, ``s: inhabited α`` is the element to be inferred by the elaborator.

   ::

     namespace ualib
       class inhabited (α: Type _) := (default: α)
       instance Prop_inhabited: inhabited Prop := inhabited.mk true
       instance bool_inhabited: inhabited bool := inhabited.mk tt
       instance nat_inhabited: inhabited nat := inhabited.mk 0
       instance unit_inhabited: inhabited unit := inhabited.mk ()
       -- BEGIN
       --default.
       --Extract the default element ``a`` of the given type ``α``.
       def default (α: Type _) [s: inhabited α]: α:=
       @inhabited.default α s
       -- END
     end ualib

   Now the expression ``default α`` will prompt the elaborator to synthesize an inhabitant of type ``α``, if possible.

   We can check the type of, and even see, the synthesized value with the ``#check`` and ``#reduce`` directives.

   ::

     namespace ualib
       class inhabited (α: Type _) := (default: α)
       instance Prop_inhabited: inhabited Prop := inhabited.mk true
       instance bool_inhabited: inhabited bool := inhabited.mk tt
       instance nat_inhabited: inhabited nat := inhabited.mk 0
       instance unit_inhabited: inhabited unit := inhabited.mk ()

       --default.
       --Extract the default element ``a`` of the given type ``α``.
       def default (α: Type _) [s: inhabited α]: α:=
       @inhabited.default α s
       -- BEGIN
       #check default Prop    -- Prop
       #reduce default Prop   -- true
       -- END
     end ualib

Chaining instances
~~~~~~~~~~~~~~~~~~~

As described thus far, type class inference is merely a means of providing the elaborator with a look-up table to consults when an instance of certain given type is needed.

The true power of type class inference lies in the ability to *chain* instances; that is, an instance declaration can in turn depend on an implicit instance of a type class. Thus type class inference can chain through instances recursively, backtracking when necessary.

.. proof:example:: prod_inhabited

   ::

     namespace ualib

       class inhabited (α: Type _) := (default: α)
       def default (α: Type _) [s: inhabited α]: α :=
       @inhabited.default α s

       instance prod_inhabited {α β: Type _}
       [inhabited α] [inhabited β]: inhabited (prod α β) :=
       ⟨(default α, default β)⟩

       --Type class inference yields a default ``nat × bool``:
       #check  default (nat × bool) -- ℕ × bool
       #reduce default (nat × bool) -- (0, tt)
       example: default (nat × bool) = (0, tt) := rfl

     end ualib

.. proof:example:: prod_inhabited, fun_inhabited

      In this example we first demonstrate that, if types ``α`` and ``β`` are both inhabited, then so is their product. We then show how to select a function to be the ``default`` value in a function space, so long as the codomain type is ``inhabited``.  (The constant function that takes the default value is the only choice.)

   ::

     namespace ualib

       class inhabited (α: Type _) := (default: α)

       def default (α: Type _) [s: inhabited α]: α :=
       @inhabited.default α s

       instance prod_inhabited {α β: Type _}
       [inhabited α] [inhabited β]: inhabited (prod α β) :=
       ⟨(default α, default β)⟩

       instance fun_inhabited (α: Type _) {β: Type _}
       [inhabited β]: inhabited (α → β) :=
       inhabited.mk (λ (a: α), default β)

       #check  default (nat → bool) -- ℕ → bool
       #reduce default (nat → bool) -- λ (a: ℕ), tt
       example: default (nat → bool) = λ (a: ℕ), tt := rfl

       #check  default (nat → Prop × unit) -- ℕ → Prop × unit
       #reduce default (nat → Prop × unit)
       -- λ (a: ℕ), (true, punit.star)

       example:
       default (nat → Prop × unit) = λ (a: ℕ), (true, ()) := rfl
     end ualib

(*Spoiler alert!* The reader is urged to think about natural default instances for ``list`` and ``sum`` types before proceeding to the next two examples.)

.. proof:example:: list_inhabited

   A natural ``default`` instance for a ``list α``, where ``α`` is ``inhabited``, is the following.

   ::

     namespace ualib
       class inhabited (α: Type _) := (default: α)

       def default (α: Type _) [s: inhabited α]: α :=
       @inhabited.default α s

       instance list_inhabited (α: Type _) [inhabited α]:
       inhabited (list α) :=
       inhabited.mk (list.cons (default α) list.nil)
     end ualib

.. proof:example:: sum_inhabited

   Here's a natural default instance for the ``sum`` of types, one of which is ``inhabited``, depends of course on which type is inhabited.

   ::

     namespace ualib
       class inhabited (α: Type _) := (default: α)
       def default (α: Type _) [s: inhabited α]: α :=
       @inhabited.default α s

       instance sum_inl_inhabited (α: Type _) (β: Type _)
       [inhabited α]: inhabited (sum α β) :=
       inhabited.mk (sum.inl (default α))

       instance sum_inr_inhabited (α: Type _) (β: Type _)
       [inhabited β]: inhabited (sum α β) :=
       inhabited.mk (sum.inr (default β))

       #check  default (sum nat bool) -- ℕ ⊕ bool
       #check  default (sum α bool)   -- α ⊕ bool
       #check  default (sum Prop β)   -- Prop ⊕ β

       example: default (sum nat bool) = sum.inr tt := rfl
       example: default (sum   α bool) = sum.inr tt := rfl
       example: default (sum nat    β) = sum.inl 0 := rfl
       example: default (sum nat unit) = sum.inr () := rfl
     end ualib

   If neither type ``α`` nor ``β`` is assumed ``inhabited``, then of course ``default (sum α β)`` should result in an error. Indeed,

   ::

     namespace ualib
       class inhabited (α: Type _) := (default: α)
       def default (α: Type _) [s: inhabited α]: α :=
       @inhabited.default α s

       instance sum_inl_inhabited (α: Type _) (β: Type _)
       [inhabited α]: inhabited (sum α β) :=
       inhabited.mk (sum.inl (default α))

       instance sum_inr_inhabited (α: Type _) (β: Type _)
       [inhabited β]: inhabited (sum α β) :=
       inhabited.mk (sum.inr (default β))

       variables (α : Type) (β : Type)
       #check  default (sum α β)
       -- results in error:
       --   failed to synthesize type class instance
       --   for α β : type ⊢ inhabited (α ⊕ β)
     end ualib

------------------------------

Inferring notation
-------------------

A slogan that captures the original motivation for the use of type classes (e.g., in a functional programming language like Haskell) is,

  *To overload is human*.
  *To do so in a principled way, divine*.

Indeed, type classes were invented in Haskell to lend order to the chaos of *ad hoc* overloading, so that programmers would overload in a more "principled" way.

For example, a symbol like ``+`` can be have unrelated meanings, but typically denotes a binary operation, of type ``α → α → α`` for some ``α``. Type classes let us infer an appropriate addition function for a given type.  *This is especially useful for developing algebraic hierarchies of structures in a formal setting*.

The standard library declares a type class ``has_add α`` as follows:

::

  namespace hide

    universes u v

    class has_add (α: Type u) := (add: α → α → α)

    def add {α: Type u} [has_add α]: α → α → α :=
    has_add.add

    local notation a `+` b := add a b

    instance nat_has_add: has_add nat:=
    has_add.mk nat.add

    instance bool_had_add: has_add bool:= has_add.mk bor

    #reduce 2 + 2   -- 4
    #reduce tt + ff -- tt

  end hide

.. proof:example:: prod_has_add := element-wise addition of pairs

   ::

     namespace ualib

       instance prod_has_add {α: Type u} {β: Type v}
       [has_add α] [has_add β]: has_add (α × β) :=
       has_add.mk (λ (p q: α × β), (p.fst + q.fst, p.snd + q.snd))

       #check (1, tt) + (2, ff) -- ℕ × bool
       example: (1, tt) + (2, ff) = (3, tt) := rfl

    end ualib

.. proof:example:: fun_has_add := point-wise addition of functions

   ::

     namespace ualib

       instance fun_has_add {α: Type u} {β: Type v}
       [has_add β]: has_add (α → β) :=
       has_add.mk (λ (f g: α → β), (λ (a:α), (f a) + (g a)))

       #reduce (λ (n:nat), n+1) + (λ (n:nat), n-1)
       #reduce (λ (n:nat), 1) + (λ (n:nat), 3) -- λ (a: ℕ), 4

     end ualib

(*Spoiler alert!* The reader is urged to think about how to implement a ``has_add`` for ``list`` types before proceeding to the next example.)

.. proof:example:: list_has_add := element-wise addition of lists

   A natural instance of ``has_add`` for the type ``list α`` adds elements of two lists point-wise, under the assumption ``[has_add α]``.

   ::

     namespace ualib

       def add_lists {α: Type u} [has_add α]:
       (list α) → (list α) → (list α)
       | l1 list.nil := l1
       | list.nil l2 := l2
       | (h1::t1) (h2::t2) := list.cons (h1 + h2) (add_lists t1 t2)

       --list_has_add
       instance list_has_add {α: Type u}
       [has_add α]: has_add (list α) :=
       has_add.mk (λ (l1 l2: list α), add_lists l1 l2)

       #reduce add_lists [0,10] [1,2,3] -- [1, 12, 3]

     end ualib


.. proof:example:: apply_instance, infer_instance

   We can see what classes and instances are currently in scope and which are ``inhabited`` with the very useful ``#print classes`` and ``#print inhabited`` directives.

   Suppose we need an expression that (we believe) Lean should be able to infer by using the type class inference mechanism. Then we might employ the tactic ``apply_instance`` or the expression ``infer_instance``.

   Here are some examples.

   ::

     def foo: has_add nat := by apply_instance
     #print foo -- nat.has_add

     #reduce foo -- add := λ (a a_1: ℕ), ... proof object ...

     def bar: has_add nat := infer_instance
     #print bar -- infer_instance
     #reduce bar -- add := λ (a a_1: ℕ), ... proof object ...

     def baz: inhabited (nat → nat) := by apply_instance
     #print baz -- pi.inhabited ℕ
     #reduce baz -- {default := λ (a: ℕ), 0}

     def bla: inhabited (nat → nat) := infer_instance
     #print bla -- infer_instance
     #reduce bla -- {default := λ (a: ℕ), 0}

     lemma ex1 : inhabited (nat → nat) := by apply_instance
     #print ex1 -- fun_inhabited ℕ
     #reduce ex1 -- {default := λ (a: ℕ), 0}

     lemma ex2 : inhabited (nat → nat) := ualib.fun_inhabited ℕ
     #print ex2 -- fun_inhabited ℕ
     #reduce ex2 -- {default := λ (a: ℕ), 0}

     lemma ex3 : inhabited (nat → nat) := infer_instance
     #print ex3 -- infer_instance
     #reduce ex3 -- {default := λ (a: ℕ), 0}

.. proof:example:: unwrapping a definition

   The next example fails because Lean can't find an instance of ``inhabited (set α)``.

   ::

     lemma ex4 {α: Type*}: inhabited (set α) := by apply_instance

   It turns out, the class is buried under a definition.  We could deal with by explicitly specifying an instance, or by unfolding the definition of ``set``.

   ::

     lemma ex4 {α: Type*} : inhabited (set α) := ⟨∅⟩
     #print ex4 -- λ {α: Type u_1}, {default := ∅}
     #reduce @ex4 nat -- {default := λ (a: ℕ), false}

     lemma ex4' {α: Type*} : inhabited (set α) :=
     by unfold set; apply_instance
     #print ex4' -- λ {α: Type u_1}, eq.mpr _ (fun_inhabited α)
     #reduce @ex4' -- λ {α: Type u_1}, {default := λ (a: α), true}


------------------------------------

.. _coercions-using-type-classes:

Coercions using type classes
----------------------------

The most basic type of coercion maps elements of one type to elements of another; e.g., by a coercion from ``nat`` to ``int``, we identify ``n: nat`` with the integer ``n: int``.

But some coercions depend on parameters. For example, we may wish to view ``l: list α`` (with parameter ``α``) as an inhabitant of ``set α`` by taking the ``set`` of elements that appear in ``l``. The corresponding coercion is defined on the *family* of types ``list α``, parameterized by ``α``.

In Lean, there are three kinds of coercions that work on a family of types or a type class. These provide maps from a family of types (e.g., ``list α``) to, respectively,

  #. another family of types (e.g., ``set α``),
  #. the class of sorts (e.g., ``Type u``), or
  #. the class of function types (e.g., ``α → α``).

We now consider each of the three flavors of coercion in turn.

#. **Type family to type family**. This is the first kind of coersion.  It allows us to view an inhabitant of a member of the source family as inhabiting a corresponding member of the target family.

   We declare a coercion from ``α`` to ``β`` using ``has_coe α β``; e.g., if ``α`` is ``bool`` and ``β`` is ``Prop``,

   ::

     instance bool_to_Prop: has_coe bool Prop := 
     has_coe.mk (λ b, b=tt)

     #reduce if tt then 3 else 5
     #reduce if ff then 3 else 5

   To encode a coercion from ``list α`` to ``set α``, we use a little helper function.

   ::

     def list.to_set {α: Type u}: list α → set α
     | [] := ∅
     | (h::tl) := {h} ∪ (list.to_set tl)

     --coercion from ``list α`` to ``set α``.
     instance list_to_set_coe (α: Type u):
     has_coe (list α) (set α) :=
     has_coe.mk list.to_set

     def s: set nat := {1, 2}
     def l: list nat := [3, 4]
     #check s ∪ l -- s ∪ ↑l: set ℕ

     --#check s ∪ [3,4] -- fails since [3,4] is of type ``list ?m``
     #check s ∪ ↑[3,4]   -- set ℕ (okay)

   The standard library defines a coercion from subtype ``{x : α // p x}`` to ``α`` as follows:

   ::

     instance coe_subtype {α: Type u} {p: α → Prop}: 
     has_coe {x // p x} α := has_coe.mk (λ s, subtype.val s)

#. **Type family to the class of sorts**.

   The second kind of coercion allows us to view an inhabitant of a member of the source family a member of the *class of sorts*, that is, as a type.

   By "class of sorts" we mean the collection ``{Type u: u`` is a universe``}``.

   A coercion of this kind is of the form

     ``c: Π x1: A1, ..., xn: An, F x1 ... xn → Type u``

   where ``F`` is a family of types.

   We can write ``s: t`` whenever ``t`` is of type ``F a1 ... an``; i.e., the coercion allows us to view the elements of ``F a1 ... an`` as types.

   This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a ``Type``. For example, we can define a semigroup as follows:

   ::

     structure Semigroup: Type (u+1) :=
     (carrier: Type u) (mul: carrier → carrier → carrier)
     ( mul_assoc: ∀ a b c: carrier,
       mul (mul a b) c = mul a (mul b c) )

     instance Semigroup_has_mul (S: Semigroup):
     has_mul (S.carrier) := has_mul.mk S.mul

#. **Type family to the class of function types**.

   This kind of coercion allows us to view an inhabitant of the source family as a function.

   .. todo:: complete this section

------------------------------

.. _algebraic-structure-hierarcy:

Algebraic structure hierarcy
-----------------------------

.. include:: structure_hierarchy_dual_no_rng.tex

In our ``algebra`` type, we used ``has_coe_to_sort`` and ``has_coe_to_fun``.  Here are the definitions of these coercions in the :term:`LSTL`.

::

  class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
  (S : Sort v) (coe : a → S)

  class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
  (F : a → Sort v) (coe : Π x, F x)

Group-like structures
-------------------------

.. include:: grouplike_hierarchy.tex

Magma
Semigroup
Monoid
Group
Rack
Quandle
Quasigroup
Loop
Abelian group
Lie group

Ring-like structures
---------------------
Ring
Semiring
Nearing
Commutative ring
Integral domain
UFD
PID
Euclidean domain
Division ring
Field

Module-like structures
------------------------
Module 
Group with operators
Vector space
Linear algebra

Algebra-like structures
-------------------------
Algebra
Associative algebra
Nonassociative algebra 
Composition algebra
Lie algebra
Graded algebra
Bialgebra

Lattice hierarchy
------------------

Proofs of the relationships in the map
Algebraic structures
Group-like[show]
Ring-like[show]
Lattice-like[show]
Module-like[show]
Algebra-like[show]
vte

#. A boolean algebra is a complemented distributive lattice. (def)

#. A boolean algebra is a heyting algebra.

#. A boolean algebra is orthocomplemented.

#. A distributive orthocomplemented lattice is orthomodular.

#. A boolean algebra is orthomodular. (1,3,4)

#. An orthomodular lattice is orthocomplemented. (def)

#. An orthocomplemented lattice is complemented. (def)

#. A complemented lattice is bounded. (def)

#. An algebraic lattice is complete. (def)

#. A complete lattice is bounded.

#. A heyting algebra is bounded. (def)

#. A bounded lattice is a lattice. (def)

#. A heyting algebra is residuated.

14. A residuated lattice is a lattice. (def)

15. A distributive lattice is modular.[4]

16. A modular complemented lattice is relatively complemented.[5]

17. A boolean algebra is relatively complemented. (1,15,16)

18. A relatively complemented lattice is a lattice. (def)

19. A heyting algebra is distributive.[6]

20. A totally ordered set is a distributive lattice.

21. A metric lattice is modular.[7]

22. A modular lattice is semi-modular.[8]

23. A projective lattice is modular.[9]

24. A projective lattice is geometric. (def)

25. A geometric lattice is semi-modular.[10]

26. A semi-modular lattice is atomic.[11][disputed – discuss]

27. An atomic lattice is a lattice. (def)

28. A lattice is a semi-lattice. (def)

29. A semi-lattice is a partially ordered set. (def)

-------------

.. include:: hyperlink_references.rst
