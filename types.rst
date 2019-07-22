.. include:: _static/math_macros.rst

.. _types:

=====
Types
=====

This section presents some of the rudiments of **type theory**.  For more details, a nice and easy introduction to the basics is `Logic and Proof`_. 

A more comprehensive treatment is :cite:`Mitchell:1996`; more advanced treatments are :cite:`Nederpelt:2014` and :cite:`HoTT:2013`.

.. _curry-howard:

Curry-Howard correspondence
----------------------------

The rule for *function application* corresponds, under the “Curry-Howard” or “propositions-as-types” correspondence, to the *implication elimination* rule of natural deduction (sometimes called *modus ponens*). It is the following:

This simply codifies our intuitive notion of function application, viz. applying the function :math:`f` to an inhabitant :math:`a` of the domain :math:`A`, we obtain an inhabitant :math:`f \ a` of the codomain :math:`B`. If we interpret :math:`A` and :math:`B` as propositions, :math:`f` as a proof of the implication :math:`A → B`, and :math:`a` as a proof of :math:`A`, then the rule :math:`\mathsf{app}` becomes the implication elimination rule (*modus ponens*).

.. index:: dependent types 

.. _dependent-types:

Dependent types
---------------

Lean_ is a functional programming language that supports **dependent types**. Here we give an example demonstrating that dependent types provide a more precise representation of the types of certain functions that are important in universal algebra and elsewhere. Besides being more precise and elegant, this representation is intrinsically computational.

Before getting to the example, however, we should first briefly explain what makes dependent types *dependent*, and why they are so useful.

Types can depend on *parameter values*.  For example, the type ``list α`` (lists with elements from α) depends on the argument α and the type ``vec α n`` (vectors of length ``n`` with entries from α) depends on ``α: Type`` (the type of the elements in the vectors) and ``n: ℕ`` (the length of the vectors).

The first, ``list α``, is an example of a **polymorphic type** which is usually not considered a kind of dependent type.  One could argue that the type ``list α`` *depends* on the argument α; for example, this dependence distinguishes ``list ℕ`` from ``list bool``.  However, since the dependence is on the argument ``α``, which denotes denotes a type, rather than a particular *value* (or *inhabitant*) of a type, this dependence is called **polymorphism**.

Contrast this with the example in the previous paragraph, where the type ``vec α n`` depends on the *value* of the variable ``n`` (which is an *inhabitant* of the type ℕ). This is the sort of dependence for which we reserve the moniker "dependent type".

Suppose we wish to write a function ``cons`` that inserts a new element at the head of a list. What type should cons have? Such a function is polymorphic: we expect the ``cons`` function for ℕ, ``bool``, or an arbitrary type α to behave the same way. So it makes sense to take the type to be the first argument to ``cons``, so that for any type, α, ``cons α`` is the insertion function for lists of type ``α``. In other words, for every ``α``, ``cons α`` is the function that takes an element ``a: α`` and a list ``l: list α``, and returns a new list, so that ``con α a l: list α``.

It is clear that ``cons α`` should have type ``α → list α → list α``. But what type should ``cons`` have?  Certainly not ``Type → α → list α → list α`` since the ``α``  appears as if from nowhere, while it should refer to an argument of type ``Type``, 

In other words, we must first assume that a specific (arbitrary) ``α: Type`` is the first argument to the function, so that the type of the next two elements are can be specified as ``α`` and ``list α``. This is an instance of a :term:`pi type`, or :term:`dependent function type <pi type>`. Given ``α: Type`` and ``β: α → Type``, think of ``β`` as a family of types, one type ``β a`` for each ``a: α``.

In this case, the type ``Π(x:α),β x`` denotes the type of functions ``f`` with the property that, for each ``a: α``, ``f a`` is an element of ``β a``. In other words, the type of the value returned by ``f`` *depends* on its input.

Notice that ``Π(x:α),β`` makes sense for any expression ``β: Type``. When the value of ``β`` depends on ``x`` (as does, for example, the expression ``β x`` in the previous paragraph), ``Π(x:α),β`` denotes a dependent function type. If ``β`` doesn't depend on ``x``, then ``Π(x:α),β`` is no different from the type ``α → β``. Indeed, in dependent type theory (and in Lean_), the Pi construction is fundamental, and ``α → β`` is just notation for ``Π(x:α),β`` in the special case in which ``β`` does not depend on ``x``.

.. index:: type of; dependent functions (pi type)

The :term:`pi type` :math:`\Pi_{(x:A)}, B x`, also known as the :ref:`dependent function type <pi-type>`, generalizes the function type :math:`A → B` by allowing the codomain :math:`B x` to depend on the value :math:`x: A` of the function's "input."

The simplest example of a pi type is the Cartesian product :math:`B_0 × B_1` which, when viewed as the collection of functions that map :math:`i ∈ \{0, 1\}` to some element of :math:`B_i`, is the type :math:`\Pi_{(i:\mathsf{bool})}, B_i`. [1]_

.. index:: type of; dependent pairs (Sigma type)

Similarly, the :term:`sigma type` :math:`\sum_{(x:A)}, B x`, also known as the :ref:`dependent pair type <sigma-type>`, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.

The simplest example of a Sigma type is the disjoint union :math:`B_0 \coprod B_1` which may be viewed as a collection of ordered pairs :math:`(i, b_i)`, where the first coordinate indicates to which set the second element belongs.  For example, if the two sets are :math:`B_0 = \{a, b\}` and :math:`B_1 = \{a, b, c\}` we form the disjoint union of :math:`B_0` and :math:`B_1` as follows:

.. math:: B_0 + B_1 = \{(0,a), (0,b), (1,a), (1,b), (1,c)\}.

Alternatively, some authors prefer to use an injection function to indicate the set from which an element originated.  For example, if we choose to denote the injective function by :math:`ι: \{0, 1\} → \{a, b\} ∐ \{a, b, c\}`, then we could represent the coproduct in the example above as follows:

.. math:: B_0 + B_1 = \{ι_0 a,\, ι_0 b,\, ι_1 a,\, ι_1 b,\, ι_1 c\}.

(The symbol ι is produced by typing ``\iota``; see :numref:`symbol-commands`.)

-----------------------------------------------

.. _generalized-projections:

.. index:: projection

Generalized projections
-----------------------

Here we present a more general way of describing projections.

Let :math:`\{A_i: i ∈ I\}` be a collection of sets (for some :math:`I ⊆ ℕ`) and let :math:`\underline{A} = ∏_{i ∈ I} A_i`. View the elements of :math:`\underline{A}` as functions:

.. math:: a ∈ ∏_{i∈I} A_i \quad ⟷ \quad \begin{cases} a : I → ⋃_{i∈I} A_i, & \\ a(i) ∈ A_i, & ∀ i ∈ I. \end{cases}
   :label: 7
   
This correspondence simply records the fact that the product type (on the left of the ⟷ symbol) represents a special kind of function type (depicted on the right of ⟷ using the usual arrow notation for function types). In other words, :eq:`7` says that an element of the product type :math:`∏_{i∈I} A_i` is a function from :math:`I` into :math:`⋃_{i∈I} A_i` whose codomain :math:`A_i` *depends* on the input argument :math:`i`. Such a function (or product) type is known as a :term:`dependent type`.

Now, given a subset :math:`J ⊆ I`, a function :math:`g : J → I`, and an element :math:`a ∈ ∏_{i∈I} A_i`, consider the composition :math:`a ∘ g`. This is a function from :math:`J` to :math:`⋃_{j∈J} A_{g(j)}`, where :math:`(a ∘ g)(j) ∈ A_{g(j)}`. Again, we could express this function type using the arrow notation, ":math:`a ∘ g : J → ⋃_{j∈J} A_{g(j)}` where :math:`(a ∘ g)(j) ∈ A_{g(j)}`," but this specification has a nicer, more compact description using a :term:`dependent function type`.

.. math:: a ∘ g ∈ ∏_{j∈J} A_{g(j)}.

Assume :math:`g` is one-to-one and define the “projection” function,

.. math:: \Proj(g) : ∏_{i∈I} A_{i} → ∏_{j∈J} A_{g(j)}

by :math:`\Proj(g): a ↦ (a ∘ g)`. That is, :math:`\Proj(g)(a) = a ∘ g`.

We could try to specify the type of :math:`\Proj` using the arrow notation as follows:

.. math::    \Proj : (J → I) → \bigl( I → \bigcup_{i∈I} A_{i} \bigr) → \bigl(J → ⋃_{i∈I} A_{i}\bigr),
   :label: 8

but the deficiencies of the arrow notation are now even more glaring. The function type specification given in :eq:`8` is imprecise and arguably misleading. The result of applying :math:`\Proj` first to some :math:`g: J → I` and then :math:`a : I → ⋃_{i∈I} A_{i}` is :math:`\Proj (g) (a) = a ∘ g`, and to say that this is a function of type :math:`J → ⋃_{i∈I} A_{i}` is ambiguous at best.

Rather, the complete, correct type specification is actually “:math:`\Proj (g) (a) : J → ⋃_{j∈J} A_{g(j)}` where :math:`\Proj (g) (a) (j) ∈ A_{g(j)}`.”

Again, we can express this more concisely with a dependent function type, :math:`\Proj (g)(a) ∈ ∏_{j∈J} A_{g(j)}`. Thus, to denote the type of :math:`\Proj`, we must add to :eq:`8` the constraints on codomains that depend on argument values. For specifying the type of a "function of higher order" (or "functional"), the arrow notation can be cumbersome.

The following is closer to what we want, but still imperfect:

.. math:: \Proj: (J → I) → ∏_{i∈I} A_{i} → ∏_{j∈J} A_{g(j)}.
   :label: 9

This says that :math:`\Proj` takes a function :math:`g : J → I` and a function :math:`a ∈ ∏_{i∈I} A_i` and returns the function :math:`a ∘ g ∈ ∏_{j∈J} A_{g(j)}`.

Here again we see that the arrow notation is not expressive enough because :math:`∏_{j∈J} A_{g(j)}` depends on :math:`g`, but there is no :math:`g` symbol available from earlier in :eq:`9`.

The solution is again to denote the function type as a product. Product types are very expresive and enable us to concisely specify such dependent function types. Before demonstrating this, we make one more notational adjustment. Instead of denoting set membership by :math:`a ∈ A`, we adopt the type-theoretic notation :math:`a:A`, which expresses the fact that :math:`a` *has type* :math:`A`. Thus, the full :term:`dependent type` specification of the projection operation is

.. math:: \Proj: ∏_{g:J→I} \left( ∏_{i:I} A_{i} →  ∏_{j:J} A_{g(j)} \right).

This is a special case of the more general (and more elegant) types that we define in later chapters, after reviewing some concepts of category theory in :numref:`postmodern-algebra` that are essential for this purpose.

---------------------------------------

.. _kernels-of-projections:

.. index:: projection kernel

Kernels of projections
----------------------

Let :math:`𝔸 = ∏_{i:I} 𝔸_i` be a product of algebras with the same :term:`signature`, and suppose :math:`g: J → I` is a one-to-one function, where :math:`∅ ≠ J ⊆ I ⊆ ℕ`.

Define the **kernel of the projection of** :math:`𝔸` **onto** :math:`∏_{j:J} A_{g(j)}` as follows:

.. math:: Δ_g = \{(a,a') : 𝔸^2 | a ∘ g = a' ∘ g \} = \ker (\Proj g)

This is a congruence of :math:`𝔸`. More generally, if :math:`θ` is a congruence of :math:`∏_{j:J} A_{g(j)}`, define :math:`θ_g: \Con 𝔸` as follows:

.. math:: θ_g = (\Proj g)^{-1}(θ) =  \{ (a, a') : 𝔸^2 | (a ∘ g) \mathrel{\theta} (a' ∘ g) \}.

This indicates the origin of the notation :math:`Δ_g`, where :math:`Δ` denotes the trivial (identity) relation on :math:`∏_{j:J} A_{g(j)}`. If :math:`J = \{0\}` and
:math:`g: I` is just a constant, say, :math:`g(0) = k`,
then we write :math:`\theta_k` instead of :math:`\theta_{\{k\}}`, so

.. math:: \theta_k = \{(a, a') \in 𝔸^2 : a(k) \mathrel{\theta} a'(k)\}.

(Here, :math:`\theta` must be in :math:`\Con 𝔸_k`.)

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

Fix :math:`m ∈ ℕ`. If :math:`a = (a_0, a_1, \dots, a_{m-1})` is an :math:`m`-tuple of elements from :math:`A`, then (keeping in mind that :math:`m` is the set :math:`\{0, 1, \dots, m-1\}`) it is useful to understand that this tuple is a function :math:`a: m → A`, where :math:`a(i) = a_i`, for each :math:`i<m`. If :math:`h: A → A`,
then :math:`h ∘ a: m → A` is the tuple :math:`(h(a_0), h(a_1), \dots, h(a_{m-1})) ∈ A^m`, whose :math:`i`-th coordinate is :math:`(h ∘ a)(i) = h(a(i)) = h(a_i) ∈ A`.

On the other hand, if :math:`g: A^m \to A`---equivalently, :math:`g: (m → A) → A`---then :math:`g a` is the element :math:`g(a_0, a_1, \dots, a_{m-1}) ∈ A`.

If :math:`f: (ρ f → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, if :math:`a: ρ f → A` is a :math:`ρ f`-tuple on :math:`A`, and if :math:`h: A → B`, then
:math:`h ∘ a: ρ f → B`, so :math:`f (h ∘ a): B`.

-----------------------------------------------------

.. index:: partial application

.. _partial-application:

Partial application
-------------------

Let :math:`I` be a nonempty set and :math:`\{A_i | i: I\}` a family of sets.

Elements of the product :math:`∏_{i∈ I} A_i` are functions :math:`a: I → ⋃_{i:I} A_{i}` such that for each :math:`i` we have :math:`a(i): A_i`.

Let :math:`J ⊆ I` and let :math:`g: J → I` be one-to-one. Then, as above, :math:`a ∘ g: ∏_{j: J} A_{g(j)}` gives the projection of :math:`a` onto certain coordinates of the full product, namely, the coordinates :math:`\im g = \{g(j) ∣ j:J\}`.

Suppose :math:`f` is a self map of the set :math:`\underline{A} := ∏_{i: I} A_i`. That is, :math:`f: \underline{A} → \underline{A}`. If :math:`I = \{0, 1, \dots, n-1\}`, then :math:`\underline{A} = ∏_{i=0}^{n-1} A_i` and the (curried) type of :math:`f` is

.. math:: f: A_0 → (A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

For a given :math:`a_0: A_0`, the function :math:`f` partially applied at the first coordinate has type

.. math:: f(a_0): A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

To ease notation we will sometimes write function application by juxtaposition so that :math:`f a_0 := f(a_0)`, for example. For elements :math:`a_0` and :math:`a_1` inhabiting types :math:`A_0` and :math:`A_1` (resp.), the partial application of :math:`f` to these elements yields the following function and typing judgment:

.. math:: f a_0 a_1: A_2 → (A_3 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1}))\cdots ).

In general, for :math:`a_i: A_i`, :math:`0 ≤ i < ℓ`,

.. math:: f a_0 a_1 \dots a_{ℓ-1}: A_ℓ → (A_{ℓ+1} → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

It would be useful to have a means of partial function application in case the domain :math:`I` is not simply :math:`\{0, 1, \dots, n-1\}`, or in case we wish to partially apply a function to an arbitrary subset of its operands (coordinates of its domain). If we have, as above,

+ :math:`\underline{𝔸} = ∏_{i:I} A_i`,

+ :math:`g: J → I` (one-to-one),

+ :math:`a ∘ g: ∏_{j:J} A_{g(j)}`, for each :math:`a : ∏_{i:I} A_i`,

Let :math:`f` have type :math:`∏_{i:I} A_i → ∏_{i:I} A_i`, which means that if we apply :math:`f` to an element :math:`a : ∏_{i:I} A_i` the result has the same type, that is, :math:`f a : ∏_{i:I} A_i`.

We may wish to apply :math:`f` to just a portion of :math:`a` but it may not be the case that :math:`I` is a subset of :math:`ℕ`, or an ordered enumeration of some other set, so there is no natural notion of “the first :math:`ℓ` operands.” Even if there was such a notion, we may wish to partially apply :math:`f` to something other than the first :math:`ℓ` operands. Therefore, we define a more general notion of partial application as follows: :math:`f` partially applied to the coordinates :math:`\im g = \{g(j) ∣ j: J\}` of the element :math:`a` gives the function : type judgment

.. math:: f ∘ (a ∘ g): ∏_{\substack{i: I\\ i ∉ \im g}} A_i → ∏_{i:I} A_i.

Asynchronous currying
~~~~~~~~~~~~~~~~~~~~~

.. todo:: continue to describe asynchronous curry type

------------------------------

.. index:: inductive type, universes

.. _inductive-types:

Inductive types
-----------------

.. todo:: complete this section

(See also: the `Inductive Types <https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#>`_ section of :term:`TPIL`.)

--------------------------------------------

.. rubric:: Footnotes

.. [1]
   It is more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1) : b_i ∈ B_i, i = 0, 1\}`, but identifying tuples with functions yields a :term:`pi type`.

.. _Agda: https://wiki.portal.chalmers.se/agda/pmwiki.php

.. _Coq: http://coq.inria.fr
      
.. _NuPRL: http://www.nuprl.org/

.. _Lean: https://leanprover.github.io/

.. _Logic and Proof: https://leanprover.github.io/logic_and_proof/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. _mathlib: https://github.com/leanprover-community/mathlib/

.. _Lean Standard Library: https://github.com/leanprover/lean

.. _lattice.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/lattice.lean

.. _basic.lean: https://github.com/leanprover-community/mathlib/blob/master/src/data/set/basic.lean

.. _set.lean: https://github.com/leanprover/lean/blob/master/library/init/data/set.lean

.. _2015 post by Floris van Doorn: https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean/


