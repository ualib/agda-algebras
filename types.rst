.. role:: cat

.. include:: _static/math_macros.rst

.. _types:

=====
Types
=====

This section presents little more of the rudiments of :term:`type theory` than we will need for formalizing universal algebra in the `Lean`_ :term:`proof assistant`.  For more details, a very nice and gentle introduction to type theory and Lean is the textbook `Logic and Proof`_, by Avigad, et al.

A more comprehensive yet still gentle treatment is *Foundations for Programming Languages* by Mitchell :cite:`Mitchell:1996`. More advanced books on this topic are *Type Theory and Formal Proof* by Geuvers and Nederpelt :cite:`Nederpelt:2014` and *Homotopy Type Theory: Univalent Foundations of Mathematics* (aka "The HoTT Book") :cite:`HoTT:2013` by roughly two dozen participants of the Univalent Foundations Program held in 2013 at the IAS in Princeton.

-----------------------------

The Basics
-----------

We begin with a slogan.  

  *In set theory virtually everything* **is** *a set, in type theory, everything* **has** *a type*.


.. todo:: complete this section

----------------------------------

.. index:: pair: ! implication elimination; ! modus ponens

.. _curry-howard:

Curry-Howard correspondence
----------------------------

The rule for :term:`function application` corresponds, under the :term:`Curry-Howard <Curry-Howard correspondence>` (or :term:`propositions-as-types`/:term:`proofs-as-programs`) :term:`correspondence <Curry-Howard correspondence>`, to the :term:`implication elimination` rule of natural deduction (sometimes called :term:`modus ponens`). This simply codifies our intuitive notion of function application, viz., applying the function :math:`f: A → B` to an element :math:`a` of :math:`A` yields a member :math:`f\,a` of the codomain :math:`B`.

If we interpret the types :math:`A` and :math:`B` as propositions and the function :math:`f: A → B` as a proof of the proposition ":math:`A` implies :math:`B`," and if we view :math:`a` as a proof of :math:`A`, then the application rule is the so called :term:`implication elimination` rule (or, :term:`modus ponens`); that is, "if :math:`A → B` and :math:`A`, then :math:`B`."

---------------------------------------

.. _dependent-types:

.. index:: type of; dependent functions
.. index:: type of; dependent pairs
.. index:: type of; lists
.. index:: type of; vectors

Dependent types
---------------

`Lean`_ is a :term:`functional programming` language that supports :term:`dependent types <dependent type>`.

In the present section we show how dependent types can be used to represent many concepts that are important in universal algebra in a way that we feel is precise, elegant, and intrinsically computational. [1]_ 

Before trying to understand why dependent types are so useful, it helps to know what dependent types *are*. Let us begin by explaining what makes a type dependent.

Types can depend on *parameters*.  For example, if ``α`` is a type, then ``list α`` is the type of lists whose entries have type ``α``.  The type ``list α``  depends on the parameter ``α``. The type of vectors of length ``n`` with entries from ``α`` is sometimes denoted by ``vec α n``. This type depends on the parameter ``α`` (the type of the elements that populate the vectors) and the *value* ``n`` of type ``ℕ`` (denoting the length of the vectors).

The type ``list α`` is an example of a :term:`polymorphic type`, which is not what we mean by a "dependent type."  Of course ``list α`` does depends on the argument ``α``, and this dependence distinguishes ``list ℕ`` from ``list bool``.  But in this instance, the argument ``α`` is not seen as a particular *value* (or *inhabitant*) of a type, but rather as a type parameter, and we call this type of dependence **polymorphism**. [2]_

Contrast this with the type ``vec α n``, which depends on the parameter ``α`` as well as the *value* of the variable ``n``. This is the sort of dependence for which we reserve the label "dependent type."

This example is somewhat misleading. It is not true that the only dependent types are those that depend on a concrete value of a type, e.g., ``n`` in the last example. In fact, types themselves may also be viewed as inhabitants of other types.  Indeed, in type theory, *everything* (even every type) has a type.

For example, if ``α:Type``, then ``α`` is both a type in its own right and an inhabitant of ``Type`` (which is Lean syntax for the "ground type.")

Consider the ``cons`` function that inserts a new element at the head of a list. What type should ``cons`` have?  Before answering, let us consider a few facts.

* For each type ``α``, ``cons α`` is the insertion function for lists of type ``list α``; it takes an element ``a:α`` and a list ``l:list α``, and returns a new list---the concatenation of ``a`` with the list ``l`` (sometimes denoted ``a::l``).

* ``cons`` is polymorphic and should behave in roughly the same way for lists with entries of type ℕ, or ``bool``, or an arbitrary type ``α``. 

* ``cons α`` has type ``α → list α → list α``.

But what about ``cons`` itself?  We might try ``cons: Type → α → list α → list α``, but this somehow choses a specific inhabitant of ``Type``---namely, ``α``---in advance, which we don't want.

Instead, since ``cons`` should be polymorphic, the caller of ``cons`` is free to choose some (any) type ``α:Type`` as the first argument; then (and only then) do we know the types, ``α`` and ``list α``, of the second and third arguments to ``cons``.

.. index:: ! Pi type
.. index:: type of; dependent functions

.. _pi-types:

Pi types
~~~~~~~~~

What we need in the situation just described is known as a :term:`Pi type`, or :term:`dependent function type <Pi type>`.  In the ``cons`` example, the correct typing judgement is

  ``cons: Π(a:Type), (α → list α → list α).``
  
Before explaining this notation and the type that it represents, let us first describe Pi types more generally.

If ``α`` is a type, we write ``α:Type``.  Then a function ``β`` of type ``α → Type`` represents a family of types, one type ``β x`` for each member ``x`` of the type ``α``.  The product of all these types is denoted by

  ``Π(a:α), β a``, 
  
which is itself a type, and is called a **dependent function type**.  This name arises because, for each inhabitant ``f: Π(a:α), β a``, we see that the type of the image ``f a`` of each ``a:α`` may depend on ``a``.  Precisely, ``f a: β a`` for each ``a:α``.

Suppose for all ``a:α`` the type ``β a`` does *not* depend on ``a``. Then ``Π(a:α), β a`` is equivalent to the (nondependent) function type ``α → β``.  Whence we see that ``α → β`` is a special case of the type ``Π(a:α), β a``. Indeed, in dependent type theory (and in Lean_) Pi types may be viewed as fundamental and function types as a special case.

To summarize, for each type ``α:Type`` and for every family of types ``β: α → Type``, we have the :term:`Pi type`, ``Π(a:α), β a`` which generalizes the function type ``α → β`` by allowing each section ``β a`` of the codomain to depend on a value ``a:α`` of the domain.

.. index:: type of; booleans
.. index:: Cartesian product

.. proof:example:: Cartesian product

   The simplest example of a Pi type is the **Cartesian product** :math:`B₀ × B₁` which is the set of all functions of the form :math:`f: \{0, 1\} → B₀ ∪ B₁` such that :math:`f \, 0 ∈ B₀` and :math:`f\, 1 ∈ B₁`.

   Suppose ``B₀:Type`` and ``B₁:Type`` are types and let ``bool`` denote the **Boolean type** inhabited by just ``0`` and ``1``.
   
   Let ``B: bool → Type`` be the function defined by ``B 0 = B₀`` and ``B 1 = B₁``.
   
   Then we represent the Cartesian product :math:`B_0 × B_1` by the type ``Π(i:bool), B i``. [3]_

.. index:: ! Sigma type
.. index:: type of; dependent pairs

.. _sigma-types:

Sigma types
~~~~~~~~~~~

Similarly, a :term:`Sigma type`, also known as the `dependent pair type <sigma-type>`_, generalizes the Cartesian product ``α × β`` by allowing the *type* of the second argument of an ordered pair to depend on the *value* of the first.

Sigma types arise from a type ``α:Type`` and a "type former" ``β: α → Type``, and are denoted using the ``Σ`` symbol, as follows:

  ``Σ(a:α), β a``. 

This type is inhabited by the "dependent pairs" ``(x,y)``, where ``x`` has type ``α`` and ``y`` has type ``β x``.

.. index:: ! disjoint union

.. proof:example:: Disjoint union in general

   The simplest example of a Sigma type is the disjoint union of two types, say, ``X:Type`` and ``Y:Type``. This is comprised of all pairs of the form ``(0,x)`` for ``x:X`` and ``(1,y)`` for ``y:Y``, and is sometimes denoted by ``X ∐ Y``.
   
   Note that the value of the first coordinate of such pairs indicates the type to which the second coordinate belongs.
   
   Expressing ``X ∐ Y`` in the ``Σ`` notation, we have ``α = bool`` and ``β: bool → X ∪ Y`` where ``β 0: X`` and ``β 1: Y``. Thus,
   
     ``X ∐ Y = Σ(a:bool), β a``.

.. proof:example:: Disjoint union example

   Suppose ``X =  {a, b}`` and ``Y = {a, b, c}``. Then, 

     ``X ∐ Y = {(0,a), (0,b), (1,a), (1,b), (1,c)}``.

   If ``(i,a): X ∐ Y``, then the second coordinate is the ``a`` of type ``A`` if ``i = 0``, while ``a:B`` if ``i = 1``.
   
   Some authors prefer to use an "injection" function, say, ``ι``, to indicate the set from which an element originated; in the present example,

     ``X ∐ Y = {ι0 a, ι0 b, ι1 a, ι1 b, ι1 c}``.

   (For ι type ``\iota``; some authors write ``inl`` ("in left") and ``inr`` ("in right") for ``ι0`` and ``ι1``.)

-----------------------------------------------

.. index:: ! projection operator, ! idempotent operation

.. _projection-operators:

Projection operators
--------------------

An operation :math:`f: A^n → A` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`.

Examples of idempotent operations are the *projections* and these play an important role in the theory, so we introduce a sufficiently general and flexible notation for them.

Denote and define the set ℕ of natural numbers inductively as follows:

.. math:: 0 = ∅, \quad 1 = \{0\}, \quad  2 := \{0, 1\}, \dots, n = \{0, 1, \dots, n-1\}.

Let :math:`\{A_i: i ∈ I\}` be a collection of sets (for some :math:`I ⊆ ℕ`) and let :math:`A = ∏_{i ∈ I} A_i`. View the elements of :math:`A` as functions:

.. math:: a ∈ ∏_{i∈I} A_i \quad ⟷ \quad \begin{cases} a : I → ⋃_{i∈I} A_i, & \\ a\,i ∈ A_i, & ∀ i ∈ I. \end{cases}
   :label: 7
   
This correspondence simply records the fact that the product type (on the left of the ⟷ symbol) is a special kind of function type (depicted on the right of ⟷ using the usual arrow notation for function types).

In other words, :eq:`7` says that an element of the product type :math:`∏_{i∈I} A_i` is a function from :math:`I` into :math:`⋃_{i∈I} A_i`.  As explained in :numref:`pi-types`, such a function (or product) type is known as a :term:`dependent type`.

Given a subset :math:`J ⊆ I`, a function :math:`σ: J → I`, and an element :math:`a ∈ ∏_{i∈I} A_i`, consider the composition :math:`a ∘ σ`. This is a function from :math:`J` to :math:`⋃_{j∈J} A_{σ\, j}`, where :math:`(a ∘ σ)\, j ∈ A_{σ\, j}`.

We could express this function type using the arrow notation, as in, ":math:`a ∘ σ: J → ⋃_{j∈J} A_{σ\, j}` where :math:`(a ∘ σ)\, j ∈ A_{σ\, j}`," but this specification has a nicer, more compact description using a :term:`dependent function type`, namely, 

.. math:: a ∘ σ ∈ ∏_{j∈J} A_{σ \, j}.

If :math:`σ` happens to be one-to-one, then we will define the **projection operator induced by** :math:`σ`. We denote this operator by

.. math:: \Proj\, σ : ∏_{i∈I} A_i → ∏_{j∈J} A_{σ \, i},
   :label: projection

and define it for each :math:`a ∈ ∏_{i∈I} A_i` by :math:`\Proj\, σ \, a = a ∘ σ`.

The following is closer to what we want, but still imperfect:

.. math:: \Proj: (J → I) → ∏_{i∈I} A_{i} → ∏_{j∈J} A_{g(j)}.
   :label: 9

This says that :math:`\Proj` takes a function :math:`σ: J → I` and a function :math:`a ∈ ∏_{i∈I} A_i` and returns the function :math:`a ∘ σ ∈ ∏_{j∈J} A_{σ \, j}`.

Here again we see that the arrow notation is not expressive enough because :math:`∏_{j∈J} A_{σ \, j}` depends on :math:`σ`, but there is no :math:`σ` symbol available from earlier in :eq:`9`.

The solution is again to denote the function type as a product. Product types are very expresive and enable us to concisely specify such dependent function types. Before demonstrating this, we make one more notational adjustment. Instead of denoting set membership by :math:`a ∈ A`, we adopt the type-theoretic notation :math:`a:A`, which expresses the fact that :math:`a` *has type* :math:`A`. Thus, the full :term:`dependent type` specification of the projection operator is

.. math:: \Proj: ∏_{σ:J→I} \left( ∏_{(i:I)} A_{i} →  ∏_{(j:J)} A_{σ\, j} \right).

This is a special case of the more general types that we define in later chapters, after reviewing some concepts of category theory in :numref:`Chapter %s <postmodern-algebra>` that are essential for this purpose.

.. proof:example:: Projection terminology

   Let us explain why the term "projection" is reserved for the case when :math:`σ` is one-to-one.
   
   Suppose :math:`k=4`, :math:`n=3`, and consider the 4-tuple :math:`σ = (1, 0, 1, 1)`.
   
   Then :math:`σ` is the function :math:`σ : \{0,1,2,3\} → \{0,1,2\}` given by
   
   .. math:: σ\, 0 = 1, \; σ\, 1 = 0`, \; σ\, 2 = 1, \; σ\, 3 = 1,
   
   and so :math:`a ↦ a ∘ σ` is the function that takes :math:`(a\, 0, a\, 1, a\, 2) ∈ A_0 × A_1 × A_2` to :math:`(a\, 1, a\, 0, a\, 1, a\, 1) ∈ A_1 × A_0 × A_1 × A_1`.

Let :math:`A = ∏_{0≤ i<n} A_i`, let :math:`σ: k → n` be one-to-one, and define the projection :math:`\Proj\, σ` as in :eq:`projection` above. Then the :term:`kernel` of :math:`\Proj\, σ`, which we denote by :math:`\mathbf{0} σ`, is denoted and defined by

.. math:: \mathbf{0} σ &= \ker \Proj\, σ = \{(a,a') ∈ A^2 | \Proj\, σ a = \Proj\, σ a'\}\\
                       &= \{ (a,a') ∈ A^2 | a ∘ σ = a' ∘ g \} = \{ (a,a') ∈ A^2 | ∀ j ∈ \im σ, \ a\, j = a'\, j \}.
   :label: kernel

It is obvious that :math:`\mathbf{0} σ` is an equivalence relation on the set :math:`A`.

More generally, if :math:`θ` is an equivalence relation on the set :math:`∏_{0≤ j<k} A_{σ\,j}`---that is, :math:`θ ⊆ (∏_{0≤ j<k} A_{σ\, j})^2` and :math:`θ` is reflexive, symmetric, and transitive---then we define the equivalence relation :math:`θ σ` on the set :math:`A = ∏_{0≤ i<n} A_i` as follows:

.. math:: θ σ = \{(a, a') ∈ A^2 ∣ (a ∘ σ) \mathrel{\theta} (a' ∘ σ)\}.
   :label: 17

In other words, :math:`θ σ` consists of all pairs in :math:`A^2` that land in :math:`θ` when projected onto the coordinates in :math:`\im σ`.

#. Recall that :math:`\Proj\, σ : A → ∏_{j<k} A_{σ\, j}` is the function that maps :math:`a` to :math:`a ∘ σ`.

   Now, suppose we have a tuple :math:`(a\, 0, a\, 1, \dots, a\, (p-1))∈ A^p`, and suppose we intend to apply :math:`\Proj\, σ` to each component, :math:`a \, j`.

   To do so, we need to lift :math:`\Proj\, σ` from type :math:`A → ∏_{j<k} A_{σ\, j}` to type :math:`A^p → (∏_{j<k} A_{σ\, j})^p`, which is accomplished using a functor that often goes by the name :math:`map`.

   For instance, if :math:`(a, a') ∈ A^2`, then :math:`map \,(\Proj\, σ)\, (a, a') = (\Proj\, σ \, a, \Proj\, σ \, a')`.

   Therefore,

   .. math:: θ σ =\{(a, a') ∈ A^2 ∣ map \, (\Proj\, σ)\, (a, a') ∈ θ \},

   whence, :math:`θ_g = map \, (\Proj\, σ)^{-1} \, θ`.

#. If :math:`f: X → A` and :math:`g: X → B` are functions defined  on the same domain :math:`X`, then :math:`(f,g): X → A × B` is the unique function that composes with the first projection to give :math:`f` and composes with the second projection to give :math:`g`. For example, in the last remark there appears the expression :math:`(\Proj\, σ\, a, \Proj\, σ \, a') = (a ∘ σ, a' ∘ σ)`, which has type :math:`( ∏_{j<k} A_{σ\, j} )^2`. [5]_

#. If the domain of :math:`σ` is a singleton, :math:`k = \{0\}`, then of course :math:`σ` is just a one-element list, say, :math:`σ = (j)`. In such cases, we write :math:`\Proj\, j` instead of :math:`\Proj\, {(j)}`.  Similarly, we write and :math:`\mathbf{0}\, j` and :math:`θ\, j` instead of :math:`\mathbf{0}\, {(j)}` and :math:`θ\, {(j)}`. Thus, :math:`\Proj\, j \, a = a\, j`, and :math:`\mathbf{0} \, j = \{(a, a') ∈ A^2 ∣ a \, j = a' \, j\}`, and, if :math:`θ ∈ \Con 𝔸_j`, then :math:`θ \, j = \{(a, a') ∈ A^2 ∣ a \, j \mathrel{\theta} a'\, j\}`.

Here are some obvious consequences of the foregoing notation and definitions that are worth noting.

.. math::

   ⋁_{0≤j<n}\mathbf{0}j = A^2, \quad \mathbf{0} σ = ⋀_{j ∈ σ} \mathbf{0} j, \quad \mathbf{0}n = ⋀_{0≤j<n}\mathbf{0} j = 0_A, \quad
   θσ = ⋀_{0≤j<k} θ \, σ\, j,

where :math:`0_{A}` denotes the least equivalence relation on :math:`A`, that is, :math:`0_{A}:= \{(a, a') ∈ A^2 ∣ a = a'\}`.

.. As we alluded to above, :math:`η_σ` is shorthand for :math:`(0_A)_σ`.

--------------------------------

.. _kernels-of-projections:

.. index:: projection kernel

Kernels of projections
----------------------

Let :math:`𝔸 = ∏_{(i:I)} 𝔸_i` be a product of algebras with the same :term:`signature`, and suppose :math:`g: J → I` is a one-to-one function, where :math:`∅ ≠ J ⊆ I ⊆ ℕ`.

Define the **kernel of the projection of** :math:`𝔸` **onto** :math:`∏_{(j:J)} A_{g(j)}` as follows:

.. math:: Δg = \{(a,a'): 𝔸^2 | a ∘ g = a' ∘ g \} = \ker (\Proj\, g)

This is a congruence of :math:`𝔸`. More generally, if :math:`θ` is a congruence of :math:`∏_{(j:J)} A_{g(j)}`, define :math:`θg: \Con 𝔸` as follows:

.. math:: θg = (\Proj\, g)^{-1}(θ) =  \{ (a, a') : 𝔸^2 | (a ∘ g) \mathrel{\theta} (a' ∘ g) \}.

This indicates the origin of the notation :math:`Δg`, where :math:`Δ` denotes the trivial (identity) relation on :math:`∏_{(j:J)} A_{g(j)}`. If :math:`J = \{0\}` and :math:`g:I` is just a constant, say, :math:`g(0) = k`, then we write :math:`θ k` instead of :math:`θ \{k\}`, so

.. math:: θ k = \{(a, a') \in 𝔸^2 : a\,k \mathrel{\theta} a'\,k\}.

(Here, :math:`\theta` must be in :math:`\Con 𝔸_k`.)

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

Fix :math:`m ∈ ℕ`. If :math:`a = (a_0, a_1, \dots, a_{m-1})` is an :math:`m`-tuple of elements from :math:`A`, then (keeping in mind that :math:`m` is the set :math:`\{0, 1, \dots, m-1\}`) it is useful to understand that this tuple is a function :math:`a: m → A`, where :math:`a\,i = a_i`, for each :math:`i<m`. If :math:`h: A → A`, then :math:`h ∘ a: m → A` is the tuple :math:`(h\, a_0, h\, a_1, \dots, h\, a_{m-1}) ∈ A^m`, whose :math:`i`-th coordinate is :math:`(h ∘ a)\, i = h(a\, i) = h(a_i) ∈ A`.

On the other hand, if :math:`g: A^m → A`---equivalently, :math:`g: (m → A) → A`---then :math:`g a` is the element :math:`g(a_0, a_1, \dots, a_{m-1}) ∈ A`.

If :math:`f: (ρ f → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, if :math:`a: ρ f → A` is a :math:`ρ f`-tuple on :math:`A`, and if :math:`h: A → B`, then
:math:`h ∘ a: ρ f → B`, so :math:`f (h ∘ a): B`.

-----------------------------------------------------

.. index:: partial application

.. _partial-application:

Partial application
-------------------

Let :math:`I` be a nonempty set and :math:`\{A_i | i: I\}` a family of sets.

Elements of the product :math:`∏_{i∈ I} A_i` are functions :math:`a: I → ⋃_{i:I} A_{i}` such that for each :math:`i` we have :math:`a\,i: A_i`.

Let :math:`J ⊆ I` and let :math:`g: J → I` be one-to-one. Then, as above, :math:`a ∘ g: ∏_{j: J} A_{g(j)}` gives the projection of :math:`a` onto certain coordinates of the full product, namely, the coordinates :math:`\im g = \{g\, j ∣ j:J\}`.

Suppose :math:`f` is a self-map of the set :math:`A := ∏_{i: I} A_i`. That is, :math:`f: A → A`. If :math:`I = \{0, 1, \dots, n-1\}`, then :math:`A = ∏_{i=0}^{n-1} A_i` and the (curried) type of :math:`f` is

.. math:: f: A_0 → (A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

For a given :math:`a_0: A_0`, the function :math:`f` partially applied at the first coordinate has type

.. math:: f\, a_0: A_1 → (A_2 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

For elements :math:`a_0` and :math:`a_1` inhabiting types :math:`A_0` and :math:`A_1` (resp.), the partial application of :math:`f` to these elements yields the following function and typing judgment:

.. math:: f a_0 a_1: A_2 → (A_3 → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1}))\cdots ).

In general, for :math:`a_i: A_i`, :math:`0 ≤ i < ℓ`,

.. math:: f a_0 a_1 \dots a_{ℓ-1}: A_ℓ → (A_{ℓ+1} → \cdots → (A_{n-3} → (A_{n-2} → A_{n-1} ) ) \cdots ).

.. Asynchronous currying
.. ~~~~~~~~~~~~~~~~~~~~~

.. It would be useful to have a means of partial function application in case the domain :math:`I` is not simply :math:`\{0, 1, \dots, n-1\}`, or in case we wish to partially apply a function to an arbitrary subset of its operands (coordinates of its domain).

.. Suppose, as above,

.. * :math:`𝔸 = ∏_{i:I} A_i`,

.. * :math:`g: J → I` (one-to-one),

.. * :math:`a ∘ g: ∏_{j:J} A_{g(j)}`, for each :math:`a : ∏_{i:I} A_i`.

.. Let :math:`f` have type :math:`∏_{i:I} A_i → ∏_{i:I} A_i`, which means that if we apply :math:`f` to an element :math:`a : ∏_{i:I} A_i` the result has the same type, that is, :math:`f a : ∏_{i:I} A_i`.

.. We may wish to apply :math:`f` to just a portion of :math:`a` but it may not be the case that :math:`I` is a subset of :math:`ℕ`, or an ordered enumeration of some other set, so there is no natural notion of “the first :math:`ℓ` operands.” Even if there was such a notion, we may wish to partially apply :math:`f` to something other than the first :math:`ℓ` operands. Therefore, we define a more general notion of partial application as follows: :math:`f` partially applied to the coordinates :math:`\im g = \{g(j) ∣ j: J\}` of the element :math:`a` gives the function : type judgment

.. .. math:: f ∘ (a ∘ g): ∏_{\substack{i: I\\ i ∉ \im g}} A_i → ∏_{i:I} A_i.

.. .. todo:: define/describe the asynchronous curry type

------------------------------

.. _tuple-functors:

Tuple functors
--------------

This (and the next) section assumes the reader knows what a functor is (see, e.g., categorytheory.gitlab.io_, for the definition). However, nothing beyond the basic definitions of category theory is required, so readers with no prior exposure to that subject should be able to comprehend all of the concepts we introduce here.

For :math:`m: ℕ`, the :math:`\mathrm{mtuple}` functor on :cat:`Set` is denoted and defined as follows by its action on

+ **objects**: if :math:`A` is a set, then :math:`\mathrm{mtuple}(A) := \{(a_0, \dots, a_{m-1}) ∣ a_i : A\}`;

+ **arrows**: if :math:`f: A → B` is a function from the set :math:`A` to the set :math:`B`, then :math:`\mathrm{mtuple} f: \mathrm{mtuple}(A) → \mathrm{mtuple}(B)` is defined for each :math:`(a_0, \dots, a_{m-1})` of type :math:`\mathrm{mtuple}(A)` as follows:

.. math:: \mathrm{mtuple} f (a_0, \dots, a_{m-1}) = (f a_0, \dots, f a_{m-1}),

which inhabits the type :math:`\mathrm{mtuple}(A)`.

We use the standard set-theoretic convention that identifies the natural number :math:`0≤ m < ω` with the set :math:`\{0,1,\dots, m-1\}`.

Then :math:`a:=(a_0, \dots, a_{m-1})` has type :math:`\mathrm{mtuple}(A)` iff it can be identified with a function of type :math:`m → A`; that is, iff the mtuple :math:`(a_0, \dots, a_{m-1})` is equivalent to the function :math:`a: m → A` defined for each :math:`0 ≤ i < n` by :math:`a(i) = a_i`.

Thus, we have the following equivalence of types: :math:`\mathrm{mtuple}(A) ≅ m \to A`.

Let :math:`m = (m_0, \dots, m_{n-1}): \mathrm{ntuple}(ℕ)`.

The :math:`\mathbf{mtuple}` functor is defined as follows by its action on

+ **objects**: if :math:`A` is a set, then

  .. math:: \mathbf{mtuple}(A) = \{((a_{00}, \dots, a_{0(m_1-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(m_n-1)})) ∣ a_{ij} : A\}.

  (We may write :math:`𝐚_i` in place of :math:`(a_{i0}, \dots, a_{i(k-1)})`, if :math:`k` is clear from context.)

+ **arrows**: if :math:`f` is a function from :math:`A` to :math:`B`, then :math:`\mathbf{mtuple} f :  \mathbf{mtuple}(A) →  \mathbf{mtuple}(B)` is defined for each :math:`(𝐚_0, \dots, 𝐚_{n-1})` in :math:`\mathbf{mtuple}(A)` as follows:

  .. math:: \mathbf{mtuple} f (𝐚_1, \dots, 𝐚_n) &= (\mathrm{m_1tuple}f 𝐚_1, \dots, \mathrm{m_ntuple} f 𝐚_n) \\
                                            &= ((f a_{11}, \dots, f a_{1m_1}), \dots, (f a_{n1}, \dots, f a_{nm_n})).

Notice that :math:`𝐚_i` has type :math:`\mathrm{m_ituple}(A)` iff it can be represented as a function of type :math:`m_i → A`; that is, iff the tuple :math:`(a_{i0}, \dots, a_{i(m_i-1)})` is (the graph of) the function defined by :math:`𝐚_i(j) = a_{ij}` for each :math:`0 ≤ j < m_i`.

Thus, if :math:`m = (m_0, \dots, m_{n-1}): \mathrm{ntuple}(ℕ)`, then :math:`\mathbf{mtuple}(A)` is the :term:`dependent function type`,

.. math:: \prod_{(i:n)} (m_i → A).

-------------------------------------

.. index:: fork, dependent fork, eval

.. _general-composition:

General composition
-------------------

In this section we give a somewhat unconventional presentation of general composition of functions and operations. We feel our presentation is more elegant and concise than those typically found in books on universal algebra.

Of course, to each, his own, particularly when it comes to notational sensibilities.  But aesthetics aside, our main reason for what may seem like a belabored discussion of such an elementary topic is that our definition---via composition of the standard "fork" and "eval" operators familiar to most (functional) programmers---leads to a more natural and efficient implementation of general composition in any functional programming language that supports dependent types.

.. index:: ! fork, ! eval

.. _fork:

fork
~~~~

Recall the definition of :term:`product`.  Given types :math:`A`, :math:`B`, :math:`C`, and functions :math:`f: A → B` and :math:`g: A → C`, there exists a unique function :math:`(f, g): A → B × C` such that :math:`π_1 (f, g) = f` and :math:`π_2 (f, g) = g`.

Evidently, this, the so called universal, mapping is defined for each :math:`a: A` by :math:`(f, g)\, a = (f\,a, g\,a)`.

Denote and define the (nondependent) **fork operator** (on :math:`A`, :math:`B`, and :math:`C`) by

.. math:: \fork: (A → B) → (A → C) → A → (B × C),

and, for each :math:`f: A → B` and :math:`g: A → C`, 

.. math:: \fork \, f\, g: A → (B × C)

is the function that takes each :math:`a:A` to the pair,
  
.. math:: (\fork \, f\, g)\, a = (f\,a, g\,a): B × C.

(Of course, we could have taken the domain of :math:`\fork` to be :math:`(A → B) × (A → C)`, but we prefer the "curried" version defined above for a number of reasons; e.g., it's easier to implement partial application of a curried function.)

The definition of the universal mapping for the product naturally generalizes to arbitrary collections of functions with common domain.  Therefore, it's no surprise that the definition of :math:`\fork` is just a special case of a more general definition that operates on :term:`dependent function types <dependent function type>`, as we now describe.

If :math:`n<ω` and if :math:`f_i: A → B_i` for each :math:`0≤ i < n`, then there exists a unique function of type :math:`A → (B_0 × \cdots × B_{n-1})` whose :math:`k`-th projection is :math:`f_k`.  Precisely, this function is denoted by :math:`(f_0, \dots, f_{n-1})` and defined for each :math:`a:A` by

.. math:: (f_0, \dots, f_{n-1})\, a = (f_0\, a, \dots, f_{n-1}\, a).

More generally still, if :math:`I` is a type and :math:`f: ∏_{(i:I)} (A → B_i)` denotes an :math:`I`-tuple of functions, then we define :math:`\fork f : A → ∏_{(i:I)}B_i` to be the function that takes :math:`a:A` to the :math:`I`-tuple :math:`\fork f \, a`, where :math:`\fork f \, a \, i = f_i\, a`.

.. .. raw:: latex
..    \begin{prooftree}
..    \AXM{\exists x A(x)}
..    \AXM{}
..    \RLM{1}
..    \UIM{A(y)}
..    \noLine
..    \UIM{\vdots}
..    \noLine
..    \UIM{B}
..    \RLM{1}
..    \BIM{B}
..    \end{prooftree}

.. .. include:: latex_images/first_order_logic.8.tex

To generalize in another direction, suppose that :math:`A` is a type and :math:`B: A → \Type` and :math:`C: A → \Type` are such that, for each :math:`a:A`, we have types :math:`B a` and :math:`C a`.

Denote and define the (dependent) **fork operator** by

.. math:: \fork: ∏_{(x:A)} B x → ∏_{(y:A)} C y → ∏_{(a:A)} (B a × C a),

and, for each :math:`f: ∏_{(x:A)} B x` and :math:`g: ∏_{(y:A)} C y`,

.. math:: \fork \, f\, g: ∏_{(a:A)} B a × C a

is the function that maps each :math:`a:A` to the pair

.. math:: (\fork \, f\, g)\, a = (f\,a, g\,a): B a × C a.

(Incidentally, since we opted for a "curried" version of :math:`\fork`, we can partially apply it, obtaining the typing judgment,

.. math:: \fork \, f: ∏_{(a:A)} C a → ∏_{(a:A)} (B a × C a).)

The last two generalizations above may be viewed as special cases of our final definition of :math:`\fork`.

Suppose :math:`I` and :math:`A` are types, and let :math:`B: I → A → \Type` be a **type constructor**; that is, for each :math:`i:I` and :math:`a:A` we obtain a new type by applying :math:`B`, namely, :math:`Bia: \Type`.

Next suppose that for each :math:`i:I` we have a dependent function :math:`f_i: ∏_{(a:A)} B i a` (so the codomain types of :math:`f_i` depend on both :math:`i` and :math:`a`. Let :math:`f: ∏_{(i:I)} ∏_{(a:A)}B i a` be the tuple of these functions; that is, for each :math:`i:I` we have :math:`f\, i = f_i`.

Then, :math:`\fork f` is the function that maps each :math:`a:A` to the function :math:`\fork f \, a` of type :math:`∏_{(i:I)} Bia`.  Thus, for each :math:`a:A` and :math:`i:I`, we have :math:`(\fork f \, a)\, i = f_i\, a`.

To summarize, 

.. math:: \fork: ∏_{(i:I)} ∏_{(a:A)}B i a → ∏_{(a:A)} ∏_{(i:I)} B i a;

so if we have an :math:`I`-tuple :math:`f: ∏_{(i:I)} ∏_{(a:A)}B i a` of dependent functions, then

.. math:: \fork f : ∏_{(a:A)} ∏_{(i:I)} B i a. 

.. _eval:

eval
~~~~

Next, we define a :term:`function application` operation on types :math:`A` and :math:`B`.

Denote and define the **eval operator** by

.. math:: \eval: ((A → B) × A) → B

and for each :math:`f: A → B`, :math:`\eval \, f` is the function that maps each :math:`a: A` to :math:`f\, a:B`. 

Notice that :math:`\eval` is polymorphic as it depends on the types :math:`A` and :math:`B`. Indeed,

.. math:: \eval: \prod_{(A: \mathsf{Type})} \prod_{(B: \mathsf{Type})} ((A → B) × A) → B,

so it would seem that when we introduced the :math:`\eval` operation above, we should have said,

  "...the eval operator *on* :math:`A` *and* :math:`B` is denoted by :math:`\eval \, A \, B: ((A → B) × A) → B`..."
  
However, our implementation of :math:`\eval` will use :term:`implicit arguments <implicit arguments>`, so that :math:`A` and :math:`B` need not be mentioned explicitly.

.. proof:example::

   As an example of function application with dependent types, let :math:`f: ∏_{a:A}(Ca → D)` and :math:`g: ∏_{(a:A)} Ca`. Then for each :math:`a:A` we have :math:`f\,a : Ca → D` and :math:`g\,a: Ca`. Thus, :math:`\eval\, (f\,a, g\,a) = (f\,a)(g\,a): D`.

   We can also specify the types explicitly if desired, as in,

   .. math:: (@ \eval\ Ca \ D) (f\,a, g\,a) = (f\,a)(g\, a).

   As shown here, the :math:`@` symbol indicates that we will explicitly specify all arguments. (`Lean`_ also uses the :math:`@` symbol for this purpose.)

.. proof:example::

   Let us briefly mention a typical use case on which our definition of general composition in :numref:`general-composition-of-operations` will depend. (For more details, see the next section.) In the foregoing descriptions of :math:`\fork` and :math:`\eval`, make the following substitutions:

     * :math:`n = \{0,1,\dots, n-1\}` for :math:`A`, 
  
     * :math:`A` for :math:`D`, and
  
     * :math:`k_i → A` for :math:`Ca`, for each :math:`i:n`.

   Then :math:`g: ∏_{(i:n)} ((k_i → A) → A)` is an :math:`n`-tuple of operations on :math:`A` and :math:`a: ∏_{(i:n)}(k_i → A)` is an :math:`n`-tuple of tuples of elements of type :math:`A`.  Thus,

   .. math:: (\fork \, g \, a)\, i = (g\,i, a\,i): ((k_i → A) → A) × (k_i → A),

   and :math:`\eval \, (\fork \, g\, a) \, i = \eval(g\,i, a\,i) = (g\,i)(a\,i): A`.

.. _general-composition-of-operations:

General composition of operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In universal algebra we mainly deal with *finitary* operations in :cat:`Set` (the category of sets).

By an :math:`n`-**ary operation** on the set :math:`A` we mean a function :math:`f: A^n → A`, that takes an :math:`n`-tuple :math:`(a_0, \dots, a_{n-1})` of elements of type :math:`A` and returns an element :math:`f(a_0,\dots, a_{n-1})` of type :math:`A`. [4]_

If we identify the natural number :math:`n: ℕ` with the set :math:`\{0,1,\dots, n-1\}`, and the :math:`\mathrm{ntuple}` type with function type :math:`n →  A`, then the type of :math:`n`-ary operations on :math:`A` is :math:`(n → A) → A`. Evaluating such an operation :math:`f:(n → A) → A` at the tuple :math:`a: n → A` is simply function application, expressed by the usual rule (sometimes called "implication elimination" or "modus ponens").

.. .. raw:: latex

..   \begin{prooftree}
..   \AxiomC{$f : (n → A) → A$}
..   \AxiomC{$a : n → A$}
..   \RightLabel{$_{(→ \mathrm{E})}$}
..   \BinaryInfC{$f a : A$}
..   \end{prooftree}

Letting :math:`a_i` denote the value of :math:`a` at :math:`i`, and identifying :math:`a` with it's graph (the tuple :math:`(a_0, \dots, a_{n-1})`), we have :math:`f\,a = f(a_0, \dots, a_{n-1})`.

Denote and define the collection of all finitary operations on :math:`A` by

.. math:: \mathrm{Op}(A) = A^{A^n} \cong ⋃_{n<ω} (A^n → A) \cong ⋃_{n<ω} ((n → A) → A).

We now develop a general formulation of composition of operations on sets that is more elegant and computationally practical than the standard formulation, but we first briefly review the standard description of operation composition.

Let :math:`f : (n → A) → A` be an :math:`n`-ary operation and for each :math:`0≤ i < n` let :math:`g_i : (k_i → A) → A` a :math:`k_i`-ary operation on :math:`A`. The **composition of** :math:`f` **with** :math:`(g_0, \dots, g_{n-1})`, denoted :math:`f ∘ (g_0, \dots, g_{n-1})`, is usually expressed as follows: for each

.. math:: ((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})): A^{k_0} × \cdots × A^{k_{n-1}},
   :label: args

.. math:: f & ∘ (g_0, \dots, g_{n-1})((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\
                &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).

This notation is ugly and tedious and lends itself poorly to computation. Let us try to clean it up.

Consider the :math:`n`-tuple :math:`(g_0, \dots, g_{n-1})` of operations from :math:`\mathrm{Op}(A)`.

Let :math:`g: ∏_{(i:n)} ((k_i → A) → A)` be the function with domain the set :math:`n = \{0,1,\dots, n-1\}`, codomain :math:`\mathrm{Op}(A)`, and defined for each :math:`0 ≤ i < n` by :math:`g\,i = g_i`.

Let :math:`a: ∏_{(i:n)} (k_i → A)` be such that for each :math:`0≤ i < n` we have a function :math:`a\,i: k_i → A` which is defined for each :math:`0≤ j < k_i` by :math:`a\,i\,j = a_{ij}`.
  
Then the :math:`n`-tuple of arguments in expression :eq:`args` above can be identified with the :math:`n`-tuple :math:`a = (a\,0, \dots, a\,(n-1))` of functions.

Recalling the definitions of :math:`\fork` (:numref:`fork`) and :math:`\eval` (:numref:`eval`), it is not hard to see how to perform general composition using these definitions and dependent types.

If :math:`g: ∏_{(i:n)} ((k_i → A) → A)` and :math:`a: ∏_{(i:n)}(k_i → A)`, then 

.. math:: \fork \, g\, a: ∏_{(i:n)}\bigl((k_i → A) → A\bigr) \times (k_i → A)

is the function that maps each :math:`0≤ i < n` to the pair

.. math:: (\fork \, g\, a)\, i = (g\,i, a\,i): \bigl((k_i → A) → A\bigr) × (k_i → A).

Applying :math:`g\,i` to :math:`a\,i` with the :math:`\eval` function, we have

.. math:: \eval \, (\fork \, g\, a)\, i = \eval \, (g\,i, a\,i) = (g\,i)(a\,i).

Observe that the codomain :math:`A` of the function :math:`\eval\, (\fork \, g\, a)` does not depend on :math:`i`, so the type :math:`∏_{(i:n)} A` simplifies to :math:`n → A` in this case, resulting in the typing judgment, :math:`\eval \, (\fork \, g\, a): n → A`.

.. On the other hand,

.. .. math:: \eval\,\fork \, g: ∏_{(i:n)}  (k_i → A) → (n → A).

Thus, if

  :math:`f: (n → A) → A` (an :math:`n`-ary operation) and 
  
  :math:`g: ∏_{(i:n)} ((k_i → A) → A)` (an :math:`n`-tuple of operations), then we 
  
  *define* the **composition of** :math:`f` **with** :math:`g` as follows:

.. math:: f ∘ g := f \, \eval \, \fork \, g: ∏_{(i:n)}((k_i → A) → A).

Indeed, if :math:`a: ∏_{(i:n)}(k_i → A)`, then :math:`\eval \, \fork \, g \, a` has type :math:`n → A`, which is the domain type of :math:`f`; therefore, :math:`f\, \eval \, \fork \, g \, a` has type :math:`A`, as desired.

.. _greater-generality:

Greater generality
~~~~~~~~~~~~~~~~~~

In the last section we looked at an operation :math:`f` on a set :math:`A`. We took the domain of :math:`f` to be :math:`n → A` (the type of :math:`n`-tuples over :math:`A`) for some :math:`n`.  In particular, we assumed that :math:`A` was a set, and that the arity of :math:`f` was some natural number, say, :math:`n`. Although this is the standard setup in universal algebra.  However, it is not necessary to be so specific about the arities, domains, and codomains of operations.

In this section we start with two types :math:`α` and :math:`γ` and consider :math:`γ`-**ary operations on** :math:`α`---e.g., :math:`f: (γ → α) → α`---and show how to express composition of operations in this general context.

Suppose that for each :math:`i: γ` we have a type :math:`γ_i` and an operation :math:`g_i` of type :math:`(γ_i → α) → α` on :math:`α`.

Denote by :math:`G` the ":math:`γ`-tuple" of these operations; that is, for each :math:`i: γ` the ":math:`i`-th component" of :math:`G` is 
:math:`G\, i = g_i`. Evidently, this results in the typing judgment,

.. math:: G: ∏_{(i:γ)} ((γ_i → α) → α).

Even in this more general context, we can still use the fork and eval maps introduced above to express composition of operations.
Indeed, we *define* the **composition of** :math:`f` **with** :math:`G` to be

.. math:: f \, \eval \, \fork \, G.

Let us adopt the following convenient notation:

  *Denote by* :math:`∘` *the general composition operation* :math:`\eval \, \fork`.

Then, given :math:`f: (γ → α) → α` and :math:`G: ∏_{(i:γ)} ((γ_i → α) → α)`, the **general composition of** :math:`f` **with** :math:`G` is :math:`f ∘ G := f \, \eval \, \fork \, G`.  Evidently, this yields the typing judgment,

.. math:: f ∘ G : \bigl(∏_{(i:γ)}(γ_i → α)\bigr) → α.

Indeed, if :math:`a: ∏_{(i:γ)}(γ_i → α)`, then for each :math:`i:γ` we have,

.. math:: a\, i : γ_i → α \quad \text{ and } \quad  G\, i : (γ_i → α) → α,

so evaluation of :math:`∘\, G \, a` at a particular :math:`i: γ` is simply function application. That is,

.. math:: ∘\, G \, a \, i:= \eval \, \fork \, G \, a \, i = (G\, i)(a\, i): α.

Thus, :math:`∘\, G \, a` has type :math:`γ → α`, which is precisely the domain type of :math:`f`.

To summarize, we have the following typing judgments:

.. math:: ∘\, G \, a : γ → α \quad \text{ and } \quad f: (γ → α) → α,

whence :math:`f ∘ G \, a: α` is well-typed.

----------------------------

.. index:: inductive type, universes

.. _inductive-types:

Inductive types
-----------------

The chapter on `Inductive Types`_ in :term:`TPIL` gives a nice presentation of this topic. We start our presentation by quoting four key points from the start of that chapter.

#. "Lean's formal foundation includes basic types, ``Prop, Type 0, Type 1, ...``, and allows for the formation of :term:`dependent function types <dependent function type>`, ``Π x : α, β``."

#. "In Lean's library, every concrete type other than the universes and every type constructor other than ``Pi`` is an instance of a general family of type constructions known as *inductive types*."

#. "It is remarkable that it is possible to construct a substantial edifice of mathematics based on nothing more than the type universes, Pi types, and inductive types; everything else follows from those."

#. "Intuitively, an inductive type is built up from a specified list of constructors. In Lean, the syntax for specifying such a type is as follows:

   .. code-block:: text

       inductive foo : Sort u
       | constructor₁ : ... → foo
       | constructor₂ : ... → foo
       ...
       | constructorₙ : ... → foo

   The intuition is that each constructor specifies a way of building new objects of type ``foo``, possibly from previously constructed values. The type ``foo`` consists of nothing more than the objects that are constructed in this way."

In :numref:`Chapter %s <inductively-defined-types>` we will describe the key role played by inductive types in our formalization of universal algebra.

--------------------------------------------

.. rubric:: Footnotes

.. [1]
   What we mean by "intrinsically computational" ought to become clearer as we progress.

.. [2]
   Although, as we note below, like everything in type theory, ``α`` may also be viewed as an inhabitant of a type.

.. [3]
   It is more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1): b_i ∈ B_i, i = 0, 1\}`, but identifying tuples with functions results in a :term:`Pi type`.

.. [4]
   Using the tuple constructor described in :numref:`tuple-functors`, we could also represent such an operation as :math:`f: \mathrm{ntuple} A → A`. However,  we wish to postpone taking this viewpoint until we have some experience with categories and functors.

.. [5]
   In retrospect, a more appropriate name for :math:`\mathbf{0} σ` might be :math:`Δ_σ`, or even :math:`=_σ`, but this may lead to conflicts with more standard notational conventions.

.. include:: hyperlink_references.rst

