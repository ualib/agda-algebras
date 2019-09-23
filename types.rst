.. role:: cat

.. include:: _static/math_macros.rst

.. _types:

=====
Types
=====

This section presents some of the rudiments of :term:`type theory`.  For more details, a nice and gentle introduction to the basics of both (type theory and the `Lean`_ :term:`proof assistant`) is the textbook `Logic and Proof`_, by Avigad, et al.

A more comprehensive (yet still gentle) treatment is *Foundations for Programming Languages* by Mitchell :cite:`Mitchell:1996`. More advanced treatments are found in the book *Type Theory and Formal Proof* by Geuvers and Nederpelt :cite:`Nederpelt:2014`, as well as "The HoTT Book" :cite:`HoTT:2013` (authored by two dozen participants of the Univalent Foundations Program held in 2013 at the IAS in Princeton).

-----------------------------

.. _curry-howard:

Curry-Howard correspondence
----------------------------

The rule for *function application* corresponds, under the “Curry-Howard” or “propositions-as-types” correspondence, to the *implication elimination* rule of natural deduction (sometimes called *modus ponens*).

This simply codifies our intuitive notion of function application, viz., applying the function :math:`f: A → B` to an inhabitant :math:`a` of the domain :math:`A`, we obtain an element :math:`f\,a` of the codomain :math:`B`.

If we interpret the types :math:`A` and :math:`B` as propositions, the function :math:`f: A → B` as a proof of the proposition ":math:`A` implies :math:`B`," and if :math:`a` is a proof of :math:`A`, then the application rule is the so called *implication elimination* rule (or, *modus ponens*); that is, "if :math:`A → B` and :math:`A`, then :math:`B`."

---------------------------------------

.. index:: dependent types 

.. _dependent-types:

Dependent types
---------------

`Lean`_ is a functional programming language that supports :term:`dependent types <dependent type>`.

In the present section we will present an example that demonstrates how dependent types can be used to representation of many concepts that are important in universal algebra in a more precise and elegant way. Besides being more precise and elegant, the representation we present is intrinsically computational. [1]_ 

Before the example, however, let us first briefly mention what it is that makes a type *dependent*, and why :term:`dependent types <dependent type>` are so useful.

Types can depend on *parameter values*.  For example, the type ``list α`` (lists with elements from ``α``) depends on the argument ``α`` and the type ``vec α n`` (vectors of length ``n`` with entries from ``α``) depends on ``α:Type`` (the type of the elements that populate the vectors) and ``n:ℕ`` (the length of the vectors).

The first, ``list α``, is an example of a :term:`polymorphic type`, which is not usually considered a "dependent type."  One could argue that the type ``list α`` *depends* on the argument ``α``; for example, this dependence distinguishes ``list ℕ`` from ``list bool``.  However, since the dependence is on the argument ``α``, which denotes denotes a type, rather than a particular *value* (or *inhabitant*) of a type, this dependence is referred to as **polymorphism**.

Contrast this with the example in the previous paragraph, where the type ``vec α n`` depends on the *value* of the variable ``n`` (which is an *inhabitant* of the type ℕ). This is the sort of dependence for which we reserve the moniker "dependent type."

Suppose we wish to write a function ``cons`` that inserts a new element at the head of a list. What type should ``cons`` have? Such a function is polymorphic: we expect the ``cons`` function for ℕ, ``bool``, or an arbitrary type ``α`` to behave in roughly the same way, so it makes sense to take the type to be the first argument to ``cons``. Thus, for any type ``α``, ``cons α`` is the insertion function for lists of type ``α``. In other words, for every ``α``, ``cons α`` is the function that takes an element ``a:α`` and a list ``l:list α``, and returns a new list---the concatenation of the single element list ``(a)`` with the list ``l``---so that ``con α a l`` is again of type ``list α``.

Evidently, ``cons α`` has type ``α → list α → list α``. But what type should ``cons`` have?  Certainly not ``Type → α → list α → list α`` since the ``α``  appears as if from nowhere, while it should refer to an argument of type ``Type``, 

To put it another way, we first assume that a specific (arbitrary) ``α:Type`` is the first argument to the function, and consequently the type of the next two elements are ``α`` and ``list α``. This is an instance of a :term:`Pi type`, or :term:`dependent function type <Pi type>`. Given ``α:Type`` and ``β:α → Type``, think of ``β`` as a family of types, one type ``β a`` for each ``a:α``.

In this case, the type ``Π(a:α),β x`` denotes the type of functions ``f`` with the property that ``f a`` is an element of ``β a``, for each ``a:α``. In other words, the type of the value returned by ``f`` *depends* on its input.

Notice that ``Π(a:α),β`` makes sense for any expression ``β:Type``. When the value of ``β`` depends on ``a`` (as does ``β a`` in the previous paragraph), ``Π(a:α),β`` denotes a dependent function type.

If, on the other hand, ``β`` does not depend on ``a``, then ``Π(a:α),β`` is no different from the type ``α → β``. Indeed, in dependent type theory (and in Lean_), the Pi construction is fundamental, and ``α → β`` is simply notation for ``Π(a:α),β`` for the special case in which ``β`` does not depend on ``a``.

.. index:: type of; dependent functions (Pi type)

To summarize, the :term:`Pi type` :math:`\Pi_{(a:A)}, B a` generalizes the function type :math:`A → B` by allowing the codomain :math:`B a` to depend on the *value* :math:`a: A` (the function's "input").

The simplest example of a Pi type is the Cartesian product :math:`B_0 × B_1` which, when viewed as the collection of functions that map :math:`i ∈ \{0, 1\}` to some element of :math:`B_i`, is the type :math:`\Pi_{(i:\mathsf{bool})}, B_i`. [1]_

.. index:: type of; dependent pairs

Similarly, the :term:`Sigma type` :math:`\sum_{(x:A)}, B x`, also known as the `dependent pair type <sigma-type>`_, generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second argument of the ordered pair to depend on the value :math:`x` of the first.

The simplest example of a Sigma type is the disjoint union :math:`B_0 \coprod B_1` which may be viewed as a collection of ordered pairs :math:`(i, b_i)`, where the first coordinate indicates to which set the second element belongs.  For example, if the two sets are :math:`B_0 = \{a, b\}` and :math:`B_1 = \{a, b, c\}` we form the disjoint union of :math:`B_0` and :math:`B_1` as follows:

.. math:: B_0 + B_1 = \{(0,a), (0,b), (1,a), (1,b), (1,c)\}.

Alternatively, some authors prefer to use an injection function to indicate the set from which an element originated.  For example, if we choose to denote the injective function by :math:`ι: \{0, 1\} → \{a, b\} ∐ \{a, b, c\}`, then we could represent the coproduct in the example above as follows:

.. math:: B_0 + B_1 = \{ι_0 a,\, ι_0 b,\, ι_1 a,\, ι_1 b,\, ι_1 c\}.

(The symbol ι is produced by typing ``\iota``; see :numref:`symbol-commands`.)

-----------------------------------------------

.. index:: ! projection operator, ! idempotent operation

.. _projection-operators:

Projection operators
--------------------

An operation :math:`f: A^n → A` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`.

Examples of idempotent operations are the projection functions and these play an important role, so we introduce a sufficiently general and flexible notation for them.

Denote and define the set ℕ of natural numbers inductively, as usual;

.. math:: 0 = ∅, \quad 1 = \{0\}, \quad  2 := \{0, 1\}, \dots, n = \{0, 1, \dots, n-1\}.

Let :math:`\{A_i: i ∈ I\}` be a collection of sets (for some :math:`I ⊆ ℕ`) and let :math:`\underline{A} = ∏_{i ∈ I} A_i`. View the elements of :math:`\underline{A}` as functions:

.. math:: a ∈ ∏_{i∈I} A_i \quad ⟷ \quad \begin{cases} a : I → ⋃_{i∈I} A_i, & \\ a\,i ∈ A_i, & ∀ i ∈ I. \end{cases}
   :label: 7
   
This correspondence simply records the fact that the product type (on the left of the ⟷ symbol) represents a special kind of function type (depicted on the right of ⟷ using the usual arrow notation for function types). In other words, :eq:`7` says that an element of the product type :math:`∏_{i∈I} A_i` is a function from :math:`I` into :math:`⋃_{i∈I} A_i` whose codomain :math:`A_i` *depends* on the input argument :math:`i`. Such a function (or product) type is known as a :term:`dependent type`.

Now, given a subset :math:`J ⊆ I`, a function :math:`σ: J → I`, and an element :math:`a ∈ ∏_{i∈I} A_i`, consider the composition :math:`a ∘ σ`. This is a function from :math:`J` to :math:`⋃_{j∈J} A_{σ\, j}`, where :math:`(a ∘ σ)\, j ∈ A_{σ\, j}`.

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

.. proof:example::

   To see why the term "projection" is reserved for the case when :math:`σ` is one-to-one, suppose :math:`k=4`, :math:`n=3`, and consider the 4-tuple :math:`σ = (1, 0, 1, 1)`. Then :math:`σ` is the function :math:`σ : \{0,1,2,3\} → \{0,1,2\}` given by :math:`σ(0) = 1`, :math:`σ(1) = 0`, :math:`σ(2) = 1`, :math:`σ(3) = 1`, and so :math:`a ↦ a ∘ σ` is the function that takes :math:`(a_0, a_1, a_2)∈ A_0 × A_1 × A_2` to :math:`(a_1, a_0, a_1, a_1) ∈ A_1 × A_0 × A_1 × A_1`. [2]_

Let :math:`A = ∏_{i<n} A_i`, let :math:`σ : k → n` be one-to-one, and define the projection :math:`\Proj_σ` as in :eq:`projection` above. Then the :term:`kernel` of :math:`\Proj_σ`, which we denote by :math:`\mathbf{0}_σ`, is denoted and defined by

.. math:: \mathbf{0}_σ &= \ker \Proj_σ = \{(a,a') ∈ A^2 | \Proj_σ a = \Proj_σ a'\}\\
                       &= \{ (a,a') ∈ A^2 | a ∘ σ = a' ∘ g \} = \{ (a,a') ∈ A^2 | ∀ j ∈ \im σ, \ a(j) = a'(j) \}.
   :label: kernel

It is obvious that :math:`\mathbf{0}_σ` is an equivalence relation on the set :math:`A`.

More generally, if :math:`θ` is an equivalence relation on the set :math:`∏_{j<k} A_{σ(j)}`---that is, :math:`θ ⊆ (∏_{j<k} A_{σ(j)})^2` and :math:`θ` is reflexive, symmetric, and transitive---then we define the equivalence relation :math:`θ_σ` on the set :math:`A = ∏_{i<n} A_i` as follows:

.. math:: θ_σ = \{(a, a') ∈ A^2 ∣ (a ∘ σ) \mathrel{\theta} (a' ∘ σ)\}.
   :label: 17

In other words, :math:`θ_σ` consists of all pairs in :math:`A^2` that land in :math:`θ` when projected onto the coordinates in :math:`\im σ`.

#. Recall that :math:`\Proj_σ : A → ∏_{j<k} A_{σ(j)}` is the function that maps :math:`a` to :math:`a ∘ σ`.

   Now, suppose we have a tuple :math:`(a_0, a_1, \dots, a_{p-1})\in A^p`, and suppose we intend to apply :math:`\Proj_σ` to each component, :math:`a_j`.

   To do so, we need to lift :math:`\Proj_σ` from type :math:`A → ∏_{j<k} A_{σ(j)}` to type :math:`A^p → (∏_{j<k} A_{σ(j)})^p`, which is accomplished using a functor that often goes by the name :math:`map`.

   For instance, if :math:`(a, a') ∈ A^2`, then :math:`map(\Proj_σ)(a, a') = (\Proj_σ(a), \Proj_σ(a'))`.

   Therefore,

   .. math:: θ_σ =\{(a, a') ∈ A^2 ∣ map(\Proj_σ)(a, a') ∈ θ \},

   whence, :math:`θ_g = map(\Proj_σ)^{-1}θ`.

#. If :math:`f: X → A` and :math:`g: X → B` are functions defined  on the same domain :math:`X`, then :math:`(f,g): X → A × B` is the unique function that composes with the first projection to give :math:`f` and composes with the second projection to give :math:`g`. For example, in the last remark there appears the expression :math:`(\Proj_σ(a), \Proj_σ(a')) = (a ∘ σ, a' ∘ σ)`, which has type :math:`( ∏_{j<k} A_{σ(j)} )^2`.

    In retrospect, a more appropriate name for :math:`\mathbf{0}_σ` might be :math:`Δ_σ`, or even :math:`=_σ`.

#. If the domain of :math:`σ` is a singleton, :math:`k = \{0\}`, then of course :math:`σ` is just a one-element list, say, :math:`σ = (j)`. In such cases, we write :math:`\Proj_j` instead of :math:`\Proj_{(j)}`.  Similarly, we write and :math:`\mathbf{0}_j` and :math:`θ_j` instead of :math:`\mathbf{0}_{(j)}` and :math:`θ_{(j)}`. Thus, :math:`\Proj_j a = a(j)`, and :math:`\mathbf{0}_j = \{(a, a') ∈ A^2 ∣ a(j) = a'(j)\}`, and, if :math:`θ ∈ \Con 𝔸_j`, then :math:`θ_j = \{(a, a') ∈ A^2 ∣ a(j) \mathrel{\theta} a'(j)\}`.

Here are some obvious consequences of the foregoing notation and definitions that are worth noting.

.. math::

   ⋁_{j<n}\mathbf{0}_j = A^2, \qquad \mathbf{0}_σ = ⋀_{j ∈ σ} \mathbf{0}_j, \qquad \mathbf{0}_{n} = ⋀_{j<n}\mathbf{0}_j = 0_{A}, \qquad
   θ_σ = ⋀_{j<k} θ_{σ(j)},

where :math:`0_{A}` denotes the least equivalence relation on :math:`A`, that is, :math:`0_{A}:= \{(a, a') ∈ A^2 ∣ a = a'\}`.

.. As we alluded to above, :math:`η_σ` is shorthand for :math:`(0_A)_σ`.

--------------------------------

.. _kernels-of-projections:

.. index:: projection kernel

Kernels of projections
----------------------

Let :math:`𝔸 = ∏_{(i:I)} 𝔸_i` be a product of algebras with the same :term:`signature`, and suppose :math:`g: J → I` is a one-to-one function, where :math:`∅ ≠ J ⊆ I ⊆ ℕ`.

Define the **kernel of the projection of** :math:`𝔸` **onto** :math:`∏_{(j:J)} A_{g(j)}` as follows:

.. math:: Δ_g = \{(a,a'): 𝔸^2 | a ∘ g = a' ∘ g \} = \ker (\Proj g)

This is a congruence of :math:`𝔸`. More generally, if :math:`θ` is a congruence of :math:`∏_{(j:J)} A_{g(j)}`, define :math:`θ_g: \Con 𝔸` as follows:

.. math:: θ_g = (\Proj g)^{-1}(θ) =  \{ (a, a') : 𝔸^2 | (a ∘ g) \mathrel{\theta} (a' ∘ g) \}.

This indicates the origin of the notation :math:`Δ_g`, where :math:`Δ` denotes the trivial (identity) relation on :math:`∏_{(j:J)} A_{g(j)}`. If :math:`J = \{0\}` and
:math:`g:I` is just a constant, say, :math:`g(0) = k`,
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

Asynchronous currying
~~~~~~~~~~~~~~~~~~~~~

It would be useful to have a means of partial function application in case the domain :math:`I` is not simply :math:`\{0, 1, \dots, n-1\}`, or in case we wish to partially apply a function to an arbitrary subset of its operands (coordinates of its domain).

Suppose, as above,

+ :math:`\underline{𝔸} = ∏_{i:I} A_i`,

+ :math:`g: J → I` (one-to-one),

+ :math:`a ∘ g: ∏_{j:J} A_{g(j)}`, for each :math:`a : ∏_{i:I} A_i`.

Let :math:`f` have type :math:`∏_{i:I} A_i → ∏_{i:I} A_i`, which means that if we apply :math:`f` to an element :math:`a : ∏_{i:I} A_i` the result has the same type, that is, :math:`f a : ∏_{i:I} A_i`.

We may wish to apply :math:`f` to just a portion of :math:`a` but it may not be the case that :math:`I` is a subset of :math:`ℕ`, or an ordered enumeration of some other set, so there is no natural notion of “the first :math:`ℓ` operands.” Even if there was such a notion, we may wish to partially apply :math:`f` to something other than the first :math:`ℓ` operands. Therefore, we define a more general notion of partial application as follows: :math:`f` partially applied to the coordinates :math:`\im g = \{g(j) ∣ j: J\}` of the element :math:`a` gives the function : type judgment

.. math:: f ∘ (a ∘ g): ∏_{\substack{i: I\\ i ∉ \im g}} A_i → ∏_{i:I} A_i.

.. todo:: define/describe the asynchronous curry type

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

In this section we give a modern, perhaps unconventional presentation of general composition of functions and operations. We feel our presentation is more elegant and concise than those typically found in books on universal algebra.

Of course, to each, his own, particularly when it comes to notational sensibilities.  But aesthetics aside, our main reason for what may seem like a belabored discussion of such an elementary topic is that our definition---via composition of the standard "fork" and "eval" operators familiar to every seasoned (functional) programmer---leads to a more natural and efficient implementation of general composition in any functional programming language that supports dependent types.

.. index:: ! fork, ! eval

.. _fork-and-eval:

fork and eval
~~~~~~~~~~~~~

We begin by defining the "fork" and "eval" operators mentioned in the opening paragraph of this section.

Recall the definition of :term:`product`.  Given types :math:`A`, :math:`B`, :math:`C`, and functions :math:`f: A → B` and :math:`g: A → C`, there exists a unique function :math:`⟨f, g⟩: A → B × C` such that :math:`π_1 ⟨f, g⟩ = f` and :math:`π_2 ⟨f, g⟩ = g`.  Evidently, this function is defined for each :math:`a: A` by :math:`⟨f, g⟩(a) = (f\,a, g\,a): B × C`.

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

Denote and define the (nondependent) **fork operator** (on :math:`A`, :math:`B`, and :math:`C`) by

.. math:: \fork: (A → B) → (A → C) → A → (B × C),

and, for each :math:`f: A → B` and :math:`g: A → C`, 

.. math:: \fork \, f\, g: A → (B × C)

is the function that takes each :math:`a:A` to the pair,
  
.. math:: \fork \, f\, g\, a = (f\,a, g\,a): B × C.

(Alternatively, we could have taken the domain of :math:`\fork` to be :math:`(A → B) × (A → C)`, but we prefer the "curried" version defined above for a number of reasons; e.g., it's easier to implement partial application of a curried function.)

The above definition of :math:`\fork` is really just a special case of a more general definition that operates on :term:`dependent function types <dependent function type>`, as we now describe.

Let :math:`A` be a type and for each :math:`a: A` let :math:`B_a` and :math:`C_a` be types.

Denote and define the (dependent) **fork operator** by

.. math:: \fork: ∏_{(a:A)} B_a → ∏_{(a:A)} C_a → ∏_{(a:A)} (B_a × C_a),

and, for each :math:`f: ∏_{(a:A)} B_a` and :math:`g: ∏_{(a:A)} C_a`,

.. math:: \fork \, f\, g: ∏_{(a:A)} B_a × C_a

is the function that maps each :math:`a:A` to the pair

.. math:: \fork \, f\, g\, a = (f\,a, g\,a): B_a × C_a.

Since our definition of :math:`\fork` is presented in curried form, we can partially apply it to obtain the typing judgment,

.. math:: \fork \, f: ∏_{(a:A)} C_a → ∏_{(a:A)} (B_a × C_a).

Next, we define a :term:`function application` operation on types :math:`A` and :math:`B`.

Denote and define the **eval operator** by

.. math:: \eval: ((A → B) × A) → B

and for each :math:`f: A → B` and :math:`a: A`, :math:`\eval \, f` is the function that maps each :math:`a: A` to :math:`f\, a:B`. 

Notice that :math:`\eval` is polymorphic as it depends on the types :math:`A` and :math:`B`. Indeed,

.. math:: \eval: \prod_{(A: \mathsf{Type})} \prod_{(B: \mathsf{Type})} ((A → B) × A) → B,

so it would seem that when we introduced the :math:`\eval` operation above, we should have said,

  "...the eval operator *on* :math:`A` *and* :math:`B` is denoted by :math:`\eval \, A \, B: ((A → B) × A) → B`..."
  
However, our implementation of :math:`\eval` will use implicit types, so :math:`A` and :math:`B` need not be mentioned explicitly.

As an example of function application, let :math:`f: ∏_{a:A}(C_a → D)` and :math:`g: ∏_{(a:A)} C_a` and :math:`a: A`. Then,

  :math:`f\,a : C_a → D` and :math:`g\,a: C_a` and 

.. math:: \eval \, (f\,a) \, (g\,a) = (f\,a)(g\,a): D.

We could also have specified the types explicitly. For this purpose, we adopt the :math:`@` symbol, which is used by `Lean`_ for this purpose.

.. math:: (@ \eval\, C_a \, D)\,  (f\,a)\, (g\,a) = (f\,a)(g\, a): D.

Let us briefly mention a typical use case on which our definition of general composition in :numref:`general-composition-of-operations` will depend. In the foregoing, substitute

  * :math:`n = \{0,1,\dots, n-1\}` for :math:`A`, 
  
  * :math:`A` for :math:`D`, and
  
  * :math:`k_i → A` for :math:`C_a`, for each :math:`i:n`.

Then :math:`g: ∏_{(i:n)} ((k_i → A) → A)` is an :math:`n`-tuple of operations on :math:`A` and :math:`a: ∏_{(i:n)}(k_i → A)` is an :math:`n`-tuple of tuples of elements of type :math:`A`.  Thus,

.. math:: \fork  (g) (a) (i) = (g\,i, a\,i): ((k_i → A) → A) × (k_i → A),

and :math:`\eval \, \fork \, g\, a\, i = \eval(g\,i, a\,i) = (g\,i)(a\,i): A`.

.. _general-composition-of-operations:

General composition of operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In universal algebra we mainly deal with *finitary* operations in :cat:`Set` (the category of sets).

By an :math:`n`-**ary operation** on the set :math:`A` we mean a function :math:`f: A^n → A`, that takes an :math:`n`-tuple :math:`(a_0, \dots, a_{n-1})` of elements of type :math:`A` and returns an element :math:`f(a_0,\dots, a_{n-1})` of type :math:`A`. [3]_

If we identify the natural number :math:`n ∈ ℕ` with the set :math:`\{0,1,\dots, n-1\}`, and the :math:`\mathrm{ntuple}` type with function type :math:`n →  A`, then the type of :math:`n`-ary operations on :math:`A` is :math:`(n → A) → A`. Evaluating such an operation :math:`f:(n → A) → A` at the tuple :math:`a: n → A` is simply function application, expressed by the usual rule (sometimes called "implication elimination" or "modus ponens").

.. raw:: latex

  \begin{prooftree}
  \AxiomC{$f : (\underline n → A) → A$}
  \AxiomC{$a : \underline n → A$}
  \RightLabel{$_{(→ \mathrm{E})}$}
  \BinaryInfC{$f a : A$}
  \end{prooftree}

Letting :math:`a_i` denote the value of :math:`a` at :math:`i`, and identifying :math:`a` with it's graph (the tuple :math:`(a_0, \dots, a_{n-1})`), we have :math:`f\,a = f(a_0, \dots, a_{n-1})`.

Denote and define the collection of all finitary operations on :math:`A` by

.. math:: \mathrm{Op}(A) = ⋃_{n<ω} (A^n → A)\cong ⋃_{n<ω} ((n → A) → A).

We now develop a general formulation of :term:`composition of operations` on sets that is more elegant and computationally practical than the standard formulation, but first, let us briefly review the standard formulation.

Let :math:`f : (n → A) → A` be an :math:`n`-ary operation, and :math:`g_i : (k_i → A) → A` a :math:`k_i`-ary operation on :math:`A`, for each :math:`0≤ i < n`. Define the **composition of** :math:`f` **with** :math:`(g_0, \dots, g_{n-1})`, denoted by :math:`f [g_0, \dots, g_{n-1}]`, in the following standard way: for each

.. math:: ((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})): A^{k_0} × \cdots × A^{k_{n-1}},
   :label: args

.. math:: f & [g_0, \dots, g_{n-1}]((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\
                &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).

This notation is ugly and tedious, and it lends itself poorly to computation. We now show how it can be vastly improved.

Consider the :math:`n`-tuple :math:`(g_0, \dots, g_{n-1})` of operations from :math:`\mathrm{Op}(A)`.

Let :math:`g: ∏_{(i:n)} ((k_i → A) → A)` be the function with domain the set :math:`n = \{0,1,\dots, n-1\}`, codomain :math:`\mathrm{Op}(A)`, and defined for each :math:`0 ≤ i < n` by :math:`g\,i = g_i`.

Let :math:`a: ∏_{(i:n)} (k_i → A)` be the function defined for each :math:`0≤ i < n` by :math:`a\,i: k_i → A`, and for each :math:`j: k_i`, by :math:`a\,i\,j = a_{ij}: A`.
  
Then the :math:`n`-tuple of arguments in expression :eq:`args` above can be identified with the :math:`n`-tuple :math:`a = (a\,0, \dots, a\,(n-1))` of functions.

Recalling the definitions of :math:`\fork ` and :math:`\eval` (:numref:`fork-and-eval`), it is not hard to see how to perform general composition using these definitions and dependent types.

If :math:`g: ∏_{(i:n)} ((k_i → A) → A)` and :math:`a: ∏_{(i:n)}(k_i → A)`, then 

.. math:: \fork \, g\, a: ∏_{(i:n)}\bigl((k_i → A) → A) \times (k_i → A)\bigr)

is the function that maps each :math:`i:n` to the pair

.. math:: (g\,i, a\,i): (k_i → A) → A) × (k_i → A).

Applying :math:`g\,i` to :math:`a\,i` with the :math:`\eval` function, we have

.. math:: \eval \, \fork \, g\, a\, i = \eval (g\,i, a\,i) = (g\,i)(a\,i): A.

Observe that the codomain :math:`A` of the function :math:`\eval \, \fork \, g\, a` does not depend on :math:`i`, so the type :math:`∏_{(i:n)} A` simplifies to :math:`n → A` in this case, resulting in the typing judgment, :math:`\eval \, \fork \, g\, a: n → A`.

.. On the other hand,

.. .. math:: \eval\,\fork \, g: ∏_{(i:n)}  (k_i → A) → (n → A).

Thus, if

  :math:`f: (n → A) → A` (an :math:`n`-ary operation) and 
  
  :math:`g: ∏_{(i:n)} ((k_i → A) → A)` (an :math:`n`-tuple of operations), then we 
  
  *define* the **composition of** :math:`f` **with** :math:`g` as follows:

.. math:: f [g] := f \, \eval \, \fork \, g: ∏_{(i:n)}((k_i → A) → A).

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
   What we mean by "intrinsically computational" ought to become clearer as one progresses through this documentation.

.. [2]
   It is more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1): b_i ∈ B_i, i = 0, 1\}`, but identifying tuples with functions results in a :term:`Pi type`.

.. [3]
   Using the tuple constructor described in :numref:`tuple-functors`, we could also represent such an operation as :math:`f: \mathrm{ntuple} A → A`. However,  we wish to postpone taking this viewpoint until we have some experience with categories and functors.

.. include:: hyperlink_references.rst

