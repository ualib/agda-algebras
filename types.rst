.. include:: _static/math_macros.rst

.. role:: cat

.. _types:

=====
Types
=====

This section presents little more of the rudiments of :term:`type theory` than we will need for formalizing universal algebra in the `Lean`_ :term:`proof assistant`.  For more details, a very nice and gentle introduction to type theory and Lean is the textbook `Logic and Proof`_, by Avigad, et al.

A more comprehensive yet still gentle treatment is *Foundations for Programming Languages* by Mitchell :cite:`Mitchell:1996`. More advanced books on this topic are *Type Theory and Formal Proof* by Geuvers and Nederpelt :cite:`Nederpelt:2014` and *Homotopy Type Theory: Univalent Foundations of Mathematics* (aka "The HoTT Book") :cite:`HoTT:2013` by roughly two dozen participants of the Univalent Foundations Program held in 2013 at the IAS in Princeton.

We begin with a slogan that may be helpful to those who know about sets but have no prior exposure to type theory.

  *In set theory virtually everything* **is** *a set, in type theory, everything* **has** *a type*.

.. todo:: maybe add some basic background on types here

----------------------------------

.. index:: pair: implication elimination; modus ponens

.. _curry-howard:

Curry-Howard correspondence
----------------------------

The rule for :term:`function application` corresponds, under the :term:`Curry-Howard <Curry-Howard correspondence>` (or :term:`propositions-as-types`/:term:`proofs-as-programs`) :term:`correspondence <Curry-Howard correspondence>`, to the :term:`implication elimination` rule of natural deduction (sometimes called :term:`modus ponens`). This simply codifies our intuitive notion of function application, viz., applying the function :math:`f: A → B` to an element :math:`a` of :math:`A` yields a member :math:`f\,a` of the codomain :math:`B`.

If we interpret the types :math:`A` and :math:`B` as propositions and the function :math:`f: A → B` as a proof of the proposition ":math:`A` implies :math:`B`," and if we view :math:`a` as a proof of :math:`A`, then the application rule is the so called :term:`implication elimination` rule (or, :term:`modus ponens`); that is, "if :math:`A → B` and :math:`A`, then :math:`B`."

---------------------------------------

.. index:: type of; dependent functions
.. index:: type of; dependent pairs
.. index:: type of; lists
.. index:: type of; vectors

.. _dependent-types:

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

.. math:: ∏_{(i:n)} (m_i → A).

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

.. math:: \fork: ∏_{(i:I)} ∏_{(a:A)}B i a →∏_{(a:A)} ∏_{(i:I)} B i a;

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

.. math:: \eval: ∏_{(A: \mathsf{Type})} ∏_{(B: \mathsf{Type})} ((A → B) × A) → B,

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
  
  denote and define the **composition of** :math:`f` **with** :math:`g` as follows:

.. math:: f \comp g := f \, \eval \, \fork \, g: ∏_{(i:n)}((k_i → A) → A).

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

  *Denote by* :math:`\comp` *the general composition operation* :math:`\eval \, \fork`.

Then, given :math:`f: (γ → α) → α` and :math:`G: ∏_{(i:γ)} ((γ_i → α) → α)`, the **general composition of** :math:`f` **with** :math:`G` is :math:`f \comp G := f \, \eval \, \fork \, G`.  Evidently, this yields the typing judgment,

.. math:: f \comp G : \bigl(∏_{(i:γ)}(γ_i → α)\bigr) → α.

Indeed, if :math:`a: ∏_{(i:γ)}(γ_i → α)`, then for each :math:`i:γ` we have,

.. math:: a\, i : γ_i → α \quad \text{ and } \quad  G\, i : (γ_i → α) → α,

so evaluation of :math:`\comp\, G \, a` at a particular :math:`i: γ` is simply function application. That is,

.. math:: \comp \,G \, a \, i:= \eval \, \fork \, G \, a \, i = (G\, i)(a\, i): α.

Thus, :math:`\comp\, G \, a` has type :math:`γ → α`, which is precisely the domain type of :math:`f`.

To summarize, we have the following typing judgments:

.. math:: \comp\, G \, a : γ → α \quad \text{ and } \quad f: (γ → α) → α,

whence :math:`f \comp G \, a: α` is well-typed.

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

.. index:: equivalence class, ! quotient
.. index:: type of; quotients

.. _quotient-types:

Quotient types
---------------

In this section we define *quotients*, first as sets and then as types.  We define a *quotient type* and describe how to implement and make use of such a type in Lean.

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

Let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.

Define the **quotient** :math:`α/R` (read, "alpha modulo :math:`R`") to be the collection of :math:`R`-classes in :math:`α`. That is, for each :math:`x:α`, there is a class :math:`x/R ⊆ α` consisting of all :math:`y:α` such that :math:`x \mathrel R y`, that is,

.. math:: x/R = \{y : α ∣  x \mathrel R y\}.

The type of the class :math:`x/R` is a **quotient type**, denoted in this case by :math:`α/R`.

.. index:: keyword: quot, quot.mk, quot.ind

.. _quotients-in-lean:

Quotients in Lean
~~~~~~~~~~~~~~~~~~

Four quotient types are defined as constants in the :term:`LSTL`.  For consistency, we have decided to redefine these types in the `lean-ualib`_, as follows: [6]

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

-------------------

.. index:: ! lift of; a function

.. _lifts:

Lifts
------

Throughout this section, let :math:`α` be a type and :math:`R` a binary relation on :math:`α`.

.. _lift-of-a-function:

Lift of a function
~~~~~~~~~~~~~~~~~~~

Let :math:`f: α → β` be a function. We say that :math:`f` **lifts** from :math:`α` to :math:`α/R` provided the implication

.. math:: (x, y) ∈ R \ → \ f x = f y
   :label: lift

holds for all :math:`x` and :math:`y` of type :math:`α`.

Evidently, implication :eq:`lift` holds iff :math:`R` is contained in the **kernel** of :math:`f`; that is,

.. math:: R ⊆ \ker f := \{(x, y) ∈ α × α ∣ f x = f y\}.

Let :math:`f[R] := \{(f x, f y) ∈ β × β ∣ (x, y) ∈ R\}` and let :math:`0_α := \{(x, y) ∈ α × α ∣ x = y\}` be the identity relation on :math:`α`. Then :math:`f` :term:`lifts <lifts (v)>` from :math:`α` to :math:`α/R` if and only if :math:`f[R] ⊆ 0_α` if and only if :math:`R ⊆ \ker f`.

If :math:`f` :term:`lifts <lifts (v)>` from :math:`α` to :math:`α/R`, then there is a function :math:`fₗ : α/R → β` defined by :math:`fₗ (x/R) = f x`, for each :math:`x/R: α/R`. We call this function the :term:`lift <lift (n)>` of :math:`f` from :math:`α` to :math:`α/R`.

The `Lean Standard Library`_ (:term:`LSTL`) extends the :term:`CiC` with additional constants that construct such lifts, and make the equation :math:`fₗ(x/R) = f x` available as a definitional reduction rule. [5]_

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

.. index:: pair: respect; preserve
.. index:: ! quotient tuple
.. index:: ! lift of; a tuple
.. index:: ! lift of; an operation

.. _respectsing-relations:

Respecting relations
~~~~~~~~~~~~~~~~~~~~

The last subsection explained the quotient construction that is built into Lean and that is useful for lifting a function :math:`f: α → β` to a function :math:`f': α/R → β` for some relation :math:`R ⊆ α × α` "respected" by :math:`f` (in the sense denoted above by ``f ⫢ R``).  In this section, we generalize this lifting construction to a lift that is more common in universal algebra.  Namely, we wish to take an operation of type :math:`(β → α) → α` and lift it to an operation of type :math:`(β → α/R) → α/R`.

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

.. _lift-of-an-operation:

Lift of an operation
~~~~~~~~~~~~~~~~~~~~~

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

.. _computation-principles:

Computation principles
----------------------

Finally, let us assert some computation principles for the lifts defined above. [6]_

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
   What we mean by "intrinsically computational" ought to become clearer as we progress.

.. [2]
   Although, as we note below, like everything in type theory, ``α`` may also be viewed as an inhabitant of a type.

.. [3]
   It is more common in mathematics to view :math:`B_0 × B_1` as the collection of pairs :math:`\{(b_0, b_1): b_i ∈ B_i, i = 0, 1\}`, but identifying tuples with functions results in a :term:`Pi type`.

.. [4]
   Using the tuple constructor described in :numref:`tuple-functors`, we could also represent such an operation as :math:`f: \mathrm{ntuple} A → A`. However,  we wish to postpone taking this viewpoint until we have some experience with categories and functors.

.. [5]
   The issue here is whether we can define :math:`fₗ (x/R)` without invoking some :term:`Choice` axiom.  Indeed, :math:`x/R` is a class of inhabitants of type :math:`α` and, if :math:`fₗ(x/R)` is taken to be the value returned when :math:`f` is evaluated at some member of this class, then we must have a way to choose one such member.  Note that we use :math:`x/R` to denote the :math:`R`-class containing :math:`x`, while the notation defined in the :term:`LSTL` for this :math:`R`-class is :math:`⟦x⟧`.

.. [6]
   Definitions in the ``ualib`` namespace are not part of Lean's built-in logical framework, so the computation principles we would like these definitions to satisfy must be assumed (as an ``axiom``), rather than proved (as a ``theorem``). If we had stuck with the ``quot`` constants defined in the `Lean Standard Library`_ (instead of defining our own versions of these constants), we could have *proved* the the ``flift_comp_principle``,  since this principle is taken as part of the logical framework of the :term:`LSTL`.

.. [7]
   Lean code appearing in this section is drawn mainly from the `quotient.lean`_ file of the `lean-ualib`_ repository.

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

