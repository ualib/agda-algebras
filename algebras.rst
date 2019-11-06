.. File: algebras.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 17 May 2019
.. Updated: 5 Nov 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _algebras:

========
Algebras
========

In this chapter we use the informal language of universal algebra to present foundational definitions and theorems about :term:`subalgebras <subalgebra>`, :term:`terms <term>`, and :term:`clones <clone>`.  In :numref:`Chapters %s <algebras-in-lean>` and :numref:`%s <clones-and-terms-in-lean>` we will show how the definitions and results presented in this section can be formalized (or "implemented") in type theory using Lean.

The idea is to demonstrate the power and utility of implementing our mathematical are of expertise in a formal language that supports dependent and inductive types, which are essential for expressing and working with infinite objects in a :term:`constructive` and :term:`computable` way, and for proving properties of these objects.

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

Evidently, this (the so called :term:`universal mapping <universal mapping property>`) is defined for each :math:`a: A` by :math:`(f, g)\, a = (f\,a, g\,a)`.

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

Next, we define a :term:`function application <eval>` operation on types :math:`A` and :math:`B`.

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

   As shown here, the :math:`@` symbol indicates that we will explicitly specify all arguments. (Lean_ also uses the :math:`@` symbol for this purpose.)

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

By an :math:`n`-**ary operation** on the set :math:`A` we mean a function :math:`f: A^n → A`, that takes an :math:`n`-tuple :math:`(a_0, \dots, a_{n-1})` of elements of type :math:`A` and returns an element :math:`f(a_0,\dots, a_{n-1})` of type :math:`A`.

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




-----------------------------------------


.. index:: ! graph (of a function)
.. index:: ! idempotent, ! projection
.. index:: operation, arity, image
.. index:: pair: ℕ; ω 

.. _operations:

Operations
-----------

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m: ℕ` and say ":math:`m` has type ℕ." [1]_

We denote and define natural numbers by :math:`m := \{0, 1, \dots, m-1\}`.

It is sometimes convenient to formally identify a function with its graph.  For example, the function :math:`a: m → A` may be identified with the tuple :math:`(a\,0, a\,1, \dots, a\,(m-1)): A^m`.

.. It seems an egregious abuse of notation to simply write :math:`a = (a\,0, a\,1, \dots, a\,(m-1))`, so we opt for the more standard notation :math:`a[m]` to denote the **image** of the set :math:`m` under the function :math:`a`; that is, :math:`a[m]:=(a\, 0, a\, 1, \dots, a\, (m-1))`.

If :math:`h: A → A` and :math:`a: m → A` are functions, then :math:`h ∘ a: m → A` denotes the composition of :math:`h` with :math:`a`; this is the function that maps each :math:`i: m` to the element

.. math:: (h ∘ a)(i) = h(a\, i)

of :math:`A`.

We may formally identify the function :math:`h ∘ a: m → A` with its graph, which is the :math:`m`-tuple,

.. math:: (h(a\, 0), h(a\, 1), \dots, h(a\, (m-1))).

Suppose :math:`A` is a nonempty set and :math:`n ∈ ℕ` is a natural number.

An :math:`n`-**ary operation** on :math:`A` is a function :math:`f: A^n → A` which, if :math:`n>0`, maps each :math:`n`-tuple :math:`(a_0, a_1, \dots, a_{n-1})` in :math:`A^n` to a particular element :math:`f(a_0, a_1, \dots, a_{n-1})` in :math:`A`. If :math:`n=0`, then :math:`f: () → A` is a function that takes no arguments and returns an element of :math:`A`, so :math:`f` in this case is merely notation for a particular element of :math:`A`.

An operation gives rise to a special kind of :math:`(n+1)`-ary relation, namely

.. math:: Gf := \{(a_0, a_1, \dots, a_{n-1}, b) \in A^{n+1} ∣ b = f(a_0, a_1, \dots, a_{n-1})\},

which is sometimes called the **graph** of :math:`f`.

For two sets :math:`A` and :math:`B`, the collection of all functions :math:`f: B → A` is denoted by :math:`A^B`. When :math:`B = A^n`, this is set :math:`A^{A^n}` of all :math:`n`-ary operations on :math:`A`.

If we let :math:`𝖮_A` denote the collection of all finitary operations on :math:`A`, then

.. math:: 𝖮_A = ⋃_{n ∈ ℕ} A^{A^n}.

If :math:`F ⊆ 𝖮_A` is a set of operations on :math:`A`, let us denote by :math:`F_n` the :math:`n`-ary operations in :math:`F`.

Clearly, :math:`F_n = F ∩ A^{A^n}`. For example, the set of *all* :math:`n`-ary operations on :math:`A` is

.. math:: (𝖮_A)_n = 𝖮_A ∩ A^{A^n} = A^{A^n}`.

Given an :math:`n`-tuple :math:`a = (a_0, a_1, \dots, a_{n-1}) ∈ A^n`, we will need a convenient way to refer to the set :math:`\{a_i : 0 ≤ i < n\}` of elements that occur in the tuple without explicitly naming each element in this set.  In fact, we already have notation for this, since an :math:`n`-tuple is actually a function, defined on the (ordered) set :math:`\{0, 1, \dots, n-1\}`, whose image is the set of elements in the tuple.

That is, if :math:`a = (a_0, a_1, \dots, a_{n-1})`, then :math:`\im a = \{a_0, a_1, \dots, a_{n-1}\}`. In particular, :math:`|\im a|` is a convenient way to write the number of distinct
elements that occur in the tuple :math:`a`.

For example, if :math:`a = (1,1,3)`, then :math:`\im a = \{1, 3\}`, and :math:`|\im a| = 2`.

An operation :math:`f ∈ A^{A^n}` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`.

Important examples of idempotent operations are the projections. If :math:`k` and :math:`n` are natural numbers with :math:`1 ≤ k ≤ n` then the :math:`k`-**th** :math:`n`-**ary projection** of :math:`A` is denoted by :math:`π^n_k` and defined to be the function that maps :math:`A^n` onto :math:`A` according to the rule :math:`(a_1, \dots, a_n) ↦ a_k`.

Thus, the arity of an operation is the number of operands upon which it acts, and we say that :math:`f` is an :math:`n`-**ary operation on** :math:`A` if :math:`\dom f = A^n` and :math:`\cod f = A`.

An operation is called **nullary** (or constant) if its arity is zero. **Unary**, **binary**, and **ternary** operations have arities 1, 2, and 3, respectively.


---------------------------

.. index:: signature, arity

.. _signatures:

Signatures
----------

(Our formal `Lean`_ implementation of the concept of signature is described in :numref:`signatures-in-lean`.)

Classically, a **signature** is a pair :math:`(F, ρ)` consisting of a set :math:`F` of operation symbols and an "arity" function :math:`ρ: F → ℕ`.

For each operation symbol :math:`f ∈ F`, the value :math:`ρ f` is the **arity** of :math:`f`. (Intuitively, the arity can be thought of as the "number of arguments" that :math:`f` takes as "input".)

If the arity of :math:`f` is :math:`n`, then we call :math:`f` an :math:`n`-**ary** function. In case :math:`n` is 0, 1, 2, or 3, we call the function "nullary", "unary", "binary", or "ternary," respectively.

If :math:`A` is a set and :math:`f` is a :math:`ρ f`-ary function on :math:`A`, then we often write :math:`f: A^{ρf} → A` to indicate this.

On the other hand, the arguments of such a function form a :math:`ρ f`-tuple, :math:`(a_0, a_1, \dots, a_{ρf -1})`, which may be viewed as the graph of the function :math:`a: ρf → A`, where :math:`a\, i = a_i`.

Thus, by identifying the :math:`ρ f`-th power :math:`A^{ρf}` with the type :math:`ρ f → A` of functions from :math:`\{0, 1, \dots, ρ f-1\}` to :math:`A`, we identify the function type :math:`A^{ρ f} → A` with the function (or "functional") type :math:`(ρf → A) → A`. [2]_

.. proof:example::

   Suppose 

     :math:`g : (m → A) → A` is an :math:`m`-ary operation on :math:`A`, and 
   
     :math:`a : m → A` is an :math:`m`-tuple on :math:`A`.

   Then :math:`g\, a = g(a\, 0, a\, 1, \dots, a\, (m-1))` has type :math:`A`.

   Suppose

     :math:`f : (ρf → B) → B` is a :math:`ρf`-ary operation on :math:`B`,

     :math:`a : ρf → A` is a :math:`ρf`-tuple on :math:`A`, and

     :math:`h : A → B`.
      
   Then :math:`h ∘ a : ρf → B` and :math:`f (h ∘ a) : B`.

It is important to be familiar with the classical notions of signature and arity, since these are used at the present time by virtually all algebraists.

In :numref:`Chapter %s <postmodern-algebra>` we give alternative, category theoretic definitions of these concepts and show how this alternative presentation can often simplify implementation of the mathematics in :term:`type theory`.

--------------------------

.. index:: ! pair: algebra; algebraic structure
.. index:: ! σ-algebra, ! arity, ! trivial algebra, ! reduct

.. _algebraic-structures:

Algebraic Structures
---------------------

(Our formal `Lean`_ implementation of the concept of algebraic structure is described in :numref:`Chapter %s <algebras-in-lean>`.)

Our first goal is to develop a working vocabulary and formal library for classical (single-sorted, set-based) universal algebra.  In this section we define the main objects of study. 

An **algebraic structure** (or **algebra**) is a pair :math:`⟨A, F⟩` where :math:`A` is a *nonempty* set and :math:`F = \{f_i: i ∈ I\}` is a collection of finitary operations on :math:`A`. That is, for each :math:`i∈ I` there exists an :math:`n ∈ ℕ` such that :math:`f_i: A^n → A`. The number :math:`n` is called the **arity** of the operation :math:`f_i`.

.. proof:example::

   If :math:`A=ℝ` and :math:`f: ℝ × ℝ → ℝ` is the map that takes each pair :math:`(a, b) ∈ ℝ × ℝ` to the number :math:`f(a,b) = a+b ∈ ℝ`, then :math:`⟨A, \{f\}⟩` is an example of an algebra with a single binary operation. In such cases, we often simplify the notation and write :math:`⟨A, f⟩` in stead of :math:`⟨A, \{f\}⟩`.

An algebra is **finite** if :math:`|A|` is finite, and is called **trivial** if :math:`|A| = 1`.

Given two algebras :math:`𝔸` and :math:`𝔹`, we say that :math:`𝔹` is a **reduct** of :math:`𝔸` if both algebras have the same universe and :math:`𝔹` can be obtained from :math:`𝔸` by removing  operations.

.. index:: ! operation symbol, ! arity, ! interpretation, ! signature, ! similarity type

A better approach
~~~~~~~~~~~~~~~~~

We start with a set :math:`F` and call the members of :math:`F` "operation symbols."  An **operation symbol** is simply an object that has an associated **arity**.

We denote the arity of :math:`f` by :math:`ρ \,f`, where :math:`ρ: F → N` is an "arity function" that maps :math:`F` into some "arity type" :math:`N`.  Often we take the arity type to be :math:`ℕ`, so that the arity of each symbol is a natural number, :math:`N = ℕ`, and :math:`ρ \, f ∈ ℕ` for all :math:`f∈ F`. 

A pair :math:`(F, ρ)` consisting of a set :math:`F` of operation symbols and an **arity function** :math:`ρ: F → N` is called a **signature** (or **similarity type**).

An **algebraic structure** (or **algebra**) in the signature :math:`σ = (F, ρ)` is denoted by :math:`𝔸 = ⟨A, F^𝔸⟩` and consists of 

  #. :math:`A` := a set, called the **carrier** (or **universe**) of the algebra,
  #. :math:`F^𝔸 = \{ f^𝔸 ∣ f ∈ F, \ f^𝔸 : (ρ f → A) → A \}` is a collection of operations on :math:`A`,
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝔸`.

Note that to each operation symbol :math:`f∈ F` corresponds an operation :math:`f^𝔸` on :math:`A` of arity :math:`ρ f`; we call this :math:`f^𝔸` the **interpretation** of :math:`f` in :math:`𝔸`.

We call an algebra in the signature :math:`σ` a :math:`σ`-**algebra** (although this is not standard). [3]_ 

.. proof:example::

   Consider the set of integers :math:`ℤ` with operation symbols :math:`F = \{0, 1, -(\,), +, ⋅\}`, which have respective arities :math:`\{0, 0, 1, 2, 2\}`.

   The operation :math:`+^ℤ` is the usual binary addition, while :math:`-^ℤ(\,)` is negation, which takes the integer :math:`z` to :math:`-^ℤ(z) = -z`.

   The constants :math:`0^ℤ` and :math:`1^ℤ` are nullary operations. Of course we usually just write :math:`+` for :math:`+^ℤ`, etc.

More :ref:`examples of algebraic structures <examples-of-algebras>` that have historically played a central role in mathematics over the last century (e.g., groups, rings, modules) appear in the appendix.

Some of the renewed interest in universal algebra focuses on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`Adamek:2011`, :cite:`Behrisch:2012`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`Meinke:1992`). These are natural generalizations that we will incorporate in our development later. (See :numref:`Chapter %s <postmodern-algebra>`.)

---------------------------

.. index:: ! subuniverse, ! subalgebra
.. index:: 𝖲(𝔸)
.. index:: 𝖲𝗀

.. _subalgebras:

Subalgebras
-------------

This section introduces two important concepts in universal algebra, **subuniverse** and **subalgebra**.

.. A **subuniverse** of an algebra :math:`𝔸 = ⟨A, F^𝔸⟩` is a subset :math:`B ⊆ A` that is closed under the operations in :math:`F^𝔸`.

Suppose :math:`𝔸 = ⟨A, F^𝔸⟩` is an algebra. Recall, the (nonempty) set :math:`A` is called the **universe** of 𝔸.

We call a subset :math:`B ⊆ A` **closed under** (the operations in) :math:`F^𝔸` if for each :math:`f ∈ F` and all :math:`b_0, \dots, b_{ρf-1} ∈ B` we have :math:`f^𝔸(b_0, \dots, b_{ρ f-1}) ∈ B`.  Equivalently,

.. math:: ∀ f ∈ F,\ ∀ b: ρ f → B, \ (f^𝔸 \, b) ∈ B`.

If a subset :math:`B ⊆ A` is closed under :math:`F^𝔸`, then we call :math:`B` a **subuniverse** of :math:`𝔸`.

If :math:`B ≠ ∅` is a subuniverse of 𝔸, and if we let :math:`F^𝔹 = \{ f^𝔸 ↾ B : f ∈ F \}`, then :math:`𝔹 = ⟨ B, F^𝔹 ⟩` is an algebra, called a **subalgebra** of 𝔸.

.. Equivalently, if :math:`B ≠ ∅` is a subuniverse of 𝔸 and :math:`F^{𝔹|_A} = \{f^𝔸|_B ∣ f ∈ F\}` is the set of basic operations of 𝔸 restricted to the set :math:`B`, then :math:`𝔹 = ⟨B, F^{𝔹|_A}⟩` is a **subalgebra** of 𝔸.

Conversely, all subalgebras are of this form.

If 𝔹 is a subalgebra of 𝔸, we denote this fact by :math:`𝔹 ≤ 𝔸`. Similarly, we write :math:`B ≤ 𝔸` if :math:`B` is a subuniverse of :math:`𝔸`. 

  *The empty set is a subuniverse of every algebra, but the universe of an algebra is never empty*.

In other terms, if :math:`𝖲(𝔸)` denotes the collection of all subalgebras of :math:`𝔸`, then 

.. math:: 𝖲 (𝔸) = \{⟨B, F^𝔹⟩ : B ≤ 𝔸 \text{ and } B ≠ ∅\}.

It is obvious that the intersection of subuniverses is again a subuniverse. Let us nevertheless record this observation.

.. proof:lemma::

   Suppose :math:`A_i ≤ 𝔸` for all :math:`i` in some set :math:`I`. Then :math:`⋂_{i∈ I} A_i` is a subuniverse of :math:`𝔸`.

.. index:: subuniverse generation

.. _subuniverse-generation:

Subuniverse generation
~~~~~~~~~~~~~~~~~~~~~~

As above :math:`𝖲(𝔸)` denotes the collection of all subalgebras of 𝔸.  If 𝔸 is an algebra and :math:`A_0 ⊆ A` a subset of the universe of 𝔸, then the **subuniverse of** 𝔸 **generated by** :math:`A_0`, denoted by :math:`\Sg^𝔸 (A_0)` or :math:`⟨A_0⟩`, is the smallest subuniverse of 𝔸 containing the set :math:`A_0`.  Equivalently, 

.. math:: \Sg^{𝔸}(A_0)  =  ⋂ \{ U ∈ 𝖲 (𝔸) ∣ A_0 ⊆ U \}.
  :label: SgDef

We can also use recursion to define the **subuniverse of** 𝔸 **generated by a set** and prove that this new definition is equivalent to the one given by :eq:`SgDef`

.. (cf. :cite:`Bergman:2012` Thm. 1.14).

.. in :numref:`subuniverse-and-subalgebra` 

.. _thm-1-14:

.. proof:theorem:: Subuniverse generation

   Let :math:`𝔸 = ⟨A, F^{𝔸}⟩`  be  an  algebra in the signature :math:`σ = (F, ρ)` and let :math:`A_0` be a subset of :math:`A`.

   Define, by recursion on :math:`n`, the sets :math:`A_n` as follows:

     If :math:`A_0 = ∅`, then :math:`A_n = ∅` for all :math:`n<ω`.

     If :math:`A_0 ≠ ∅`, then

     .. math:: A_{n+1} =  A_n ∪ \{ f\, a ∣ f ∈ F, \ a ∈ ρ f → A_n\}.
        :label: subalgebra-inductive

   Then the subuniverse of 𝔸 generated by :math:`A_0` is :math:`\Sg^𝔸(A_0) = ⋃_{n<ω} A_n`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let :math:`Y := ⋃_{n < ω} A_n`. Clearly :math:`A_n ⊆ Y ⊆ A`, for every :math:`n < ω`. In particular :math:`A = A_0 ⊆ Y`. We first show that :math:`Y` is a subuniverse of 𝔸.

      Let :math:`f` be a basic :math:`k`-ary operation and let :math:`a: k → Y` be a :math:`k`-tuple of elements of :math:`Y`.
    
      From the construction of :math:`Y`, there is an :math:`n < ω` such that :math:`∀ i,\ a,\ i ∈ A_n`.
    
      From its definition, :math:`f \,a ∈ A_{n+1} ⊆ Y`. Since :math:`f` was arbitrary, it follows that :math:`Y` is a subuniverse of 𝔸 containing :math:`A_0`.
    
      Thus, by :eq:`SgDef`, :math:`\Sg^𝔸(A_0) ⊆ Y`.
    
      For the opposite inclusion, it is enough to check, by induction on :math:`n`, that :math:`A_n ⊆ \Sg^𝔸(A_0)`.
    
      Clearly, :math:`A_0 ⊆ \Sg^𝔸(A_0)`.
      
      Assume :math:`A_n ⊆ \Sg^𝔸(A_0)`.  We show :math:`A_{n+1} ⊆ \Sg^𝔸(A_0)`.
      
      If :math:`b ∈ A_{n+1} - A_n`, then :math:`b = f\, a` for a basic :math:`k`-ary operation :math:`f` and some :math:`a: k → A_n`.
      
      But :math:`∀ i, \ a i ∈ \Sg^𝔸(A_0)` and since this latter object is a subuniverse, :math:`b ∈ \Sg^𝔸(X)` as well.
    
      Therefore, :math:`A_{n+1} ⊆ \Sg^𝔸(A_0)`, as desired. ☐ 

.. The argument in the proof of :numref:`Theorem %s <thm-1-14>` is of a type that one encounters frequently throughout algebra. It has two parts.

..   #. Some set :math:`Y` is shown to be a subuniverse of 𝔸 that contains :math:`A_0`.

..   #. Every subuniverse containing :math:`A_0` is shown to contain :math:`Y` as well.

..   #. One concludes that :math:`Y = \Sg^𝔸 (A_0)`.


**Formalization**. Our formal implementation (in `Lean`_) of the concept of subalgebra is described in :numref:`Sections %s <subalgebras-in-lean>` and :numref:`%s <subalgebras-in-lean_reprise>`, and is included in the `subuniverse.lean`_ file of the `lean-ualib`_ library.

---------------------------

.. index:: ! subdirect product

.. _subdirect-products:

Subdirect products
-------------------

If :math:`k, n ∈ ℕ`, if :math:`A = (A_0, A_1, \dots, A_{n-1})` is a list of sets, and if :math:`σ : k → n` is a :math:`k`-tuple, then a relation :math:`R` over :math:`A` with scope :math:`σ` is a subset of the Cartesian product :math:`A_{σ(0)} × A_{σ(1)} × \cdots × A_{σ(k-1)}`.

Let :math:`F` be a set of operation symbols and for each :math:`i<n` let :math:`𝔸_i = ⟨ A_i, F ⟩` be an algebra of type :math:`F`. If :math:`𝔸 = ∏_{i<n}𝔸_i` is the product of these algebras, then a relation :math:`R` over :math:`𝔸` with scope :math:`σ` is called **compatible with** 𝔸 if it is closed under the basic operations in
:math:`F`. In other words, :math:`R` is compatible if the induced algebra :math:`ℝ = ⟨ R, F ⟩` is a subalgebra of :math:`\prod_{j<k} 𝔸_{σ(j)}`.

If :math:`R` is compatible with the product algebra and if the projection of :math:`R` onto each factor is surjective, then :math:`ℝ` is called a **subdirect product** of the algebras in the list :math:`(𝔸_{σ(0)}, 𝔸_{σ(1)}, \dots, 𝔸_{σ(k-1)})`; we denote this situation by writing :math:`ℝ ≤_{\mathrm{sd}} \prod_{j< k} 𝔸_{σ(j)}`.

**Formalization**. (not yet implemented)

.. todo:: implement subdirect product in Lean

-----------------------------------------------

.. index:: ! homomorphism
.. index:: ! epimorphism, ! monomorphism, ! automorphism

.. _homomorphisms:

Homomorphisms
-------------

Let :math:`𝔹 = ⟨ B, F^𝔹 ⟩` and :math:`ℂ = ⟨ C, F^ℂ ⟩` be algebras of the same signature, and let :math:`h: B → C` be a function (e.g., on sets).

Take an operation symbol :math:`f ∈ F`, and suppose that for all :math:`ρ f`-tuples :math:`b: ρ f → B` of :math:`B` the following equation holds:

.. math:: h (f^𝔹 \, b) = f^ℂ (h ∘ b).

Then :math:`h` is said to **respect the interpretation of** :math:`f`.

If :math:`h` respects the interpretation of every :math:`f ∈ F`, then we call :math:`h` a **homomorphism** from 𝔹 to ℂ, and we write :math:`h ∈ \hom(𝔹, ℂ)`, or simply, :math:`h: 𝔹 → ℂ`.

A homomorphism :math:`h: 𝔹 → ℂ` is called an **epimorphism** if for every algebra :math:`𝔻` and pair :math:`g_1, g_2: ℂ → 𝔻` of homomorphisms, the equation :math:`g_1 ∘ h = g_2 ∘ h` implies :math:`g_1 = g_2`. We often write :math:`h: 𝔹 ↠ ℂ`, and we say ":math:`h` is **epi**" and ":math:`h` maps 𝔹 **onto** ℂ," in this case.

A homomorphism :math:`h: 𝔹 → ℂ` is called a **monomorphism** if for every algebra :math:`𝔸` and every pair :math:`g_1, g_2: 𝔸 → 𝔹` of homomorphisms, the equation :math:`h ∘ g_1 = h ∘ g_2` implies :math:`g_1 = g_2`.  We sometimes write :math:`h: 𝔸 ↣ 𝔹`, and we say ":math:`h` is **mono**" and ":math:`h` maps 𝔹 **into** ℂ," in this case.

.. proof:notation:: homo-, epi-, mono-, automorphism

   We adopt the following notation. If :math:`𝔹` and :math:`ℂ` are algebras in the same signature, then

   + :math:`\hom(𝔹, ℂ) =` the set of homomorphisms from 𝔹 to ℂ.
   + :math:`\epi(𝔹, ℂ) =` the set of epimorphisms from 𝔹 onto ℂ.
   + :math:`\mono(𝔹, ℂ) =` the set of monomorphisms from 𝔹 into ℂ.
   + :math:`\aut(𝔹, ℂ) =` the set of automorphisms from 𝔹 into and onto ℂ.

**Formalization**. Our formal implementation (in `Lean`_) of these concepts is described in  :numref:`subalgebras-in-lean`, :numref:`basic-facts-in-lean`, :numref:`factoring-homomorphisms`, and is included in the `birkhoff.lean`_ and `subuniverse.lean`_ files of the `lean-ualib`_ library.

----------------------

.. index:: ! projection operator, ! idempotent operation

.. _idempotence-and-projections:

Idempotence and projections
----------------------------

An operation :math:`f: A^n → A` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`.

Examples of idempotent operations are the *projections* and these play an important role in the theory, so we introduce a sufficiently general and flexible notation for them.

Denote and define the set ℕ of natural numbers inductively as follows:

.. math:: 0 = ∅, \quad 1 = \{0\}, \quad  2 := \{0, 1\}, \dots, n = \{0, 1, \dots, n-1\}.

Let :math:`\{A_i: i ∈ I\}` be a collection of sets (for some :math:`I ⊆ ℕ`) and let :math:`A = ∏_{i ∈ I} A_i`. View the elements of :math:`A` as functions:

.. math:: a ∈ ∏_{i∈I} A_i \quad ⟷ \quad \begin{cases} a : I → ⋃_{i∈I} A_i, & \\ a\,i ∈ A_i, & ∀ i ∈ I. \end{cases}
   :label: 7
   
This correspondence simply records the fact that the product type (on the left of the ⟷ symbol) is a special kind of function type (depicted on the right of ⟷ using the usual arrow notation for function types).

In other words, :eq:`7` says that an element of the product type :math:`∏_{i∈I} A_i` is a function from :math:`I` into :math:`⋃_{i∈I} A_i`.  As explained in the section on :ref:`Pi types <pi-types>`, such a function (or product) type is known as a :term:`dependent type`.

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

#. If :math:`f: X → A` and :math:`g: X → B` are functions defined  on the same domain :math:`X`, then :math:`(f,g): X → A × B` is the unique function that composes with the first projection to give :math:`f` and composes with the second projection to give :math:`g`. For example, in the last remark there appears the expression :math:`(\Proj\, σ\, a, \Proj\, σ \, a') = (a ∘ σ, a' ∘ σ)`, which has type :math:`( ∏_{j<k} A_{σ\, j} )^2`. [4]_

#. If the domain of :math:`σ` is a singleton, :math:`k = \{0\}`, then of course :math:`σ` is just a one-element list, say, :math:`σ = (j)`. In such cases, we write :math:`\Proj\, j` instead of :math:`\Proj\, {(j)}`.  Similarly, we write and :math:`\mathbf{0}\, j` and :math:`θ\, j` instead of :math:`\mathbf{0}\, {(j)}` and :math:`θ\, {(j)}`. Thus, :math:`\Proj\, j \, a = a\, j`, and :math:`\mathbf{0} \, j = \{(a, a') ∈ A^2 ∣ a \, j = a' \, j\}`, and, if :math:`θ ∈ \Con 𝔸_j`, then :math:`θ \, j = \{(a, a') ∈ A^2 ∣ a \, j \mathrel{\theta} a'\, j\}`.

Here are some obvious consequences of the foregoing notation and definitions that are worth noting.

.. math::

   ⋁_{0≤j<n}\mathbf{0}j = A^2, \quad \mathbf{0} σ = ⋀_{j ∈ σ} \mathbf{0} j, \quad \mathbf{0}n = ⋀_{0≤j<n}\mathbf{0} j = 0_A, \quad
   θσ = ⋀_{0≤j<k} θ \, σ\, j,

where :math:`0_{A}` denotes the least equivalence relation on :math:`A`, that is, :math:`0_{A}:= \{(a, a') ∈ A^2 ∣ a = a'\}`.

.. As we alluded to above, :math:`η_σ` is shorthand for :math:`(0_A)_σ`.

.. index:: projection kernel

.. _kernels-of-projections:

Kernels of projections
~~~~~~~~~~~~~~~~~~~~~~~

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

----------------------------------------------


.. index:: ! clone
.. index:: ! clone of projections
.. index:: ! clone of polynomial operations
.. index:: ! clone of term operations

.. _clones:

Clones
------

**Formalization**. For a description of our implementation (in `Lean`_) of the objects described in this section, see :numref:`Chapter %s <clones-and-terms-in-lean>`.

An **operational clone** (or just **clone**) on a nonempty set :math:`A` is a set of operations on :math:`A` that contains the projection operations and is closed under general composition.

Let :math:`𝖢 A` denote the collection of all clones on :math:`A`.

The smallest clone on :math:`A` is the **clone of projections**, which we denote and define as follows:

.. math:: \Proj  A = ⋃_{i < n < ω}  \{π^n_i : ∀ a ∈ A^n,\ π^n_i\, a = a(i)\}.

Let us set down some conventions that will help simplify notation.  Recall, the natural number :math:`k< ω` may be constructed as (or at least identified with) the set :math:`\{0,1,\dots, k-1\}`, and this will be helpful here.

For each :math:`k< ω`, denote and define the tuple :math:`\pi^k: k → ((k → A) → A)` of all :math:`k`-ary projections on :math:`A` as follows: for each :math:`0≤ i < k`,  :math:`π^k(i)` is the :math:`i`-th :math:`k`-ary projection operation that takes each :math:`k`-tuple :math:`a: k → A` to its entry at index :math:`i`:

.. math:: π^k (i) a = a(i).

Observe that if :math:`f: (k → A) → A` is a :math:`k`-ary operation on :math:`A`, then 

The **clone of term operations** of a σ-algebra 𝔸 is the smallest clone on :math:`A` containing the basic operations of 𝔸; this is
denoted and defined by

.. math:: \Clo (F^𝔸) = ⋂ \{ U ∈ 𝖢 A ∣ F^𝔸 ⊆ U\}.

The set of :math:`n`-ary members of :math:`\Clo (F^𝔸)` is sometimes denoted by :math:`\Clo _n (F^𝔸)` (despite the fact that the latter is clearly not a clone).

The **clone of polynomial operations** (or **polynomial clone**) of a σ-algebra 𝔸 is denoted by :math:`\Pol (F^𝔸)` and is defined to be the clone generated by the collection consisting of the basic operations (i.e., :math:`F^𝔸`) of 𝔸 along with the **constants** on :math:`A`. [6]_

The set of :math:`n`-ary members of :math:`\Pol (F^𝔸)` is sometimes denoted by :math:`\Pol _n (F^𝔸)`. 

.. .. [9] Lean's built-in sigma type is defined as follows: :math:`structure sigma {α : Type u} (β : α → Type v) := mk :: (fst : α) (snd : β fst)`

The clone :math:`\Clo (F^𝔸)` is associated with the algebra :math:`𝔸` only insofar as the former is constructed out of the basic operations of 𝔸 and the set :math:`A` on which those operations are defined.  However, all that is required when defining a clone is a set :math:`A` and some collection :math:`F` of operations defined on :math:`A`; from only these ingredients, we can construct the clone generated by :math:`F`, which we denote by :math:`\Clo (F)`.

Thus

  *the clone of terms operations can be implemented (e.g., in Lean) as an inductive type*.
  
The following theorem makes this more precise (cf. Theorem 4.32 of :cite:`Bergman:2012`). (See also :numref:`Chapter %s <inductively-defined-types>`, where we formalize this in Lean.)

.. We seek a "bottom-up," inductive description of the members of :math:`\Clo (F)`.  By thinking of the clone itself as a kind of algebra, a description analogous to :numref:`Obs %s <thm-1-14>` ought to be possible.  In fact, since function composition is associative, a slightly slicker formulation is available.

..  Theorem  4.3. of Bergman [1].

.. _obs-five:

.. proof:observation::

   Let :math:`A` be a set and let :math:`F ⊆ \Op (A):= ⋃_{n<ω} A^{A^n}` be a collection of operations on :math:`A`.
   
   Define :math:`F_0 := \Proj (A)` (the set of projections on :math:`A`) and for all :math:`0 ≤ n < ω` let
 
   .. math:: F_{n+1} := F_n ∪ \{ f g \mid f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.
 
   Then :math:`\Clo (F) = ⋃_n F_n`.
 
   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Let :math:`F̄ = ⋃_n F_n`. It is easy to argue by induction that every :math:`F_n` is a subset of :math:`\Clo (F)`. Thus, :math:`F ⊆ \Clo (F)`.
    
      For the converse, we must show that :math:`F̄` is a clone that contains :math:`F`.
    
      Obviously :math:`F̄` contains the projection operations, :math:`F_0 ⊆ F̄`.

      For every :math:`f ∈ F`, we have :math:`f π^k ∈ F_1 ⊆ F̄`, where :math:`k:= ρ f`.
 
      We are reduced to showing that :math:`F̄` is closed under generalized composition. This follows from the following claim.
 
      **Claim**. If :math:`f ∈ F_n` and :math:`g_0, \dots, g_{ρ f-1} ∈ F_m` are all :math:`k`-ary, then :math:`f g \in F_{n+m}`, where we have defined :math:`g: ρ f → (k → A) → A` to be the tuple given by :math:`g\,i = g_i` for each :math:`0 ≤ i < ρ f`.

      Note that the types match up; indeed, for each :math:`a: (k → A) → A`, we have

      .. math:: f (g ∘ a) = f(g_0(a_0, \dots, a_{k-1}), 
 
      We prove the claim by induction on :math:`n`.
      
      If :math:`n = 0` then :math:`f` is a projection, so :math:`f g = g_i ∈ F_{0+m}` for some :math:`0≤ i < ρ f`.

      Assume the claim holds for :math:`n` and that :math:`f ∈ F_{n+1} - F_n`.
      
      From the definition, there is a :math:`t`-ary operation :math:`f_i ∈ F` and a :math:`t`-tuple :math:`h = (h_0, \dots, h_{t-1}) ∈ t → F_n`, such that :math:`f = f_i h`. (Note that :math:`h: t → (ρ f → A) → A` is given by :math:`h(j) = h_j`, and that the arity of each :math:`h_i` must be equal to that of :math:`f`, namely :math:`ρ f`.)
      
      By the induction hypothesis, for each :math:`i ≤ k`, :math:`h_i' = h_i g \in F_{n+m}` (where, as above, :math:`g = (g_0, \dots, g_{k-1})`).
      
      Applying the definition, :math:`f_1 h' ∈ F_{n+m+1} = F_{(n+1)+m}`. Since 
      
      .. math:: f_1 h' = f_1 ∘ (h_1 g, \dots, h_t g) = f g,

      the claim is proved. □

------------------------

.. index:: ! term, ! term algebra, ! σ-term 

.. _terms:

Terms
-----

**Formalization**. For a description of our implementation (in `Lean`_) of the objects described in this section, see :numref:`Chapter %s <clones-and-terms-in-lean>`.

Fix a :term:`signature` :math:`σ = (F, ρ)`, let :math:`X` be a set of **variables**, and assume :math:`X ∩ F = ∅`.

By a **word** on :math:`X ∪ F` we mean a nonempty, finite sequence of members of :math:`X ∪ F`, and we will denote the concatenation of such sequences by simple juxtaposition.

Let :math:`F_0` denote the set of nullary operation symbols. We define by induction on :math:`n` the sets :math:`T_n` of **terms on** :math:`X ∪ F` as follows:

.. math::      T_0 &= X ∪ F_0;\\
           T_{n+1} &= T_n ∪ \{ f\, s ∣ f ∈  F, \ s: ρf → T_n \},

and we define the collection of **terms of signature** :math:`σ` **over** :math:`X` by :math:`T_σ(X) = ⋃_{n < ω}T_n`.

By a :math:`σ`-**term** we mean a term in the signature :math:`σ`. 

The definition of :math:`T_σ (X)` is recursive, indicating that

  *terms can be implemented as an inductive type*

(in Lean, for example). We confirm this in :numref:`Chapter %s <inductively-defined-types>` below.

Before doing so, let us impose an algebraic structure on :math:`T_σ (X)`, and then state and prove some basic facts about this important algebra. These will be formalized in :numref:`Chapter %s <inductively-defined-types>`, giving us a chance to show off inductively defined types in Lean.

If :math:`t` is a term, then the **height** of :math:`t` is denoted by :math:`|t|` and defined to be the least :math:`n` such that :math:`t ∈ T_n`. The height of is a useful index for recursion and induction.

.. Let :math:`ρ: T_σ(X) → ℕ` denote the **arity function for term**, defined as follows:
.. .. math:: ρ t = \min \{n ∣t ∈ T_n,\; 0≤ n < ω\}.

Notice that :math:`T_σ (X)` is nonempty iff :math:`X ∪ F_0` is nonempty.

If :math:`T_σ (X)` is nonempty, then we can impose upon it an algebraic structure, which we denote by :math:`𝕋_σ (X)` (or :math:`𝕋` when :math:`σ` and :math:`X` are clear from context).

We call :math:`𝕋_σ (X)` the **term algebra in the signature** :math:`σ` **over** :math:`X` (or, the :math:`σ`-**term algebra over** :math:`X`); it is constructed as follows:

  For every basic operation symbol :math:`f ∈ F` let :math:`f^𝕋` be the operation on :math:`T_σ (X)` that maps each tuple :math:`s: ρ f → T_σ (X)` to the formal term :math:`f\,s`; define :math:`𝕋_σ(X)` to be the algebra with universe :math:`T_σ (X)` and basic operations :math:`\{f^𝕋 | f ∈ F\}`. [5]_

Let us now prove a couple of easy but important consequences of these definitions.

.. about the :math:`σ`-term algebra over :math:`X`.

.. _obs-six:

.. proof:observation::

   #. :math:`𝕋 := 𝕋_σ(X)` is generated by :math:`X`.
 
   #. For every :math:`\sigma`-algebra :math:`𝔸 = ⟨A, F^𝔸⟩` and function :math:`g: X → A` there is a unique homomorphism :math:`h: 𝕋 → 𝔸` such that :math:`h|_X = g`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*.
     
      The definition of :math:`𝕋` exactly parallels the construction in :numref:`Theorem %s <thm-1-14>`. That accounts for the first assertion.
     
      For the second assertion, define :math:`h\,t` by induction on the :term:`height` of :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ F_0`.
      
      If :math:`t ∈ X`, then define :math:`h\,t = g\,t`. If :math:`t ∈ F_0`, then let :math:`h\,t = t^𝔸`.
     
      For the inductive step, assume :math:`|t| = n + 1`. Then :math:`t = f\,s` for some :math:`f ∈ F` and :math:`s: ρ f → T_n`, where for each :math:`0 ≤ i< ρ f` the term :math:`s\, i` has height at most :math:`n`. We define :math:`h\,t = f^𝔸(h ∘ s) = f^𝔸(h\,s_1, \dots, h\,s_k)`.
     
      By its very definition, :math:`h` is a homomorphism that agrees with :math:`g` on :math:`X`. The uniqueness of :math:`h` follows from :numref:`Obs %s <obs-two>`. ☐

.. index:: interpretation (of a term), ! arity (of a term)

.. _interpretation-of-a-term:

Interpretation of a term
~~~~~~~~~~~~~~~~~~~~~~~~

..  and let :math:`T_n := T_σ(X_n)` be the subalgebra of :math:`T_σ(X_ω)` generated by :math:`X_n`.  Then, :math:`T_0 ⊆  T_1 ⊆ T_2 ⊆ \cdots` and :math:`T_σ(X_ω) = ⋃_{n<ω}  T_n`.

We denote and define the set :math:`X := \{x_0,x_1,\dots \}` of variable symbols, and for each natural number :math:`n` we let :math:`X_n:=\{x_0,x_1,\dots, x_{n-1}\}`.

Let :math:`σ = (F, ρ)` be a signature, :math:`𝔸` a :math:`σ`-algebra, and :math:`𝕋` the :math:`σ`-term algebra over :math:`X`; that is, 

.. math:: 𝔸 := ⟨A, F^𝔸⟩ \quad \text{ and } \quad 𝕋 := ⟨T_σ(X), F^𝕋⟩. 

Each operation symbol :math:`f ∈ F` gives rise to

#.  a :math:`ρ f`-ary operation on :math:`T_σ(X)`, denoted by :math:`f^𝕋`, which maps each :math:`ρ f`-tuple :math:`s: ρ f → T_σ(X)` to the formal term :math:`f \,s` in :math:`T_σ(X)`, and

#.  a :math:`ρ f`-ary operation on :math:`A`, denoted by :math:`f^𝔸`, which maps each :math:`ρ f`-tuple :math:`a: ρ f → A` to the element :math:`f^𝔸 \,a` in :math:`A`. The operation :math:`f^𝔸` is called the **interpretation of** :math:`f` **in the algebra** :math:`𝔸`.  

In the present section we explain how to define the interpretation of a :math:`σ`-term in a :math:`σ`-algebra.

As usual, for each :math:`0<n<ω` we identify the :math:`n`-tuple :math:`(x_0, x_1, \dots, x_{n-1})` with the function :math:`x: n → X_n` defined by :math:`x\, i = x_i` :math:`(0≤i<n)`.

Recall, a term :math:`t` is either a variable, say, :math:`t = x`, or has the form :math:`t = f \,s` for some operation symbol :math:`f ∈ F`, and some :math:`ρ f`-tuple :math:`s: ρ f → T_σ (X)` of terms.

.. and suppose :math:`|t| = n`.
..  : (n → X_n) → T_n` be an :math:`n`-ary term. 

Let :math:`t ∈ T_σ(X)` be a term. Define the **operation** :math:`t^𝔸` **on** :math:`A` by recursion on the :term:`height` :math:`|t|` of :math:`t` as follows: for each tuple :math:`a: X → A` of :math:`A`, 

#. (:math:`|t| = 0`) if :math:`t` is the variable :math:`x_i ∈ X`, then :math:`t^𝔸 \, a = π^X_i\, a = a\, i`,
#. (:math:`|t| = n+1`) if :math:`t = f\, s` where :math:`f ∈ F` is an operation symbol and :math:`s: ρ f → T_n` is a tuple of terms whose heights are at most :math:`n` (i.e., :math:`∀ i < ρf, |s\, i| ≤ n`), then :math:`t^𝔸 = f^𝔸 \, s^𝔸`.
 
.. .. Let :math:`X_ω := \{x_0, x_1, \dots\}` be a collection of variables and define :math:`X_n:=\{x_0, x_1, \dots, x_{n-1}\}`.

In the next observation, assume :math:`𝔸 = ⟨A, F^𝔸⟩` and :math:`𝔹 = ⟨B, F^𝔹⟩` are algebras in the same signature :math:`σ = (F, ρ)`, and let :math:`t ∈ T_σ (X)` be an :math:`n`-ary term.

In particular, as we just explained, :math:`t` has an interpretation in :math:`𝔸`, denoted by :math:`t^𝔸 a = t^𝔸 (a\, 0, a\, 1, \dots, a\, (n-1))`, where :math:`a: n → A`, as well as an interpretation :math:`t^𝔹: (n → B) → B` in :math:`𝔹`.
    
.. _thm-4-32:

.. _obs-seven:

.. proof:observation:: homomorphisms commute with terms

   #. :math:`g: 𝔸 → 𝔹` is a homomorphism, then :math:`g ∘ a: n → B` is the :math:`n`-tuple whose :math:`i`-th component is :math:`(g ∘ a)\, i = g(a\, i)`, and
  
      .. math:: g(t^𝔸 a) = t^𝔹(g ∘ a).

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      This is an easy induction on :math:`|t|`. ☐
    
.. _obs-eight:

.. proof:observation:: terms respect congruences

   If :math:`θ` is a congruence of :math:`𝔸` and :math:`a, a': n → A` are :math:`n`-tuples over :math:`A`, then
    
   .. math:: (a, a') ∈ θ \; ⟹  \; (t^𝔸\,a, t^𝔸\,a') ∈ θ.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      This follows from :numref:`Obs %s <obs-seven>` by taking :math:`⟨B, F^𝔹⟩ = ⟨A, F^𝔸⟩/θ = ⟨A/θ, F^{𝔸/θ}⟩` and :math:`g=` the canonical homomorphism. ☐
    
.. _obs-nine:

.. proof:observation:: subuniverse generation as image of terms

   If :math:`Y` is a subset of :math:`A`, then

      .. math:: \Sg^{𝔸}(Y) = \{ t^𝔸 \, a ∣ t ∈ T_σ(X_n), \, n ∈ ℕ, \; a: ρ t → Y\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      A straightforward induction on the height of :math:`t` shows that every subuniverse is closed under the action of :math:`t^𝔸`. Thus the right-hand side is contained in the left. On the other hand, the right-hand side is a subuniverse that contains the elements of :math:`Y` (take :math:`t = x_1`), so it contains :math:`\Sg^{𝔸}(Y)` as the latter is the smallest subuniverse containing :math:`Y`. ☐

.. todo:: complete this section (include material on free algebras)

.. .. index:: ! Malcev condition, ! Taylor term
..
.. Special terms
.. ~~~~~~~~~~~~~~
.. .. _thm-4-3:
..
.. .. proof:theorem::
..
..    Let :math:`X` be a set and :math:`σ = (F, ρ)` a signature. Define
..
..    .. math:: F_0 &= X;\\
..          F_{n+1} &= F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρ g → X)) \}, \quad n < ω.
..
..    Then :math:`\Clo ^X(F) = ⋃_n F_n`.
..
..
.. For a nonempty set :math:`A`, we let :math:`𝖮_A` denote the set of all finitary operations on :math:`A`. That is, :math:`𝖮_A = ⋃_{n∈ ℕ} A^{A^n}` on :math:`A` is a subset of :math:`𝖮_A` that contains all projection operations and is closed under the (partial) operation of :ref:`general composition <general-composition>`.
..
.. If :math:`𝔸 = ⟨ A, F^𝔸 ⟩` denotes the algebra with universe :math:`A` and set of basic operations :math:`F`, then :math:`\Clo  (𝔸)` denotes the clone generated by :math:`F`, which is also known as the **clone of term operations** of :math:`𝔸`.
..
.. We will discuss varieties in more detail later, but for now define a :index:`variety` to be a collection of algebras of the same signature which is defined by a set of identities. [3]_ 
..   
.. In 1977, Walter Taylor showed (:cite:`Taylor1977`) that a variety 𝕍 satisfies some nontrivial :term:`idempotent` :term:`Malcev condition` if and only if it satisfies one of the following form: for some :math:`n`, 𝕍 has an idempotent :math:`n`-ary term  :math:`t` such that for each :math:`0 ≤ i < n` there is an identity of the form 
..
..    .. math:: t(∗, \cdots, ∗, x, ∗, \cdots, ∗) ≈ t(∗, \cdots, ∗, y, ∗, \cdots, ∗)
..
.. that is true in 𝕍 and is such where distinct variables :math:`x` and :math:`y` appear in the :math:`i`-th position on each side of the identity. Such a term :math:`t` now goes by the name :index:`Taylor term`.

.. .. [3]
..   We will also have much to say about Malcev conditions, but for now we ask the reader to trust us when we say that such conditions play an important role in many deep results in universal algebra.

--------------------------

.. _basic-facts:

Basic facts
------------

.. Some of them involve homomorphisms, or terms, or clones.  

Throughout this section,

+ :math:`𝔸 = ⟨A, F^𝔸⟩, \ 𝔹 = ⟨B, F^𝔹⟩, \ ℂ = ⟨C, F^ℂ⟩\ ` are algebras in the same signature :math:`σ = (F, ρ)`, and

+ :math:`g, h : \hom(𝔸, 𝔹)` are homomorphisms from 𝔸 to 𝔹;

.. index:: ! equalizer

The **equalizer** of :math:`g` and :math:`h` is the set

.. math:: 𝖤(g,h) = \{a: A ∣ g\, a = h\, a\}.

Here is a small collection of basic observations that we will need later. When we refer back to these, we will call them :numref:`Obs %s <obs-one>`, etc.

.. _obs-one:

.. proof:observation::

   :math:`𝖤(g,h)` is a subuniverse of 𝔸.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      Fix arbitrary :math:`f ∈ F` and :math:`a : ρf → 𝖤(g,h)`.

      We show that :math:`g (f^𝔸 \, a) = h (f^𝔸 \, a)`, as this will show that :math:`𝖤(g, h)` is closed under the operation :math:`f^𝔸` of :math:`𝔸`.

      For all :math:`i<ρ f` we have :math:`a \, i ∈ 𝖤(g,h)`, so :math:`g\, a \, i= h\, a\, i`.  Therefore (by function extensionality) :math:`g ∘ a = h ∘ a` and so, by definition of homomorphism,

      .. math:: g  (f^𝔸\,a) = f^𝔹 (g ∘ a) = f^𝔹 (h ∘ a) = h (f^𝔸\, a).

      ☐

**Formalization**. Our formal implementation (in `Lean`_) of :numref:`Obs %s <obs-one>` is described in :numref:`equalizer-as-subuniverse`,  and is included in the `birkhoff.lean`_ file of the `lean-ualib`_ library.

.. _obs-two:

.. proof:observation::

   If the set :math:`X ⊆ A` generates 𝔸 and :math:`g|_X = h|_X`, then :math:`g = h`.

   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Suppose the subset :math:`X ⊆ A` generates :math:`⟨A, F^𝔸⟩` and suppose :math:`g|_X = h|_X`.
 
      Fix an arbitrary :math:`a: A`. We show :math:`g\, a = h\, a`.
 
      Since :math:`X` generates 𝔸, there exists a term :math:`t` and a tuple :math:`x: ρt → X` of generators such that :math:`a = t^𝔸\, x`.
 
      Therefore, since :math:`g|_X = h|_X`, we have
    
      .. math:: g ∘ x = (g\, x_0, \dots, g\, x_{ρ t}) = (h\, x_0, \dots, h\, x_{ρ t}) = h ∘ x,

      so

      .. math:: g\, a = g(t^𝔸 \, x) = t^𝔹 (g ∘ x) = t^𝔹 (h ∘ x) = h(t^𝔸 \,x) = h\, a.

      ☐

**Formalization**. Our formal implementation (in `Lean`_) of :numref:`Obs %s <obs-two>` is described in :numref:`homomorphisms-that-agree-on-a-generating-set`,  and is included in the `birkhoff.lean`_ file of the `lean-ualib`_ library.

.. _obs-three:

.. proof:observation::

   If :math:`A, B` are finite and :math:`X` generates 𝔸, then :math:`|\hom(𝔸, 𝔹)| ≤ |B|^{|X|}`.

   .. container:: toggle
    
      .. container:: header
    
         *Proof*.

      By :ref:`Obs 2 <obs-two>`, a homomorphism is uniquely determined by its restriction to a generating set.

      If :math:`X` generates 𝔸, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\hom(𝔸, 𝔹)| ≤ |B|^{|X|}`. ☐
    
.. _obs-four:

.. proof:observation::

   If :math:`g ∈ \epi (𝔸, 𝔹)`, :math:`h ∈ \hom (𝔸, ℂ)`, and :math:`\ker g ⊆ \ker h`, then

   .. math:: ∃ k ∈ \hom(𝔹, ℂ), \ h = k ∘ g.
    
   .. container:: toggle
    
      .. container:: header
    
         *Proof*.

      We define :math:`k ∈ \hom(𝔹, ℂ)` as follows:

      Fix :math:`b ∈ B`.

      Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} ⊆ A` is nonempty, and since :math:`\ker g ⊆ \ker h`, it is clear that every element of :math:`g^{-1}\{b\}` is mapped by :math:`h` to a single element of :math:`C`.

      Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a ∈ g^{-1}\{b\}`.
   
      For each such :math:`b`, and its associated :math:`c_b`, define :math:`k(b) = c_b`.
   
      The observant reader may have noticed a slight-of-hand in the foregoing "construction" of the function :math:`k`. While it's true that for each :math:`b ∈ B` there exists a :math:`c_b` such that :math:`h(a) = c_b` for all :math:`a ∈ g^{-1}\{b\}`, it's also true that we have no means of producing such :math:`c_b` constructively.
      
      One could argue that each :math:`c_b` is easily computed as :math:`c_b = h(a)` for some (every) :math:`a ∈ g^{-1}\{b\}`. But this requires producing a particular :math:`a ∈ g^{-1}\{b\}` to use as "input" to the function :math:`h`. How do we select such an element from the (nonempty) set :math:`g^{-1}\{b\}`?
      
      We must appeal to the Axiom of :term:`Choice` at this juncture and concede that the function :math:`k` will not be constructively defined. (We have more to say about this in :numref:`Sec %s <basic-facts-in-lean>` when we implement :numref:`Obs %s <obs-four>` in Lean.)  Nonetheless, we forge ahead (nonconstructively) and define :math:`k` as described above, using the Axiom of :term:`Choice` to compute a :math:`c_b` for each :math:`b ∈ B`.
   
      It is then easy to see that :math:`k ∘ g = h`.  Indeed, for each :math:`a ∈ A`, we have :math:`a ∈ g^{-1}\{g(a)\}`, so :math:`k(g(a)) = h(a)` by definition.

      Finally, to prove that :math:`k` is a homomorphism, fix an operation symbol :math:`f ∈ F` and a tuple :math:`b: ρ f → B`; we will show that
      
      .. math:: f^ℂ (k ∘ b) = k (f^𝔹(b)).
         :label: hom1

      Let :math:`a: ρ f → A` be such that :math:`g ∘ a = b`.  Then the left hand side of :eq:`hom1` is :math:`f^ℂ (k ∘ g ∘ a) = f^ℂ (h ∘ a)`, which is equal to :math:`h (f^𝔸 (a))` since :math:`h` is a homomorphism.
   
      Therefore,
   
      .. math:: 
      
         f^ℂ (k ∘ b) &= f^ℂ (k ∘ g ∘ a) = f^ℂ (h ∘ a)\\ 
                 & = h (f^𝔸 (a)) = (k ∘ g)(f^𝔸 (a))\\
                 & = k (f^𝔹 (g ∘ a)) = k (f^𝔹 (b)),

      as desired, where the penultimate equality holds by virtue of the fact that :math:`g` is a homomorphism. ☐

**Formalization**. Our formal implementation (in `Lean`_) of :numref:`Obs %s <obs-four>` is described in :numref:`factoring-homomorphisms`, and is included in the `birkhoff.lean`_ file of the `lean-ualib`_ library.


---------------------------

.. rubric:: Footnotes

.. [1]
   For a brief and gentle introduction to type theory see the `section on axiomatic foundations <https://leanprover.github.io/logic_and_proof/axiomatic_foundations.html?highlight=type#type-theory>`_ in `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_.  Alternatively, viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. [3]
   The term :math:`σ`-**algebra** has a special meaning, different from ours, in other areas of mathematics such as real analysis, probability, and measure theory.

.. [4]
   In retrospect, a more appropriate name for :math:`\mathbf{0} σ` might be :math:`Δ_σ`, or even :math:`=_σ`, but this may lead to conflicts with more standard notational conventions.

.. [5]
   By "the constants on :math:`A`" we mean the **constant operations**; i.e., functions :math:`f: A → A` such that :math:`∀ a ∈ A, f(a) = c`, for some :math:`c ∈ A`.

.. [6]
   The construction of :math:`𝕋_ρ (X)` may seem to be making something out of nothing, but it plays an significant role in the theory.

.. include:: hyperlink_references.rst





.. include:: hyperlink_references.rst
