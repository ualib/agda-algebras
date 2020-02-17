.. File: algebras.lagda.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 11 Feb 2020
.. Updated: 11 Feb 2020
.. Copyright (c) 2019 William DeMeo


.. .. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _algebras:

========
Algebras
========

In this chapter we use the informal language of universal algebra to present foundational definitions and theorems about :term:`subalgebras <subalgebra>`, :term:`terms <term>`, and :term:`clones <clone>`.  In :numref:`Chapters %s <Datatypes for Algebras>`--:numref:`%s <Datatypes for Subalgebras>`, we show how the definitions and results presented in this section can be formalized (or "implemented") in type theory using Agda.

The idea is to demonstrate the power and utility of implementing our mathematical are of expertise in a formal language that supports dependent and inductive types, which are essential for expressing and working with infinite objects in a :term:`constructive` and :term:`computable` way, and for proving properties of these objects.

One goal of our project was to provide, as a "proof of concept" a formal implementation of a deep result in universal algebra. As the focus of this goal, we have chosen what was among the first major results of the theory of universal algebras---namely, the celebrated `HSP Theorem`_ that Garrett Birkhoff proved in 1933. (`The original paper is available online <https://web.archive.org/web/20180330012312/https://pdfs.semanticscholar.org/a282/3f992ea5e2d2a1e989ce01844da71e4ec6a5.pdf>`_.)

A nice (informal) proof of the HSP Theorem appears on pages 106 and 107 of Cliff Bergman's book :cite:`Bergman:2012`. Naturally, the proof relies on many defeinitions and results developed in earlier chapters of the book.  Nonetheless, Cliff's path to a proof of the HSP theorem is the most straightforward and efficient one we know, and we will follow his presentation quite closely.

On the other hand, in order to get as directly as possible to a formal proof of the HSP Theorem, we will extract all the ingredients we need from Bergman's book, and present them as a list of results at the end of this chapter, so that we can more easily try (in :numref:`Chapter %s <basic facts in agda>`) to implement each proof, one-by-one in Agda.

Of course, when we quote or paraphrase a result from Cliff's book, we will include a citation that indicates where the corresponding result is found in the book. When doing so, we will use the acronym :term:`UAFST` to refer to the book.

We owe Cliff a huge debt of gratitude for authoring such a beautiful and constructive (wherever possible) treatment of basic universal algebra.

..  Birkhoff, G. (Oct 1935), "On the structure of abstract algebras" (PDF), Proceedings of the Cambridge Philosophical Society, 31 (4): 433–454, archived from the original (pdf) on 2018-03-30

------------------------------

.. index:: ! graph (of a function)
.. index:: ! idempotent, ! projection
.. index:: operation, arity, image
.. index:: pair: ℕ; ω 

.. _operations:

Operations
-----------

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m: ℕ` and say ":math:`m` has type ℕ." [1]_

In set theory, we typically denote and define natural numbers by :math:`m := \{0, 1, \dots, m-1\}`.  However, it systems based on type theory (such as Agda_ or Lean_), we use a type to denote finite sets, called ``Fin``.  We will define this type precisely later, but for now we simply use the notation :math:`\mathsf{Fin}(m)` to denote the ``m``-element set (for each natural number :math:`m`).  That is, *for now* we let,

.. math:: \mathsf{Fin}(m) := \{0, 1, \dots, m-1\}.

It is sometimes convenient to formally identify a function with its graph.  For example, the function :math:`a: \mathsf{Fin}(m) → A` may be identified with the tuple :math:`(a(0), a(1), \dots, a(m-1)): A^m`.

(Sometimes all these parentheses are unnecessary and we may simply write :math:`a\ i` in place of :math:`a(i)`.)

If :math:`h: A → A` and :math:`a: \mathsf{Fin}(m) → A` are functions, then :math:`h ∘ a: \mathsf{Fin}(m) → A` denotes the composition of :math:`h` with :math:`a`; this is the function that maps each :math:`i < m` to the element :math:`(h ∘ a)(i) = h(a\, i)` of :math:`A`.

We may formally identify the function :math:`h ∘ a: \mathsf{Fin}(m) → A` with its graph, which of course is the :math:`m`-tuple, :math:`(h(a\, 0), h(a\, 1), \dots, h(a\, (m-1)))`.

Suppose :math:`A` is a nonempty set and :math:`n ∈ ℕ` is a natural number. An :math:`n`-**ary operation** on :math:`A` is a function :math:`f: A^n → A` which (for :math:`n>0`) maps each :math:`n`-tuple :math:`(a_0, a_1, \dots, a_{n-1})` in :math:`A^n` to a particular element :math:`f(a_0, a_1, \dots, a_{n-1})` in :math:`A`.  If :math:`n=0`, then :math:`f: () → A` is a function that takes no arguments and returns an element of :math:`A`, so :math:`f` in this case is merely notation for a particular element of :math:`A`.

An operation is called **nullary** (or constant) if its arity is zero. **Unary**, **binary**, and **ternary** operations have arities 1, 2, and 3, respectively.

An operation gives rise to a special kind of :math:`(n+1)`-ary relation, namely

.. math:: Gf := \{(a_0, a_1, \dots, a_{n-1}, b) \in A^{n+1} ∣ b = f(a_0, a_1, \dots, a_{n-1})\},

which is sometimes called the **graph** of :math:`f`.

For two sets :math:`A` and :math:`B`, the collection of all functions :math:`f: B → A` is, for obvious reasons, denoted by :math:`A^B`. When :math:`B = A^n` this is :math:`A^{A^n}`, the collection of all :math:`n`-ary operations on :math:`A`.

If we let :math:`\mathsf{Op}_A` denote the collection of all finitary operations on :math:`A`, then

.. math:: \mathsf{Op}_A = ⋃_{n ∈ ℕ} A^{A^n}.

If :math:`F ⊆ \mathsf{Op}_A` is a set of operations on :math:`A`, let us denote by :math:`F_n` the :math:`n`-ary operations in :math:`F`.

Clearly, :math:`F_n = F ∩ A^{A^n}`. For example, the set of *all* :math:`n`-ary operations on :math:`A` is

.. math:: (\mathsf{Op}_A)_n = \mathsf{Op}_A ∩ A^{A^n} = A^{A^n}.

Given an :math:`n`-tuple :math:`a = (a_0, a_1, \dots, a_{n-1}) ∈ A^n`, we will need a convenient way to refer to the set :math:`\{a_i : 0 ≤ i < n\}` of elements that occur in the tuple without explicitly naming each element in this set.  In fact, we already have notation for this, since an :math:`n`-tuple is actually a function, with domain :math:`\mathsf{Fin}(n) := \{0, 1, \dots, n-1\}`, and image the set of elements occuring in the tuple.  That is, if :math:`a = (a_0, a_1, \dots, a_{n-1})`, then :math:`\mathsf{im} a = \{a_0, a_1, \dots, a_{n-1}\}` (with repeated values included only once). In particular, :math:`|\mathsf{im} a|` is a convenient way to write the number of distinct elements that occur in the tuple :math:`a`.

For example, if :math:`a = (1,1,3)`, then :math:`\mathsf{im} a = \{1, 3\}`, and :math:`|\mathsf{im} a| = 2`.

An operation :math:`f ∈ A^{A^n}` is called **idempotent** provided :math:`f(a, a, \dots, a) = a` for all :math:`a ∈ A`.

Important examples of idempotent operations are the projections. If :math:`k` and :math:`n` are natural numbers with :math:`0 ≤ k < n` then the :math:`k`-**th** :math:`n`-**ary projection** of :math:`A` is denoted by :math:`π^n_k` and defined to be the function that maps :math:`A^n` onto :math:`A` according to the rule :math:`(a_0, \dots, a_{n-1}) ↦ a_k`.

---------------------------

.. _general-composition-of-operations:

General composition
-------------------

In universal algebra we mainly deal with *finitary* operations in :cat:`Set` (the category of sets).  We will identify the :math:`\mathsf{ntuple}` type with the function type :math:`\mathsf{Fin}(n) →  A`.  Thus, the type of :math:`n`-ary operations on :math:`A` is :math:`(\mathsf{Fin}(n) → A) → A`.  Evaluating such an operation at the tuple :math:`a: \mathsf{Fin}(n) → A` is simply function application, expressed by the usual rule (sometimes called "implication elimination" or "modus ponens").

Letting :math:`a_i` denote the value of :math:`a` at "input" (or "index") :math:`i < n`, and identifying :math:`a` with it's graph (the tuple :math:`(a_0, \dots, a_{n-1})`), we have :math:`f\,a = f(a_0, \dots, a_{n-1})`, for each  :math:`f: (\mathsf{Fin}(n) → A) → A`. 

As above, we denote and define the collection of all finitary operations on :math:`A` by :math:`\mathsf{Op}(A) = A^{A^n} = ⋃_{n<ω} ((\mathsf{Fin}(n) → A) → A)`.

Let us develop a general formulation of composition of operations that is more elegant and computationally practical than the standard formulation.

Recall, the standard description of operation composition: if :math:`f : (\mathsf{Fin}(n) → A) → A` is an :math:`n`-ary operation and :math:`g_i : (\mathsf{Fin}(k_i) → A) → A` is a :math:`k_i`-ary operation for each :math:`0≤ i < n`, then the **composition of** :math:`f` **with** :math:`(g_0, \dots, g_{n-1})`, denoted :math:`f ∘ (g_0, \dots, g_{n-1})`, is usually expressed as follows: for each :math:`n`-tuple of tuples,

.. math:: ((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})): A^{k_0} × \cdots × A^{k_{n-1}},
   :label: args

.. math:: f & ∘ (g_0, \dots, g_{n-1})((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\
                &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).

This notation is quite ugly and, even worse, it lends itself poorly to computation. Let us try to clean it up.

Consider the :math:`n`-tuple :math:`(g_0, \dots, g_{n-1})` of operations from :math:`\mathsf{Op}(A)`.

Let :math:`g: ∏_{(i:n)} (\mathsf{Fin}(k_i) → A) → A)` be the function with domain the set :math:`n = \{0,1,\dots, n-1\}`, codomain :math:`\mathsf{Op}(A)`, and defined for each :math:`0 ≤ i < n` by :math:`g\,i = g_i`.

Let :math:`a: ∏_{(i:n)} (\mathsf{Fin}(k_i) → A)` be such that for each :math:`0≤ i < n` we have a function :math:`a\,i: \mathsf{Fin}(k_i) → A` which is defined for each :math:`0≤ j < k_i` by :math:`a\,i\,j = a_{ij}`.
  
Then the :math:`n`-tuple of arguments in expression :eq:`args` above can be identified with the :math:`n`-tuple :math:`a = (a\,0, \dots, a\,(n-1))` of functions.

Using the :ref:`fork` and :ref:`eval` operators (defined in :ref:`general-composition`), it is not hard to define general composition using these operators along with dependent types.

If :math:`g: ∏_{(i:n)} ((\mathsf{Fin}(k_i) → A) → A)` and :math:`a: ∏_{(i:n)}(\mathsf{Fin}(k_i) → A)`, then 

.. math:: \mathsf{fork} \, g\, a: ∏_{(i:n)}\bigl((\mathsf{Fin}(k_i) → A) → A\bigr) \times (\mathsf{Fin}(k_i) → A)

is the function that maps each :math:`0≤ i < n` to the pair

.. math:: (\mathsf{fork} \, g\, a)\, i = (g\,i, a\,i): \bigl((\mathsf{Fin}(k_i) → A) → A\bigr) × (\mathsf{Fin}(k_i) → A).

Applying :math:`g\,i` to :math:`a\,i` with the :math:`\mathsf{eval}` function, we have

.. math:: \mathsf{eval} \, (\mathsf{fork} \, g\, a)\, i = \mathsf{eval} \, (g\,i, a\,i) = (g\,i)(a\,i).

Observe that the codomain :math:`A` of the function :math:`\mathsf{eval}\, (\mathsf{fork} \, g\, a)` does not depend on :math:`i`, so the type :math:`∏_{(i:n)} A` simplifies to :math:`\mathsf{Fin}(n) → A` in this case, resulting in the typing judgment, :math:`\mathsf{eval} \, (\mathsf{fork} \, g\, a): \mathsf{Fin}(n) → A`.

.. On the other hand,

.. .. math:: \mathsf{eval}\,\mathsf{fork} \, g: ∏_{(i:n)}  (k_i → A) → (\mathsf{Fin}(n) → A).

Thus, if

  :math:`f: (\mathsf{Fin}(n) → A) → A` (an :math:`n`-ary operation) and 
  
  :math:`g: ∏_{(i:n)} ((\mathsf{Fin}(k_i) → A) → A)` (an :math:`n`-tuple of operations), then we 
  
  denote and define the **composition of** :math:`f` **with** :math:`g` as follows:

.. math:: f\, \mathsf{comp}\, g := f \, \mathsf{eval} \, \mathsf{fork} \, g: ∏_{(i:n)}((\mathsf{Fin}(k_i) → A) → A).

Indeed, if :math:`a: ∏_{(i:n)}(\mathsf{Fin}(k_i) → A)`, then :math:`\mathsf{eval} \, \mathsf{fork} \, g \, a` has type :math:`\mathsf{Fin}(n) → A`, which is the domain type of :math:`f`; therefore, :math:`f\, \mathsf{eval} \, \mathsf{fork} \, g \, a` has type :math:`A`, as desired.

.. _greater-generality:

Greater generality
~~~~~~~~~~~~~~~~~~

In the last section we looked at an operation :math:`f` on a set :math:`A`. We took the domain of :math:`f` to be :math:`\mathsf{Fin}(n) → A` (the type of :math:`n`-tuples over :math:`A`) for some :math:`n`.  In particular, we assumed that :math:`A` was a set, and that the arity of :math:`f` was some natural number, say, :math:`n`. Although this is the standard setup in universal algebra.  However, it is not necessary to be so specific about the arities, domains, and codomains of operations.

In this section we start with two types :math:`α` and :math:`γ` and consider :math:`γ`-**ary operations on** :math:`α`---e.g., :math:`f: (γ → α) → α`---and show how to express composition of operations in this general context.

Suppose that for each :math:`i: γ` we have a type :math:`γ_i` and an operation :math:`g_i` of type :math:`(γ_i → α) → α` on :math:`α`.

Denote by :math:`G` the ":math:`γ`-tuple" of these operations; that is, for each :math:`i: γ` the ":math:`i`-th component" of :math:`G` is 
:math:`G\, i = g_i`. Evidently, this results in the typing judgment,

.. math:: G: ∏_{(i:γ)} ((γ_i → α) → α).

Even in this more general context, we can still use the fork and eval maps introduced in the appendix (see :ref:`general-composition`) to express composition of operations.
Indeed, we *define* the **composition of** :math:`f` **with** :math:`G` to be

.. math:: f \, \mathsf{eval} \, \mathsf{fork} \, G.

Let us adopt the following convenient notation:

  *Denote by* :math:`\mathsf{comp}` *the general composition operation* :math:`\mathsf{eval} \, \mathsf{fork}`.

Then, given :math:`f: (γ → α) → α` and :math:`G: ∏_{(i:γ)} ((γ_i → α) → α)`, the **general composition of** :math:`f` **with** :math:`G` is :math:`f\, \mathsf{comp}\, G := f \, \mathsf{eval} \, \mathsf{fork} \, G`.  Evidently, this yields the typing judgment,

.. math:: f\, \mathsf{comp}\, G : \bigl(∏_{(i:γ)}(γ_i → α)\bigr) → α.

Indeed, if :math:`a: ∏_{(i:γ)}(γ_i → α)`, then for each :math:`i:γ` we have,

.. math:: a\, i : γ_i → α \quad \text{ and } \quad  G\, i : (γ_i → α) → α,

so evaluation of :math:`\mathsf{comp}\, G \, a` at a particular :math:`i: γ` is simply function application. That is,

.. math:: \mathsf{comp} \,G \, a \, i:= \mathsf{eval} \, \mathsf{fork} \, G \, a \, i = (G\, i)(a\, i): α.

Thus, :math:`\mathsf{comp}\, G \, a` has type :math:`γ → α`, which is precisely the domain type of :math:`f`.

To summarize, we have the following typing judgments:

.. math:: \mathsf{comp}\, G \, a : γ → α \quad \text{ and } \quad f: (γ → α) → α,

whence :math:`f \, \mathsf{comp}\, G \, a: α` is well-typed.


----------------------------------------

.. index:: signature, arity

.. _signatures:

Signatures
----------

(Our formal `Agda`_ implementation of the concept of signature is described in :numref:`signatures in agda`.)

Classically, a **signature** is a pair :math:`(F, ρ)` consisting of a set :math:`F` of operation symbols and an "arity" function :math:`ρ: F → ℕ`.

For each operation symbol :math:`f ∈ F`, the value :math:`ρ f` is the **arity** of :math:`f`. (Intuitively, the arity can be thought of as the "number of arguments" that :math:`f` takes as "input".)

If the arity of :math:`f` is :math:`n`, then we call :math:`f` an :math:`n`-**ary** function. In case :math:`n` is 0, 1, 2, or 3, we call the function "nullary", "unary", "binary", or "ternary," respectively.

If :math:`A` is a set and :math:`f` is a :math:`ρ f`-ary function on :math:`A`, then we often write :math:`f: A^{ρf} → A` to indicate this.

On the other hand, the arguments of such a function form a :math:`ρ f`-tuple, :math:`(a_0, a_1, \dots, a_{ρf -1})`, which may be viewed as the graph of the function :math:`a: \mathsf{Fin}(ρf) → A`, where :math:`a\, i = a_i`.

Thus, by identifying the :math:`ρ f`-th power :math:`A^{ρf}` with the type :math:`\mathsf{Fin}(ρ f) → A` of functions from :math:`\{0, 1, \dots, ρ f-1\}` to :math:`A`, we identify the function type :math:`A^{ρ f} → A` with the function (or "functional") type :math:`(\mathsf{Fin}(ρf) → A) → A`. [2]_

**Example**.

   Suppose 

     :math:`g : (\mathsf{Fin}(m) → A) → A` is an :math:`m`-ary operation on :math:`A`, and 
   
     :math:`a : \mathsf{Fin}(m) → A` is an :math:`m`-tuple on :math:`A`.

   Then :math:`g\, a = g(a\, 0, a\, 1, \dots, a\, (m-1))` has type :math:`A`.

   Suppose

     :math:`f : (\mathsf{Fin}(ρf) → B) → B` is a :math:`ρf`-ary operation on :math:`B`,

     :math:`a : \mathsf{Fin}(ρf) → A` is a :math:`ρf`-tuple on :math:`A`, and

     :math:`h : A → B`.
      
   Then :math:`h ∘ a : \mathsf{Fin}(ρf) → B` and :math:`f (h ∘ a) : B`.

It is important to be familiar with the classical notions of signature and arity, since these are used at the present time by virtually all algebraists.

.. In :numref:`Chapter %s <postmodern-algebra>` we give alternative, category theoretic definitions of these concepts and show how this alternative presentation can often simplify implementation of the mathematics in :term:`type theory`.

--------------------------

.. index:: ! pair: algebra; algebraic structure
.. index:: ! σ-algebra, ! arity, ! trivial algebra, ! reduct

.. _algebraic-structures:

Algebraic Structures
---------------------

(Our formal `Agda`_ implementation of the concept of algebraic structure is described in :numref:`Chapter %s <algebras in agda>`.)

Our first goal is to develop a working vocabulary and formal library for classical (single-sorted, set-based) universal algebra.  In this section we define the main objects of study. 

An **algebraic structure** (or **algebra**) is a pair :math:`𝑨 = ⟨A, F⟩` where :math:`A` is a *nonempty* set and :math:`F = \{f_i: i ∈ I\}` is a collection of finitary operations on :math:`A`. That is, for each :math:`i∈ I` there exists an :math:`n ∈ ℕ` such that :math:`f_i: A^n → A`. The number :math:`n` is called the **arity** of the operation :math:`f_i`.

**Example**.

  If :math:`A=ℝ` and :math:`f: ℝ × ℝ → ℝ` is the map that takes each pair :math:`(a, b) ∈ ℝ × ℝ` to the number :math:`f(a,b) = a+b ∈ ℝ`, then :math:`⟨A, \{f\}⟩` is an example of an algebra with a single binary operation. In such cases, we often simplify the notation and write :math:`⟨A, f⟩` in stead of :math:`⟨A, \{f\}⟩`.

  An algebra is **finite** if :math:`|A|` is finite, and is called **trivial** if :math:`|A| = 1`.

  Given two algebras :math:`𝑨` and :math:`𝑩`, we say that :math:`𝑩` is a **reduct** of :math:`𝑨` if both algebras have the same universe and :math:`𝑩` can be obtained from :math:`𝑨` by removing  operations.

.. index:: ! operation symbol, ! arity, ! interpretation, ! signature, ! similarity type

A better approach
~~~~~~~~~~~~~~~~~

.. todo:: remove redundancies in this section
	  
We start with a set :math:`F` and call the members of :math:`F` "operation symbols."  An **operation symbol** is simply an object that has an associated **arity**.

We denote the arity of :math:`f` by :math:`ρ \,f`, where :math:`ρ: F → N` is an "arity function" that maps :math:`F` into some "arity type" :math:`N`.  Usually we take the arity type to be :math:`ℕ`, so that the arity of each symbol is a natural number, :math:`N = ℕ`, and :math:`ρ \, f ∈ ℕ` for all :math:`f∈ F`. 

A pair :math:`(F, ρ)` consisting of a set :math:`F` of operation symbols and an **arity function** :math:`ρ: F → N` is called a **signature** (or **similarity type**).

An **algebraic structure** (or **algebra**) in the signature :math:`σ = (F, ρ)` is denoted by :math:`𝑨 = ⟨A, F^𝑨⟩` and consists of 

  #. :math:`A` := a set, called the **carrier** (or **universe**) of the algebra,
  #. :math:`F^𝑨 = \{ f^𝑨 ∣ f ∈ F, \ f^𝑨 : (\mathsf{Fin}(ρ f) → A) → A \}` is a collection of operations on :math:`A`,
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝑨`.

Note that to each operation symbol :math:`f∈ F` corresponds an operation :math:`f^𝑨` on :math:`A` of arity :math:`ρ f`; we call this :math:`f^𝑨` the **interpretation** of :math:`f` in :math:`𝑨`.

We call an algebra in the signature :math:`σ` a :math:`σ`-**algebra** (although this is not standard). [3]_ 

..
   **Example**.

     Consider the set of integers :math:`ℤ` with operation symbols :math:`F = \{0, 1, -(\,), +, ⋅\}`, which have respective arities :math:`\{0, 0, 1, 2, 2\}`.

     The operation :math:`+^ℤ` is the usual binary addition, while :math:`-^ℤ(\,)` is negation, which takes the integer :math:`z` to :math:`-^ℤ(z) = -z`.

     The constants :math:`0^ℤ` and :math:`1^ℤ` are nullary operations. Of course we usually just write :math:`+` for :math:`+^ℤ`, etc.

   .. More :ref:`examples of algebraic structures <examples-of-algebras>` that have historically played a central role in mathematics over the last century (e.g., groups, rings, modules) appear in the appendix.

   Some of the renewed interest in universal algebra focuses on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`Adamek:2011`, :cite:`Behrisch:2012`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`Meinke:1992`). These are natural generalizations that we plan to incorporate in our development later.

.. (See :numref:`Chapter %s <postmodern-algebra>`.)

---------------------------

.. index:: ! subuniverse, ! subalgebra
.. index:: 𝖲(𝑨)
.. index:: 𝖲𝗀

.. _subalgebras:

Subalgebras
-------------

This section introduces two important concepts in universal algebra, **subuniverse** and **subalgebra**.

.. A **subuniverse** of an algebra :math:`𝑨 = ⟨A, F^𝑨⟩` is a subset :math:`B ⊆ A` that is closed under the operations in :math:`F^𝑨`.

Suppose :math:`𝑨 = ⟨A, F^𝑨⟩` is an algebra. Recall, the (nonempty) set :math:`A` is called the **universe** of 𝑨.

We call a subset :math:`B ⊆ A` **closed under** (the operations in) :math:`F^𝑨` if for each :math:`f ∈ F` and all :math:`b_0, \dots, b_{ρf-1} ∈ B` we have :math:`f^𝑨(b_0, \dots, b_{ρ f-1}) ∈ B`.  Equivalently,

.. math:: ∀ f ∈ F,\ ∀ b: \mathsf{Fin}(ρ f) → B, \ (f^𝑨 \, b) ∈ B`.

If a subset :math:`B ⊆ A` is closed under :math:`F^𝑨`, then we call :math:`B` a **subuniverse** of :math:`𝑨`.

If :math:`B ≠ ∅` is a subuniverse of 𝑨, and if we let :math:`F^𝑩 = \{ f^𝑨 ↾ B : f ∈ F \}`, then :math:`𝑩 = ⟨ B, F^𝑩 ⟩` is an algebra, called a **subalgebra** of 𝑨.

.. Equivalently, if :math:`B ≠ ∅` is a subuniverse of 𝑨 and :math:`F^{𝑩|_A} = \{f^𝑨|_B ∣ f ∈ F\}` is the set of basic operations of 𝑨 restricted to the set :math:`B`, then :math:`𝑩 = ⟨B, F^{𝑩|_A}⟩` is a **subalgebra** of 𝑨.

Conversely, all subalgebras are of this form.

If 𝑩 is a subalgebra of 𝑨, we denote this fact by :math:`𝑩 ≤ 𝑨`. Similarly, we write :math:`B ≤ 𝑨` if :math:`B` is a subuniverse of :math:`𝑨`. 

  *The empty set is a subuniverse of every algebra, but the universe of an algebra is never empty*.

In other terms, if :math:`𝖲(𝑨)` denotes the collection of all subalgebras of :math:`𝑨`, then 

.. math:: 𝖲 (𝑨) = \{⟨B, F^𝑩⟩ : B ≤ 𝑨 \text{ and } B ≠ ∅\}.

It is obvious that the intersection of subuniverses is again a subuniverse. Nevertheless, we will record this observation below (see :numref:`Observation %s <obs 5>`).

.. index:: subuniverse generation

.. _subuniverse-generation:

Subuniverse generation
~~~~~~~~~~~~~~~~~~~~~~

As above :math:`𝖲(𝑨)` denotes the collection of all subalgebras of 𝑨.  If 𝑨 is an algebra and :math:`A_0 ⊆ A` a subset of the universe of 𝑨, then the **subuniverse of** 𝑨 **generated by** :math:`A_0`, denoted by :math:`\mathsf{Sg}^𝑨 (A_0)` or :math:`⟨A_0⟩`, is the smallest subuniverse of 𝑨 containing the set :math:`A_0`.  Equivalently, 

.. math:: \mathsf{Sg}^{𝑨}(A_0)  =  ⋂ \{ U ∈ 𝖲 (𝑨) ∣ A_0 ⊆ U \}.
  :label: SgDef

We can also use recursion to define the **subuniverse of** 𝑨 **generated by a set** and prove that this new definition is equivalent to the one given by :eq:`SgDef`.  We will do this below (see :numref:`Observation %s <obs 2>`).

---------------------------

.. index:: ! subdirect product

.. _subdirect-products:

Subdirect products
-------------------

If :math:`k, n ∈ ℕ`, if :math:`A = (A_0, A_1, \dots, A_{n-1})` is a list of sets, and if :math:`σ : \mathsf{Fin}(k) → n` is a :math:`k`-tuple, then a relation :math:`R` over :math:`A` with scope :math:`σ` is a subset of the Cartesian product :math:`A_{σ(0)} × A_{σ(1)} × \cdots × A_{σ(k-1)}`.

Let :math:`F` be a set of operation symbols and for each :math:`i<n` let :math:`𝑨_i = ⟨ A_i, F ⟩` be an algebra of type :math:`F`. If :math:`𝑨 = ∏_{i<n}𝑨_i` is the product of these algebras, then a relation :math:`R` over :math:`𝑨` with scope :math:`σ` is called **compatible with** 𝑨 if it is closed under the basic operations in :math:`F`. In other words, :math:`R` is compatible if the induced algebra :math:`ℝ = ⟨ R, F ⟩` is a subalgebra of :math:`\prod_{j<k} 𝑨_{σ(j)}`.

If :math:`R` is compatible with the product algebra and if the projection of :math:`R` onto each factor is surjective, then :math:`ℝ` is called a **subdirect product** of the algebras in the list :math:`(𝑨_{σ(0)}, 𝑨_{σ(1)}, \dots, 𝑨_{σ(k-1)})`; we denote this situation by writing :math:`ℝ ≤_{\mathrm{sd}} \prod_{j< k} 𝑨_{σ(j)}`.

**Formalization**. (not yet implemented)

.. todo:: implement subdirect product in Agda

-----------------------------------------------

.. index:: ! homomorphism
.. index:: ! epimorphism, ! monomorphism, ! automorphism

.. _homomorphisms:

Homomorphisms
-------------

Let :math:`𝑩 = ⟨ B, F^𝑩 ⟩` and :math:`𝑪 = ⟨ C, F^𝑪 ⟩` be algebras of the same signature, and let :math:`h: B → C` be a function (e.g., on sets).

Take an operation symbol :math:`f ∈ F`, and suppose that for all :math:`ρ f`-tuples :math:`b: \mathsf{Fin}(ρ f) → B` of :math:`B` the following equation holds:

.. math:: h (f^𝑩 \, b) = f^𝑪 (h ∘ b).

Then :math:`h` is said to **respect the interpretation of** :math:`f`.

If :math:`h` respects the interpretation of every :math:`f ∈ F`, then we call :math:`h` a **homomorphism** from 𝑩 to 𝑪, and we write :math:`h ∈ \mathsf{Hom}(𝑩, 𝑪)`, or simply, :math:`h: 𝑩 → 𝑪`.

A homomorphism :math:`h: 𝑩 → 𝑪` is called an **epimorphism** if for every algebra :math:`𝔻` and pair :math:`g_1, g_2: 𝑪 → 𝔻` of homomorphisms, the equation :math:`g_1 ∘ h = g_2 ∘ h` implies :math:`g_1 = g_2`. We often write :math:`h: 𝑩 ↠ 𝑪`, and we say ":math:`h` is **epi**" and ":math:`h` maps 𝑩 **onto** 𝑪," in this case.

A homomorphism :math:`h: 𝑩 → 𝑪` is called a **monomorphism** if for every algebra :math:`𝑨` and every pair :math:`g_1, g_2: 𝑨 → 𝑩` of homomorphisms, the equation :math:`h ∘ g_1 = h ∘ g_2` implies :math:`g_1 = g_2`.  We sometimes write :math:`h: 𝑨 ↣ 𝑩`, and we say ":math:`h` is **mono**" and ":math:`h` maps 𝑩 **into** 𝑪," in this case.

**Notation**.

  We adopt the following notation. If :math:`𝑩` and :math:`𝑪` are algebras in the same signature, then

    + :math:`\mathsf{Hom}(𝑩, 𝑪) =` the set of homomorphisms from 𝑩 to 𝑪.
    + :math:`\mathsf{Epi}(𝑩, 𝑪) =` the set of epimorphisms from 𝑩 onto 𝑪.
    + :math:`\mathsf{Mono}(𝑩, 𝑪) =` the set of monomorphisms from 𝑩 into 𝑪.
    + :math:`\mathsf{Aut}(𝑩, 𝑪) =` the set of automorphisms from 𝑩 into and onto 𝑪.

.. **Formalization**. Our formal implementation (in `Agda`_) of these concepts is described in  :numref:`subalgebras in agda`, :numref:`basic facts in agda`, :numref:`factoring homomorphisms`, and is included in the `birkhoff.agda`_ and `subuniverse.agda`_ files of the `agda-ualib`_ library.

----------------------


.. index:: ! clone
.. index:: ! clone of projections
.. index:: ! clone of polynomial operations
.. index:: ! clone of term operations

.. _clones:

Clones
------

.. **Formalization**. For a description of our implementation of the objects described in this section, see :numref:`Chapter %s <clones-and-terms-in-agda>`.

An **operational clone** (or just **clone**) on a nonempty set :math:`A` is a set of operations on :math:`A` that contains the projection operations and is closed under general composition.

Let :math:`𝖢 A` denote the collection of all clones on :math:`A`.

The smallest clone on :math:`A` is the **clone of projections**, which we denote and define as follows:

.. math:: \mathsf{Proj}  A = ⋃_{i < n < ω}  \{π^n_i : ∀ a ∈ A^n,\ π^n_i\, a = a(i)\}.

Let us set down some conventions that will help simplify notation.  Recall, the natural number :math:`k< ω` may be constructed as (or at least identified with) the set :math:`\{0,1,\dots, k-1\}`, and this will be helpful here.

For each :math:`k< ω`, denote and define the tuple :math:`\pi^k: (\mathsf{Fin}(k) → A) → A` of all :math:`k`-ary projections on :math:`A` as follows: for each :math:`0≤ i < k`,  :math:`π^k(i)` is the :math:`i`-th :math:`k`-ary projection operation that takes each :math:`k`-tuple :math:`a: \mathsf{Fin}(k) → A` to its entry at index :math:`i`:

.. math:: π^k (i) a = a(i).

Observe that if :math:`f: (\mathsf{Fin}(k) → A) → A` is a :math:`k`-ary operation on :math:`A`, then 

The **clone of term operations** of a σ-algebra 𝑨 is the smallest clone on :math:`A` containing the basic operations of 𝑨; this is
denoted and defined by

.. math:: \mathsf{Clo}(F^𝑨) = ⋂ \{ U ∈ 𝖢 A ∣ F^𝑨 ⊆ U\}.

The set of :math:`n`-ary members of :math:`\mathsf{Clo}(F^𝑨)` is sometimes denoted by :math:`\mathsf{Clo}_n (F^𝑨)` (despite the fact that the latter is clearly not a clone).

The **clone of polynomial operations** (or **polynomial clone**) of a σ-algebra 𝑨 is denoted by :math:`\mathsf{Pol} (F^𝑨)` and is defined to be the clone generated by the collection consisting of the basic operations (i.e., :math:`F^𝑨`) of 𝑨 along with the **constants** on :math:`A`. [4]_

The set of :math:`n`-ary members of :math:`\mathsf{Pol} (F^𝑨)` is sometimes denoted by :math:`\mathsf{Pol}_n (F^𝑨)`. 

The clone :math:`\mathsf{Clo}(F^𝑨)` is associated with the algebra :math:`𝑨` only insofar as the former is constructed out of the basic operations of 𝑨 and the set :math:`A` on which those operations are defined.  However, all that is required when defining a clone is a set :math:`A` and some collection :math:`F` of operations defined on :math:`A`; from only these ingredients, we can construct the clone generated by :math:`F`, which we denote by :math:`\mathsf{Clo}(F)`.

Thus

  *the clone of terms operations can be implemented as an inductive type*.
  
We will make this precise below (see :numref:`Observation %s <obs 7>` and :term:`UAFST` Thm 4.32).

------------------------

.. index:: ! term, ! term algebra, ! σ-term 

.. _terms:

Terms
-----

.. **Formalization**. For a description of our implementation of the objects described in this section, see :numref:`Chapter %s <clones-and-terms-in-agda>`.

Fix a :term:`signature` :math:`σ = (F, ρ)`, let :math:`X` be a set of **variables**, and assume :math:`X ∩ F = ∅`.

By a **word** on :math:`X ∪ F` we mean a nonempty, finite sequence of members of :math:`X ∪ F`, and we will denote the concatenation of such sequences by simple juxtaposition.

Let :math:`F_0` denote the set of nullary operation symbols. We define by induction on :math:`n` the sets :math:`T_n` of **terms on** :math:`X ∪ F` as follows (cf. :term:`UAFST` Def 4.19):

.. math::      T_0 &= X ∪ F_0;\\
           T_{n+1} &= T_n ∪ \{ f\, s ∣ f ∈  F, \ s: \mathsf{Fin}(ρf) → T_n \},

and we define the collection of **terms of signature** :math:`σ` **over** :math:`X` by :math:`T_σ(X) = ⋃_{n < ω}T_n`.

By a :math:`σ`-**term** we mean a term in the signature :math:`σ`. 

The definition of :math:`T_σ (X)` is recursive, indicating that

  *terms can be implemented as an inductive type*.

We will confirm this in :numref:`Chapter %s <datatypes for terms>` when we implement terms using an inductive type.

Before doing so, let us impose an algebraic structure on :math:`T_σ (X)`, and then state and prove some basic facts about this important algebra. These will be formalized in :numref:`Chapter %s <datatypes for terms>`, giving us a chance to show off inductively defined types in Agda.

If :math:`t` is a term, then the **height** of :math:`t` is denoted by :math:`|t|` and defined to be the least :math:`n` such that :math:`t ∈ T_n`. The height of is a useful index for recursion and induction.

.. Let :math:`ρ: T_σ(X) → ℕ` denote the **arity function for term**, defined as follows:
.. .. math:: ρ t = \min \{n ∣t ∈ T_n,\; 0≤ n < ω\}.

Notice that :math:`T_σ (X)` is nonempty iff :math:`X ∪ F_0` is nonempty.

If :math:`T_σ (X)` is nonempty, then we can impose upon it an algebraic structure, which we denote by :math:`𝑻_σ (X)` (or :math:`𝑻` when :math:`σ` and :math:`X` are clear from context).

We call :math:`𝑻_σ (X)` the **term algebra in the signature** :math:`σ` **over** :math:`X` (or, the :math:`σ`-**term algebra over** :math:`X`); it is constructed as follows:

  For every basic operation symbol :math:`f ∈ F` let :math:`f^𝑻` be the operation on :math:`T_σ (X)` that maps each tuple :math:`s: \mathsf{Fin}(ρ f) → T_σ (X)` to the formal term :math:`f\,s`; define :math:`𝑻_σ(X)` to be the algebra with universe :math:`T_σ (X)` and basic operations :math:`\{f^𝑻 | f ∈ F\}`. [5]_


.. _essential arity:

Essential arity
~~~~~~~~~~~~~~~~~~~

The definition of arity of an operation or term is a bit nuanced as the next example demonstrates.

**Example**.

  Suppose 𝑓 is a binary term, and 𝑝 and 𝑞 are ternary terms.

  What is the arity of the following term?

  .. math:: 𝑡(𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧) = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))
     :label: arity1

  On the face of it, it seems safe to say that 𝑡 has arity 6, since it is expressible as a function of 6 variables.

  But what if we decided to throw in some useless (or "dummy") variables, like so,

  .. math:: t'(𝑢', 𝑣', 𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧, 𝑧') = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))?
     :label: arity2

  And what happens if :math:`𝑝(𝑥, 𝑦, 𝑧) = 𝑧`, so that 𝑝 depends on just one of its arguments? Then we could replace it with :math:`𝑝'(𝑧) = 𝑝(𝑥, 𝑦, 𝑧)`, and 𝑡 could be expressed as,

  .. math:: 𝑡''(𝑢, 𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))).
     :label: arity3
	     
  The respective arities of :math:`𝑡, 𝑡'` and :math:`𝑡''` are 6, 9, and 5, yet :eq:`arity1`--:eq:`arity3` merely give three different ways to present the term :math:`𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))`.
   
As the example demonstrates, the notion of arity of a term is not uniquely defined (modulo equivalence of terms). As such, it is sometimes useful to speak of the **essential arity** of a term, which is defined to be the minimum number of variables required to express that term; it should be clear that this is equal to the number of arguments with respect to which the term is not constant.

**Example**.

  It is impossible to know the essential arity of a term until we know that of each of its subterms.

  Picking up where we left off in the previous example, suppose 𝑓 depends on both of its arguments and :math:`𝑞(𝑢, 𝑣, 𝑤) = 𝑓(𝑣, 𝑤)`. Then 𝑡 is expressible as

  .. math:: s(𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑓(𝑣, 𝑤))

  and we finally see the lower bound on the number of variables required to express 𝑡, namely 4.  Therefore, 𝑡 has essential arity 4.


.. index:: interpretation (of a term), ! arity (of a term)

.. _interpretation of terms:

Interpretation of terms
~~~~~~~~~~~~~~~~~~~~~~~~

..  and let :math:`T_n := T_σ(X_n)` be the subalgebra of :math:`T_σ(X_ω)` generated by :math:`X_n`.  Then, :math:`T_0 ⊆  T_1 ⊆ T_2 ⊆ \cdots` and :math:`T_σ(X_ω) = ⋃_{n<ω}  T_n`.

We denote and define the set :math:`X := \{x_0,x_1,\dots \}` of variable symbols, and for each natural number :math:`n` we let :math:`X_n:=\{x_0,x_1,\dots, x_{n-1}\}`.

Let :math:`σ = (F, ρ)` be a signature, :math:`𝑨` a :math:`σ`-algebra, and :math:`𝑻` the :math:`σ`-term algebra over :math:`X`; that is, 

.. math:: 𝑨 := ⟨A, F^𝑨⟩ \quad \text{ and } \quad 𝑻 := ⟨T_σ(X), F^𝑻⟩. 

Each operation symbol :math:`f ∈ F` gives rise to

#.  a :math:`ρ f`-ary operation on :math:`T_σ(X)`, denoted by :math:`f^𝑻`, which maps each :math:`ρ f`-tuple :math:`s: \mathsf{Fin}(ρ f) → T_σ(X)` to the formal term :math:`f \,s` in :math:`T_σ(X)`, and

#.  a :math:`ρ f`-ary operation on :math:`A`, denoted by :math:`f^𝑨`, which maps each :math:`ρ f`-tuple :math:`a: \mathsf{Fin}(ρ f) → A` to the element :math:`f^𝑨 \,a` in :math:`A`. The operation :math:`f^𝑨` is called the **interpretation of** :math:`f` **in the algebra** :math:`𝑨`.  

In the present section we explain how to define the interpretation of a :math:`σ`-term in a :math:`σ`-algebra.

As usual, for each :math:`0<n<ω` we identify the :math:`n`-tuple :math:`(x_0, x_1, \dots, x_{n-1})` with the function :math:`x: \mathsf{Fin}(n) → X_n` defined by :math:`x\, i = x_i` :math:`(0≤i<n)`.

Recall, a term :math:`t` is either a variable, say, :math:`t = x`, or has the form :math:`t = f \,s` for some operation symbol :math:`f ∈ F`, and some :math:`ρ f`-tuple :math:`s: \mathsf{Fin}(ρ f) → T_σ (X)` of terms.

.. and suppose :math:`|t| = n`.
..  : (\mathsf{Fin}(n) → X_n) → T_n` be an :math:`n`-ary term. 

Let :math:`t ∈ T_σ(X)` be a term. Define the **operation** :math:`t^𝑨` **on** :math:`A` by recursion on the :term:`height` :math:`|t|` of :math:`t` as follows: for each tuple :math:`a: X → A` of :math:`A`, 

#. (:math:`|t| = 0`) if :math:`t` is the variable :math:`x_i ∈ X`, then :math:`t^𝑨 \, a = π^X_i\, a = a\, i`,
#. (:math:`|t| = n+1`) if :math:`t = f\, s` where :math:`f ∈ F` is an operation symbol and :math:`s: \mathsf{Fin}(ρ f) → T_n` is a tuple of terms whose heights are at most :math:`n` (i.e., :math:`∀ i < ρf, |s\, i| ≤ n`), then :math:`t^𝑨 = f^𝑨 \, s^𝑨`.
 
.. .. Let :math:`X_ω := \{x_0, x_1, \dots\}` be a collection of variables and define :math:`X_n:=\{x_0, x_1, \dots, x_{n-1}\}`.


..  **Definition**. UAFST 4.31

      Let 𝑿 be an infinite set (of variables), and let 𝑨 = ⟨𝐴,...⟩ be an algebra of signature :math:`S`.

      .. , and let 𝑐 : ω → 𝑿 be an injective function. (We might call 𝑐 a "choice function" or "indexing function".)

      If :math:`t` is a :math:`(ρ t)`-ary term symbol in the signature :math:`S`, and if we select a :math:`(ρ t)`-tuple of variables, say :math:`x : (ρ t) → X`, then the term associated with the symbols :math:`t` and :math:`x` is :math:`t(x)`.

      The **interpretation** of :math:`t(x)` in 𝑨, often denoted by :math:`t^𝑨(x)`, is the :math:`(ρ t)`-ary operation on :math:`A` defined by recursion on the structure of :math:`t`, as follows:

	#. if :math:`t(x)` is simply the variable :math:`x i ∈ X`, and if 𝑎 is a :math:`(ρ t)`-tuple of :math:`A`, then :math:`t^𝑨(a) = a i`; that is, :math:`t^𝑨(a)` is the projection of the input tuple onto its :math:`i`-th coordinate.

	#. if :math:`t = 𝓸 𝑓`, where 𝓸 is a basic operation symbol with interpretation :math:`𝓸^𝑨` in 𝑨 and :math:`𝑓 : (ρ 𝓸) →` Term is a (ρ 𝓸)-tuple of terms, each with interpretation :math:`(𝑓 i)^𝑨`, then :math:`t^𝑨(𝑓)` is :math:`𝓸^𝑨 \bigl( λ (i : ρ 𝓸) . (𝑓 i)^𝑨\bigr)`.



---------------------------------------------------------------------------------------------------

.. index:: ! model
.. index:: ! pair: σ-identity; σ-equation
.. index:: ! pair: identity; equation
.. index:: ! pair: equational base; axiomatization
.. index:: ! pair: equational theory; theory
.. index:: ! pair: equational class; variety

.. _models_and_theories:

Models and theories
-------------------

Let :math:`σ = (F, ρ)` be a signature and :math:`X := \{x_0, x_1, \dots\}` a countable collection of variable symbols.

An **identity in the signature** :math:`σ` (or, :math:`σ`-**identity**) is an ordered pair :math:`(t,s)` of terms from :math:`T_σ (X)` of the same arity (:math:`ρ t = ρ s`).

We write :math:`p ≈ q` to indicate such a :math:`σ`-identity; here :math:`p, q ∈ T_σ (X)` and :math:`ρ p = ρ q`. [6]_

**N.B.** We sometimes refer to an identity as an **equation**; in our treatment of the subject the words "identity" and "equation" are synonyms.

Let :math:`𝒜_σ`, resp. :math:`ℰ_σ`, denote the class of all :math:`σ`-algebras, resp. :math:`σ`-identities.

For :math:`𝔸 ∈ 𝒦 ⊆ 𝒜_σ` and :math:`p ≈ q ∈ Σ ⊆ ℰ_σ`, we say

* :math:`𝔸` **models** :math:`p ≈ q`, denoted :math:`𝔸 ⊧ p ≈ q`, just in case :math:`p^𝔸 = q^𝔸` *extensionally* (i.e., :math:`ρ t = ρ s` and :math:`∀ a: \mathsf{Fin}(ρ p) → A, \; p^𝔸 \, a = q^𝔸 \, a`.); [7]_

* :math:`𝔸` **models** :math:`Σ`, denoted :math:`𝔸 ⊧ Σ`, just in case :math:`𝔸 ⊧ p ≈ q` for every :math:`p ≈ q` in :math:`Σ`;

* :math:`𝒦` **models** :math:`p ≈ q`, denoted :math:`𝒦 ⊧ p ≈ q`, just in case :math:`𝔸 ⊧ p ≈ q` for every :math:`𝔸` in :math:`𝒦`;

* :math:`𝒦` **models** :math:`Σ`, denoted :math:`𝒦 ⊧ Σ`, just in case :math:`𝔸 ⊧ Σ` for every :math:`𝔸 ∈ 𝒦`.

The binary relation :math:`⊧` induces an obvious :term:`Galois connection`. Indeed, the :term:`Galois pair` :math:`(\mathsf{Mod}, \mathsf{Th})` is defined as follows: for all :math:`Σ ⊆ ℰ_σ` and :math:`𝒦 ⊆ 𝒜_σ`, 

.. math:: \mathsf{Mod}(Σ) := \{𝔸: 𝔸 ⊧ Σ \} \quad \text{ and } \quad \mathsf{Th}(𝒦) := \{Σ: 𝒦 ⊧ Σ\}.

The first of these, the class of **models** of :math:`Σ`, contains those and only those algebras modelling :math:`Σ`. It is called an **equational class**, and :math:`Σ` is called an **equational base** for, or an **axiomatization** of, the class.

Dually, :math:`\mathsf{Th}(𝒦)` is the class of identities modelled by all algebras in :math:`𝒦`.  Such a class of identities is called an **equational theory**.

Alternatively and equivalently we could define "equational class" and "equational theory" in terms of the two :term:`closure operators <closure operator>` induced by the Galois pair :math:`(\mathsf{Mod}, \mathsf{Th})`.  Indeed, :math:`\mathsf{Mod} \mathsf{Th}: 𝒫 (𝒜) → 𝒫(𝒜)` is a closure operator on :math:`𝒜` and :math:`\mathsf{Th} \mathsf{Mod}: 𝒫 (ℰ) → 𝒫(ℰ)` is a closure operator on :math:`ℰ`, and 

* an **equational class** is a :math:`\mathsf{Mod} \mathsf{Th}`-:term:`closed set` of :math:`σ`-algebras;

* an **equational theory** is a :math:`\mathsf{Th} \mathsf{Mod}`-:term:`closed set` of :math:`σ`-identities.

(Here, as usual, :math:`𝒫` denotes the :term:`power set operator`.)

**N.B.** We sometimes refer to an equational class as a **variety**; in our treatment of the subject "equational class" and "variety" are synonyms.

--------------------------

.. _basic facts:

Basic facts
------------

We conclude this chapter with a list of basic facts (as well as proofs, in some cases).  These results are classical, straightforward consequences of the definitions above. We will need them below and when we cite them later, we will refer to them as, e.g, :numref:`Obs %s <obs 1>`, :numref:`Obs %s <obs 2>`, etc.  As mentioned above, we use the acronym :term:`UAFST` to cite the book :cite:`Bergman:2012`.

Throughout this section,

  :math:`𝑨 = ⟨A, F^𝑨⟩, \ 𝑩 = ⟨B, F^𝑩⟩, \ 𝑪 = ⟨C, F^𝑪⟩\ ` are algebras in the same signature :math:`σ = (F, ρ)`.

We start with the simple observation that composing homomorphisms gives a homomorphism.

.. _composition of homomorphisms:

.. _obs 0:

.. proof:observation:: composing homs gives a hom

   If :math:`g: \mathsf{Hom}(𝑨, 𝑩)` and :math:`h: \mathsf{Hom}(𝑩, 𝑪)` (homomorphisms from 𝑨 to 𝑩 and 𝑩 to 𝑪, resp.), then :math:`h \circ g : \mathsf{Hom}(𝑩, 𝑪)` (a homomorphisms from 𝑨 to 𝑪).


.. index:: ! equalizer

.. about the :math:`σ`-term algebra over :math:`X`.

.. _obs 1:

.. proof:observation:: UAFST Exercise 1.4.6.a

   If :math:`g, h : \mathsf{Hom}(𝑨, 𝑩)` are homomorphisms from 𝑨 to 𝑩, then the **equalizer** of :math:`g` and :math:`h`, which we denote :math:`𝖤(g,h) = \{a: A ∣ g\, a = h\, a\}`, is a subuniverse of 𝑨.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      Fix arbitrary :math:`f ∈ F` and :math:`a : ρf → 𝖤(g,h)`.

      We show that :math:`g (f^𝑨 \, a) = h (f^𝑨 \, a)`, as this will show that :math:`𝖤(g, h)` is closed under the operation :math:`f^𝑨` of :math:`𝑨`.

      For all :math:`i<ρ f` we have :math:`a \, i ∈ 𝖤(g,h)`, so :math:`g\, a \, i= h\, a\, i`.  Therefore (by function extensionality) :math:`g ∘ a = h ∘ a` and so, by definition of homomorphism,

      .. math:: g  (f^𝑨\,a) = f^𝑩 (g ∘ a) = f^𝑩 (h ∘ a) = h (f^𝑨\, a).

      ☐

.. **Formalization**. Our formal implementation of :numref:`Obs %s <obs 1>` is described in :numref:`equalizer-as-subuniverse`,  and is included in the `birkhoff.agda`_ file of the `agda-ualib`_ library.

.. _obs 2:

.. proof:observation:: UAFST Exercise 1.4.6.b

   If :math:`g, h : \mathsf{Hom}(𝑨, 𝑩)` are homomorphisms from 𝑨 to 𝑩, if the set :math:`X ⊆ A` generates 𝑨, and if :math:`g|_X = h|_X`, then :math:`g = h`.

   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Suppose the subset :math:`X ⊆ A` generates :math:`⟨A, F^𝑨⟩` and suppose :math:`g|_X = h|_X`.
 
      Fix an arbitrary :math:`a: A`. We show :math:`g\, a = h\, a`.
 
      Since :math:`X` generates 𝑨, there exists a term :math:`t` and a tuple :math:`x: ρt → X` of generators such that :math:`a = t^𝑨\, x`.
 
      Therefore, since :math:`g|_X = h|_X`, we have
    
      .. math:: g ∘ x = (g\, x_0, \dots, g\, x_{ρ t}) = (h\, x_0, \dots, h\, x_{ρ t}) = h ∘ x,

      so

      .. math:: g\, a = g(t^𝑨 \, x) = t^𝑩 (g ∘ x) = t^𝑩 (h ∘ x) = h(t^𝑨 \,x) = h\, a.

      ☐

.. **Formalization**. Our formal implementation of :numref:`Obs %s <obs 2>` is described in :numref:`homomorphisms-that-agree-on-a-generating-set`,  and is included in the `birkhoff.agda`_ file of the `agda-ualib`_ library.

.. _obs 3:

.. proof:observation:: UAFST Exercise 1.4.6.c

   If :math:`A, B` are finite and :math:`X` generates 𝑨, then :math:`|\mathsf{Hom}(𝑨, 𝑩)| ≤ |B|^{|X|}`.

   .. container:: toggle
    
      .. container:: header
    
         *Proof*.

      By :numref:`Obs %s <obs 2>`, a homomorphism is uniquely determined by its restriction to a generating set.

      If :math:`X` generates 𝑨, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\mathsf{Hom}(𝑨, 𝑩)| ≤ |B|^{|X|}`. ☐
    
.. _obs 4:

.. proof:observation::

   If :math:`g ∈ \mathsf{Epi} (𝑨, 𝑩)`, :math:`h ∈ \mathsf{Hom} (𝑨, 𝑪)`, and :math:`\ker g ⊆ \ker h`, then

   .. math:: ∃ k ∈ \mathsf{Hom}(𝑩, 𝑪), \ h = k ∘ g.
    
   .. container:: toggle
    
      .. container:: header
    
         *Proof*.

      We define :math:`k ∈ \mathsf{Hom}(𝑩, 𝑪)` as follows:

      Fix :math:`b ∈ B`.

      Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} ⊆ A` is nonempty, and since :math:`\ker g ⊆ \ker h`, it is clear that every element of :math:`g^{-1}\{b\}` is mapped by :math:`h` to a single element of :math:`C`.

      Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a ∈ g^{-1}\{b\}`.
   
      For each such :math:`b`, and its associated :math:`c_b`, define :math:`k(b) = c_b`.
   
      The observant reader may have noticed a slight-of-hand in the foregoing "construction" of the function :math:`k`. While it's true that for each :math:`b ∈ B` there exists a :math:`c_b` such that :math:`h(a) = c_b` for all :math:`a ∈ g^{-1}\{b\}`, it's also true that we have no means of producing such :math:`c_b` constructively.
      
      One could argue that each :math:`c_b` is easily computed as :math:`c_b = h(a)` for some (every) :math:`a ∈ g^{-1}\{b\}`. But this requires producing a particular :math:`a ∈ g^{-1}\{b\}` to use as "input" to the function :math:`h`. How do we select such an element from the (nonempty) set :math:`g^{-1}\{b\}`?
      
      We must appeal to the Axiom of :term:`Choice` at this juncture and concede that the function :math:`k` will not be constructively defined. (We have more to say about this in :numref:`Chapter %s <basic facts in agda>` when we implement :numref:`Obs %s <obs 4>` in Agda.)  Nonetheless, we forge ahead (nonconstructively) and define :math:`k` as described above, using the Axiom of :term:`Choice` to compute a :math:`c_b` for each :math:`b ∈ B`.
   
      It is then easy to see that :math:`k ∘ g = h`.  Indeed, for each :math:`a ∈ A`, we have :math:`a ∈ g^{-1}\{g(a)\}`, so :math:`k(g(a)) = h(a)` by definition.

      Finally, to prove that :math:`k` is a homomorphism, fix an operation symbol :math:`f ∈ F` and a tuple :math:`b: \mathsf{Fin}(ρ f) → B`; we will show that
      
      .. math:: f^𝑪 (k ∘ b) = k (f^𝑩(b)).
         :label: hom1

      Let :math:`a: \mathsf{Fin}(ρ f) → A` be such that :math:`g ∘ a = b`.  Then the left hand side of :eq:`hom1` is :math:`f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a)`, which is equal to :math:`h (f^𝑨 (a))` since :math:`h` is a homomorphism.
   
      Therefore,
   
      .. math:: 
      
         f^𝑪 (k ∘ b) &= f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a)\\ 
                 & = h (f^𝑨 (a)) = (k ∘ g)(f^𝑨 (a))\\
                 & = k (f^𝑩 (g ∘ a)) = k (f^𝑩 (b)),

      as desired, where the penultimate equality holds by virtue of the fact that :math:`g` is a homomorphism. ☐

.. .. **Formalization**. Our formal implementation of :numref:`Obs %s <obs 4>` is described in :numref:`factoring homomorphisms`, and is included in the `birkhoff.agda`_ file of the `agda-ualib`_ library.

.. _obs 5:

.. proof:observation::

   Suppose :math:`A_i ≤ 𝑨` for all :math:`i` in some set :math:`I`. Then :math:`⋂_{i∈ I} A_i` is a subuniverse of :math:`𝑨`.


.. --------------------------------------------------------------------------------------
.. SUBUNIVERSE GENERATION
.. -------------------------------------------

.. _obs 6:

.. proof:observation:: UAFST Thm 1.14

   Let :math:`𝑨 = ⟨A, F^{𝑨}⟩`  be  an  algebra in the signature :math:`σ = (F, ρ)` and let :math:`A_0` be a subset of :math:`A`.

   Define, by recursion on :math:`n`, the sets :math:`A_n` as follows:

     If :math:`A_0 = ∅`, then :math:`A_n = ∅` for all :math:`n<ω`.

     If :math:`A_0 ≠ ∅`, then

     .. math:: A_{n+1} =  A_n ∪ \{ f\, a ∣ f ∈ F, \ a ∈ \mathsf{Fin}(ρ f) → A_n\}.
        :label: subalgebra-inductive

   Then the subuniverse of 𝑨 generated by :math:`A_0` is :math:`\mathsf{Sg}^𝑨(A_0) = ⋃_{n<ω} A_n`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let :math:`Y := ⋃_{n < ω} A_n`. Clearly :math:`A_n ⊆ Y ⊆ A`, for every :math:`n < ω`. In particular :math:`A = A_0 ⊆ Y`. We first show that :math:`Y` is a subuniverse of 𝑨.

      Let :math:`f` be a basic :math:`k`-ary operation and let :math:`a: \mathsf{Fin}(k) → Y` be a :math:`k`-tuple of elements of :math:`Y`.
    
      From the construction of :math:`Y`, there is an :math:`n < ω` such that :math:`∀ i,\ a,\ i ∈ A_n`.
    
      From its definition, :math:`f \,a ∈ A_{n+1} ⊆ Y`. Since :math:`f` was arbitrary, it follows that :math:`Y` is a subuniverse of 𝑨 containing :math:`A_0`.
    
      Thus, by :eq:`SgDef`, :math:`\mathsf{Sg}^𝑨(A_0) ⊆ Y`.
    
      For the opposite inclusion, it is enough to check, by induction on :math:`n`, that :math:`A_n ⊆ \mathsf{Sg}^𝑨(A_0)`.
    
      Clearly, :math:`A_0 ⊆ \mathsf{Sg}^𝑨(A_0)`.
      
      Assume :math:`A_n ⊆ \mathsf{Sg}^𝑨(A_0)`.  We show :math:`A_{n+1} ⊆ \mathsf{Sg}^𝑨(A_0)`.
      
      If :math:`b ∈ A_{n+1} - A_n`, then :math:`b = f\, a` for a basic :math:`k`-ary operation :math:`f` and some :math:`a: \mathsf{Fin}(k) → A_n`.
      
      But :math:`∀ i, \ a i ∈ \mathsf{Sg}^𝑨(A_0)` and since this latter object is a subuniverse, :math:`b ∈ \mathsf{Sg}^𝑨(X)` as well.
    
      Therefore, :math:`A_{n+1} ⊆ \mathsf{Sg}^𝑨(A_0)`, as desired. ☐ 

.. The argument in the proof of :numref:`Obs <obs 6>` is of a type that one encounters frequently throughout algebra. It has two parts.

..   #. Some set :math:`Y` is shown to be a subuniverse of 𝑨 that contains :math:`A_0`.

..   #. Every subuniverse containing :math:`A_0` is shown to contain :math:`Y` as well.

..   #. One concludes that :math:`Y = \mathsf{Sg}^𝑨 (A_0)`.


**Formalization**. Our formal implementation of the concept of subalgebra is described in :numref:`Sections %s <subalgebras in agda>`.

.. and is included in the `subuniverse.agda`_ file of the `agda-ualib`_ library.


.. --------------------------------------------------------------------------------------
.. CLONE GENERATION
.. -------------------------------------------

.. We seek a "bottom-up," inductive description of the members of :math:`\mathsf{Clo}(F)`.  By thinking of the clone itself as a kind of algebra, a description analogous to :numref:`Obs %s <obs 6>` ought to be possible.  In fact, since function composition is associative, a slightly slicker formulation is available.


.. _obs 7:

.. proof:observation:: UAFST Thm 4.3


   Let :math:`A` be a set and let :math:`F ⊆ \mathsf{Op}(A):= ⋃_{n<ω} A^{A^n}` be a collection of operations on :math:`A`.
   
   Define :math:`F_0 := \mathsf{Proj} (A)` (the set of projections on :math:`A`) and for all :math:`0 ≤ n < ω` let
 
   .. math:: F_{n+1} := F_n ∪ \{ f g \mid f ∈ F, g : \mathsf{Fin}(ρ f) → (F_n ∩ (ρg → A)) \}.
 
   Then :math:`\mathsf{Clo}(F) = ⋃_n F_n`.
 
   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Let :math:`F̄ = ⋃_n F_n`. It is easy to argue by induction that every :math:`F_n` is a subset of :math:`\mathsf{Clo}(F)`. Thus, :math:`F ⊆ \mathsf{Clo}(F)`.
    
      For the converse, we must show that :math:`F̄` is a clone that contains :math:`F`.
    
      Obviously :math:`F̄` contains the projection operations, :math:`F_0 ⊆ F̄`.

      For every :math:`f ∈ F`, we have :math:`f π^k ∈ F_1 ⊆ F̄`, where :math:`k:= ρ f`.
 
      We are reduced to showing that :math:`F̄` is closed under generalized composition. This follows from the following claim.
 
      **Claim**. If :math:`f ∈ F_n` and :math:`g_0, \dots, g_{ρ f-1} ∈ F_m` are all :math:`k`-ary, then :math:`f g \in F_{n+m}`, where we have defined :math:`g: \mathsf{Fin}(ρ f) → (k → A) → A` to be the tuple given by :math:`g\,i = g_i` for each :math:`0 ≤ i < ρ f`.

      Note that the types match up; indeed, for each :math:`a: (\mathsf{Fin}(k) → A) → A`, we have

      .. math:: f (g ∘ a) = f(g_0(a_0, \dots, a_{k-1}), 
 
      We prove the claim by induction on :math:`n`.
      
      If :math:`n = 0` then :math:`f` is a projection, so :math:`f g = g_i ∈ F_{0+m}` for some :math:`0≤ i < ρ f`.

      Assume the claim holds for :math:`n` and that :math:`f ∈ F_{n+1} - F_n`.
      
      From the definition, there is a :math:`t`-ary operation :math:`f_i ∈ F` and a :math:`t`-tuple :math:`h = (h_0, \dots, h_{t-1}) ∈ t → F_n`, such that :math:`f = f_i h`. (Note that :math:`h: \mathsf{Fin}(t) → (\mathsf{Fin}(ρ f) → A) → A` is given by :math:`h(j) = h_j`, and that the arity of each :math:`h_i` must be equal to that of :math:`f`, namely :math:`ρ f`.)
      
      By the induction hypothesis, for each :math:`i ≤ k`, :math:`h_i' = h_i g \in F_{n+m}` (where, as above, :math:`g = (g_0, \dots, g_{k-1})`).
      
      Applying the definition, :math:`f_1 h' ∈ F_{n+m+1} = F_{(n+1)+m}`. Since 
      
      .. math:: f_1 h' = f_1 ∘ (h_1 g, \dots, h_t g) = f g,

      the claim is proved. □

.. _obs 8:

.. proof:observation:: UAFST Thm 4.21

   #. :math:`𝑻 := 𝑻_σ(X)` is generated by :math:`X`.
 
   #. For every :math:`\sigma`-algebra :math:`𝑨 = ⟨A, F^𝑨⟩` and function :math:`g: X → A` there is a unique homomorphism :math:`h: 𝑻 → 𝑨` such that :math:`h|_X = g`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*.
     
      The definition of :math:`𝑻` exactly parallels the construction in :numref:`Theorem %s <obs 6>`. That accounts for the first assertion.
     

      For the second assertion, define :math:`h\,t` by induction on the :term:`height` of :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ F_0`.
      
      If :math:`t ∈ X`, then define :math:`h\,t = g\,t`. If :math:`t ∈ F_0`, then let :math:`h\,t = t^𝑨`.
     
      For the inductive step, assume :math:`|t| = n + 1`. Then :math:`t = f\,s` for some :math:`f ∈ F` and :math:`s: ρ f → T_n`, where for each :math:`0 ≤ i< ρ f` the term :math:`s\, i` has height at most :math:`n`. We define :math:`h\,t = f^𝑨(h ∘ s) = f^𝑨(h\,s_1, \dots, h\,s_k)`.
     
      By its very definition, :math:`h` is a homomorphism that agrees with :math:`g` on :math:`X`. The uniqueness of :math:`h` follows from :numref:`Obs %s <obs 2>`. ☐
   
In the next observation, assume :math:`𝑨 = ⟨A, F^𝑨⟩` and :math:`𝑩 = ⟨B, F^𝑩⟩` are algebras in the same signature :math:`σ = (F, ρ)`, and let :math:`t ∈ T_σ (X)` be an :math:`n`-ary term.

In particular, :math:`t` has an interpretation in :math:`𝑨` (see :numref:`interpretation of terms`). We denote the interpretation of :math:`t` in :math:`𝑨` by :math:`t^𝑨 a = t^𝑨 (a\, 0, a\, 1, \dots, a\, (n-1))`, where :math:`a: \mathsf{Fin}(n) → A`. Similarly, :math:`t^𝑩: (\mathsf{Fin}(n) → B) → B` is the interpretation of :math:`t` in :math:`𝑩`.
    
.. _thm 4.32:

.. _obs 9:

.. proof:observation:: homomorphisms commute with terms

   #. :math:`g: 𝑨 → 𝑩` is a homomorphism, then :math:`g ∘ a: \mathsf{Fin}(n) → B` is the :math:`n`-tuple whose :math:`i`-th component is :math:`(g ∘ a)\, i = g(a\, i)`, and
  
      .. math:: g(t^𝑨 a) = t^𝑩(g ∘ a).

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      This is an easy induction on :math:`|t|`. ☐
    
.. _obs 10:

.. proof:observation:: terms respect congruences

   If :math:`θ` is a congruence of :math:`𝑨` and :math:`a, a': \mathsf{Fin}(n) → A` are :math:`n`-tuples over :math:`A`, then
    
   .. math:: (a, a') ∈ θ \; ⟹  \; (t^𝑨\,a, t^𝑨\,a') ∈ θ.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      This follows from :numref:`Obs %s <obs 8>` by taking :math:`⟨B, F^𝑩⟩ = ⟨A, F^𝑨⟩/θ = ⟨A/θ, F^{𝑨/θ}⟩` and :math:`g=` the canonical homomorphism. ☐
    
.. _obs 11:

.. proof:observation:: subuniverse generation as image of terms

   If :math:`Y` is a subset of :math:`A`, then

      .. math:: \mathsf{Sg}^{𝑨}(Y) = \{ t^𝑨 \, a ∣ t ∈ T_σ(X_n), \, n ∈ ℕ, \; a: ρ t → Y\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      A straightforward induction on the height of :math:`t` shows that every subuniverse is closed under the action of :math:`t^𝑨`. Thus the right-hand side is contained in the left. On the other hand, the right-hand side is a subuniverse that contains the elements of :math:`Y` (take :math:`t = x_1`), so it contains :math:`\mathsf{Sg}^{𝑨}(Y)` as the latter is the smallest subuniverse containing :math:`Y`. ☐


.. -----------------------------------------------------------------
.. MALCEV TERMS and CONDITIONS

.. .. index:: ! Malcev condition, ! Taylor term
..
.. Special terms
.. ~~~~~~~~~~~~~~
.. .. _thm 4.3:
..
.. .. proof:observation::
..
..    Let :math:`X` be a set and :math:`σ = (F, ρ)` a signature. Define
..
..    .. math:: F_0 &= X;\\
..          F_{n+1} &= F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρ g → X)) \}, \quad n < ω.
..
..    Then :math:`\mathsf{Clo}^X(F) = ⋃_n F_n`.
..
..
.. For a nonempty set :math:`A`, we let :math:`\mathsf{Op}_A` denote the set of all finitary operations on :math:`A`. That is, :math:`\mathsf{Op}_A = ⋃_{n∈ ℕ} A^{A^n}` on :math:`A` is a subset of :math:`\mathsf{Op}_A` that contains all projection operations and is closed under the (partial) operation of :ref:`<general composition>`.
..
.. If :math:`𝑨 = ⟨ A, F^𝑨 ⟩` denotes the algebra with universe :math:`A` and set of basic operations :math:`F`, then :math:`\mathsf{Clo}(𝑨)` denotes the clone generated by :math:`F`, which is also known as the **clone of term operations** of :math:`𝑨`.
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



.. (fact-m1)
   
.. _obs 12:

.. proof:observation::

   For every class 𝒦, each of the classes :math:`𝖲(𝒦)`, :math:`𝖧(𝒦)`, :math:`𝖯(𝒦)`, and :math:`𝕍(𝒦)` satisfies exactly the same identities as does 𝒦.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      We prove the result for :math:`𝖧(𝒦)` and leave the others as exercises.

      Clearly :math:`𝒦 ⊆ 𝖧(𝒦)`, so :math:`\mathsf{Th} \, 𝖧 (𝒦) ⊆  \mathsf{Th} \,𝒦`. 


.. fact-m2

.. _obs 13:   

.. proof:observation:: UAFST Lem 4.37

   :math:`𝒦 ⊧ p ≈ q` if and only if :math:`∀ 𝔸 ∈ 𝒦`, :math:`∀ h ∈ \mathsf{Hom}(𝕋(X_ω), 𝔸)`, :math:`h\, p^𝔸 = h\, q^𝔸`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      (⇒) Assume that :math:`𝒦 ⊧ p ≈ q`.
      
          Fix :math:`𝔸 ∈ 𝒦` and :math:`h ∈ \mathsf{Hom}(𝕋(X_ω), 𝔸)`.
      
          We must show :math:`∀ a: \mathsf{Fin}(ρ p) → A` that :math:`h(p^{𝔸}\, a) = h(q^{𝔸}\, a)`.

          Fix :math:`a: \mathsf{Fin}(ρ p) → A`.

          By :math:`𝔸 ⊧ p ≈ q` we have :math:`p^{𝔸} = q^{𝔸}` which implies :math:`p^{𝔸}(h ∘ a) = q^{𝔸}(h ∘ a)`.
      
          Since :math:`h` is a homomorphism, we obtain :math:`h(p^{𝔸}\, a) = h(q^{𝔸}\, a)`, as desired.

      (⇐) Assume :math:`∀ 𝔸 ∈ 𝒦`, :math:`∀ h ∈ \mathsf{Hom}(𝕋(X_ω), 𝔸)`, :math:`h\, p^𝔸 = h\, q^𝔸`.
      
          We must show :math:`𝒦 ⊧ p ≈ q`.
          
          Fix :math:`𝔸 ∈ 𝒦` and :math:`a: \mathsf{Fin}(ρ p) → A`.
          
          We must prove :math:`p^𝔸 \, a = q^𝔸\, a`.
          
          Let :math:`h_0 : X_ω → A` be a function with :math:`h_0\, x\, i = a\, i` for all :math:`0≤ i < ρ p`, for some :math:`x: ρ p → X_ω`.
          
          By :numref:`Obs %s <obs 6>`, :math:`h_0` extends to a homomorphism :math:`h` from :math:`𝕋(X_ω)` to 𝔸.
      
          By assumption :math:`h\, p^𝔸 = h\, q^𝔸`, and since :math:`h` is a homomorphism,
      
          .. math:: p^{𝔸}\, a =  p^{𝔸}(h ∘ x) = h(p^{𝔸} \, x) = h(q^𝔸 \, x) = q^𝔸 (h ∘ x) = q^𝔸 \, a,
      
          so :math:`p^{𝔸}\, a = q^𝔸 \, a`, as desired. ☐

.. (fact-m3)

.. _obs 14:   

.. proof:observation:: 

   Let 𝒦 be a class of algebras and :math:`p ≈ q` an equation. The following are equivalent.

     #. :math:`𝒦 ⊧ p ≈ q`.

     #. :math:`(p, q)` belongs to the congruence :math:`λ_{𝒦}` on :math:`𝕋(X_ω)`.

     #. :math:`𝔽_{𝒦}(X_ω) ⊧ p ≈ q`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      We shall show (1) ⟹ (3) ⟹ (2) ⟹ (1). 
      
      Recall that :math:`𝔽_{𝒦}(X_ω) = 𝕋/λ ∈ 𝖲 𝖯 (𝒦)`.
      
      From (1) and Lemma 4.36 of :term:`UAFST` we have :math:`𝖲 𝖯 (𝒦) ⊧ p ≈ q`. Thus (3) holds.

      From (3), :math:`p^{𝔽} \, [x] = q^{𝔽} \, [x]`, where :math:`[x]: ρ p → 𝔽_𝒦 (X_ω)` is defined by :math:`[x]\, i = x_i/λ`.
      
      From the definition of 𝔽, :math:`p^{𝕋}\, x ≡_λ q^{𝕋} ×`, from which (2) follows since :math:`p = p^{𝕋}\, x` 
      and :math:`q = q^{𝕋}\, x`.

      Finally assume (2). We wish to apply Lemma 4.37 of :term:`UAFST`.
      
      Let :math:`𝔸 ∈ 𝒦` and :math:`h ∈ \mathsf{Hom}(𝕋, 𝔸)`.
      
      Then :math:`𝕋/\ker h ∈ 𝖲 (𝔸) ⊆ 𝖲(𝒦)` so :math:`\ker h ⊇ λ`.  Thus, (2) implies :math:`h\, p = h\, q` hence (1) holds, completing the proof. ☐

The last result tells us that we can determine whether an identity is true in a variety by consulting a particular algebra, namely :math:`𝔽(X_ω)`. Sometimes it is convenient to work with algebras free on other generating sets besides :math:`X_ω`. The following corollary takes care of that for us.


.. (fact-m4):

.. _obs 15:   

.. proof:observation:: 

   Let :math:`𝒦` be a class of algebras, :math:`p` and :math:`q` :math:`n`-ary terms, :math:`Y` a set and :math:`y_1, \dots, y_n` distinct elements of :math:`Y`. Then :math:`𝒦 ⊧ p ≈ q` if and only if
   :math:`p^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n) = q^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n)`. In particular, :math:`𝒦 ⊧ p ≈ q` if and only if :math:`𝔽_{𝒦}(X_n) ⊧ p ≈ q`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Since :math:`𝔽_{𝒦}(Y) ∈ 𝖲 𝖯 (𝒦)`, the left-to-right direction uses the same argument as in Thm 4.38 of :term:`UAFST`. (See :numref:`Obs %s <obs 14>` above.)
      
      So assume that :math:`p^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n) = q^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n)`.
      
      To show that :math:`𝒦 ⊧ p ≈ q`, let :math:`𝔸 = ⟨ A, f^{𝔸} ⟩ ∈ 𝒦` and :math:`a_1, \dots, a_n ∈ A`. We must show :math:`p^{𝔸}(a_1, \dots, a_n) = q^{𝔸}(a_1, \dots, a_n)`.

      There is a homomorphism :math:`h : 𝔽_{𝒦}(Y) → (A, f^A)` such that :math:`h(y_i) = a_i` for :math:`i ≤ n`. Then

      .. math:: p^{𝔸}(a_1, \dots, a_n) &= p^{𝔸}(h (y_1), \dots, h (y_n)) = h(p^{𝔽_𝒦(Y)}(y_1, \dots, y_n))\\
                                       &= h(q^{𝔽_𝒦(Y)}(y_1, \dots, y_n)) = q^{𝔸}(h(y_1), \dots, h(y_n))\\
                                       &= q^{𝔸}(a_1, \dots, a_n).

      It now follows from :numref:`Obs %s <obs 12>` that every equational class is a variety. The converse is **Birkhoff's HSP Theorem**. ☐

We end this subsection with yet another standard but important result.

.. _obs 16:   

.. proof:observation::

    Every  finitely  generated  variety  is  locally finite.

    (See Thm 3.49 of :term:`UAFST` for the proof.)

    The converse of the last theorem is false.  That is, there exist locally finite varieties that are not finitely generated (e.g., the variety of :math:`p`-algebras; see Cor. 4.55 of :term:`UAFST`).


   

---------------------------

.. rubric:: Footnotes

.. [1]
   Viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. [3]
   The term :math:`σ`-**algebra** has a special meaning, different from ours, in other areas of mathematics such as real analysis, probability, and measure theory.

.. [4]
   By "the constants on :math:`A`" we mean the **constant operations**; i.e., functions :math:`f: A → A` such that :math:`∀ a ∈ A, f(a) = c`, for some :math:`c ∈ A`.

.. [5]
   The construction of :math:`𝑻_ρ (X)` may seem to be making something out of nothing, but it plays an significant role in the theory.

.. [6]
   Produce ``≈`` with ``\approx``.

.. [7]
   Produce ⊧ with ``\models``.

------------------

.. include:: hyperlink_references.rst

