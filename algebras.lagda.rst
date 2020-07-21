.. File: algebras.lagda.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 11 Feb 2020
.. Updated: 22 Jun 2020
.. Copyright (c) 2019 William DeMeo


.. _algebras:

========
Algebras
========

In this chapter we use the informal language of universal algebra to present foundational definitions and theorems about :term:`subalgebras <subalgebra>`, :term:`terms <term>`, and :term:`clones <clone>`.  In :numref:`types for algebras` --:numref:`types for subalgebras`, we show how the definitions and results presented in this section can be formalized (or "implemented") in type theory using Agda.

The idea is to demonstrate the power and utility of implementing our mathematical are of expertise in a formal language that supports dependent and inductive types, which are essential for expressing and working with infinite objects in a :term:`constructive` and :term:`computable` way, and for proving properties of these objects.

One goal of our project was to provide, as a "proof of concept" a formal implementation of a deep result in universal algebra. As the focus of this goal, we have chosen what was among the first major results of the theory of universal algebras---namely, the celebrated `HSP Theorem`_ that Garrett Birkhoff proved in 1933. (`The original paper is available online <https://web.archive.org/web/20180330012312/https://pdfs.semanticscholar.org/a282/3f992ea5e2d2a1e989ce01844da71e4ec6a5.pdf>`_.)

A nice (informal) proof of the HSP Theorem appears on pages 106 and 107 of Cliff Bergman's book :cite:`Bergman:2012`. Naturally, the proof relies on many defeinitions and results developed in earlier chapters of the book.  Nonetheless, Professor Bergman's path to a proof of the HSP theorem is the most straightforward and efficient one we know, and we will follow his presentation quite closely.

On the other hand, in order to get as directly as possible to a formal proof of the HSP Theorem, we will extract all the ingredients we need from :cite:`Bergman:2012`, and present them as a list of results at the end of this chapter, and then later, in :numref:`birkhoffs theorem in agda`, we will formalize each of these results in Agda.

Whenever we quote or paraphrase a result from :cite:`Bergman:2012` book, we will include a citation that indicates where the corresponding result is found in the book.

------------------------------

.. index:: ! graph (of a function)
.. index:: ! idempotent, ! projection
.. index:: operation, arity, image
.. index:: pair: ℕ; ω 

.. _operations:

Operations
-----------

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If 𝑚 is a natural number, we write 𝑚 : ℕ and say that 𝑚 *has type* ℕ. [1]_  We typically denote and define natural numbers by 𝑚 := {0, 1, …, 𝑚-1}.

It is sometimes convenient to formally identify a function with its graph.  For example, the function 𝑎 : 𝑚 → 𝐴 may be identified with the tuple (𝑎 0, 𝑎 1, …, 𝑎(𝑚-1)) : 𝐴ᵐ.

If ℎ : 𝐴 → 𝐴 and 𝑎 : 𝑚 → 𝐴 are functions, then ℎ ∘ 𝑎 : 𝑚 → 𝐴 denotes the composition of ℎ with 𝑎; this is the function that maps each 𝑖 < 𝑚 to the element (ℎ ∘ 𝑎)(𝑖) = ℎ(𝑎 𝑖) of 𝐴.

We may formally identify the function ℎ ∘ 𝑎 : 𝑚 → 𝐴 with its graph, which of course is the 𝑚-tuple, (ℎ(𝑎 0), ℎ(𝑎 1), …, ℎ(𝑎 (𝑚-1))).

Suppose 𝐴 is a nonempty set and 𝑛 ∈ ℕ is a natural number. An 𝑛-**ary operation** on 𝐴 is a function 𝑓 : 𝐴ⁿ → 𝐴 which (for 𝑛 > 0) maps each 𝑛-tuple (𝑎₀, 𝑎₁, …, 𝑎ₙ₋₁) in 𝐴ⁿ to a particular element 𝑓(𝑎₀, 𝑎₁, …, 𝑎ₙ₋₁) in 𝐴.  If 𝑛=0, then 𝑓 : () → 𝐴 is a function that takes no arguments and returns an element of 𝐴, so 𝑓 in this case is merely notation for a particular element of 𝐴, and we may write 𝑓 : 𝐴 in this case. An operation is called **nullary** (or constant) if its arity is zero. **Unary**, **binary**, and **ternary** operations have arities 1, 2, and 3, respectively.

An operation gives rise to a special kind of (𝑛+1)-ary relation, namely

.. math:: Gf := \{(a_0, a_1, \dots, a_{n-1}, b) \in A^{n+1} ∣ b = f(a_0, a_1, \dots, a_{n-1})\},

which is sometimes called the **graph** of 𝑓.

For two sets 𝐴 and 𝐵, the collection of all functions 𝑓 : 𝐵 → 𝐴 is, for obvious reasons, denoted by :math:`A^B`. If  𝐵 = 𝐴ⁿ, then we have :math:`A^{A^n}`, the collection of all 𝑛-ary operations on 𝐴; as noted above, this can be represented by the function type (𝑛 → 𝐴) → 𝐴.

If we let Op(𝐴) denote the collection of all finitary operations on 𝐴, then,

.. math:: \mathrm{Op}(𝐴) = ⋃_{n ∈ ℕ} A^{A^n} = ⋃_{n<ω} ((𝑛 → A) → A).

If 𝐹 ⊆ Op(𝐴) is a set of operations on 𝐴, let us denote by 𝐹ₙ the 𝑛-ary operations in 𝐹. Clearly, :math:`F_n = F ∩ A^{A^n}`.

Given an 𝑛-tuple :math:`a = (a_0, a_1, \dots, a_{n-1}) ∈ A^n`, it helps to be able to refer to the set :math:`\{a_i : 0 ≤ i < n\}` of elements that occur in the tuple without explicitly naming each element in this set.  In fact, we already have notation for this, since an 𝑛-tuple is truly a function, with domain 𝑛 := {0, 1, …, 𝑛-1}, and image the set of elements occuring in the tuple.  Thus, im 𝑎 is {𝑎₀, 𝑎₁, …, 𝑎ₙ₋₁}, where each value is included in the set only once (no repeats). In particular, ∣im 𝑎∣ is a convenient way to write the number of distinct elements that occur in the tuple 𝑎.  For example, if 𝑎 = (1, 1, 3), then im 𝑎 = {1, 3}, and ∣im 𝑎∣ = 2.

-----------------------------------------

.. _general composition:

General composition
-------------------

In universal algebra we mainly deal with *finitary* operations in **Set** (the category of sets).  We will identify the ``ntuple`` type with the function type 𝑛 → 𝐴.  Thus, the type of 𝑛-ary operations on 𝐴 is (𝑛 → 𝐴) → 𝐴.  Evaluating such an operation at the tuple 𝑎 : 𝑛 → 𝐴 is simply function application.

As above, we denote and define the collection of all finitary operations on 𝐴 by Op(𝐴) = :math:`⋃_{n<ω}` ((𝑛 → 𝐴) → 𝐴). Let us now develop a general formulation of composition of operations that is more elegant and computationally practical than the standard formulation.

Recall, the standard description of operation composition: if 𝑓 : (𝑛 → 𝐴) → 𝐴 is an 𝑛-ary operation and :math:`g_i : (k_i → A) → A` is a :math:`k_i`-ary operation for each 0 ≤ 𝑖 < 𝑛, then the **composition of** 𝑓 **with** :math:`(g_0, \dots, g_{n-1})`, denoted :math:`f ∘ (g_0, \dots, g_{n-1})`, is usually expressed as follows: for each 𝑛-tuple of tuples,

.. math:: ((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})): A^{k_0} × \cdots × A^{k_{n-1}},
   :label: args

.. math:: f & ∘ (g_0, \dots, g_{n-1})((a_{00}, \dots, a_{0(k_0-1)}), \dots, (a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)}))\\
                &= f(g_0(a_{00}, \dots, a_{0(k_0-1)}), \dots, g_{n-1}(a_{(n-1)0}, \dots, a_{(n-1)(k_{n-1}-1)})).

This notation is quite ugly and, even worse, it lends itself poorly to computation. Let us clean it up.

Consider the 𝑛-tuple :math:`(g_0, \dots, g_{n-1})` of operations from Op(𝐴).

Let :math:`g : ∏_{(i:n)} ((k_i → A) → A)` be the function with domain the set :math:`n = \{0,1,\dots, n-1\}`, codomain :math:`\mathrm{Op}(A)`, and defined for each 0 ≤ 𝑖 < 𝑛 by :math:`g\,i = g_i`.

Let :math:`a : ∏_{(i:n)} (k_i → A)` be such that for each 0 ≤ 𝑖 < 𝑛 we have a function 𝑎 𝑖 : 𝑘ᵢ → 𝐴 which is defined for each 0 ≤ 𝑗 < 𝑘ᵢ by 𝑎 𝑖 𝑗 = 𝑎ᵢⱼ.

Then the 𝑛-tuple of arguments in expression :eq:`args` above can be identified with the 𝑛-tuple 𝑎 = (𝑎 0, …, 𝑎 (𝑛-1)) of functions.

Using the :ref:`fork` and :ref:`eval` operators (defined in :ref:`general-composition`), it is not hard to define general composition using these operators along with dependent types.

If :math:`g: ∏_{(i:n)} ((k_i → A) → A)` and :math:`a: ∏_{(i:n)}(k_i → A)`, then

.. math:: \mathrm{fork} \, g\, a: ∏_{(i:n)}((k_i → A) → A) × (k_i → A)

is the function that maps each 0 ≤ 𝑖 < 𝑛 to the pair

.. math:: (\mathrm{fork} \, g\, a)\, i = (g\,i, a\,i): ((k_i → A) → A) × (k_i → A).

Applying :math:`g\,i` to 𝑎 𝑖 with the eval function, we have

.. math:: \mathrm{eval} \, (\mathrm{fork} \, g\, a)\, i = \mathrm{eval} \, (g\,i, a\,i) = (g\,i)(a\,i).

Observe that the codomain 𝐴 of the function eval fork :math:`g\, a` does not depend on 𝑖, so the type :math:`∏_{(i:n)} A` simplifies to 𝑛 → 𝐴 in this case, resulting in the typing judgment, eval fork :math:`g\, a` : 𝑛 → 𝐴.

.. On the other hand,

.. .. math:: \mathrm{eval}\,\mathrm{fork} \, g: ∏_{(i:n)}  (k_i → A) → (n → A).

Thus, if

  𝑓 : (𝑛 → 𝐴) → 𝐴 (an 𝑛-ary operation) and

  :math:`g: ∏_{(i:n)} ((k_i → A) → A)` (an 𝑛-tuple of operations), then we

  denote and define the **composition of** 𝑓 **with** :math:`g` as follows:

.. math:: f\, \mathrm{comp}\, g := f \, \mathrm{eval} \, \mathrm{fork} \, g: \bigl(∏_{(i:n)}(k_i → A)\bigr) → A.

Indeed, if :math:`a: ∏_{(i:n)}(k_i → A)`, then eval fork :math:`g \, a` has type 𝑛 → 𝐴, which is the domain type of 𝑓; therefore, 𝑓 eval fork :math:`g \, a` has type 𝐴, as desired.

.. _greater-generality:

Greater generality
~~~~~~~~~~~~~~~~~~

In the last section we looked at an operation 𝑓 on a set 𝐴. We took the domain of 𝑓 to be 𝑛 → 𝐴 (the type of 𝑛-tuples over 𝐴) for some 𝑛.  In particular, we assumed that 𝐴 was a set, and that the arity of 𝑓 was some natural number, say, 𝑛. This is the standard setup in universal algebra.  However, it is not necessary to be so specific about the arities, domains, and codomains of operations.

In this section we start with two types α and γ and consider γ-**ary operations on** α---e.g., f : (γ → α) → α---and show how to express composition of operations in this general context.

Suppose that for each 𝑖 : γ we have a type γᵢ and an operation :math:`g_i` of type (γᵢ → α) → α on α.

Denote by 𝐺 the "γ-tuple" of these operations; that is, for each 𝑖 : γ the "𝑖-th component" of 𝐺 is 𝐺 𝑖 = :math:`g_i`. Evidently, this results in the typing judgment,

.. math:: G: ∏_{(i:γ)} ((γ_i → α) → α).

Even in this more general context, we can still use the fork and eval maps introduced in the appendix (see :ref:`general-composition`) to express composition of operations. Indeed, we *define* the **composition of** 𝑓 **with** 𝐺 to be

.. math:: f \, \mathrm{eval} \, \mathrm{fork} \, G.

Let us adopt the following convenient notation:

  *Denote by* comp *the general composition operation* eval fork.

Then, given 𝑓 : (γ → α) → α and :math:`G: ∏_{(i:γ)} ((γ_i → α) → α)`, the **general composition of** 𝑓 **with** 𝐺 is 𝑓 comp 𝐺 := 𝑓 eval fork 𝐺.  Evidently, this yields the typing judgment,

.. math:: f\, \mathrm{comp}\, G : \bigl(∏_{(i:γ)}(γ_i → α)\bigr) → α.

Indeed, if :math:`a: ∏_{(i:γ)}(γ_i → α)`, then for each 𝑖 : γ we have,

.. math:: a\, i : γ_i → α \quad \text{ and } \quad  G\, i : (γ_i → α) → α,

so evaluation of comp 𝐺 𝑎 at a particular 𝑖 : γ is simply function application. That is,

.. math:: \mathrm{comp} \,G \, a \, i:= \mathrm{eval} \, \mathrm{fork} \, G \, a \, i = (G\, i)(a\, i): α.

Thus, comp 𝐺 𝑎 has type γ → α, which is precisely the domain type of 𝑓.

To summarize, we have the following typing judgments:

.. math:: \mathrm{comp}\, G \, a : γ → α \quad \text{ and } \quad f: (γ → α) → α,

whence 𝑓 comp 𝐺 𝑎 : α is well-typed.


----------------------------------------

.. index:: signature, arity

.. _signatures:

Signatures
----------

Recall (from :term:`model theory`) that a **signature** 𝑆 = (𝐶, 𝐹, 𝑅, ρ) consists of three (possibly empty) sets 𝐶, 𝐹, and 𝑅---called *constant symbols*, *function symbols*, and *relation symbols*, respectively---along with a function ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁 that assigns an :term:`arity` to each symbol. Often (but not always) 𝑁 = ℕ.

As our focus here is universal algebra, we are more concerned with the restricted notion of an **algebraic signature** (or **signature** for :term:`algebraic structures <algebraic structure>`), by which we mean a pair 𝑆 = (𝐹, ρ) consisting of a collection 𝐹 of *operation symbols* and an :term:`arity` function :math:`ρ : 𝐹 → 𝑁` that maps each operation symbol to its arity; here, 𝑁 denotes the "arity type" (which is sometimes taken to be ℕ). (Intuitively, the arity ρ 𝑓 of an operation symbol 𝑓 ∈ 𝐹 may be thought of as the "number of arguments" that 𝑓 takes as "input".)

If the arity of 𝑓 is 𝑛, then we call 𝑓 an 𝑛-**ary** operation. In case 𝑛 is 0 (or 1 or 2 or 3, resp.) we call the function *nullary* (or *unary* or *binary* or *ternary*, resp.).

If 𝐴 is a set and 𝑓 is a (ρ 𝑓)-ary operation on 𝐴, we often indicate this by writing :math:`f : A^{ρ f} → A`. On the other hand, the arguments of such an operation form a (ρ 𝑓)-tuple, say, (𝑎₀, 𝑎₁, …, :math:`a_{ρf-1}`), which may be viewed as the graph of the function 𝑎 : ρ𝑓 → 𝐴, where 𝑎 𝑖 = 𝑎ᵢ.

(When the codomain of ρ is ℕ, we may view ρ𝑓 as the finite set {0, 1, …, ρ𝑓 - 1}. Thus, by identifying the ρ𝑓-th power :math:`A^{ρf}` with the type ρ𝑓 → 𝐴 of functions from {0, 1, …, ρ𝑓 - 1} to 𝐴, we identify the function type :math:`A^{ρf} → A` with the function (or "functional") type (ρ𝑓 → 𝐴) → 𝐴. [2]_

.. proof:example::

   Suppose :math:`𝑔 : (𝑚 → 𝐴) → 𝐴` is an 𝑚-ary operation on 𝐴, and 𝑎 : 𝑚 → 𝐴 is an 𝑚-tuple on 𝐴. Then :math:`𝑔 𝑎` may be viewed as :math:`𝑔 (𝑎 0, 𝑎 1, …, a (𝑚-1))`, which has type 𝐴.

   Suppose  𝑓 : (ρ𝑓 → 𝐵) → 𝐵 is a ρ𝑓-ary operation on 𝐵, 𝑎 : ρ𝑓 → 𝐴 is a ρ𝑓-tuple on 𝐴, and ℎ : 𝐴 → 𝐵. Then ℎ ∘ 𝑎 : ρ𝑓 → 𝐵 and 𝑓 (ℎ ∘ 𝑎) : 𝐵.

Our formal implementation of the concept of signature in `Agda`_ is described in :numref:`signature type`.)

--------------------------

.. index:: ! pair: algebra; algebraic structure
.. index:: ! 𝑆-algebra, ! arity, ! trivial algebra, ! reduct

.. _algebraic-structures:

Algebraic Structures
---------------------

Our first goal is to develop a working vocabulary and formal library for classical (single-sorted, set-based) universal algebra.  In this section we define the main objects of study.

An **algebraic structure** (or **algebra**) in the signature 𝑆 = (𝐹, ρ) is denoted by :math:`𝑨 = ⟨A, F^𝑨⟩` and consists of

  #. 𝐴 := a set (or type), called the **carrier** (or **universe**) of the algebra,
  #. :math:`F^𝑨 := \{ f^𝑨 ∣ f ∈ F, \ f^𝑨 : (ρ𝑓 → A) → A \}`, a collection of **operations** on 𝐴,
  #. a collection of identities satisfied by elements of 𝐴 and the operations in :math:`F^𝑨`.

Note that to each operation symbol 𝑓 ∈ 𝐹 corresponds an operation :math:`f^𝑨` on 𝐴 of arity ρ𝑓; we call such :math:`f^𝑨` an **interpretation** of the symbol 𝑓 in the algebra 𝑨. We call an algebra in the signature 𝑆 an 𝑆-**algebra**. An algebra is called **finite** if it has a finite universe, and is called **trivial** if its universe is a singleton.  Given two algebras 𝑨 and 𝑩, we say that 𝑩 is a **reduct** of 𝑨 if both algebras have the same universe and 𝑩 can be obtained from 𝑨 by removing some operations.

Our formal implementation of the concept of algebraic structure is described in :numref:`algebras in agda`.)

.. Some of the renewed interest in universal algebra focuses on representations of algebras in categories other than **Set**, such as multisorted algebras, and higher-type universal algebra :cite:`Adamek:2011`, :cite:`Behrisch:2012`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`Meinke:1992`). These are natural generalizations that we plan to incorporate in our development later.

.. (See :numref:`Chapter %s <postmodern-algebra>`.)

---------------------------

.. index:: ! subuniverse, ! subalgebra
.. index:: 𝖲(𝑨)
.. index:: 𝖲𝗀

.. _subalgebras:

Subalgebras
-------------

This section introduces two important concepts in universal algebra, **subuniverse** and **subalgebra**. Suppose :math:`𝑨 = ⟨A, F^𝑨⟩` is an algebra. Recall, the (nonempty) set 𝐴 is called the **universe** of 𝑨.

We call a subset 𝐵 ⊆ 𝐴 **closed under** (the operations in) :math:`F^𝑨` if for each 𝑓 ∈ 𝐹 and all 𝑏 : ρ𝑓 → 𝐵 we have :math:`f^𝑨 \, b ∈ B`.

If a subset 𝐵 ⊆ 𝐴 is closed under :math:`F^𝑨`, then we call 𝐵 a **subuniverse** of 𝑨.

If 𝐵 ≠ ∅ is a subuniverse of 𝑨, and if we let :math:`F^𝑩 = \{ f^𝑨 ↾ B : f ∈ F \}`, then :math:`𝑩 = ⟨ B, F^𝑩 ⟩` is an algebra, called a **subalgebra** of 𝑨. Conversely, all subalgebras are of this form.

If 𝑩 is a subalgebra of 𝑨, we denote this fact by 𝑩 ≤ 𝑨. Similarly, we write 𝐵 ≤ 𝑨 if 𝐵 is a subuniverse of 𝑨 (relying on context and notation to disambiguate).  It helps to keep in mind the following consequence of the definitions:

  *The empty set is a subuniverse of every algebra, but the universe of an algebra is never empty*.

In other terms, if S(𝑨) denotes the collection of all subalgebras of 𝑨, then

.. math:: \mathrm S(𝑨) = \{⟨B, F^𝑩⟩ : ∅ ≠ B ≤ 𝑨\}.

If 𝒦 is a class of 𝑆-algebras, then the class of all subalgebras of algebras in 𝒦 is denoted by S(𝒦).

It is obvious that the intersection of subuniverses is again a subuniverse. Nevertheless, we will record this fact below (see :numref:`Obs. %s <obs 5>`). We will also formalize the statement and proof of this fact in Agda; see :numref:`obs 5 in Agda`.

.. index:: subuniverse generation

.. _subuniverse-generation:

Subuniverse generation
~~~~~~~~~~~~~~~~~~~~~~

As above S(𝑨) denotes the collection of all subalgebras of 𝑨.  If 𝑨 is an algebra and 𝐴₀ ⊆ 𝐴 a subset of the universe of 𝑨, then the **subuniverse of** 𝑨 **generated by** 𝐴₀ is denoted by :math:`\mathrm{Sg}^𝑨(A_0)` and defined to be the smallest subuniverse of 𝑨 containing 𝐴₀.  Equivalently,

.. math:: \mathrm{Sg}^{𝑨}(A_0)  =  ⋂ \{ U ∈ \mathrm S(𝑨) ∣ A_0 ⊆ U \}.
  :label: SgDef

We can also use recursion to define the **subuniverse of** 𝑨 **generated by a set** and prove that this new definition is equivalent to the one given by :eq:`SgDef`.  We will do this below in :numref:`Obs. %s <obs 7>` and again in :numref:`obs 7 in agda`.

---------------------------

.. index:: ! subdirect product

.. _subdirect-products:

Subdirect products
-------------------

If 𝑘, 𝑛 ∈ ℕ, if :math:`A = (A_0, A_1, \dots, A_{n-1})` is a list of sets, and if σ : 𝑘 → 𝑛 is a 𝑘-tuple, then a relation 𝑅 over 𝐴 with scope σ is a subset of the Cartesian product :math:`A_{σ(0)} × A_{σ(1)} × \cdots × A_{σ(k-1)}`.

Let 𝑆 = (𝐹, ρ) be a signature and for each 𝑖 < 𝑛 let :math:`𝑨_i = ⟨ A_i, F ⟩` be an 𝑆-algebra. If :math:`𝑨 = ∏_{i<n}𝑨_i` is the product of these algebras, then a relation 𝑅 over 𝐴 with scope σ is called **compatible with** 𝐴 if it is closed under the basic operations in 𝐹. In other words, 𝑅 is compatible if the induced algebra 𝑹 = ⟨𝑅, 𝐹⟩ is a subalgebra of :math:`\prod_{j<k} 𝑨_{σ(j)}`.

If 𝑅 is compatible with the product algebra and if the projection of 𝑅 onto each factor is surjective, then 𝑹 is called a **subdirect product** of the algebras in the list :math:`(𝑨_{σ(0)}, 𝑨_{σ(1)}, \dots, 𝑨_{σ(k-1)})`; we denote this situation by writing :math:`𝑹 ≤_{\mathrm{sd}} \prod_{j< k} 𝑨_{σ(j)}`.

**Formalization**. (not yet implemented)

.. todo:: implement subdirect product in Agda

-----------------------------------------------

.. index:: ! homomorphism
.. index:: ! epimorphism, ! monomorphism, ! automorphism

.. _homomorphisms:

Homomorphisms
-------------

Let :math:`𝑩 = ⟨B, F^𝑩⟩` and :math:`𝑪 = ⟨C, F^𝑪⟩` be algebras of the same signature, and let ℎ : 𝐵 → 𝐶 be a function (e.g., on sets).

Take an operation symbol 𝑓 ∈ 𝐹, and suppose that for all :math:`ρ f`-tuples 𝑏 : ρ𝑓 → 𝐵 of 𝐵 the following equation holds:

.. math:: h (f^𝑩 \, b) = f^𝑪 (h ∘ b).

Then ℎ is said to **respect the interpretation of** 𝑓.

If ℎ respects the interpretation of every 𝑓 ∈ 𝐹, then we call ℎ a **homomorphism** from 𝑩 to 𝑪, and we write ℎ ∈ Hom(𝑩, 𝑪), or simply, ℎ : 𝑩 → 𝑪. (Later, in Agda, we will typically use notation like ``h : hom B C``, or sometimes ``h : Hom 𝑩 𝑪``.)

A homomorphism ℎ : 𝑩 → 𝑪 is called an **epimorphism** if for every algebra 𝑫 and pair :math:`g_1, g_2: 𝑪 → 𝑫` of homomorphisms, the equation :math:`g_1 ∘ h = g_2 ∘ h` implies :math:`g_1 = g_2`. We often write ℎ : 𝑩 ↠ 𝑪, and say that "ℎ is **epi**" and "ℎ maps 𝑩 **homomorphically onto** 𝑪" in this case.

A homomorphism ℎ : 𝑩 → 𝑪 is called a **monomorphism** if for every algebra 𝑨 and every pair :math:`g_1, g_2: 𝑨 → 𝑩` of homomorphisms, the equation :math:`h ∘ g_1 = h ∘ g_2` implies :math:`g_1 = g_2`.  We sometimes write ℎ : 𝑨 ↣ 𝑩, and say that "ℎ is **mono**" and "ℎ maps 𝑩 **homomorphically into** 𝑪" in this case.

If 𝑨, 𝑩 are 𝑆-algebras and ℎ : 𝑨 → 𝑩 is a homomorphism, then the image ℎ(𝐴) of 𝐴 under ℎ is called a **homomorphic image** of 𝑨.  The collection of all homomorphic images of an 𝑆-algebra 𝑨 is the class denoted and defined by

.. math:: \mathrm H(𝑨) := \{h(𝐴) : h \text{ is a homomorphism from 𝑨 to some other 𝑆-algebra}\}.

If 𝒦 is a class of 𝑆-algebras, then the class of all homomorphic images of algebras in 𝒦 is denoted by H(𝒦).

----------------------

.. index:: ! clone
.. index:: ! clone of projections
.. index:: ! clone of polynomial operations
.. index:: ! clone of term operations

.. _clones:

Clones
------

An **operational clone** (or just **clone**) on a nonempty set 𝐴 is a collection of operations on 𝐴 that contains the projection operations and is closed under general composition.

Let 𝓒𝓵(𝐴) denote the collection of all clones on 𝐴.

The smallest clone on 𝐴 is the **clone of projections**, which we denote and define as follows:

.. math:: \mathrm{Proj}  A = ⋃_{i < n < ω}  \{π^n_i : ∀ a ∈ A^n,\ π^n_i\, a = a(i)\}.

Recall, the natural number 𝑘 < ω can be constructed as (or at least identified with) the set {0, 1, …, 𝑘-1}. For each 𝑘 < ω, denote and define the tuple πᵏ : (𝑘 → 𝐴) → 𝐴 of all 𝑘-ary projections on 𝐴 as follows: for each 0 ≤ 𝑖 < 𝑘, πᵏ(𝑖) is the 𝑖-th 𝑘-ary projection operation that takes each 𝑘-tuple 𝑎 : 𝑘 → 𝐴 to its entry at index 𝑖, 

.. math:: π^k (i) a = a(i).

.. Observe that if 𝑓 : (𝑘 → 𝐴) → 𝐴 is a 𝑘-ary operation on 𝐴, then

The **clone of term operations** of an 𝑆-algebra 𝑨 is the smallest clone on 𝐴 containing the basic operations of 𝑨; this is denoted and defined by

.. math:: \mathrm{Clo}(F^𝑨) = ⋂ \{ U ∈ 𝓒𝓵 A ∣ F^𝑨 ⊆ U\}.

The set of 𝑛-ary members of :math:`\mathrm{Clo}(F^𝑨)` is sometimes denoted by :math:`\mathrm{Clo}_n (F^𝑨)` (despite the fact that the latter is obviously not a clone).

The **clone of polynomial operations** (or **polynomial clone**) of an 𝑆-algebra 𝑨 is denoted by :math:`\mathrm{Pol} (F^𝑨)` and is defined to be the clone generated by the collection consisting of the basic operations (i.e., :math:`F^𝑨`) of 𝑨 along with the **constants** on 𝐴. [3]_

The set of 𝑛-ary members of :math:`\mathrm{Pol} (F^𝑨)` is sometimes denoted by :math:`\mathrm{Pol}_n (F^𝑨)`. 

The clone :math:`\mathrm{Clo}(F^𝑨)` is associated with the algebra 𝑨 only insofar as the former is constructed out of the basic operations of 𝑨 and the set 𝐴 on which those operations are defined.  However, all that is required when defining a clone is a set 𝐴 and some collection 𝐹 of operations defined on :math:`A`; from only these ingredients, we can construct the clone generated by 𝐹, which we denote by Clo(𝐹).

Thus

  *the clone of terms operations can be implemented as an inductive type*.

We will make this precise below (see :numref:`Obs. %s <obs 7>`).

------------------------

.. index:: ! term, ! term algebra, ! free algebra

.. _terms and free algebras:

Terms and free algebras
---------------------------

This section is based on the section of the same title in Cliff Bergman's excellent textbook (:cite:`Bergman:2012`). Apart from notation, our presentation is quite similar in style and content to Cliff's, but we have attempted to give a more compact, abridged treatment in order to get more quickly to our ultimate goal (in the next chapter), which is to show how it is possible to express the concepts and theorems of universal algebra in type theory and to formalize them in the Agda language.  We refer the reader to Section 4.3 of :cite:`Bergman:2012` for more details and examples about "classical" (informal) universal algebra than we present here.

.. _terms:

Terms
~~~~~~~~~~

Fix a :term:`signature` 𝑆 = (𝐹, ρ), let 𝑋 be a set of **variables**, and assume 𝑋 ∩ 𝐹 = ∅.

By a **word** on 𝑋 ∪ 𝐹 we mean a nonempty, finite sequence of members of 𝑋 ∪ 𝐹, and we will denote the concatenation of such sequences by simple juxtaposition.

Let 𝐹₀ denote the set of nullary operation symbols of 𝑆. We define by induction on 𝑛 the sets 𝑇ₙ of **terms on** 𝑋 ∪ 𝐹 as follows (cf. :cite:`Bergman:2012` Def. 4.19):

.. math::      T_0 &= X ∪ F_0;\\
           T_{n+1} &= T_n ∪ \{ f\, s ∣ f ∈  F, \ s: ρf → T_n \},

and we define the collection of **terms of signature** 𝑆 **over** 𝑋 by 𝑇(𝑋) = :math:`⋃_{n < ω}T_n`.

By an 𝑆-**term** we mean a term in the signature 𝑆.

The definition of 𝑇(𝑋) is recursive, indicating that *terms could be implemented as an inductive type*. We will confirm this in :numref:`types for terms` when we implement terms in Agda. Moreover, we will formalize an algebraic structure on 𝑇(𝑋), called the **term algebra** in the signature 𝑆. We describe it here and then state and prove some basic facts about this important algebra. These will be formalized in :numref:`types for terms` and :numref:`birkhoffs theorem in agda`, giving us a chance to show off inductively defined types in Agda.

If 𝑡 is a term, then the **height** of 𝑡 is denoted by ∣𝑡∣ and defined to be the least 𝑛 such that 𝑡 ∈ 𝑇ₙ. The height is a useful index for recursion and induction.

If 𝑇(𝑋) is nonempty (equivalently, 𝑋 ∪ 𝐹₀ is nonempty), then we can impose upon it an algebraic structure, which we will denote by 𝑻(𝑋). We call 𝑻(𝑋) the **term algebra in the signature** 𝑆 **over** 𝑋; it is constructed as follows:

  * for each operation symbol 𝑓 ∈ 𝐹, let :math:`f^{𝑻(X)}` be the operation on 𝑇(𝑋) that maps each tuple :math:`𝑠 : ρ𝑓 → 𝑇(𝑋)` to the formal term 𝑓 𝑠;
  * define 𝑻(𝑋) to be the algebra with universe 𝑇(𝑋) and operations :math:`\{f^{𝑻(X)} | f ∈ F\}`.

.. _free algebras:

Free algebras
~~~~~~~~~~~~~~~~~~~

Fix a :term:`signature` 𝑆 = (𝐹, ρ), let 𝒦 be a class of 𝑆-algebras, let :math:`𝑼 = ⟨𝑈, 𝐹^𝑼⟩` be an 𝑆-algebra, and let 𝑋 be a subset of 𝑈. We say that

  #. 𝑼 has the :term:`universal mapping property` for 𝒦 over 𝑋 if for every 𝑨 ∈ 𝒦 and every function ℎ : 𝑋 → 𝐴, there is a homomorphism :math:`h' : 𝑼 → 𝑨` that agrees with ℎ on 𝑋;

  #. 𝑼 is :term:`free for 𝒦 over 𝑋` if it has the :term:`universal mapping property` and is generated by 𝑋;

  #. 𝑼 is :term:`free in 𝒦 over 𝑋` if it is free for 𝒦 over 𝑋 and belongs to 𝒦.

We use the next definition to take a free algebra *for* a class 𝒦 and produce the free algebra *in* 𝒦.

Let 𝒦 be a class of 𝑆-algebras and 𝑨 an 𝑆-algebra. Define

.. math:: ψ(𝒦, 𝑨) & := \{θ ∈ \mathrm{Con} 𝑨 : 𝑨/θ ∈ \mathrm S(𝒦)\} \text{ and } \\
          Ψ(𝒦, 𝑨) &:= ⋀ ψ(𝒦, 𝑨).

Notice that :math:`ψ(𝒦, 𝑨)` may be empty, in which case :math:`Ψ(𝒦, 𝑨) = 1_A` and :math:`𝑨/Ψ(𝒦, 𝑨)` is trivial.

We apply these ideas to the algebra 𝑻(𝑋) of 𝑆-terms over 𝑋. Since 𝑻(𝑋) is free for the class 𝒜𝓁ℊ of all 𝑆-algebras, it follows that 𝑻(𝑋) is free for every subclass 𝒦 of 𝒜𝓁ℊ.

Of course, 𝑻(𝑋) is not necessarily a member of 𝒦, but we can form the quotient of 𝑻(𝑋) modulo the congruence :math:`Ψ(𝒦, 𝑻(𝑋))`, which we denote by 

.. Let 𝑆 = (𝐹, ρ) be a signature, 𝒦 a class of 𝑆-algebras, and 𝑋 a set. Assuming 𝑋 ∪ 𝐹₀ is nonempty, we define

.. math:: 𝔽(𝒦, 𝑋) := 𝑻(𝑋)/Ψ(𝒦, 𝑻(𝑋)),

which is called the **free algebra over** 𝒦 **generated by** 𝑋; it is free *in* SP(𝒦).

Strictly speaking, 𝑋 is not a subset of 𝔽(𝒦, 𝑋) so it doesn't make sense to say that "𝑋 generates 𝔽(𝒦, 𝑋)."  But as long as 𝒦 contains a nontrivial algebra, we will have :math:`Ψ(𝒦, 𝑻(𝑋)) ∩ 𝑋² ≠ ∅`, and we can identify 𝑋 with :math:`𝑋/Ψ(𝒦, 𝑻(𝑋))` in 𝔽(𝒦, 𝑋). (See :numref:`Obs %s <obs 9.6>`.)

-------------------------------
           
.. _arity:

Arity
-----

We denote and define the set :math:`X := \{x_0,x_1,\dots \}` of variable symbols, and for each natural number :math:`n` we let :math:`X_n:=\{x_0,x_1,\dots, x_{n-1}\}`.

Let 𝑆 = (𝐹, ρ) be a signature, 𝑨 an 𝑆-algebra, and 𝑻(X) the term algebra over 𝑋; that is,

.. math:: 𝑨 := ⟨A, F^𝑨⟩ \quad \text{ and } \quad 𝑻(X) := ⟨T(X), F^{𝑻(X)}⟩.

Each operation symbol 𝑓 ∈ 𝐹 gives rise to

#.  a ρ𝑓-ary operation on 𝑇(𝑋), denoted by :math:`f^{𝑻(X)}`, which maps each tuple :math:`𝑠 : ρ𝑓 → 𝑇(𝑋)` to the formal term 𝑓 𝑠 in 𝑇(𝑋), and

#.  a ρ𝑓-ary operation on 𝐴, denoted by :math:`f^𝑨`, which maps each tuple :math:`𝑎 : ρ𝑓 → 𝐴` to the element :math:`f^𝑨 \,a` in 𝐴. The operation :math:`f^𝑨` is called the **interpretation of** 𝑓 **in the algebra** :math:`𝑨`.

.. index:: ! arity (of a term)

.. _essential arity:

Essential arity
~~~~~~~~~~~~~~~~~~~~~~

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


.. index:: ! interpretation (of a term)
.. index:: ! term operation

.. _term operations:

Term Operations
--------------------

In :numref:`terms` we defined a term in a given signature.  When we interpret such a term in a particular algebraic structure, we get what is known as a term operation.  In this section we explain how one defines the interpretation of an 𝑆-term in an 𝑆-algebra, and thus how one obtains a term *operation*.

As usual, for each 0 < 𝑛 < ω we identify the 𝑛-tuple :math:`(x_0, x_1, \dots, x_{n-1})` with the function :math:`x:  𝑛 → X_n` defined by :math:`x\, i = x_i` (0 ≤ 𝑖 < 𝑛).

Recall, a term 𝑡 is either a variable, say, 𝑡 = 𝑥, or has the form 𝑡 = 𝑓 𝑠 for some operation symbol 𝑓 ∈ 𝐹, and some ρ𝑓-tuple 𝑠 : ρ𝑓 → 𝑇(𝑋) of terms.

Let 𝑡 ∈ 𝑇(𝑋) be a term. Define the **term operation** :math:`t^𝑨` on 𝐴 by recursion on the :term:`height` ∣𝑡∣ of 𝑡 as follows: for each tuple 𝑎 : 𝑋 → 𝐴 of 𝐴,

#. (∣𝑡∣ = 0) if 𝑡 is the variable 𝑥ᵢ ∈ 𝑋, then :math:`t^𝑨 \, a = π^X_i\, a = a\, i`,
#. (∣𝑡∣ = 𝑛+1) if 𝑡 = 𝑓 𝑠 where 𝑓 ∈ 𝐹 is an operation symbol and 𝑠 : ρ𝑓 → 𝑇ₙ is a tuple of terms whose heights are at most 𝑛 (i.e., ∀ 𝑖 < ρ𝑓, ∣𝑠 𝑖∣ ≤ 𝑛), then :math:`t^𝑨 = f^𝑨 \, s^𝑨`.


.. The **interpretation** of :math:`t(x)` in 𝑨, often denoted by :math:`t^𝑨(x)`, is the :math:`(ρ t)`-ary operation on :math:`A` defined by recursion on the structure of :math:`t`, as follows:#. if :math:`t(x)` is simply the variable :math:`x i ∈ X`, and if 𝑎 is a :math:`(ρ t)`-tuple of :math:`A`, then :math:`t^𝑨(a) = a i`; that is, :math:`t^𝑨(a)` is the projection of the input tuple onto its :math:`i`-th coordinate.#. if :math:`t = 𝓸 𝑓`, where 𝓸 is a basic operation symbol with interpretation :math:`𝓸^𝑨` in 𝑨 and :math:`𝑓 : (ρ 𝓸) →` Term is a (ρ 𝓸)-tuple of terms, each with interpretation :math:`(𝑓 i)^𝑨`, then :math:`t^𝑨(𝑓)` is :math:`𝓸^𝑨 \bigl( λ (i : ρ 𝓸) . (𝑓 i)^𝑨\bigr)`.




----------------------------------------------------------------------------------------------

.. index:: ! model
.. index:: ! pair: σ-identity; σ-equation
.. index:: ! pair: identity; equation
.. index:: ! pair: equational base; axiomatization
.. index:: ! pair: equational theory; theory
.. index:: ! pair: equational class; variety

.. _models_and_theories:

Models and theories
-------------------

Let 𝑆 = (𝐹, ρ) be a signature and :math:`X := \{x_0, x_1, \dots\}` a countable collection of variable symbols.

An **identity in the signature** 𝑆 (or "𝑆-identity") is an ordered pair of terms (𝑝, 𝑞) ∈ 𝑇(𝑋) × 𝑇(𝑋). We usually write 𝑝 ≈ 𝑞 to indicate such an identity. Although, when we have a collection of identities, say, Σ, we could indicate that 𝑝 ≈ 𝑞 is among the identities in Σ by writing (𝑝, 𝑞) ∈ Σ. We sometimes refer to an identity as an **equation**; for us, the words "identity" and "equation" are synonyms.

Let :math:`𝒜_𝑆`, resp. :math:`ℰ_𝑆`, denote the class of all 𝑆-algebras, resp. 𝑆-identities.

For 𝑨 ∈ 𝒦 ⊆ :math:`𝒜_S` and :math:`(p, q) ∈ Σ ⊆ ℰ_S`, we say that

* 𝑨 **models** 𝑝 ≈ 𝑞, denoted 𝑨 ⊧ 𝑝 ≈ 𝑞, just in case :math:`p^𝑨 = q^𝑨` :term:`extensionally <extensional>` (recall, this means ∀ 𝑎 : 𝑋 → 𝐴 we have :math:`p^𝑨 \, a = q^𝑨 \, a`.);

* 𝑨 **models** Σ, denoted 𝑨 ⊧ Σ, just in case 𝑨 ⊧ 𝑝 ≈ 𝑞 holds for every (𝑝, 𝑞) ∈ Σ;

* 𝒦 **models** 𝑝 ≈ 𝑞 just in case 𝑨 ⊧ p ≈ q holds for every 𝑨 in 𝒦;

* 𝒦 **models** Σ just in case 𝑨 ⊧ Σ for every 𝑨 ∈ 𝒦.

**Notation**. To produce the symbols ≈ and ⊧ in Emacs ``agda2-mode``, type ``\~~`` and ``\models`` (resp.). To denote "𝒦 models 𝑝 ≈ 𝑞" we will use 𝒦 ⊧ 𝑝 ≋ 𝑞 instead of the more standard 𝒦 ⊧ 𝑝 ≈ 𝑞 because we distinguish it from 𝑨 ⊧ 𝑝 ≈ 𝑞 in our Agda implementation. The symbol ≋ is produced in Emacs ``agda2-mode`` with ``\~~~``.

The binary relation :math:`⊧` induces an obvious :term:`Galois connection`. Indeed, the :term:`Galois pair` (Mod, Th) is defined as follows: for all :math:`Σ ⊆ ℰ_S` and :math:`𝒦 ⊆ 𝒜_S`, 

.. math:: \mathrm{Mod}(Σ) := \{𝑨 ∈ 𝒜_S : 𝑨 ⊧ Σ \} \quad \text{ and } \quad \mathrm{Th}(𝒦) := \{Σ ∈ ℰ_S : 𝒦 ⊧ Σ\}.

The first of these, the class of **models** of Σ, contains those and only those algebras modeling every identity in Σ. It is called an **equational class**, and Σ is called an **equational base** for, or an **axiomatization** of, the class.

Dually, Th(𝒦) is the class of identities modeled by every algebra in 𝒦.  Such a class of identities is called an **equational theory**.

Alternatively and equivalently we could define "equational class" and "equational theory" in terms of the two :term:`closure operators <closure operator>` induced by the Galois pair (Mod, Th).  Indeed, :math:`\mathrm{Mod}\, \mathrm{Th} : 𝒫(𝒜) → 𝒫(𝒜)` is a closure operator on 𝒜 and :math:`\mathrm{Th}\, \mathrm{Mod} : 𝒫(ℰ) → 𝒫(ℰ)` is a closure operator on ℰ, and 

* an **equational class** is a Mod Th-:term:`closed class <closed set>` of 𝑆-algebras;

* an **equational theory** is a Th Mod-:term:`closed set` of 𝑆-identities

(where, 𝒫 denotes the :term:`power set operator`).

**N.B.** An equational class is sometimes referred to as a **variety**; this is because of the celebrated Birkhoff theorem which states that a class of algebraic structures is an equational class if and only if it is closed under the taking of homomorphic images (H), subalgebras (S), and products (P). A formal Agda proof of Birkhoff's theorem is one of our main goals which we achieve in :ref:`the birkhoff module <the birkhoff module>` described in :numref:`the birkhoff module`.

--------------------------

.. _basic facts:

Basic facts
------------

We conclude this chapter with a list of basic facts and their (informal) proofs.  These results are classical, straightforward consequences of the definitions above. We will need them below and when we cite them later, we will refer to them as, e.g, :numref:`Obs %s <obs 1>`, :numref:`Obs %s <obs 2>`, etc.  Each of these observations is formalized in Agda in the `agda-ualib`_.

Throughout this section,

  :math:`𝑨 = ⟨A, F^𝑨⟩, \ 𝑩 = ⟨B, F^𝑩⟩, \ 𝑪 = ⟨C, F^𝑪⟩\ ` are algebras in the same signature 𝑆 = (𝐹, ρ).

Equalizers
~~~~~~~~~~~~~

We start with the simple observation that equalizers of homomorphisms are subuniverses.

.. index:: ! equalizer

.. about the :math:`σ`-term algebra over :math:`X`.

.. _obs 1:

.. proof:observation:: Ex 1.4.6.a of :cite:`Bergman:2012`

   If :math:`g, h : \mathrm{Hom}(𝑨, 𝑩)` are homomorphisms from 𝑨 to 𝑩, then the **equalizer** of :math:`g` and :math:`h`, which we denote :math:`𝖤(g,h) = \{a: A ∣ g\, a = h\, a\}`, is a subuniverse of 𝑨.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      Fix arbitrary :math:`f ∈ F` and :math:`a : ρf → 𝖤(g,h)`.

      We show that :math:`g (f^𝑨 \, a) = h (f^𝑨 \, a)`, as this will show that :math:`𝖤(g, h)` is closed under the operation :math:`f^𝑨` of :math:`𝑨`.

      For all :math:`i<ρ f` we have :math:`a \, i ∈ 𝖤(g,h)`, so :math:`g\, a \, i= h\, a\, i`.  Therefore (by function extensionality) :math:`g ∘ a = h ∘ a` and so, by definition of homomorphism,

      .. math:: g  (f^𝑨\,a) = f^𝑩 (g ∘ a) = f^𝑩 (h ∘ a) = h (f^𝑨\, a).

      ☐

The Agda formalization of this result and its proof is presented in :numref:`obs 1 in agda`.

Homomorphisms
~~~~~~~~~~~~~~~

Another easy fact is that composing homomorphisms results in a homomorphism.

.. _composition of homomorphisms:

.. _obs 2:

.. proof:observation:: composing homs gives a hom

   If :math:`g: \mathrm{Hom}(𝑨, 𝑩)` and :math:`h: \mathrm{Hom}(𝑩, 𝑪)` (homomorphisms from 𝑨 to 𝑩 and 𝑩 to 𝑪, resp.), then :math:`h \circ g : \mathrm{Hom}(𝑩, 𝑪)` (a homomorphisms from 𝑨 to 𝑪).

The easy proof of this fact is formalized in :numref:`obs 2 in agda` .

Another elementary result is that homomorphisms are uniquely determined by the values they take on generating sets.

.. _obs 3:

.. proof:observation:: Ex 1.4.6.b of :cite:`Bergman:2012`

   Let 𝑨 = ⟨𝐴, …⟩ and 𝑩 be 𝑆-algebras and :math:`f, g` homomorphisms from 𝑨 to 𝑩. If the subset 𝐴₀ ⊆ 𝐴 generates 𝑨, and if :math:`f` and :math:`g` agree on 𝐴₀, then :math:`f = g`.

   .. container:: toggle

      .. container:: header

         *Proof*.

      We show that :math:`f` and :math:`g` are extensionally equal (that is, :math:`f\, a = g\, a` for every :math:`a \in A`). So, fix an arbitrary :math:`a \in A`. Since :math:`𝐴₀` generates 𝑨, there exists a term :math:`t` and a tuple :math:`𝒂 : X → 𝐴₀` of generators such that :math:`a = t^𝑨\, 𝒂`.

      Since :math:`f|_{𝐴₀} = g|_{𝐴₀}`, we have

      .. math:: f ∘ 𝒂 = (f\, 𝒂(0), f\, 𝒂(1), \dots) = (g \, 𝒂(0), g\, 𝒂(1), \dots) = g ∘ 𝒂,

      so

      .. math:: f\, a = f(t^𝑨 \, 𝒂) = t^𝑩 (f ∘ 𝒂) = t^𝑩 (g ∘ 𝒂) = g(t^𝑨 \,𝒂) = g\, a.

      ☐

Our Agda proof of :numref:`Obs %s <obs 3>` is called ``HomUnique``.  It is presented :numref:`obs 3 in agda`.

A corollary of the last result is an easily proved bound on the cardinality of :math:`|\mathrm{Hom}(𝑨, 𝑩)|`.

.. _obs 4:

.. proof:observation:: Ex 1.4.6.c of :cite:`Bergman:2012`

   If :math:`A, B` are finite and :math:`X` generates 𝑨, then :math:`|\mathrm{Hom}(𝑨, 𝑩)| ≤ |B|^{|X|}`.

   .. container:: toggle

      .. container:: header

         *Proof*.

      By :numref:`Obs %s <obs 3>`, a homomorphism is uniquely determined by its restriction to a generating set.

      If :math:`X` generates 𝑨, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\mathrm{Hom}(𝑨, 𝑩)| ≤ |B|^{|X|}`. ☐

Here is an elementary result about factorability of homomorphisms.  The informal proof is presented below and its formalization in :numref:`obs 5 in agda`.

.. _obs 5:

.. proof:observation::

   If :math:`g ∈` Hom(𝑨, 𝑩) is surjective, if ℎ ∈ Hom (𝑨, 𝑪), and if ker :math:`g` ⊆ ℎ, then

   .. math:: ∃ f ∈ \mathrm{Hom}(𝑩, 𝑪), \ h = f ∘ g.

   .. container:: toggle

      .. container:: header

         *Proof*.

      We define 𝑓 ∈ Hom(𝑩, 𝑪) as follows:

      Fix 𝑏 ∈ 𝐵

      Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} ⊆ A` is nonempty, and since ker :math:`g` ⊆ ker ℎ, it is clear that every element of :math:`g^{-1}\{b\}` is mapped by ℎ to a single element of 𝐶.

      Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a ∈ g^{-1}\{b\}`.

      For each such 𝑏, and its associated :math:`c_b`, define :math:`f(b) = c_b`. [4]_

      It is then easy to see that :math:`f ∘ g = h`.  Indeed, for each 𝑎 ∈ 𝐴, we have :math:`a ∈ g^{-1}\{g(a)\}`, so :math:`f\,g(a) = h(a)` by definition.

      Finally, to prove that :math:`k` is a homomorphism, fix an operation symbol :math:`f ∈ F` and a tuple :math:`b:ρf → B`; we will show that

      .. math:: f^𝑪 (k ∘ b) = k (f^𝑩(b)).
         :label: hom1

      Let :math:`a: ρf → A` be such that :math:`g ∘ a = b`.  Then the left hand side of :eq:`hom1` is :math:`f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a)`, which is equal to :math:`h (f^𝑨 (a))` since :math:`h` is a homomorphism.

      Therefore,

      .. math::

         f^𝑪 (k ∘ b) &= f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a)\\
                 & = h (f^𝑨 (a)) = (k ∘ g)(f^𝑨 (a))\\
                 & = k (f^𝑩 (g ∘ a)) = k (f^𝑩 (b)),

      as desired, where the penultimate equality holds by virtue of the fact that :math:`g` is a homomorphism. ☐

We formalize :numref:`Obs %s <obs 5>` in the `homomorphisms module`_ of the agda-ualib_; see :numref:`obs 5 in agda`.

Next we observe that the intersection of subuniverses is again a subuniverse, a fact that we prove formally in the `subuniverses module`_ of the agda-ualib_; see :numref:`obs 6 in agda`.

.. _obs 6:

.. proof:observation::

   Suppose :math:`A_i ≤ 𝑨` for all :math:`i` in some set :math:`I`. Then :math:`⋂_{i∈ I} A_i` is a subuniverse of :math:`𝑨`.

   .. container:: toggle

      .. container:: header

         *Proof*.

      (easy exercise)

.. --------------------------------------------------------------------------------------
.. SUBUNIVERSE GENERATION
.. -------------------------------------------

Next is a theorem that provides a means of generating subuniverses recursively.

.. _obs 7:

.. proof:observation:: Thm 1.14 of :cite:`Bergman:2012`

   Let :math:`𝑨 = ⟨A, F^{𝑨}⟩`  be  an  algebra in the signature :math:`σ = (F, ρ)` and let :math:`A_0` be a subset of :math:`A`.

   Define, by recursion on :math:`n`, the sets :math:`A_n` as follows:

     If :math:`A_0 = ∅`, then :math:`A_n = ∅` for all :math:`n<ω`.

     If :math:`A_0 ≠ ∅`, then

     .. math:: A_{n+1} =  A_n ∪ \{ f\, a ∣ f ∈ F, \ a : ρf → A_n\}.
        :label: subalgebra-inductive

   Then the subuniverse of 𝑨 generated by :math:`A_0` is :math:`\mathrm{Sg}^𝑨(A_0) = ⋃_{n<ω} A_n`.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let :math:`Y := ⋃_{n < ω} A_n`. Clearly :math:`A_n ⊆ Y ⊆ A`, for every :math:`n < ω`. In particular :math:`A = A_0 ⊆ Y`. We first show that Y is a subuniverse of 𝑨.

      Let :math:`f` be a basic :math:`k`-ary operation and let :math:`a: k → Y` be a :math:`k`-tuple of elements of :math:`Y`.

      From the construction of :math:`Y`, there is an :math:`n < ω` such that :math:`∀ i,\ a,\ i ∈ A_n`.

      From its definition, :math:`f \,a ∈ A_{n+1} ⊆ Y`. Since :math:`f` was arbitrary, it follows that :math:`Y` is a subuniverse of 𝑨 containing :math:`A_0`.

      Thus, by :eq:`SgDef`, :math:`\mathrm{Sg}^𝑨(A_0) ⊆ Y`.

      For the opposite inclusion, it is enough to check, by induction on :math:`n`, that :math:`A_n ⊆ \mathrm{Sg}^𝑨(A_0)`.

      Clearly, :math:`A_0 ⊆ \mathrm{Sg}^𝑨(A_0)`.

      Assume :math:`A_n ⊆ \mathrm{Sg}^𝑨(A_0)`.  We show :math:`A_{n+1} ⊆ \mathrm{Sg}^𝑨(A_0)`.

      If :math:`b ∈ A_{n+1} - A_n`, then :math:`b = f\, a` for a basic :math:`k`-ary operation :math:`f` and some :math:`a: k) → A_n`.

      But :math:`∀ i, \ a i ∈ \mathrm{Sg}^𝑨(A_0)` and since this latter object is a subuniverse, :math:`b ∈ \mathrm{Sg}^𝑨(X)` as well.

      Therefore, :math:`A_{n+1} ⊆ \mathrm{Sg}^𝑨(A_0)`, as desired. ☐

.. The argument in the proof of :numref:`Obs <obs 7>` is of a type that one encounters frequently throughout algebra. It has two parts.

..   #. Some set :math:`Y` is shown to be a subuniverse of 𝑨 that contains :math:`A_0`.

..   #. Every subuniverse containing :math:`A_0` is shown to contain :math:`Y` as well.

..   #. One concludes that :math:`Y = \mathrm{Sg}^𝑨 (A_0)`.

We formally implement the concept of subalgebra in the `subuniverses module`_ of the agda-ualib_, which we describe in :numref:`subuniverses in agda`. In particular, we describe the formalization of :numref:`Obs %s <obs 7>` in :numref:`obs 7 in agda`.

.. _obs 7.1:

.. proof:observation:: Lem 3.1 and Thm 3.2 of :cite:`Bergman:2012`

   Let ℎ : 𝑨 → 𝑩 be a homomorphism.

   * If 𝑈 is a subuniverse of 𝑨, then ℎ(𝑈) = \{ℎ(𝑢) : 𝑢 ∈ 𝑈\} is a subuniverse of 𝑩.

   * If 𝑉 is a subuniverse of 𝑩, then ℎ⁻¹\{𝑉\} is a subuniverse of 𝑨.

   * If 𝑋 is a subset of 𝐴, then :math:`ℎ(\mathrm{Sg}^𝑨(𝑋)) = \mathrm{Sg}^𝑩(ℎ(𝑋))`.

   .. container:: toggle

      .. container:: header

         *Proof*.

      The first two items are easy to prove (exercise).  For the third item, it is easy to check that ℎ is order-preserving on subsets. This and the first two items yield

      .. math:: 𝑋 ⊆ \mathrm{Sg}^𝑨(𝑋) \; ⇒ \; ℎ(𝑋) ⊆ ℎ(\mathrm{Sg}^𝑨(𝑋)) \; ⇒ \; \mathrm{Sg}^𝑩(ℎ(𝑋)) ⊆ ℎ(\mathrm{Sg}^𝑨(𝑋)).

      Conversely, using the lemma again,

      .. math:: X ⊆ h⁻¹ h(𝑋) ⊆ h⁻¹(\mathrm{Sg}^𝑩(h(X))) \; ⇒ \; \mathrm{Sg}^𝑨(𝑋) ⊆ h⁻¹(\mathrm{Sg}^𝑩(h(X)))

      and this implies

      .. math:: h(\mathrm{Sg}^𝑨(𝑋)) ⊆ h(h⁻¹(\mathrm{Sg}^𝑩(h(X)))) ⊆ \mathrm{Sg}^𝑩(h(X)).

Our formalization of :numref:`Obs %s <obs 7.1>` is presented in :numref:`obs 7.1 in agda`.

.. --------------------------------------------------------------------------------------
.. CLONE GENERATION
.. -------------------------------------------

.. We seek a "bottom-up," inductive description of the members of :math:`\mathrm{Clo}(F)`.  By thinking of the clone itself as a kind of algebra, a description analogous to :numref:`Obs %s <obs 6>` ought to be possible.  In fact, since function composition is associative, a slightly slicker formulation is available. Inductive version of Clo(F).  (UAFST Thm 4.3) Let A be a set and let F ⊆ Op(A):= ⋃ₙ A^Aⁿ be a collection of operations on A. Define F_0 := Proj(A) (the set of projection operations on A), and for all 0 ≤ n < ω, F_{n+1} := Fₙ ∪ {f g | f ∈ F, g : ρf → Fₙ ∩ (ρg → A)}. Then Clo(F) = ⋃ₙ Fₙ. *Proof*. Let F̄ = ⋃ₙ Fₙ. By induction, every Fₙ is a subset of Clo(F). Thus, F ⊆ Clo(F). For the converse inclusion, we must show F` is a clone that contains F. Obviously F contains the projection operations, F₀ ⊆ F̄. For every f ∈ F, we have f πᵏ ∈ F₁ ⊆ F̄, where k := ρ f. We must show that F̄ is closed under generalized composition. This follows from the following subclaim.  *Subclaim*. If f ∈ Fₙ and all entries of g := (g₀, ..., g_{ρf - 1} ∈ Fₘ are k-ary, then f g ∈ F_{n+m}, where we have defined g: ρf -> (k -> A) -> A to be the tuple given by g i = gᵢ for  each 0 ≤ i < ρ f. By induction on n: If n = 0 then f is a projection, so f g = gᵢ ∈ Fₘ for some 0 ≤ i < ρ f. Assume (IH) claim holds for n and f ∈ F_{n+1} - Fₙ.  By def, ∃ t-ary op fᵢ ∈ F, ∃ t-tuple, h = (h₀, ..., h_{t-1}) ∈ t -> Fₙ, such that f = fᵢ h. (N.B. h: Fin(t) → (Fin(ρ f) → A) → A is given by h(j) = hⱼ, and the arity of each hᵢ must be equal to that of f, namely ρ f.) By (IH) for each i ≤ k, hᵢ = hᵢ g ∈ F_{n+m}, where as above g = (g₀,...,g_{k-1}). By def, f₁ h' ∈ F_{n+m+1} = F_{(n+1)+m}. Since f₁ h' = f₁ ∘ (h₁ g, ..., hₜ g) = f g, the claim is proved. □

.. _obs 8:

.. proof:observation:: Thm 4.3 of :cite:`Bergman:2012`

   Let 𝐴 be a set and let :math:`F ⊆ \mathrm{Op}(A):= ⋃_{n<ω} A^{A^n}` be a collection of operations on 𝐴.

   Define :math:`F_0 := \mathrm{Proj} (A)` (the set of projections on :math:`A`) and for all :math:`0 ≤ n < ω` let

   .. math:: F_{n+1} := F_n ∪ \{ f g \mid f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.

   Then :math:`\mathrm{Clo}(F) = ⋃_n F_n`.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let :math:`F̄ = ⋃_n F_n`. It is easy to argue by induction that every :math:`F_n` is a subset of :math:`\mathrm{Clo}(F)`. Thus, :math:`F ⊆ \mathrm{Clo}(F)`.

      For the converse, we must show that :math:`F̄` is a clone that contains :math:`F`. Obviously :math:`F̄` contains the projection operations, :math:`F_0 ⊆ F̄`.  For every :math:`f ∈ F`, we have :math:`f π^k ∈ F_1 ⊆ F̄`, where :math:`k:= ρ f`.  We are reduced to showing that :math:`F̄` is closed under generalized composition. This holds by the following claim.

      **Claim**. If :math:`f ∈ F_n` and :math:`g_0, \dots, g_{ρ f-1} ∈ F_m` are
       all :math:`k`-ary, then :math:`f g \in F_{n+m}`, where we have defined
       :math:`g: ρf → (k → A) → A` to be the tuple given by :math:`g\,i = g_i`
       for each :math:`0 ≤ i < ρ f`.

      Note that the types match up; indeed, for each :math:`a: (k → A) → A`, we have

      .. math:: f (g ∘ a) = f(g_0(a_0, \dots, a_{k-1}),

      We prove the claim by induction on :math:`n`. If :math:`n = 0` then :math:`f` is a projection, so :math:`f g = g_i ∈ F_{0+m}` for some :math:`0≤ i < ρ f`. Assume the claim holds for :math:`n` and that :math:`f ∈ F_{n+1} - F_n`.  From the definition, there is a :math:`t`-ary operation :math:`f_i ∈ F` and a :math:`t`-tuple :math:`h = (h_0, \dots, h_{t-1}) ∈ t → F_n`, such that :math:`f = f_i h`. (Note that :math:`h: t → (ρf → A) → A` is given by :math:`h(j) = h_j`, and that the arity of each :math:`h_i` must be equal to that of :math:`f`, namely :math:`ρ f`.)

      By the induction hypothesis, for each :math:`i ≤ k`, :math:`h_i' = h_i g \in F_{n+m}` (where, as above, :math:`g = (g_0, \dots, g_{k-1})`).

      Applying the definition, :math:`f_1 h' ∈ F_{n+m+1} = F_{(n+1)+m}`. Since

      .. math:: f_1 h' = f_1 ∘ (h_1 g, \dots, h_t g) = f g,

      the claim is proved. □

We implement terms and the term algebra in Agda in the `terms module`_, as described in :numref:`terms`. Also in the `terms module`_ is a formal proof of the next result; see :numref:`obs 9 in agda`.


.. _obs 9:

.. proof:observation:: Thm 4.21 of :cite:`Bergman:2012`

   #. 𝑇(𝑋) is generated by 𝑋.

   #. For every 𝑆-algebra 𝑨 = :math:`⟨𝐴, 𝐹^𝑨⟩` and function :math:`g: X → A` there is a unique homomorphism ℎ : 𝑻(𝑋) → 𝑨 such that :math:`h|_X = g`. We call such ℎ the **lift of** :math:`g` **from** 𝑋 **to** 𝑻(𝑋) (or, more simply, the **lift of** :math:`g` **to** 𝑻(𝑋)).

   .. container:: toggle

      .. container:: header

         *Proof*.

      The definition of 𝑻(𝑋) exactly parallels the construction in :numref:`Obs. %s <obs 7>`. That accounts for the first assertion.  For the second, define ℎ 𝑡 by induction on the :term:`height` of 𝑡.

      Suppose ∣𝑡∣ = 0.  Then 𝑡 ∈ 𝑋 ∪ 𝐹₀. If 𝑡 ∈ 𝑋, then define ℎ 𝑡 = 𝑔 𝑡. If 𝑡 ∈ 𝐹₀, then let :math:`h\,t = t^𝑨`.

      For the induction step, assume ∣𝑡∣ = 𝑛 + 1. Then 𝑡 = 𝑓 𝑠 for some 𝑓 ∈ 𝐹 and 𝑠 : ρ 𝑓 → 𝑇ₙ, where for each 0 ≤ 𝑖 < ρ𝑓 the term 𝑠 𝑖 has height at most 𝑛. We define :math:`h\,t = f^𝑨(h ∘ s) = f^𝑨(h\,s_1, …, h\,s_k)`. By its very definition, ℎ is a homomorphism that agrees with :math:`g` on 𝑋. The uniqueness of ℎ follows from :numref:`Obs %s <obs 3>`.


Let 𝒜𝓁ℊ(𝑆) be the class of all 𝑆-algebras. Then :numref:`Obs %s <obs 9>` can be restated as: 𝑻(𝑋) is free in 𝒜𝓁ℊ(𝑆) over 𝑋. This is sometimes expressed by saying that 𝑻(𝑋) is **absolutely free** over 𝑋.

.. _obs 9.1:

.. proof:observation:: Prop 4.23 of :cite:`Bergman:2012`

   Let 𝑼 be free for 𝒦 over 𝑋. Then for every 𝑨 ∈ 𝒦 and :math:`𝑔 : 𝑋 → 𝐴`, the lift of :math:`g` from 𝑋 to 𝑼 (defined in the second part of :numref:`Obs %s <obs 9>`) is unique.

   .. container:: toggle

      .. container:: header

         *Proof*.

      The universal mapping property asserts the existence of the lift. The fact that 𝑼 is generated by 𝑋 accounts for uniqueness.

.. _obs 9.2:

.. proof:observation:: Prop 4.24 of :cite:`Bergman:2012`

   Let 𝑼₁ and 𝑼₂ be free in 𝒦 over 𝑋₁ and 𝑋₂ respectively. If ∣ 𝑋₁ ∣ = ∣ 𝑋₂ ∣, then 𝑼₁ ≅ 𝑼₂.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      If ∣ 𝑋₁ ∣ = ∣ 𝑋₂ ∣, then there are mutually inverse bijections ℎ : 𝑋₁ → 𝑋₂ and ℎ⁻¹ : 𝑋₂ → 𝑋₁. Since 𝑼₂ ∈ 𝒦 and 𝑼₁ is free for 𝒦, there is a homomorphism ℎ̃₁ : 𝑼₁ → 𝑼₂ extending ℎ and, by the symmetric argument, a homomorphism ℎ̃₂ : 𝑼₂ → 𝑼₁ extending ℎ⁻¹. Now, ℎ̃₂ ∘ ℎ̃₁ is an endomorphism of 𝑼₁ extending the identity map, and so is the identity morphism on 𝑼₁.  Thus, by unicity (:numref:`Obs %s <obs 9.1>`), ℎ̃₂ ∘ ℎ̃₁ is the identity morphism on 𝑼₁. By the symmetric argument,  ℎ̃₁ ∘ ℎ̃₂ is the identity morphism on 𝑼₂. Thus 𝑼₁ ≅ 𝑼₂.

It follows from :numref:`Obs %s <obs 9.2>` that, up to isomorphism, a free algebra is determined by the cardinality of a free generating set.

Next we observe that freeness extends from a class 𝒦 to the variety it generates.

.. _obs 9.3:

.. proof:observation:: Prop 4.25 of :cite:`Bergman:2012`

   If 𝑼 is free for 𝒦 over 𝑋, then it is free for HSP(𝒦) over 𝑋.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let 𝑼 be free for 𝑋 over 𝑋. It suffices to show that if C is one of H, S or P, then 𝑼 has the universal mapping property for C(𝒦) over 𝑋. Consider the case 𝑨 ∈ H(𝒦). Then there is 𝑩 ∈ 𝒦 and a surjective homomorphism 𝑓 : 𝑩 → 𝑨. Let ℎ : 𝑋 → 𝐴 be a function. We must find an extension of h to a homomorphism from 𝑼 to 𝑨. For each 𝑥 ∈ 𝑋 choose an element 𝑏ₓ ∈ 𝑓⁻¹\{ℎ(𝑥)\}. Define the function :math:`𝑔 : 𝑋 → 𝐵` by :math:`g(x) = b_x`. Since 𝑼 is free for 𝒦 and 𝑩 ∈ 𝒦, :math:`g` extends to a homomorphism :math:`g̃ : 𝑼 → 𝑩`. Then :math:`𝑓 ∘ g̃` is the desired extension of ℎ.

      Next assume 𝑨 ∈ S(𝒦). Then, 𝑨 ≤ 𝑩 ∈ 𝒦. A mapping ℎ : 𝑋 → 𝐴 is automatically a mapping to 𝐵. By freeness, ℎ extends to a homomorphism :math:`ℎ' : 𝑼 → 𝑩`. Since 𝑋 generates 𝑼,

      .. math:: ℎ'(𝑈) = \{h'(u) : u ∈ 𝑈\} = ℎ'(\mathrm{Sg}^𝑼(X)) = \mathrm{Sg}^𝑩(h'(X)) ⊆ 𝐴.

      by :numref:`Obs %s <obs 7.1>`. Consequently, :math:`ℎ'` is actually a map from 𝑈 to 𝐴.

      Finally, assume 𝑨 = Π 𝑩ᵢ, where 𝑩ᵢ ∈ 𝒦 for each 𝑖. If ℎ : 𝑋 → 𝐴 then for each 𝑖, 𝑝ᵢ ∘ ℎ is a mapping from 𝑋 to 𝐵ᵢ. By freeness we get homomorphisms :math:`ℎᵢ' : 𝑼 → 𝑩ᵢ` which can be reassembled to obtain :math:`ℎ' = Π ℎᵢ' : 𝑼 → 𝑨`.

.. _obs 9.4:

.. proof:observation:: Lem 4.27 of :cite:`Bergman:2012`

   If 𝒦 is a class of 𝑆-algebras and 𝑨 an 𝑆-algebra, then 𝑨/Ψ(𝒦, 𝑨) ∈ SP(𝒦).

   .. container:: toggle

      .. container:: header

         *Proof*.

      Observe that

      .. math:: 𝑨/Ψ(𝒦, 𝑨) ↪ Π ⟨ 𝑨/θ : θ ∈ ψ(𝒦, 𝑨) ⟩ ∈ \mathrm{PS}(𝒦),

      so :math:`𝑨/Ψ(𝒦, 𝑨)` ∈ SPS(𝒦) = SP(𝒦)`.

.. _obs 9.5:

.. proof:observation:: Thm 4.28 of :cite:`Bergman:2012`

   Let 𝑼 be free for 𝒦 over 𝑋. Then 𝑼/Ψ(𝒦, 𝑼) is free in SP(𝒦) over 𝑋/Ψ(𝒦, 𝑼).

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let :math:`𝑼' = 𝑼/Ψ(𝒦, 𝑼)` and :math:`𝑋' = 𝑋/(Ψ(𝒦, 𝑼) ∩ 𝑋²)`. Since 𝑋 generates 𝑼, it follows from :numref:`Obs %s <obs 7.1>` that 𝑋 generates :math:`𝑼'`. From :numref:`Obs %s <obs 9.4>`, :math:`𝑼'` ∈ SP(𝒦). If we can show that 𝑼 has the :term:`UMP` for 𝑋, then by :numref:`Obs %s <obs 9.3>` :math:`𝑼'` will be free in SP(𝒦) over 𝑋.

      Fix 𝑨 ∈ 𝒦 and :math:`ℎ : 𝑋' → 𝐴`, and let 𝑞 be the canonical map from 𝑼 to :math:`𝑼'`. Since 𝑼 is free over 𝑋, there is a homomorphism ℎ̃ : 𝑼 → 𝑨 extending ℎ ∘ 𝑞. Let η = ker ℎ̃. Then 𝑼/η ∈ S(𝑨) ⊆ S(𝒦), so :math:`η ∈ ψ(𝒦, 𝑼)` and therefore :math:`Ψ(𝒦, 𝑼) ≤ η`. Since :math:`Ψ(𝒦, 𝑼) = ker 𝑞`, there is a homomorphism :math:`ℎ' : 𝑼' → 𝑨` such that :math:`ℎ̃ = h' ∘ q`. But now it follows easily that :math:`h'` restricted to :math:`X'` is equal to ℎ.


As Bergman notes (see the remark after Def 4.29 in :cite:`Bergman:2012`), "strictly speaking, 𝑋 is not a subset of 𝔽(𝒦, X), so it doesn’t make sense to talk about 𝑋 generating 𝔽(𝒦, X), [but] as long as 𝒦 contains a nontrivial algebra, :math:`Ψ(𝒦, 𝑋) ∩ 𝑋² = 0_X`. In light of [:numref:`Obs %s <obs 9.2>`], we 
can identify 𝑋 with 𝑋/Ψ(𝒦, 𝑋) in 𝔽(𝒦, 𝑋). All of these considerations are accounted for in the following corollary."


.. _obs 9.6:

.. proof:observation:: Cor 4.30 of :cite:`Bergman:2012`

   Let 𝒱 be a variety of 𝑆-algebras. If 𝑋 ∪ 𝐹₀ ≠ ∅, then 𝔽(𝒱, 𝑋) is free in 𝒱 over 𝑋.  If 𝒱 = 𝕍(𝒦), the variety generated by 𝒦, then 𝔽(𝒱, 𝑋) = 𝔽(𝒦, 𝑋) ∈ SP(𝒦).


In the next observation, assume 𝑨 = :math:`⟨A, F^𝑨⟩` and 𝑩 = :math:`⟨B, F^𝑩⟩` are 𝑆-algebras , and let 𝑡 ∈ 𝑇(𝑋) be a term in the language of 𝑆.  In particular, 𝑡 has an interpretation in 𝑨 (see :numref:`interpretation of a term`), which we denote by :math:`t^𝑨`. Similarly, :math:`t^𝑩` is the interpretation of 𝑡 in 𝑩.

.. _thm 4.32:

.. _obs 10:

.. proof:observation:: homomorphisms commute with terms

   If 𝑓 : 𝑨 → 𝑩 is a homomorphism, then :math:`g ∘ a : 𝑛 → B` is the 𝑛-tuple whose 𝑖-th component is :math:`(g ∘ a)\, i = g(a\, i)`, and :math:`g(t^𝑨 a) = t^𝑩(g ∘ a)`.

   .. container:: toggle

      .. container:: header

        *Proof*.

      This is an easy induction on ∣𝑡∣.

We formalize :numref:`Obs %s <obs 10>` and its proof in the `terms module`_ of the agda-ualib_, as described in :numref:`obs 10 in agda`.

.. _obs 11:

.. proof:observation:: terms respect congruences

   Let 𝑨 be an 𝑆-algebra, 𝑡 a term in the language of 𝑆, and θ a congruence of 𝑨.  Then for all tuples 𝒂, 𝒃 : 𝑋 → 𝑨, we have (∀ 𝑖, (𝒂 𝑖) θ (𝒃 i)) → :math:`(t^𝑨 𝒂) \mathrel{θ} (t^𝑨 𝒃)`.

   .. container:: toggle

      .. container:: header

        *Proof*.

      This follows from :numref:`Obs %s <obs 10>` by taking :math:`⟨B, F^𝑩⟩ = ⟨A, F^𝑨⟩/θ = ⟨A/θ, F^{𝑨/θ}⟩` and :math:`g=` the canonical homomorphism. ☐

We formalize :numref:`Obs %s <obs 11>` and its proof in the `terms module`_ of the agda-ualib_, as described in :numref:`obs 11 in agda`.

.. _obs 12:

.. proof:observation:: subuniverse generation as image of terms

   If 𝑌 is a subset of 𝐴, then

      .. math:: \mathrm{Sg}^{𝑨}(Y) = \{t^𝑨 𝒂 : t ∈ T(X), 𝒂 : X → Y\}.

   .. container:: toggle

      .. container:: header

        *Proof*.

      A straightforward induction on the height of 𝑡 shows that every subuniverse is closed under the action of :math:`t^𝑨`. Thus the right-hand side is contained in the left. On the other hand, the right-hand side is a subuniverse that contains the elements of 𝑌 (take 𝑡 = 𝑥), so it contains :math:`\mathrm{Sg}^{𝑨}(Y)` as the latter is the smallest subuniverse containing 𝑌.

We formalize :numref:`Obs. %s <obs 12>` and its proof in the `subuniverses module`_ of the agda-ualib_, as described in :numref:`obs 12 in agda`.

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
..    Then :math:`\mathrm{Clo}^X(F) = ⋃_n F_n`.
..
..
.. For a nonempty set :math:`A`, we let :math:`\mathrm{Op}_A` denote the set of all finitary operations on :math:`A`. That is, :math:`\mathrm{Op}_A = ⋃_{n∈ ℕ} A^{A^n}` on :math:`A` is a subset of :math:`\mathrm{Op}_A` that contains all projection operations and is closed under the (partial) operation of :ref:`<general composition>`.
..
.. If :math:`𝑨 = ⟨ A, F^𝑨 ⟩` denotes the algebra with universe :math:`A` and set of basic operations :math:`F`, then Clo(𝑨) denotes the clone generated by :math:`F`, which is also known as the **clone of term operations** of :math:`𝑨`.
..
.. We will discuss varieties in more detail later, but for now define a :index:`variety` to be a collection of algebras of the same signature which is defined by a set of identities. [5]_
..
.. In 1977, Walter Taylor showed (:cite:`Taylor1977`) that a variety 𝕍 satisfies some nontrivial :term:`idempotent` :term:`Malcev condition` if and only if it satisfies one of the following form: for some :math:`n`, 𝕍 has an idempotent :math:`n`-ary term  :math:`t` such that for each :math:`0 ≤ i < n` there is an identity of the form
..
..    .. math:: t(∗, \cdots, ∗, x, ∗, \cdots, ∗) ≈ t(∗, \cdots, ∗, y, ∗, \cdots, ∗)
..
.. that is true in 𝕍 and is such where distinct variables :math:`x` and :math:`y` appear in the :math:`i`-th position on each side of the identity. Such a term :math:`t` now goes by the name :index:`Taylor term`.

.. .. [3]
..   We will also have much to say about Malcev conditions, but for now we ask the reader to trust us when we say that such conditions play an important role in many deep results in universal algebra.



.. (fact-m1)

.. _obs 13:

.. proof:observation:: Lem 4.36 of :cite:`Bergman:2012`

   If 𝒦 is a class of 𝑆-algebras, then each of the classes S(𝒦), H(𝒦), P(𝒦), 𝕍(𝒦) satisfies the same set of identities as does 𝒦.

.. container:: toggle

   .. container:: header

      *Proof*.

   We prove the result for H(𝒦). 𝒦 ⊆ H(𝒦), so Th H (𝒦) ⊆  Th 𝒦 …

We present a formalization of this result and its proof in :numref:`obs 13 in agda`.

.. fact-m2

.. _obs 14:

.. proof:observation:: Lem 4.37 of :cite:`Bergman:2012`

   Let 𝓚 be a class of 𝑆-algebras, 𝑻(𝑋) the term algebra over 𝑋, and 𝑝, 𝑞 terms in the language of 𝑆. Then,

   .. math:: 𝒦 ⊧ p ≈ q \; ⇔ \; ∀ 𝑨 ∈ 𝒦, ∀ h ∈ \mathrm{Hom}(𝑻(X), 𝑨), h ∘ p^{𝑻(X)} = h ∘ q^{𝑻(X)}.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let 𝑻(X) denote the term algebra over 𝑋, 𝑇(𝑋) the collection of terms, in the language of 𝑆.

      (⇒) Assume 𝒦 ⊧ 𝑝 ≈ 𝑞. Fix 𝑨 ∈ 𝒦,  ℎ : 𝑻(𝑋) → 𝑨, and 𝒂 : X → ∣ 𝑻(𝑋) ∣.  By 𝑨 ⊧ 𝑝 ≈ 𝑞 we have :math:`p^𝑨 = q^𝑨` which implies :math:`p^𝑨(h ∘ 𝒂) = q^𝑨(h ∘ 𝒂)`. Since ℎ is a homomorphism, we obtain :math:`h (p^{𝑻(X)} 𝒂) = h (q^{𝑻(X)} 𝒂)`, as desired.

      (⇐) Assume ∀ 𝑨 ∈ 𝒦, ∀ ℎ : Hom 𝑻(𝑋) 𝑨, we have :math:`h ∘ p^{𝑻(X)} = h ∘ q^{𝑻(X)}`. Fix 𝑨 ∈ 𝒦 and 𝒂 : X → ∣ 𝑨 ∣.  We prove :math:`p^𝑨 𝒂 = q^𝑨 𝒂`.  By :numref:`Obs. %s <obs 9>`, 𝒂 extends to a homomorphism from 𝑻(𝑋) to 𝑨. Denote this extension by 𝒂̂.  By assumption  :math:`𝒂̂ ∘ p^{𝑻(X)} = 𝒂̂ ∘ q^{𝑻(X)}`, and since 𝒂̂ is a homomorphism, :math:`p^𝑨 𝒂 =  p^𝑨(𝒂̂ ∘ x) = 𝒂̂ (p^𝑨 x) = 𝒂̂ (q^𝑨 x) = q^𝑨 (𝒂̂ ∘ x) = q^𝑨 𝒂`.

We formalize :numref:`Obs %s <obs 14>` and its proof in the `birkhoff module`_ of the agda-ualib_, as described in :numref:`obs 14 in agda`.

.. (fact-m3)

.. _obs 15:

.. _Thm 4.38:

.. proof:theorem:: Thm 4.38 of :cite:`Bergman:2012`

   Let 𝒦 be a class of algebras and 𝑝 ≈ 𝑞 an equation. The following are equivalent.

    #. 𝒦 ⊧ 𝑝 ≈ 𝑞.
    #. (𝑝, 𝑞) belongs to the congruence Ψ(𝒦, 𝑋) on 𝑻(𝑋).
    #. 𝔽(𝒦, 𝑋) ⊧ 𝑝 ≈ 𝑞.

   .. container:: toggle

      .. container:: header

         *Proof*.

     To simplify notation, let 𝔽 := 𝔽(𝒦, 𝑋) and Ψ := Ψ(𝒦, 𝑋). Recall that 𝔽 = 𝑻(𝑋)/Ψ ∈ SP(𝒦). We show (1) ⟹ (3) ⟹ (2) ⟹ (1).

      (1) ⟹ (3). From (1) and :numref:`Obs %s <obs 13>` we have SP(𝒦) ⊧ 𝑝 ≈ 𝑞. Thus (3) holds.

      (3) ⟹ (2). From (3), :math:`p^𝔽 [x] = q^𝔽 [x]`, where [x]: 𝑋 → 𝔽is defined by [x] 𝑖 = 𝑥ᵢ/Ψ. From the definition of 𝔽, :math:`p^𝑻 𝑥 Ψ q^𝑻 𝑥`, from which (2) follows since :math:`p = p^𝑻 𝑥` and :math:`q = q^𝑻 𝑥`.

      (2) ⟹ (1). We wish to apply :numref:`Obs %s <obs 14>`. Let 𝑨 ∈ 𝒦 and ℎ ∈ Hom(𝑻(𝑋), 𝑨). Then 𝑻(𝑋)/(ker ℎ) ∈ S(𝑨) ⊆ S(𝒦) so ker h ⊇ Ψ.  Thus, (2) implies ℎ 𝑝 = ℎ 𝑞 hence (1) holds.

The last result tells us that we can determine whether an identity is true in a variety 𝒱 by consulting a particular algebra, namely 𝔽(𝒱, 𝑋), the free algebra in 𝒱.

.. Sometimes it is convenient to work with algebras free on other generating sets besides 𝑋. The following corollary takes care of that for us.

.. .. _Obs 2.16:
.. .. _Thm 4.41:

.. .. proof:theorem:: Birkhoff (1935) Every  finitely  generated  variety  is  locally finite. (UAFST Thm 3.49)

.. (This is not needed for the HSP theorem, but we might want to prove it next.)

.. The converse of the last theorem is false.  That is, ∃ loc fin varieties that are not finitely generated(e.g., the variety of p-algebras; see UAFSt Cor. 4.55).

.. _obs 16:

.. proof:observation:: Cor 4.39 of :cite:`Bergman:2012`

   Let 𝒦 be a class of algebras, 𝑝, 𝑞 terms (say, 𝑛-ary), 𝑋 a set, and 𝑥 a tuple of distinct elements of 𝑋. Then 𝒦 ⊧ 𝑝 ≈ 𝑞 if and only if :math:`p^{𝔽(𝒦, 𝑋)} 𝑥 = q^{𝔽(𝒦, 𝑋)} 𝑥`. In particular, 𝒦 ⊧ 𝑝 ≈ 𝑞 iff 𝔽(𝒦, 𝑋) ⊧ 𝑝 ≈ 𝑞.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Since 𝔽(𝒦, 𝑋) ∈ SP(𝒦), the left-to-right direction uses the same argument as in :numref:`Obs %s <obs 15>`.  So assume that :math:`p^{𝔽(𝒦, 𝑋)} 𝑥 = q^{𝔽(𝒦, 𝑋)} 𝑥`. To show that 𝒦 ⊧ 𝑝 ≈ 𝑞, we fix :math:`𝑨 = ⟨𝐴, 𝑓^𝑨⟩ ∈ 𝒦` and ℎ₀ : 𝑋 → 𝐴, and show that :math:`p^𝑨 ℎ₀ = q^𝑨 ℎ₀`. By :numref:`Obs %s <obs 9>`, ℎ₀ extends to a homomorphism :math:`ℎ' : 𝑻(𝑋) → 𝑨`, so there is a homomorphism :math:`h : 𝔽(𝒦, 𝑋) → (A, f^𝑨)` such that ℎ(𝑥 𝑖) = ℎ₀(𝑥 𝑖) for all 𝑖 ≤ 𝑛. Therefore,

      .. math:: p^𝑨\, ℎ₀ = p^𝑨\, ℎ = ℎ \, p^{𝔽(𝒦, 𝑋)} = ℎ\, q^{𝔽(𝒦, 𝑋)} = q^𝑨 \, ℎ = q^𝑨\, ℎ₀.


--------------------------

.. _birkhoffs theorem:

Birkhoff's theorem
---------------------

It follows from :numref:`Obs %s <obs 13>` that every equational class is a variety.  The converse is Birkhoff's celebrated HSP theorem which we present next.

The statement and proof we give here is essentially the same as that given in Theorem 4.41 of Cliff Bergman's textbook :cite:`Bergman:2012`.  It is this statement and proof that we will formalize in Agda in the `birkhoff module`_ of the agda-ualib_; see :numref:`birkhoffs theorem in agda`.

.. proof:theorem:: Thm 4.41 of :cite:`Bergman:2012`

   Every variety is an equational class.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let 𝒲 be a class of algebras closed under H, S, and P (i.e., a variety). We must find a set Σ of equations that axiomatizes 𝒲 (that is, such that 𝒲 = Mod(Σ)), as this will prove that 𝒲 is the class of algebras satisfying the set of equations Σ (i.e., that 𝒲 is an equational class). The obvious choice for Σ is Th(𝒲), the set of all equations that hold in 𝒲. Let :math:`𝒲'` = Mod(Σ).  Clearly, :math:`𝒲 ⊆ 𝒲'`, so we must prove the reverse inclusion.

      Let 𝑨 ∈ 𝒲' and let 𝑋 be a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑋 → 𝐴. By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝑻(𝑋) → 𝑨. Since 𝔽(𝒲, 𝑋) = 𝑻(𝑋)/Ψ(𝒲, 𝑋), there is an epimorphism 𝑔 : 𝑻(𝑋) → 𝔽(𝒲, 𝑋). We claim ker 𝑔 ⊆ ker ℎ. If the claim is true, then by :numref:`Obs %s <obs 5>` there is a map 𝑓 : 𝔽(𝒲, 𝑋) → 𝐴 such that 𝑓 ∘ 𝑔 = ℎ and since ℎ is epic, so is 𝑓, so 𝑨 ∈ H(𝔽(𝒲, 𝑋)) ⊆ 𝒲` which will complete the proof.

      Now we prove the claim that ker 𝑔 ⊆ ker ℎ. Let 𝑢, 𝑣 ∈ 𝑻(𝑋) and assume 𝑔(𝑢) = 𝑔(𝑣). Since 𝑻(𝑋) is generated by 𝑋, there are terms 𝑝, 𝑞 ∈ 𝑻(𝑋) and 𝑥 such that :math:`𝑢 = p^{𝑻(𝑋)}(𝑥)` and :math:`𝑣 = q^{𝑻(X)}(𝑥)`. Therefore, applying the homomorphism 𝑔, we have

      .. math:: p^{𝔽(𝒲, 𝑋)} 𝑥 = 𝑔(𝑢) = 𝑔(𝑣) = q^{𝔽(𝒲, 𝑋)} 𝑥.

      Thus 𝒲 ⊧ 𝑝 ≈ 𝑞, hence (𝑝, 𝑞) ∈ Σ. Since 𝑨 ∈ Mod(Σ) we get 𝑨 ⊧ 𝑝 ≈ 𝑞. Therefore, :math:`ℎ(𝑢) = 𝑝^𝑨(ℎ₀ ∘ 𝑥) = 𝑞^𝑨(ℎ₀ ∘ 𝑥) = ℎ(𝑣)`, as desired.





.. We end this subsection with yet another standard but important result.
   .. _obs 17:
   .. proof:observation::
       Every  finitely  generated  variety  is  locally finite.
       (See Thm 3.49 of :term:`UAFST` for the proof.)
       The converse of the last theorem is false.  That is, there exist locally finite varieties that are not finitely generated (e.g., the variety of :math:`p`-algebras; see Cor. 4.55 of :term:`UAFST`).

---------------------------

.. rubric:: Footnotes

.. [1]
   Viewing 𝑚 : ℕ as roughly equivalent to 𝑚 ∈ ℕ is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. [3]
   By "the constants on :math:`A`" we mean the **constant operations**; i.e., functions :math:`f: A → A` such that :math:`∀ a ∈ A, f(a) = c`, for some :math:`c ∈ A`.

.. [4]
   The observant reader may have noticed a slight-of-hand in the foregoing "construction" of the function 𝑓. While it's true that for each 𝑏 ∈ 𝐵 there exists a :math:`c_b` such that :math:`h(a) = c_b` for all :math:`a ∈ g^{-1}\{b\}`, it's not immediately clear that we have a means of producing such :math:`c_b` constructively.

   One could argue that each :math:`c_b` is easily computed as :math:`c_b = h(a)` for some (every) :math:`a ∈ g^{-1}\{b\}`. But this requires producing a particular :math:`a ∈ g^{-1}\{b\}` to use as "input" to the function :math:`h`. How do we select such a "witness" from the set :math:`g^{-1}\{b\}`? Fortunately, for the purposes of formalizing this proof (constructively, in Agda) we will see that our definition of surjective function will supply such a witness whenever it is needed. (See :numref:`obs 5 in agda`.)

      ------------------

.. include:: hyperlink_references.rst

