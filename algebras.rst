.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _algebras:

========
Algebras
========

Our vision for the `lean-ualib`_ (Lean Universal Algebra Library) originated with our observation that, on the one hand, a number of the most basic and important constructs in universal algebra can be defined recursively, while on the other hand, :term:`type theory` in general, and :term:`dependent <dependent type>` and :term:`inductive types <inductive type>` in particular, facilitates elegant representations of recursively defined objects. Such objects can therefore be implemented in a :term:`proof assistant` such as `Lean`_, a language that not only supports :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`, but also provides powerful :term:`tactics <proof tactic>` for proving properties of objects that inhabit these types.

These observations suggest that there is much to gain from implementing universal algebra in a proof assistant that offers powerful tools for working with :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`. Lean is one such proof assistant.

The goal of the `Lean Universal Algebra Library`_, and this documentation explaining it, is to demonstrate that our vision manifests in a careful (and, whenever possible, :term:`constructive`) presentation of the elementary theory of universal algebra in the language of type theory, along with a formal implementation of this theory in the Lean proof assistant.  Specific examples of this manifestation appear below in :numref:`subalgebras-in-lean`, :numref:`terms-in-lean`, and :numref:`clones-in-lean`.

.. In particular, our Lean_ implementation of the notion of :term:`subuniverse` illustrates one of these underlying themes motivating our work.

Specifically, we present fundamental definitions and theorems about :term:`subalgebras <subalgebra>`, terms, and clones---first in this chapter using the informal language of universal algebra, and then in the next chapter using the formal language of Lean.

The idea is to demonstrate the power and utility of implementing the theory in a formal language that supports :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`, which are essential for expressing and working with infinite objects in a :term:`constructive` and :term:`computable` way, and for proving (by induction) properties of these objects.

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

**Formalization**. Our formal implementation (in `Lean`_) of the concept of signature is described in :numref:`Section %s <signatures-in-lean>` and is included in the `basic.lean`_ file of the `lean-ualib`_ library.

In :numref:`Chapter %s <postmodern-algebra>` we give alternative, category theoretic definitions of these concepts and show how this alternative presentation can often simplify implementation of the mathematics in :term:`type theory`.

--------------------------

.. index:: pair: ! algebra; ! algebraic structure
.. index:: ! σ-algebra, ! arity, ! trivial algebra, ! reduct

.. _algebraic-structures:

Algebraic Structures
---------------------

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`Adamek:2011`, :cite:`Behrisch:2012`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`Meinke:1992`). These are natural generalizations that we will incorporate in our development later. (See :numref:`Chapter %s <postmodern-algebra>`.) But our first goal is to develop a working library for classical (single-sorted, set-based) universal algebra. We now define such structures.

A (universal) **algebraic structure** (or, **algebra**) is a pair :math:`⟨A, F⟩` where :math:`A` is a *nonempty* set and :math:`F = \{f_i: i ∈ I\}` is a collection of finitary operations on :math:`A`.

That is, :math:`f_i: A^n → A` for some :math:`n ∈ ℕ`.

.. A common shorthand for :eq:`algebra` is :math:`⟨A, f_i⟩_{i ∈ I}`.

The number :math:`n` is called the **arity** of the operation :math:`f_i`.

If :math:`A=ℝ` and :math:`f: ℝ × ℝ → ℝ` is the map that takes each pair :math:`(a, b) ∈ ℝ × ℝ` to the number :math:`f(a,b) = a+b ∈ ℝ`, then :math:`⟨A, \{f\}⟩` is an example of an algebra with a single binary operation. In such cases, we often simplify the notation and write :math:`⟨A, f⟩` in stead of :math:`⟨A, \{f\}⟩`.

.. An algebra is called **unary** if all of its operations are unary. 

An algebra is **finite** if :math:`|A|` is finite, and is called **trivial** if :math:`|A| = 1`.

Given two algebras :math:`𝔸` and :math:`𝔹`, we say that :math:`𝔹` is a **reduct** of :math:`𝔸` if both algebras have the same universe and :math:`𝔹` can be obtained from :math:`𝔸` by removing  operations.

.. index:: ! operation symbol, ! arity, ! interpretation, ! signature, ! similarity type

A better approach
~~~~~~~~~~~~~~~~~

An **operation symbol** :math:`f` is an object that has an associated **arity**; we denote the arity of :math:`f` by :math:`ρ \,f`.

A pair :math:`(F, ρ)` consisting of a set :math:`F` of operation symbols and an arity function :math:`ρ: F → N` is called a **signature** (or, **similarity type**).

A (universal) **algebra** (or, **algebraic structure**) in the signature :math:`σ = (F, ρ)` is denoted by :math:`𝔸 = ⟨A, F^𝔸⟩` and consists of 

  #. :math:`A` := a set, called the **carrier** (or **universe**) of the algebra,
  #. :math:`F^𝔸 = \{ f^𝔸 ∣ f ∈ F, \ f^𝔸 : (ρ f → A) → A \}` is a collection of operations on :math:`A`,
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝔸`.

Note that to each operation symbol :math:`f∈ F` corresponds an operation :math:`f^𝔸` on :math:`A` of arity :math:`ρ f`; we call this :math:`f^𝔸` the **interpretation** of :math:`f` in :math:`𝔸`.

We call an algebra in the signature :math:`σ` a :math:`σ`-**algebra** (although this is not standard). [3]_ 

.. proof:example::

   Consider the set of integers :math:`ℤ` with operation symbols :math:`F = \{0, 1, -(\,), +, ⋅\}`, which have respective arities :math:`\{0, 0, 1, 2, 2\}`.

   The operation :math:`+^ℤ` is the usual binary addition, while :math:`-^ℤ(\,)` is negation, which takes the integer :math:`z` to :math:`-^ℤ(z) = -z`.

   The constants :math:`0^ℤ` and :math:`1^ℤ` are nullary operations. Of course we usually just write :math:`+` for :math:`+^ℤ`, etc.

More examples of algebraic structures that have historically played a central role in mathematics over the last century (e.g., groups, rings, modules) are described in the next section.

**Formalization**. Our formal implementation (in `Lean`_) of the concept of algebraic structure is described in :numref:`algebras-in-lean`, and is included in the `basic.lean`_ file of the `lean-ualib`_ library.


.. index:: ! magma, ! groupoid, ! binar, ! vector space, ! bilinear algebra, ! associative algebra, ! semigroup, ! monoid, ! group, multiplicative inverse, ! abelian group, additive identity, additive inverse,! ring, ! unital ring, ! multiplicative identity, ! unit, ! division ring, ! field, ! module 

.. _examples-of-algebras:

Examples of algebras
~~~~~~~~~~~~~~~~~~~~~~

Recall from above that an algebra :math:`𝔸` is an ordered pair :math:`𝔸 = ⟨A, F^𝔸⟩` where :math:`A` is a nonempty set and :math:`F` is a family of finitary operations on :math:`A`.

The set :math:`A` is called the **universe** of :math:`𝔸`, and the elements :math:`f^𝔸 ∈ F` are called the **basic operations** of :math:`𝔸`.

(In practice we often write :math:`f` instead of :math:`f^𝔸` when no ambiguity could result from this shorthand.

Here is a list of a few of the most frequently encountered and historically important algebraic structures. [4]_

* **Magma**. An algebra :math:`⟨A, ⋅⟩` with a single binary operation is called a **magma** (or **groupoid** or **binar**). The operation is usually denoted by :math:`+` or :math:`⋅`, and we write :math:`a+b` or :math:`a ⋅ b` (or just :math:`ab`) for the image of :math:`(a, b)` under this operation, which we call the *sum* or *product* of :math:`a` and :math:`b`, respectively.

* **Semigroup**. A magma :math:`⟨A, ⋅⟩` whose binary operation is associative is called a **semigroup**.  That is, a semigroup is a magma whose binary operation satisfies :math:`∀ a, b, c ∈ A`, :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)`.

* **Monoid**. If :math:`⟨A, ⋅⟩` is a semigroup and if :math:`e ∈ A` is a *multiplicative identity* (i.e., :math:`∀ a ∈ A`, :math:`e ⋅ a = a ⋅ e = a`), then :math:`⟨A, \{e, ⋅\}⟩` is called a **monoid**.

* **Group**. A **group** is a monoid along with a unary operation :math:`^{-1}` called *multiplicative inverse*. That is, the reduct :math:`⟨ A, \{e, ⋅\}⟩` is a monoid and :math:`^{-1}`
  satisfies :math:`a ⋅ a^{-1} =  a^{-1} ⋅ a = e`, for all :math:`a ∈ A`.
  
* **Abelian group**. A group is called **abelian** just in case its binary operation is commutative, in which case we usually denote the operation by :math:`+` instead of :math:`⋅`. Also in this case we let :math:`0` (instead of :math:`e`) denote the *additive identity*, and we let :math:`-\,` (instead of :math:`^{-1}`) denote the *additive inverse*. Thus, an **abelian group** is a group :math:`𝔸 = ⟨ A, 0, -,+⟩` such that :math:`a+b = b+a` for all :math:`a, b ∈ A`.

* **Ring**. An algebra :math:`⟨R, \{0, -, +, ⋅\}⟩` is called a **ring** just in case the following conditions hold:

  #. the reduct :math:`⟨R, \{0, -,+\}⟩` is an abelian group,

  #. the reduct :math:`⟨R, ⋅ ⟩` is a semigroup, and

  #. "multiplication" :math:`⋅` distributes over "addition" :math:`+`; that is, :math:`∀ a, b, c ∈ R`, :math:`a ⋅ (b+c) = a ⋅ b + a ⋅ c` and :math:`(a+b)⋅ c = a ⋅ c + b ⋅ c`.

  A **ring with unity** (or **unital ring**) is an algebra :math:`⟨R, \{0, 1, -, +, ⋅\}⟩` with a ring reduct :math:`⟨R, \{0, -, +, ⋅\}⟩` and a *multiplicative identity* :math:`1 ∈ R`; that is :math:`∀ r ∈ R`, :math:`r ⋅ 1 = r = 1 ⋅ r`.

  If :math:`⟨R, \{0, 1, -, +, ⋅\}⟩` is a unital ring, an element :math:`r ∈ R` is called a **unit** if it has a multiplicative inverse, that is, there exists :math:`s ∈ R` with :math:`r ⋅ s = 1 = s ⋅ r`.  (We usually denote such an :math:`s` by :math:`r^{-1}`.)

* **Division ring**.  A ring in which every non-zero element is a unit is called a **division ring**.

* **Field**. A commutative division ring is called a **field**.

* **Module**. Let :math:`R` be a ring with unit. A **left unitary** :math:`R`-**module** (or simply :math:`R`-**module**) is an algebra :math:`⟨M, \{0, -, +\} ∪ \{f_r : r∈ R\}⟩` with an abelian group reduct :math:`⟨M, \{0, -, +\}⟩` and unary operations :math:`\{f_r : r ∈ R\}` that satisfy the following: :math:`∀ r, s ∈ R`, :math:`∀ x, y ∈ M`,

  #. :math:`f_r(x + y)  = f_r(x) + f_r(y)`

  #. :math:`f_{r+s}(x) = f_r(x) + f_s(x)`

  #. :math:`f_r(f_s(x)) = f_{rs}(x)`

  #. :math:`f_1(x) = x`.

  Note that Condition 1 says that each :math:`f_r` is an :term:`endomorphism` of the abelian group :math:`⟨ M, \{0, -, +\}⟩`, while the other conditions amount to the following: (1) the set :math:`E := \{f_r ∣ r∈ R\}` of endomorphisms is a ring with unit where multiplication is function composition, and (2) the map :math:`r ↦ f_r` is a ring :term:`epimorphism` from :math:`R` onto :math:`E`.

  One reason modules are important is that every ring is, up to isomorphism, a ring of endomorphisms of some abelian group. This fact is analogous to the more familiar theorem of Cayley stating that every group is isomorphic to a group of permutations of some set.

* **Vector space**. In :math:`R` happens to be a field, then an :math:`R`-module is typically called a **vector space** over :math:`R`.

* **Bilinear algebra**. If :math:`𝔽 = ⟨F, \{0, 1, -, ⋅\}⟩` is a field, then the algebra :math:`𝔸 = ⟨A, \{0, -, +, ⋅\} ∪ \{f_r ∣ r ∈ F\}⟩` is called a **bilinear algebra** over :math:`𝔽` provided

  #. :math:`⟨A, \{0, -, +\} ∪ \{f_r ∣ r ∈ F\}⟩` is a vector space over :math:`𝔽` and 
  #. :math:`∀ a, b, c ∈ A`, :math:`∀ r ∈ F`,

     .. math:: \begin{gather}
               (a + b) ⋅ c = (a ⋅ c) + (b ⋅ c),\\
               c ⋅ (a + b) = (c ⋅ a) + (c ⋅ b),\\
               a ⋅ f_r(b) = f_r(a ⋅ b) = f_r(a) ⋅ b.
               \end{gather}

  If in addition :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)` for all :math:`a, b, c ∈ A`, then :math:`𝔸` is called an **associative algebra** over :math:`𝔽`. Thus an associative algebra over a field has both a vector space reduct and a ring reduct. An example of an associative algebra is the space of *linear transformations* (endomorphisms) of any vector space into itself.


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

.. _idempotent-operations-projections:

Idempotent operations, projections
----------------------------------

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


.. Formalization
.. -------------

.. Our formal implementation (in `Lean`_) of these objects is described in :numref:`Sections %s <basic-facts-in-lean>`, :numref:`%s <terms-in-lean>`, and :numref:`%s <clones-in-lean>`.

------------------------

.. rubric:: Footnotes

.. [1]
   For a brief and gentle introduction to type theory see the `section on axiomatic foundations <https://leanprover.github.io/logic_and_proof/axiomatic_foundations.html?highlight=type#type-theory>`_ in `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_.  Alternatively, viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. [3]
   The term :math:`σ`-**algebra** has a special meaning, different from ours, in other areas of mathematics such as real analysis, probability, and measure theory.

.. [4]
   A list of many others may be found at http://www.math.chapman.edu/~jipsen/structures/doku.php/index.html.

.. [5]
   In retrospect, a more appropriate name for :math:`\mathbf{0} σ` might be :math:`Δ_σ`, or even :math:`=_σ`, but this may lead to conflicts with more standard notational conventions.


.. include:: hyperlink_references.rst
