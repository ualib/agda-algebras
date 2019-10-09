.. include:: _static/math_macros.rst

.. highlight:: lean

.. _prerequisites:

=======================
Appendix. Prerequisites
=======================

Operations
----------

An **algebraic structure** is a pair :math:`⟨ A, F⟩` where :math:`A` is a *nonempty* set and :math:`F` is a set of *finitary operations* on :math:`A`.

In this section we make this notion precise by recalling some basic definitions. We also take this opportunity to agree on notation.

If :math:`f: B → A` is a function from :math:`B` to :math:`A`, we call :math:`B` the **domain** of :math:`f`, denoted :math:`\dom f`, and :math:`A` the **codomain**, denoted :math:`\cod f`.

If :math:`D` is a subset of :math:`\dom f`, and :math:`C` is a subset of :math:`\cod f`, then we define the **image of** :math:`D` **under** :math:`f` to be the set

.. math:: f[D] :=\{ f\, x ∣ x ∈ D\}.

The **inverse image of** :math:`C` **under** :math:`f` is the set

.. math:: f^{-1}[C] := \{ x \in \dom f: f(x)\in C \}.

Sometimes we refer to the **image of** :math:`f` without mentioning a subset, in which case we mean the image of :math:`\dom f` under :math:`f`, which we denote by :math:`\im f`.

Let :math:`A` be a nonempty set and :math:`n∈ ℕ` a natural number.  An :math:`n`-**ary operation** on :math:`A` is a function :math:`f: A^n → A` which, if :math:`n>0`, maps each :math:`n`-tuple :math:`(a_0, a_1, \dots, a_{n-1})` in :math:`A^n` to a particular element :math:`f(a_0, a_1, \dots, a_{n-1})` in :math:`A`. If :math:`n=0`, then :math:`f: () → A` is a function that takes no arguments and returns an element of :math:`A`, so :math:`f` in this case is merely notation for a particular element of :math:`A`.

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

----------------------------------

Algebraic Structures
---------------------

A (universal) **algebra** is a pair :math:`𝔸 = ⟨A, F⟩` where :math:`A` is a nonempty set and :math:`F = \{f_i: i ∈ I\}` is a set of finitary operations on :math:`A`.

That is, :math:`f_i: A^n → A` for some :math:`n ∈ ℕ`.

.. A common shorthand for :eq:`algebra` is :math:`⟨A, f_i⟩_{i ∈ I}`.

The number :math:`n` is called the **arity** of the operation :math:`f_i`.

Thus, the arity of an operation is the number of operands upon which it acts, and we say that :math:`f` is an :math:`n`-**ary operation on** :math:`A` if :math:`\dom f = A^n` and :math:`\cod f = A`.

An operation is called **nullary** (or constant) if its arity is zero. **Unary**, **binary**, and **ternary** operations have arities 1, 2, and 3, respectively.

If :math:`A=ℝ` and :math:`f: ℝ × ℝ → ℝ` is the map that takes each pair :math:`(a, b) ∈ ℝ × ℝ` to the number :math:`f(a,b) = a+b ∈ ℝ`, then :math:`⟨A, \{f\}⟩` is an example of an algebra with a single binary operation. In such cases, we often simplify the notation and write :math:`⟨A, f⟩` in stead of :math:`⟨A, \{f\}⟩`.

.. An algebra is called **unary** if all of its operations are unary. 

An algebra is **finite** if :math:`|A|` is finite, and is called **trivial** if :math:`|A| = 1`.

Given two algebras :math:`𝔸` and :math:`𝔹`, we say that :math:`𝔹` is a **reduct** of :math:`𝔸` if both algebras have the same universe and :math:`𝔹` can be obtained from :math:`𝔸` by removing  operations.


.. index:: ! operation symbol, ! arity, ! interpretation, ! signature, ! similarity type

A better approach
~~~~~~~~~~~~~~~~~

An **operation symbol** :math:`f` is an object that has an associated **arity**; we denote the arity of :math:`f` by :math:`ρ \,f`.

A pair :math:`(F, ρ)` consisting of a set :math:`F` of operation symbols and an arity function :math:`ρ: F → N` is called a **signature** (or, **similarity type**).

An algebra in the signature :math:`(F, ρ)` is a pair :math:`𝔸 = ⟨A, F^𝔸⟩`, where :math:`F^𝔸 = \{f^𝔸: f ∈ F\}` and :math:`f^𝔸` is an operation on :math:`A` of arity :math:`ρ f`, called the **interpretation** of :math:`f` in :math:`𝔸`.

Consider the set of integers :math:`ℤ` with operation symbols :math:`F = \{0, 1, -(\,), +, ⋅\}`, which have respective arities :math:`\{0, 0, 1, 2, 2\}`.

The operation :math:`+^ℤ` is the usual binary addition, while :math:`-^ℤ(\,)` is negation, which takes the integer :math:`z` to :math:`-^ℤ(z) = -z`.

The constants :math:`0^ℤ` and :math:`1^ℤ` are nullary operations. Of course we usually just write :math:`+` for :math:`+^ℤ`, etc.

Examples of some general algebraic structures that have historically played a central role in mathematics over the last century (e.g., groups, rings, and modules) are mentioned in the next section.

---------------------------------------

Examples of Algebraic Structures
---------------------------------

Recall from above that an algebra :math:`𝔸` is an ordered pair :math:`𝔸 = ⟨A, F^𝔸⟩` where :math:`A` is a nonempty set and :math:`F` is a family of finitary operations on :math:`A`.

The set :math:`A` is called the **universe** of :math:`𝔸`, and the elements :math:`f^𝔸 ∈ F` are called the **basic operations** of :math:`𝔸`.

(In practice we often write :math:`f` instead of :math:`f^𝔸` when no ambiguity could result from this shorthand.

Here is a list of a few of the most frequently encountered and historically important algebraic structures. [1]_ 

* **Magma**. An algebra :math:`⟨A, ⋅⟩` with a single binary operation is called a **magma** (or **groupoid** or **binar**). The operation is usually denoted by :math:`+` or :math:`⋅`, and we write :math:`a+b` or :math:`a ⋅ b` (or just :math:`ab`) for the image of :math:`(a, b)` under this operation, which we call the *sum* or *product* of :math:`a` and :math:`b`, respectively.

* **Semigroup**. A magma :math:`⟨A, ⋅⟩` whose binary operation is associative is called a **semigroup**.  That is, a semigroup is a magma whose binary operation satisfies :math:`∀ a, b, c ∈ A, \; (a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)`.

* **Monoid**. If :math:`⟨A, ⋅⟩` is a semigroup and if :math:`e ∈ A` is a *multiplicative identity* (i.e., :math:`∀ a ∈ A, \; e ⋅ a = a ⋅ e = a`), then :math:`⟨A, \{e, ⋅\}⟩` is called a **monoid**.

* **Group**. A **group** is a monoid along with a unary operation :math:`^{-1}` called *multiplicative inverse*. That is, the reduct :math:`⟨ A, \{e, ⋅\}⟩` is a monoid and :math:`^{-1}`
  satisfies :math:`a ⋅ a^{-1} =  a^{-1} ⋅ a = e`, for all :math:`a ∈ A`.
  
* **Abelian group**. A group is called **abelian** just in case its binary operation is commutative, in which case we usually denote the operation by :math:`+` instead of :math:`⋅`. Also in this case we let :math:`0` (instead of :math:`e`) denote the *additive identity*, and we let :math:`-\,` (instead of :math:`^{-1}`) denote the *additive inverse*. Thus, an **abelian group** is a group :math:`𝔸 = ⟨ A, 0, -,+⟩` such that :math:`a+b = b+a` for all :math:`a, b ∈ A`.

* **Ring**. An algebra :math:`𝔸 = ⟨ A, \{0, -, +, ⋅\}⟩` is called a **ring** just in case the following conditions hold:

  #. the reduct :math:`⟨A, \{0, -,+\}⟩` is an abelian group,

  #. the reduct :math:`⟨ A, ⋅ ⟩` is a semigroup, and

  #. :math:`⋅` distributes over :math:`+`, that is, :math:`∀ a, b, c ∈ A`,

     .. math:: a ⋅ (b+c) = a ⋅ b + a ⋅ c \;\text{ and }\; (a+b)⋅ c = a ⋅ c + b ⋅ c`.

  A **ring with unity** (or **unital ring**) is an algebra :math:`⟨A, \{0, 1, -, +, ⋅\}⟩` with a ring reduct :math:`⟨A, \{0, -, +, ⋅\}⟩` and a *multiplicative identity* :math:`1 ∈ A`; that is :math:`∀ a ∈ A,\, a ⋅ 1 = 1 ⋅ a = a`.

  If :math:`⟨A, \{0, 1, -, +, ⋅\}⟩` is a unital ring, an element :math:`r ∈ A` is called a **unit** if it has a multiplicative inverse. That is, :math:`r ∈ A` is a unit provided there exists :math:`s ∈ A` with :math:`r ⋅ s = 1 = s ⋅ r`.  (We usually denote such an :math:`s` by :math:`r^{-1}`.)

* **Division ring**.  A ring in which every non-zero element is a unit is called a **division ring**.

* **Field**. A commutative division ring is called a **field**.

* **Module**. Let :math:`R` be a ring with unit. A **left unitary** :math:`R`-**module** (or simply :math:`R`-**module**) is an algebra :math:`⟨M, \{0, -, +\} ∪ \{f_r : r∈ R\}⟩` with an abelian group reduct :math:`⟨M, \{0, -, +\}⟩` and unary operations :math:`\{f_r : r ∈ R\}` that satisfy the following four conditions for all :math:`r, s ∈ R` and :math:`x, y ∈ M`:

  #. :math:`f_r(x + y)  = f_r(x) + f_r(y)`

  #. :math:`f_{r+s}(x) = f_r(x) + f_s(x)`

  #. :math:`f_r(f_s(x)) = f_{rs}(x)`

  #. :math:`f_1(x) = x`.

  Note that the first condition says that each :math:`f_r` is an :term:`endomorphism` of the abelian group :math:`⟨ M, \{0, -, +\}⟩`.
  
  Conditions 2--4 say: (1) the collection of endomorphisms :math:`\{f_r ∣ r∈ R\}` is itself a ring with unit, where the function composition described in the third condition is the binary multiplication operation, and (2) the map :math:`r ↦ f_r` is a ring :term:`epimorphism` from :math:`R` onto :math:`\{f_r ∣ r∈ R\}`.

  Part of the importance of modules lies in the fact that every ring is, up to isomorphism, a ring of endomorphisms of some abelian group. This fact is analogous to the more familiar theorem of Cayley stating that every group is isomorphic to a group of permutations of some set.

* **Vector space**. In :math:`R` happens to be a field, then an :math:`R`-module is typically called a **vector space** over :math:`R`.

* **Bilinear algebra**. If :math:`𝔽 = ⟨F, \{0, 1, -, ⋅\}⟩` is a field, then the algebra :math:`𝔸 = ⟨A, \{0, -, +, ⋅\} ∪ \{f_r ∣ r ∈ F\}⟩` is called a **bilinear algebra** over :math:`𝔽` provided

  #. :math:`⟨A, \{0, -, +\} ∪ \{f_r ∣ r ∈ F\}⟩` is a vector space over :math:`𝔽` and 
  #. :math:`∀ a, b, c ∈ A, \, ∀ r ∈ F`,

     .. math:: \begin{gather}
               (a + b) ⋅ c = (a ⋅ c) + (b ⋅ c),\\
               c ⋅ (a + b) = (c ⋅ a) + (c ⋅ b),\\
               a ⋅ f_r(b) = f_r(a ⋅ b) = f_r(a) ⋅ b.
               \end{gather}

  If in addition :math:`(a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)` for all :math:`a, b, c ∈ A`, then :math:`𝔸` is called an **associative algebra** over :math:`𝔽`.
  
  Thus an associative algebra over a field has both a vector space reduct and a ring reduct.
  
  An example of an associative algebra is the space of linear transformations (endomorphisms) of any vector space into itself.

------------------

.. rubric:: Footnotes

.. [1]
   A list of many others may be found at http://www.math.chapman.edu/~jipsen/structures/doku.php/index.html.


.. include:: hyperlink_references.rst
