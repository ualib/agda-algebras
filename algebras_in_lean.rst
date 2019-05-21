.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _algebras-in-lean:

================
Algebras in Lean
================

This section demonstrates the utility of dependent and inductive types by expressing some fundamental concepts of universal algebra in Lean.

In particular, we will formally represent each of the following:  *operation*, *algebra*, *subuniverse*, and *term algebra*.

Our formal representations of these concepts will be clear, concise, and computable. Moreover, we strive to develop a notation and syntax that will feel natural to working algebraists.

Our goal here is to demonstrate the power of Lean's type system for expressing mathematical concepts precisely and constructively, and to show that if we make careful design choices at the start of our development, then our formal theorems *and their proofs* can approximate the efficiency and readability of analogous informal presentations found in the mathematics literature.

Most of the Lean code described in this section can be found in the files ``basic.lean`` and ``subuniverse.lean`` which reside in the ``src`` directory of the lean-ualib_ repository.

.. index:: arity, operation
.. index:: airty type, operation symbol type
.. index:: type of; operation symbols
.. index:: type of; arities
.. index:: type of; natural numbers

.. _operations-in-lean:

Operations
----------

Recall, the symbols ℕ, ω, and ``nat`` are synonymous and all denote the **type of natural numbers**.

We start with the **type of operation symbols**, which depends on our semantic notion of **arity**, also captured by a type.

Argument lists that are passed to operations are represented by tuples which are simply functions, say, of type β → α, where β is the **arity type** of the operation to which the tuple will be passed as an argument list.

Heuristically, it's fine to think of | β | as the "number" of arguments the operation takes, but the implementation is much more general than that. In particular, there is no reason to restrict the arity type to be a finite set, *a priori*.

.. index:: ! type of; operations

An **operation** takes a tuple (or, list of "arguments") of type β → α and returns an element of type α.  Here, α is the type on which the operation is defined.

In Lean, if α and β are types, we define the **type of β-ary operations on α** to be the function type (β → α) → α, and we denote this type by ``op(β α)``.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α

.. index:: ! projection function

An example of an operation of type ``op (β α)`` is the **projection function** π , defined on the type α, as follows:

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    -- BEGIN
    definition π {β α} (i) : op β α := λ a, a i
    -- END

The operation ``π i`` maps a given tuple ``a: β → α`` to its "value" ``a i`` at input ``i``.

For instance, if we have types ``α`` and ``β``, and variables ``i: β`` and ``a: β → α``, then the command ``#check π i a`` shows that the type of ``π i a`` is ``α``, as expected, since ``π i a = a i``.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ a, a i
    -- BEGIN
    variables (α : Type*) (β : Type*) (i : β) (a : β → α) 
    #check π i a       -- answer: π i a : α 
    -- END

Here are a couple of examples that are a bit more concrete.

.. code-block:: lean

    -- Example: the tuple p1 = (1, 2, 3, ...).
    definition p1 : ℕ → ℕ := λ n, n+1

    -- What's the 3rd projection of p1?
    #eval π 3 p1                         -- answer: 4

    -- Example: the constant tuple sevens = (7, 7, 7, ...)
    definition sevens : ℕ → ℕ := λ n, 7

    -- What's the 3rd projection of sevens?
    #eval π 3 sevens                      -- answer: 7

.. index:: ! signature, ! operation symbol, ! similarity type
.. index:: ! arity

.. _signatures-in-lean:

Signatures
----------

A **signature** :math:`σ = (F, ρ)` consists of

  #. :math:`F :=` a set of **operation symbols**;
  #. :math:`ρ: F → N :=` a **similarity type**.
  
For each operation symbol :math:`f : F`, the value :math:`ρ f` is called the **arity** of :math:`f`.  This value has type :math:`N`, which is the **arity type**.

In classical universal algebra we typically assume that :math:`N = ℕ`, but for most of the basic theory this choice is inconsequential. [1]_

.. index:: ! type of; signatures
.. index:: ! type of; operations
.. index:: ! arity function

We now take our first crack at implementing a type of signatures and a type of operations in Lean_. In the process we compare and contrast the formal and the informal presentations of these concepts.

We define the **type of signatures** as a structure with two fields, the type ``F`` of operation symbols and an **arity function** ``ρ : F → Type*``, which takes each operation symbol ``f`` to its arity ``ρ f``.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ f, f i
    variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
    -- BEGIN
    -- Signature
    -- F : a set of operation symbols
    -- ρ : returns the arity of a given operation symbol
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    -- END

.. index:: ! type of; interpretations of operations
.. index:: keyword: section
.. index:: keyword: local notation

In the next section, we define the **type of interpretations of operations** on the :index:`carrier type` ``α``.  Before proceeding, however, let us first start a new ``section`` which allows us to define some parameters (such as a fixed signature ``σ``) that won't change throughout the development. [2]_

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ f, f i
    variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    -- BEGIN
    section
      parameter (σ : signature)
      local notation `F` := σ.F
      local notation `ρ` := σ.ρ 
    end
    -- END

With these ``local notation`` directives, we can now write ``f : F`` (instead of ``f : σ.F``) to indicate that the operation symbol ``f`` has type ``F``; similarly, for the arity of ``f``, we can write ``ρ f`` (instead of ``σ.ρ f``). This syntactic sugar results in Lean syntax that matches that of informal algebra almost exactly. [3]_ 

.. index:: pair: variety; equational class
.. index:: triple: algebra; structure; universal algebra

.. _universal-algebras-in-lean:

Algebras
--------

Classical universal algebra is the study of **varieties** (or **equational classes**) of algebraic structures. 

A **universal algebra** (also known as an **algebraic structure**) is denoted by :math:`𝐀 = ⟨A, F^{𝐀}⟩` and consists of 

  #. :math:`A :=` a set, called the **universe** (or **carrier**) of the algebra,
  #. :math:`F^{𝐀} = \{f^{𝐀} ∣ f ∈ F, f^{𝐀} : (ρf → A) → A\} :=` a set of **operations** defined on :math:`A`, and
  #. a collection of **identities** satisfied by the elements and operations of 𝐀.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :math:`\mathbf{Set}`, such as multisorted algebras, higher-type universal algebra, etc. (:cite:`MR2757312`, :cite:`MR3003214`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`MR1173632`). These are natural generalizations that we will become part of the ``lean-ualib`` library, but only after we have an easily accessible implementation of the classical core of (single-sorted, set-based) universal algebra.

Suppose :math:`A` is a set and :math:`f` is a :math:`ρ f`-ary operation on :math:`A`. In this case, we often write :math:`f : A^{ρf} → A`. If the arity type :math:`\beta` happens to be the set ℕ of natural numbers, then :math:`ρ f` denotes the set :math:`\{0, 1, \dots, ρf-1\}`. A function :math:`g` of type :math:`ρf → A` is then simply a :math:`ρ f`-tuple of elements of :math:`A`. [4]_

Fix :math:`m : ℕ`. An :math:`m`-tuple :math:`a = (a_0, a_1, \dots , a_{m-1}) : A^m` is (the graph of) the function :math:`a : m → A`, defined for each :math:`i < m` by :math:`a\,i = a_i`. 

If :math:`h : A → B` and :math:`a : m → A`, then :math:`h ∘ a : m → B` is the tuple whose :math:`i`-th value is :math:`(h ∘ a) i = h\, a\, i = h a_i`, which has type :math:`B`.

If :math:`g : A^m → A` and :math:`a : m → A`, then the value :math:`g\, a` has type :math:`A`.

Thus, if

  + :math:`f : (ρf → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, 
  + :math:`a : ρf → A` is a :math:`ρ f`-tuple on :math:`A`, and 
  + :math:`h : A → B`,

then :math:`h ∘ a : ρf → B` and :math:`f (h ∘ a) : B`.

.. index:: type of; interpretations of operations

Before defining a type of universal algebras, we first define a type called ``algebra_on`` which will be the **type of interpretations of operations** of a given signature. Our definition of ``algebra_on`` uses the :ref:`dependent function type <pi-type>` (or "Pi type").

.. index:: ! carrier type

Given a signature :math:`σ = (F, ρ)` and a **carrier type** :math:`α`, an inhabitant of ``algebra_on α`` is determined by assigning an interpretation to each operation symbol :math:`f : F`.  Such an interpretation is a function of type :math:`(ρ f → α) → α` (which depends on :math:`f`).  Thus, given a signature :math:`σ = (F, ρ)`, the ``algebra_on α`` type is

.. math:: \prod_{f : F} (ρ f → α) → α = \prod_{f : F} \mathrm{op} \,(ρ f)\, α.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ f, f i
    variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    -- BEGIN
    section

      parameter (σ : signature)
      local notation `F` := σ.F
      local notation `ρ` := σ.ρ 

      -- Define the interpretation of an algebra on the carrier α:
      definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   

      -- This is called `algebra_on` since an algebra is fully
      -- specified by its Cayley (operation) tables. An inhabitant 
      -- of `algebra_on` assigns to each op symbol f : F, of 
      -- arity `β = σ.ρ f`, an interpretation of f, that is, 
      -- a function of type (β → α) → α.
    end
    -- END

(See also :numref:`Appendix Section %s <pi-type>`, for a more technical description of Leans ``pi`` type.)

.. index:: type of; universal algebras

Finally, let us define the **type of universal algebras** in Lean.

A :index:`universal algebra` :math:`𝐀 = ⟨A,F^𝐀⟩` is a pair consisting of a :index:`carrier` (or :index:`universe`) :math:`A` along with an set :math:`F^𝐀` of :index:`operations` (i.e., interpretations of the operation symbols in :math:`F`).

Also, we should have the concept of an algebraic structures of any given signature. Thus, the type of :math:`⟨A,F^𝐀⟩` depends on the choice of signature :math:`σ = (F, ρ)`, so it is natural to encode the type of algebras as a :index:`dependent pair`, or :index:`Sigma type`.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ f, f i
    variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    -- BEGIN
    section

      parameter (σ : signature)
      local notation `F` := σ.F
      local notation `ρ` := σ.ρ 
      definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   

      -- An algebra pairs a carrier with an interpretation of 
      -- the op symbols.
      definition algebra := sigma algebra_on

      -- sigma is the "dependent pair" type: ⟨α, β α⟩ which is
      -- appropriate since an algebra consists of a universe 
      -- (of type α), and operations on that universe; the
      -- type of the operations depends on the universe type.

    end
    -- END

(See also :numref:`Appendix Section %s <sigma-type>`, for a more technical description of the Sigma type in Lean.)

Finally, we show how to get ahold of the carrier and operations of an algebra by instantiating them as follows:

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ f, f i
    variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    -- BEGIN
    section

      parameter (σ : signature)
      local notation `F` := σ.F
      local notation `ρ` := σ.ρ 
      definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   
      definition algebra := sigma algebra_on

      instance alg_carrier : has_coe_to_sort algebra := 
      ⟨_, sigma.fst⟩
      
      instance alg_operations : has_coe_to_fun algebra := 
      ⟨_, sigma.snd⟩

    end
    -- END

.. index:: keyword: has_coe_to_sort
.. index:: keyword: has_coe_to_fun
.. index:: coersion

The last two lines are tagged with ``has_coe_to_sort`` and ``has_coe_to_fun``, respectively, because here we are using a very nice feature of Lean called **coercions**. Using coercions allows us to identify certain objects which, though not identical, are normally conflated in informal mathematics.  (See :numref:`Section %s <coercion>` for a simple example.)

The definitions of ``has_coe_to_sort`` and ``has_coe_to_fun`` in the Lean_ library are as follows:

.. code-block:: lean

    class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
    (S : Sort v) (coe : a → S)

    class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
    (F : a → Sort v) (coe : Π x, F x)

For instance, the standard notation for the interpretation of the operation symbol :math:`f` in the algebra :math:`𝐀 = ⟨A, F^𝐀⟩` is :math:`f^𝐀`. In our Lean implementation, we use ``A f`` to denote :math:`f^𝐀`. Although this syntax doesn't match the informal syntax exactly, it seems equally elegant and adapting to it should not overburden the user.

Another example that demonstrates the utility of coercions is our definition of ``is_subalgebra``, a function that takes as input two algebraic structures and decides whether the second structure is a subalgebra of the first.  Here is the definition.  

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ f, f i
    variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    section
      parameter (σ : signature)
      local notation `F` := σ.F
      local notation `ρ` := σ.ρ 
      definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   
      definition algebra := sigma algebra_on
      instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
      instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
    end
    section

    -- BEGIN
    definition is_subalgebra 
    {σ : signature} {α : Type*} {β : Type*}
    (A : algebra_on σ α) {β : set α} (B : algebra_on σ β) := 
    ∀ f b, ↑(B f b) = A f ↑b
    -- END

    end 

(See also :numref:`Appendix Section %s <coercion>`, for a more technical description of coersions in Lean.)

.. index:: homomorphism

.. _homomorphisms-in-lean:

Homomorphisms
-------------

To see this notation in action, let us look at how the ``lean-ualib`` represents the assertion that a function is a σ-**homomorphism**.

.. code-block:: lean

   import data.set
   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ f, f i
   variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   section
     parameter (σ : signature)
     local notation `F` := σ.F
     local notation `ρ` := σ.ρ 
     definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   
     definition algebra := sigma algebra_on
     instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
     instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
   end
   section

   definition is_subalgebra {σ : signature} {α : Type*} {β : Type*}
   (A : algebra_on σ α) {β : set α} (B : algebra_on σ β) :=
   ∀ f b, ↑(B f b) = A f ↑b

   -- BEGIN
   definition homomorphic {σ : signature}
   {A : algebra σ} {B : algebra σ} (h : A → B) := 
   ∀ (f : σ.F) (a : σ.ρ f → A.fst), h (A f a) = B f (h ∘ a)
   -- END

   end

Comparing this with a common informal language definition of a homomorphism, which is typically something similar to :math:`∀ f \ ∀ a \ h (f^𝐀 (a)) = f^𝐁 (h ∘ a)`, we expect working algebraists to find the ``lean-ualib`` syntax very readable and usable.

--------------------------------------------------------------

.. rubric:: Footnotes

.. [1]
   As we will see when implementing general operations in Lean, it is unnecessary to commit in advance to a specific arity type :math:`N`. An exception is the *quotient algebra type* since, unless we restrict ourselves to finitary operations, lifting a basic operation to a quotient requires some form of choice.

.. [2]
   The  ``section`` command allows us to open a section throughout which our signature ``σ`` will be available; ``section`` ends when the keyword ``end`` appears.

.. [3]
   The only exception is that in type theory we make *typing judgments*, denoted by ``:``, rather than set membership judgments, denoted by ``∈``.

.. [4]
   Technically, this assumes we identify :math:`g` with its graph, which is fairly common practice. We will try to identify any situations in which the conflation of a function with its graph might cause problems.

.. _Lean: https://leanprover.github.io/

.. _`github.com/UniversalAlgebra/lean-ualib`: https://github.com/UniversalAlgebra/lean-ualib/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

