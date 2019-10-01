.. include:: _static/math_macros.rst
.. highlight:: lean
.. role:: cat
.. role:: code

.. _algebras-in-lean:

================
Algebras in Lean
================

Most of the Lean_ code described in this section can be found in the files ``basic.lean`` residing in the ``src`` directory of the lean-ualib_ repository. [1]_

This section demonstrates the utility of dependent and inductive types by expressing some fundamental concepts of universal algebra in Lean.

In particular, we will formally represent each of the following:  *operation*, *algebra*, *subuniverse*, and *term algebra*.

Our formal representations of these concepts will be clear, concise, and computable. Moreover, we strive to develop a notation and syntax that will feel natural to working algebraists.

Our goal here is to demonstrate the power of Lean's type system for expressing mathematical concepts precisely and constructively, and to show that if we make careful design choices at the start of our development, then our formal theorems *and their proofs* can approximate the efficiency and readability of analogous informal presentations found in the mathematics literature.

.. index:: arity, operation
.. index:: airty type, operation symbol type
.. index:: ! type of; operation symbols
.. index:: ! type of; operations
.. index:: ! type of; arities
.. index:: ! type of; natural numbers

----------------------------------------

.. index:: pair: ℕ; ω
.. index:: pair: ω; 𝗇𝖺𝗍

.. _operations-in-lean:

Operations in Lean
-------------------

Recall, the symbols ℕ, ω, and ``nat`` are synonymous and all denote the **type of natural numbers**.

We start with the **type of operation symbols**, which depends on our semantic notion of **arity**, also captured by a type.

Argument lists that are passed to operations are represented by tuples which are simply functions, say, of type ``β → α``, where ``β`` is the **arity type** of the operation to which the tuple will be passed as an argument list.

Heuristically, it's fine to think of ``|β|`` as the "number" of arguments the operation takes, but the implementation is much more general than that. In particular, there is no reason to restrict the arity type to be a finite set, *a priori*.

An **operation** takes a tuple (or, list of "arguments") of type ``β → α`` and returns an element of type ``α``.  Here, ``α`` is the type on which the operation is defined.

In the `lean-ualib`_, we declare types ``α`` and ``β`` and then define the type of **β-ary operations on α** to be ``(β → α) → α``. We denote this type by ``op (β α)``.

Before getting to the implementation of the ``op`` type (which resides in the `basic.lean`_ file of the the `lean-ualib`_ library), we declare some Lean :term:`universes <universe>` that we will use throughout the library. (These appear at the top of almost every ``.lean`` files in `lean-ualib`_.)

.. include:: _static/basic.lean.1.rst

The code above is self-explanatory.  We merely declare a few universe "levels" in Lean's *type hierarchy* (:numref:`leans-type-hierarchy`), along with comments indicating the kind of types that we expect will reside in these universes.

(**N.B.** Most of the code listings below will take universe declarations for granted and will not mention them explicitly.) 

.. index:: ! projection operation

Now we define the type of operations and give a simple but important example of an operation of type ``op (β α)``---namely, the **β-ary projection on α**.

.. include:: _static/basic.lean.2.rst

The operation ``π i`` maps each ``β``-tuple of elements of type ``α`` to its "value" at input ``i``.  For instance, if we have types ``α`` and ``β``, and inhabitants ``i: β`` and ``a: β → α``, then the command ``#check π i a`` shows that the type of ``π i a`` is ``α``, as expected, since ``π i a = a i``.

.. include:: _static/basic.lean.3.rst

The next two examples are a bit more concrete.

.. include:: _static/basic.lean.4.rst

----------------------------------------------------------

.. index:: ! signature, ! operation symbol, ! similarity type
.. index:: ! arity

.. _signatures-in-lean:

Signatures in Lean
------------------

A **signature** :math:`σ = (F, ρ)` consists of

  + a set :math:`F` of **operation symbols**, and
  + a **similarity type** :math:`ρ: F → β`.
  
For each operation symbol :math:`f : F`, the value :math:`ρ f` is the **arity** of :math:`f`.  This value has type :math:`β`, which is the **arity type**.

In classical universal algebra we typically assume that :math:`β = ℕ`, but for much of the basic theory this choice is inconsequential. [2]_

.. index:: ! type of; signatures
.. index:: ! arity function

We now implement a type of signatures and a type of operations in Lean_.

Define the **type of signatures** as a structure with two fields, the type ``ℱ`` of operation symbols, and an **arity function** ``ρ: ℱ → Type w``, which takes each operation symbol ``f: σ.ℱ`` to its arity ``ρ f: Type w``.

.. include:: _static/basic.lean.5.rst

.. index:: type of; interpretations of operations
.. index:: keyword: section
.. index:: keyword: local notation

Later we will define the *type of interpretations of operations* on the :index:`carrier type` ``α``.  For now, we note that by starting a new ``section`` we could define some parameters (such as a fixed signature ``σ``) that will be available throughout the section. [3]_


.. index:: pair: variety; equational class
.. index:: pair: algebra; algebraic structure
.. index:: carrier type

-------------------------------------------------------

.. _universal-algebras-in-lean:

Algebras in Lean
----------------

Classical universal algebra is the study of **varieties** (or **equational classes**) of algebraic structures.

Recall from :numref:`Section %s <algebraic-structures>`, an **algebraic structure** (or **algebra**) in the signature :math:`σ = (F, ρ)` is denoted by :math:`𝔸 = ⟨A, F^𝔸⟩` and consists of 

  + a set :math:`A`, called the **universe** (or **carrier**) of the algebra,
  + a set :math:`F^{𝔸} = \{f^{𝔸} ∣ f ∈ F, f^{𝔸} : (ρ f → A) → A\}` of **operations** defined on :math:`A`, and
  + a collection of **identities** satisfied by the elements and operations of 𝔸.

Usually, the algebraic structures we study are **single-sorted**, meaning each structure has only one universe and that universe is of only a single type. Furthermore, in classical algebra, the universes are typically sets. We take the classical theory as our starting point, and although generalizations will eventually be incorporated into ``lean-ualib``, for now we content ourselves with developing and documenting an *accessible* implementation of the classical core of (single-sorted, set-based) universal algebra.

All functions are unary
~~~~~~~~~~~~~~~~~~~~~~~

When working informally, we typically denote an :math:`n`-ary operation by, say, :math:`f(x_0, x_1, \dots, x_{n-1})`, the arguments appearing as an :math:`n`-tuple, :math:`(x_0, x_1, \dots, x_{n-1})`.  However, when computing with functions (and even when not!) this is impractical for a number of reasons.

Functional programming languages like Lean_ are based on the :term:`lambda calculus`.  One reason for this is that there is only one kind of type (the function type); moreoever, every function is a *unary* function.  This has a major advantage for computing: our code need not depend on the arity of a given function.

Representing an :math:`n`-ary function by a unary function can be done in a number of essentially equivalent ways.  One is by :term:`currying`.  Another is by viewing the :math:`n`-tuple (e.g., passed to an :math:`n`-ary function) as a function.  We take the latter approach here (though we will have plenty of opportunities to curry later).

We explain how the correspondence between tuples and functions works using a simple example. [5]_ 

.. proof:example::

    Suppose :math:`A` is a set and :math:`f` is a :math:`ρ f`-ary operation on :math:`A`. In this case, we often write :math:`f : A^{ρf} → A`.

    Let :math:`β` be the arity type. If :math:`β` happens to be ℕ, then :math:`ρ f = \{0, 1, \dots, ρf-1\}` and a function :math:`g : ρf → A` is simply a :math:`ρ f`-tuple of elements of :math:`A`. [6]_
    
    Conversely, for :math:`m : ℕ`, an :math:`m`-tuple :math:`a = (a_0, a_1, \dots , a_{m-1}) : A^m` is (the graph of) the function :math:`a : m → A`, defined for each :math:`i < m` by :math:`a\,i = a_i`. 
    
    If :math:`h : A → B` and :math:`a : m → A`, then :math:`h ∘ a : m → B` is the tuple whose :math:`i`-th value is :math:`(h ∘ a) i = h\, a\, i = h a_i`, which has type :math:`B`.
    
    If :math:`g : A^m → A` and :math:`a : m → A`, then the value :math:`g\, a` has type :math:`A`.
    
    Putting it all together, if
    
      + :math:`f : (ρf → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, 
      + :math:`a : ρf → A` is a :math:`ρ f`-tuple on :math:`A`, and 
      + :math:`h : A → B`,
    
    then :math:`h ∘ a : ρf → B` and :math:`f (h ∘ a) : B`.

.. index:: ! type of; interpretations of operations

The ``algebra_on`` type
~~~~~~~~~~~~~~~~~~~~~~~

Before defining a type of universal algebras, we first define a type called ``algebra_on`` which will be the **type of interpretations of operations** of a given signature. Our definition of ``algebra_on`` uses a :ref:`dependent function type <pi-type>` (or "Pi type").

Given a signature :math:`σ = (F, ρ)` and a carrier type :math:`α`, an inhabitant of ``algebra_on σ α`` is determined by assigning an interpretation to each operation symbol :math:`f : F`.  Such an interpretation is a function of type :math:`(ρ f → α) → α` (which *depends* on :math:`f`).

Thus, given a signature :math:`σ = (F, ρ)`, the ``algebra_on α`` type is

.. math:: \prod_{f : F} (ρ f → α) → α = \prod_{f : F} \mathrm{op} \,(ρ f)\, α.

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)

    -- BEGIN
    -- algebra_on is the type of algebras on a carrier type
    -- α such that each symbol f is given an interpretation 
    -- as an operation on α with arity ρ f.
    definition algebra_on (σ : signature) (α : Type*) := 
    Π (f : σ.F), op (σ.ρ f) α   

      -- An inhabitant of algebra_on assigns to each op symbol 
      -- f : F of arity β = σ.ρ f, an interpretation of f, 
      -- that is, a function of type (β → α) → α.
   -- END

.. index:: Pi type

Since the :ref:`dependent function type <pi-type>` or "Pi type" (denoted ``pi`` or ``Π`` in Lean_) is among one of the most important types in dependent type theory, let us pause pause for a moment to discuss it.

A **Pi type**, such as :math:`Π_{(x:A)} B x`, is also known as a *dependent function type* because it generalizes the function type :math:`A → B` by allowing :math:`B x` (the type of the codomain) to depend on a *value* :math:`x : A` of the domain. (See :numref:`Section %s <dependent-types>` for more about dependent types.)
 
Here is how the type ``pi`` is defined in the Lean_ standard library.

.. todo:: check this!

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
    { f | ∀ a ∈ i, f a ∈ s a }

.. (See also :numref:`Appendix Section %s <pi-type>`, for a more technical description of Leans ``pi`` type.)

.. index:: ! type of; universal algebras
.. index:: type of; dependent pairs

.. _the-algebra-type:

The ``algebra`` type
~~~~~~~~~~~~~~~~~~~~~

Finally, let us define the **type of universal algebras** in Lean.

A :index:`universal algebra` :math:`𝔸 = ⟨A,F^𝔸⟩` is a pair consisting of a :index:`carrier` (or :index:`universe`) :math:`A` along with an set :math:`F^𝔸` of :index:`operations` (i.e., interpretations of the operation symbols in :math:`F`).

Also, our definition should caption the concept of an algebraic structure of any choice of signature. Thus, the type of :math:`⟨A,F^𝔸⟩` *depends* on the choice of signature :math:`σ = (F, ρ)`, so it is natural to encode the type of algebras as a :term:`dependent pair <Sigma type>`.

.. code-block:: lean

   def op (β α) := (β → α) → α
   def π {β α} (i) : op β α := λ a, a i
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   

   -- BEGIN
   -- algebra is the type of algebras consisting of a pair: 
   -- a carrier type α, along with an algebra_on α 
   definition algebra (σ : signature) := sigma (algebra_on σ)
  
     -- The Lean syntax sigma (algebra_on σ) denotes the 
     -- dependent pair type, ∑ (α : Type*) (algebra_on σ α).
   -- END

An algebra pairs a carrier with an interpretation of the op symbols.

.. index:: type of; dependent pairs

The type ``sigma`` is the so called :term:`Sigma type`, which is also known as a :term:`dependent pair type`, or :term:`dependent product type`. It is one of the most important types in (dependent) :term:`type theory`, so let's pause for a moment to discuss it.

A **Sigma type** :math:`Σ_(x:A), B x` is also known as a **dependent pair type** because it generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second component to depend on the *value* :math:`x` of the first.

Here is how the type ``sigma`` is defined in the Lean_ standard library.

.. code-block:: lean

   structure sigma {α : Type u} (β : α → Type v) :=
   mk :: (fst : α) (snd : β fst)

Sigma is the appropriate type for the ``algebra`` type since an algebra consists of a universe (of type α), along with operations on that universe, and the type of each operation is dependent on the universe type α.

.. index:: keyword: has_coe_to_sort
.. index:: keyword: has_coe_to_fun
.. index:: coercion


Syntactic sugar and coercions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Lean_ has a nifty :index:`coercion` feature which we use for the following purpose: if ``A`` is an algebra, Lean_ will try to determine the correct type of the symbol A---either the algebra itself or the universe of the algebra---depending on the context (just as we would when working informally!).

The next bit of code shows how the ``has_coe_to_sort`` and ``has_coe_to_fun`` coercion directives direct Lean_ to yield either the universe of the algebra or the whole algebra, as appropriate for the given context.

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    def algebra (σ : signature) := sigma (algebra_on σ)
 
    -- BEGIN
    -- coercion to universe of σ
    -- (essentially the forgetful functor)
    instance alg_carrier (σ : signature) : 
    has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
 
    -- coercion to operations of σ 
    instance alg_operations (σ : signature) : 
    has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    -- END

Using coercions allows us to identify certain objects which, though not identical, are typically conflated in informal mathematics. In the next section we use coercions to our advantage in a concrete example, but see also `Coercions`_ for a simpler example and for the definitions of ``has_coe_to_sort`` and ``has_coe_to_fun`` in the Lean_ library.

-----------------------------------------------

.. _subalgebras-in-lean:

Subalgebras in Lean
---------------------

The code described in this section is found in the file ``subuniverse.lean`` in the ``src`` directory of (the ``william`` branch of) the lean-ualib_ repository. 

We will cover subalgebra generation in Lean_, using inductive types, in :numref:`subuniverses-in-lean`.  In the present section we show how to use Lean_ to formally define a subalgebra and test whether a subset is a subuniverse.

We start by importing the definitions described above so that we have signatures and algebras available. We will also need to import the set.lean_ file from the mathlib_ library.  We satisfy these requirements as follows:
 
.. code-block::

   import basic     -- the basic.lean file from lean-ualib
   import data.set  -- the set.lean file from mathlib

Next, we open a ``namespace`` to collect definitions and results related to subuniverses and subalgebras.  This is done using the ``namespace`` directive. We also start a ``section`` so we can fix a signature along with some syntactic sugar. 

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    def algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
 
    -- BEGIN
    namespace subuniverse
      section sub
 
        parameter {σ : signature}
        parameter {α : Type*}
        parameter {I : Type*}
        definition F := σ.F
        definition ρ := σ.ρ 
    
      end sub
    end subuniverse
    -- END

 Although we won't make it explicit, the remainder of this section assumes all Lean_ code (apart from that being imported from another file) is part of the ``subuniverse`` namespace; that is, it occurs inside a block of the form

.. code-block:: lean

   namespace subuniverse

     -- all subuniverse code goes here --

   end subuniverse

We now implement the definition of **subuniverse**. Specifically, we say what it means for a given set ``B₀`` (comprised of elements of the carrier type of an algebra ``A``) to be closed under the operations of ``A``.

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    def algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    import data.set  -- the set.lean file from mathlib
 
    namespace subuniverse
      section sub
        parameter {σ : signature} {α : Type*} {I : Type*}
        definition F := σ.F
        definition ρ := σ.ρ 
        -- BEGIN
        -- subuniverse -----------------------------------
        definition Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:=
        ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸 f a) ∈ B₀
         
        -- 𝔸 f a ∈ B₀  is syntactic sugar for  B₀ (𝔸 f a).
        -- END
      end sub
    end subuniverse

Notice that we use ``A f`` to denote what, in the informal syntax, is usually denoted by :math:`f^𝔸`. So, although our Lean_ syntax doesn't match the informal syntax exactly, it is arguably just as elegant, and adapting to it should not overburden the user.

We also want a means of testing whether an algebra defined on a subset :math:`B₀ ⊆ A` is a subalgebra of 𝔸. (Of course, this is equivalent to testing whether :math:`B₀` is a subuniverse of 𝔸.)

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    def algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    import data.set  -- the set.lean file from mathlib
 
    namespace subuniverse
      section sub
        parameter {σ : signature} {α : Type*} {I : Type*}
        def F := σ.F
        def ρ := σ.ρ 
        def Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:= ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸 f a) ∈ B₀
        -- BEGIN
        -- is subalgebra? -----------------------
        definition is_subalgebra (𝔸: algebra σ) 
        (B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= 
        ∀ f b, ↑(𝔹 f b) = 𝔸 f ↑b
        -- END
      end sub
    end subuniverse

Next, we codify the definition of the subuniverse generated by a set that we saw in :eq:`SgDef` of :numref:`subuniverses`.

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    def algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    import data.set  -- the set.lean file from mathlib
 
    namespace subuniverse
      section sub
        parameters {σ : signature} {α : Type*} {I : Type*}
        def F := σ.F
        def ρ := σ.ρ 
        def Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:= ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸 f a) ∈ B₀
        def is_subalgebra (𝔸: algebra σ) (B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= ∀ f b, ↑(𝔹 f b) = 𝔸 f ↑b
        -- BEGIN
        -- subuniverse generated by X ----------------------
        definition Sg(A: algebra_on σ α) (X: set α): set α:= 
        ⋂₀ {U | Sub A U ∧ X ⊆ U}
        -- END
     end
   end subuniverse
   
We now formally prove that the intersection of two subuniverses is a subuniverse.  For this we will need "introduction" and "elimination" rules for the intersection operation ``Inter`` defined in the mathlib_. [7]_  (Naturally, mathlib_ allows us to use the notation ``⋂`` in place of ``Inter``.)

(See also :numref:`Section %s <intersection-and-union>`, for a more technical description of the intersection operation coercions ``⋂₀`` in Lean.)

.. code-block:: lean

    def op (β α) := (β → α) → α
    def π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    def algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    def algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    import data.set  -- the set.lean file from mathlib
 
    namespace subuniverse
      section sub
        parameters {σ : signature} {α : Type*} {I : Type*}
        def F := σ.F
        def ρ := σ.ρ 
        def Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:= ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸 f a) ∈ B₀
        def is_subalgebra (𝔸: algebra σ) (B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= ∀ f b, ↑(𝔹 f b) = 𝔸 f ↑b
        def Sg (A : algebra_on σ α) (X : set α) : set α := ⋂₀ {U | Sub A U ∧ X ⊆ U}
        -- BEGIN
        -- intersection introduction ---------------------
        theorem Inter.intro {𝔸: algebra σ} {s: I → set 𝔸}: 
        ∀ (x: 𝔸), (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
        assume x h t ⟨j, (eq: t = s j)⟩, eq.symm ▸ h j

        -- intersection elimination -----------------------------
        theorem Inter.elim {𝔸: algebra σ} {x: 𝔸} {C: I → set 𝔸}: 
        (x ∈ ⋂ i, C i) →  (∀ i, x ∈ C i):= 
        assume h: x ∈ ⋂ i, C i, by simp at h; apply h
        -- END
     end
   end subuniverse

Now we are ready to prove that the easy but important fact that intersections of subuniverses are subuniverses.

.. code-block:: lean

    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    definition algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    definition algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    import data.set  -- the set.lean file from mathlib
 
    namespace subuniverse
      section sub
        parameter {σ : signature} {α : Type*} {I : Type*}
        def F := σ.F
        def ρ := σ.ρ 
        def Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:= ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸 f a) ∈ B₀
        def is_subalgebra (𝔸: algebra σ) (B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= ∀ f b, ↑(𝔹 f b) = 𝔸 f ↑b
        def Sg (A : algebra_on σ α) (X : set α) : set α := ⋂₀ {U | Sub A U ∧ X ⊆ U}
        theorem Inter.intro {𝔸: algebra σ} {s: I → set 𝔸}: ∀ (x: 𝔸), (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
        assume x h t ⟨j, (eq: t = s j)⟩, eq.symm ▸ h j
        theorem Inter.elim {𝔸: algebra σ} {x: 𝔸} {C: I → set 𝔸}: (x ∈ ⋂ i, C i) →  (∀ i, x ∈ C i):= assume h: x ∈ ⋂ i, C i, by simp at h; apply h
        -- BEGIN
        -- Intersection of subuniverses is a subuniverse ---------
        lemma sub_of_sub_inter_sub {𝔸: algebra σ} (C: I → set 𝔸): 
        (∀ i, Sub (C i)) → Sub (⋂i, C i):= 
        assume h: (∀ i, Sub (C i)), show Sub (⋂i, C i), from
        assume (f: F) (a: ρ f → 𝔸) (h₁: ∀ x, a x ∈ ⋂i, C i),
        show 𝔸 f a ∈ ⋂i, C i, from 
          Inter.intro (𝔸 f a)
          (λ j, (h j) f a (λ x, Inter.elim (h₁ x) j))
        -- END
      end
    end subuniverse

Here, ``⋂₀`` is notation for ``sInter (S : set (set α)) : set α := Inf S``, and ``Inf S`` is defined as follows:

``Inf := λs, {a | ∀ t ∈ s, a ∈ t }``

So, if ``S : set (set α)`` (i.e., a collection of sets of type ``α``), then ``Inf S`` is the intersection of the sets in ``S``.

(See also :numref:`Appendix Section %s <intersection-and-union>`, for a more technical description of the intersection operation coercions ``⋂₀`` in Lean.)

Next we formalize three obvious facts and their proofs:

  #. ``X`` is a subset of :math:`\Sg^𝔸 (X)`, 
  #. every subuniverse containing ``X`` also contains :math:`\Sg^𝔸 (X)`, and 
  #. :math:`\Sg^𝔸 (X)` is a subuniverse.

(We will give three alternative, but similar, proofs of the second.)

.. code-block:: lean

    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    definition algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
    definition algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
    import data.set  -- the set.lean file from mathlib
 
    namespace subuniverse
      section sub
        parameter {σ : signature} {α : Type*} {I : Type*}
        def F := σ.F
        def ρ := σ.ρ 
        def Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:= ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸 f a) ∈ B₀
        def is_subalgebra (𝔸: algebra σ) (B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= ∀ f b, ↑(𝔹 f b) = 𝔸 f ↑b
        def Sg (A : algebra_on σ α) (X : set α) : set α := ⋂₀ {U | Sub A U ∧ X ⊆ U}
        theorem Inter.intro {𝔸: algebra σ} {s: I → set 𝔸}: ∀ (x: 𝔸), (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
        assume x h t ⟨j, (eq: t = s j)⟩, eq.symm ▸ h j
        theorem Inter.elim {𝔸: algebra σ} {x: 𝔸} {C: I → set 𝔸}: (x ∈ ⋂ i, C i) →  (∀ i, x ∈ C i):= assume h: x ∈ ⋂ i, C i, by simp at h; apply h
        lemma sub_of_sub_inter_sub {𝔸: algebra σ} (C: I → set 𝔸): (∀ i, Sub (C i)) → Sub (⋂i, C i):= 
        assume h: (∀ i, Sub (C i)), show Sub (⋂i, C i), from
        assume (f: F) (a: ρ f → 𝔸) (h₁: ∀ x, a x ∈ ⋂i, C i),
        show 𝔸 f a ∈ ⋂i, C i, from Inter.intro (𝔸 f a) (λ j, (h j) f a (λ x, Inter.elim (h₁ x) j))

        -- BEGIN
        -- Fact 1. X is a subset of Sgᴬ(X) -------------------
        lemma subset_X_of_SgX {𝔸: algebra σ} (X : set 𝔸): X ⊆ Sg X:= 
        assume x (h: x ∈ X), 
          show x ∈ ⋂₀ {U | Sub U ∧ X ⊆ U}, from 
            assume W (h₁: W ∈ {U | Sub U ∧ X ⊆ U}),  
            show x ∈ W, from 
              have h₂: Sub W ∧ X ⊆ W, from h₁, 
            h₂.right h
    
        -- Fact 2. A subuniverse that contains X also contains Sgᴬ X --
        lemma sInter_mem {𝔸: algebra σ} {X: set 𝔸}:
        ∀ R, Sub R → X ⊆ R → (Sg X ⊆ R) := 
        assume R (h₁: Sub R) (h₂: X ⊆ R),
        show Sg X ⊆ R, from 
          assume x (h: x ∈ Sg X), show x ∈ R, from 
            h R (and.intro h₁ h₂)

        -- An alternative proof of Fact 2. ---------
        lemma sInter_mem' {𝔸: algebra σ} {X: set 𝔸}:
        ∀ R, Sub R ∧ X ⊆ R → (Sg X ⊆ R):= 
        assume R (hc : Sub R ∧ X ⊆ R),
        have h₁: Sub R, from hc.left,
        have h₂: X ⊆ R, from hc.right,
        show Sg X ⊆ R, from 
          assume x (h: x ∈ Sg X), show x ∈ R, from 
            h R (and.intro h₁ h₂)
    
        -- Yet another derivation of Fact 2. ---------
        lemma sInter_mem'' {𝔸: algebra σ} {X: set 𝔸}:
        ∀ x, x ∈ Sg X → ∀ R, Sub R → X ⊆ R → x ∈ R:= 
        assume x (h₁: x ∈ Sg X) (R: set 𝔸) (h₂: Sub R) (h₃: X ⊆ R), 
        show x ∈ R, from h₁ R (and.intro h₂ h₃)
    
        -- Sgᴬ X is a subuniverse of A --------------------------
        lemma SgX_is_Sub {𝔸: algebra σ} (X: set 𝔸): Sub (Sg X):= 
        assume (f: F) (a: ρ f → 𝔸) (h₀: ∀ i, a i ∈ Sg X), 
        show 𝔸 f a ∈ Sg X, from 
          assume W (h: Sub W ∧ X ⊆ W), show 𝔸 f a ∈ W, from 
            have h₁: Sg X ⊆ W, from 
              sInter_mem' W h,
            have h': ∀ i, a i ∈ W, from assume i, h₁ (h₀ i),
            (h.left f a h')
        -- END


----------------------------------------------------------------

.. index:: homomorphism

.. _homomorphisms-in-lean:

Homomorphisms in Lean
---------------------

Using the types defined in the last section, it's not hard to represent the assertion that a function :math:`h : A → B` is a `homomorphism <homomorphisms>`_.

We could clean this up a bit by fixing the signature σ and algebras 𝔸 and 𝔹 in advance, the definition looks a bit cleaner.

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

   -- BEGIN
   variables {σ: signature} {A: algebra σ} {B: algebra σ}

   definition homomorphic (h: A → B) :=
   ∀ f a, h (A f a) = B f (h ∘ a)
   -- END

Comparing this with a common informal language definition of a homomorphism, which is typically something similar to :math:`∀ f \ ∀ a \ h (f^𝔸 (a)) = f^𝔹 (h ∘ a)`, we expect working algebraists to find the ``lean-ualib`` syntax quite readable.

Alternatively, we could define ``homomorphic`` so that the signature and algebras are not specified in advance, but instead passed in as arguments. This is demonstrated below, along with a third alternative that makes the types explicit which can sometimes be instructive.

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

   -- BEGIN
   def homomorphic_with_args 
   {σ : signature} {A : algebra σ} {B : algebra σ} 
   (h : A → B) := ∀ f a, h (A f a) = B f (h ∘ a)

   def homomorphic_explicit (h : A → B) := 
   ∀ (f : σ.F) (a : σ.ρ f → A.fst), h (A f a) = B f (h ∘ a)
   -- END


-------------------------------

.. highlight:: lean

.. include:: _static/math_macros.rst

.. _basic-facts-in-lean:

Basic Facts in Lean
--------------------

In this section we show how to state and prove in Lean the basic facts that we first encountered in :numref:`Chapter %s <basic-facts>`.

.. index:: ! equalizer

Recall, the **equalizer** of the functions :math:`g` and :math:`h` is the set

.. math:: 𝖤(g,h) = \{ a : A ∣ g(a) = h(a) \}.

We begin by defining in Lean

#. the equalizer of two functions, ``E``,

#. a homomorphism, ``hom``, and 

#. the equalizer of two homomorphisms, ``E_hom``.

.. include:: _static/subuniverse.lean.1.rst

.. _composition-of-homomorphisms:

Composition of homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recall the simple fact that composing two homomorphisms results in a homomorphism.

.. include:: _static/homs.lean.1.rst

(As with the other numbered results appearing in this section, we include the statement and proof of the above fact inside the ``basic_facts`` section.)

.. _equalizer-as-subuniverse:

Equalizer as subuniverse
~~~~~~~~~~~~~~~~~~~~~~~~

Next we formally prove that the equalizer ``𝖤 g h`` of two homomorphisms ``g`` and ``h`` is a subuniverse of 𝔸 (cf. :numref:`Obs %s <obs-one>`).

.. include:: _static/homs.lean.2.rst

.. _homomorphisms-that-agree-on-a-generating-set:

Homomorphisms that agree on a generating set
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recall (:numref:`Obs %s <obs-two>`) if two homomorphisms agree on a generating set, then they are equal.

More precisely, if a subset ``X`` is contained in the equalizer of two homomorphisms, then ``Sg X`` is also contained in the equalizer; thus, homomorphisms that agree on ``X`` also agree on ``Sg X``. Let us now state and prove this in Lean.

.. include:: _static/homs.lean.3.rst

Alternatively, we could have proved the last fact using the inductive nature of the definition of subalgebra generated by a set.

Indeed, recall the definition of ``Y`` above and the proof that ``Y X`` is equal to ``Sg X``; thus, properties of the subuniverse generated by the set ``X`` can be proved using the recursor of ``Y``.

.. include:: _static/homs.lean.4.rst

.. _factoring-homomorphisms:

Factoring homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~

Before implementing in Lean the result on factoring homomorphisms (:numref:`Obs %s <obs-four>`), we reiterate that we cannot do so constructively.  Here is a related passage from `Theorem Proving in Lean`_ that explains why.

  "The standard library also defines a choice principle that is entirely antithetical to a computational interpretation, since it magically produces 'data' from a proposition asserting its existence. Its use is essential to some classical constructions, and users can import it when needed. But expressions that use this construction to produce data do not have computational content, and in Lean we are required to mark such definitions ``noncomputable`` to flag that fact... To summarize, then, on top of the underlying framework of universes, dependent function types, and inductive types, the standard library adds three additional components:

  #. the axiom of propositional extensionality
  #. a quotient construction, which implies function extensionality
  #. a choice principle, which produces data from an existential proposition.

  The first two of these block normalization within Lean, but are compatible with :term:`byte-code` evaluation, whereas the third is not amenable to computational interpretation."
   
The upshot is that we cannot always use Lean's ``exists.elim`` to produce data.

Nonetheless, we can use Lean's ``classical`` library and the ``noncomputable`` keyword to formalize proofs of nonconstructive results, like :numref:`Obs %s <obs-four>` on factoring homomorphisms.

.. index:: pair: epic; surjective
.. index:: pair: monic; injective
.. index:: bijective

First we define what it means for a function to be **epic** (or **surjective**), **monic** (or **injective**), and **bijective** (i.e., both epic and monic).

.. include:: _static/homs.lean.5.rst

.. index:: inverse, right inverse

Next, we define the (``noncomputable``) **inverse** and **right inverse** and then prove that an epic function has a right inverse.

(The following is also placed inside the ``basic_facts`` section, inside the ``ualib`` namespace.)

.. include:: _static/homs.lean.6.rst

Finally, we are ready to prove the homomorphism factorization lemma of :numref:`Obs %s <obs-four>`.

(Again, this belongs inside the ``basic_facts`` section.)

.. include:: _static/homs.lean.7.rst

-------------------


.. rubric:: Footnotes

.. [1]
   As of this writing (9 June 2019), this documentation describes code residing in (the william_ branch of) the `lean-ualib`_ repository. Eventually, the latest code will reside on the master_ branch and the docs will describe the code on that branch.
   
.. [2]
   We will see very soon that when implementing general operations (e.g., in Lean) it is unnecessary to commit in advance to a specific arity type :math:`N`. An exception is the *quotient algebra type* since, unless we restrict ourselves to finitary operations, lifting a basic operation to a quotient requires some form of choice.

.. [3]
   The  ``section`` command allows us to open a section throughout which our signature ``σ`` will be available; ``section`` ends when a matching instance of the keyword ``end`` appears.

.. [5]
   For a more general and detailed treatment of this topic, see :numref:`Section %s <tuple-functors>`.

.. [6]
   Technically, this assumes we identify :math:`g` with its graph, which is fairly common practice. We will try to identify any situations in which the conflation of a function with its graph might cause problems.

.. [7]
   In Gentzen style natural deduction, which is the logical system on which Lean_ is based, "introduction" and "elimination" rules are two fundamental types of rules of deduction.  The *introduction rule for conjunction*, for example, specifies how one *forms* a conjunction in the course of a natural deduction proof, while the *elimination rule for conjunction* specifies how one *uses* a conjunction in a natural deduction proof.
   
.. include:: hyperlink_references.rst
