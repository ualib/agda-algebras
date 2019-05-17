.. math:: \newcommand{\Sg}{\mathsf{Sg}} \newcommand\hom{\operatorname{Hom}} \newcommand\epi{\operatorname{Epi}} \newcommand\aut{\operatorname{Aut}} \newcommand\mono{\operatorname{Mono}} \newcommand\Af{\ensuremath{\langle A, f \rangle}} 

.. role:: cat

.. role:: code

.. _universal-algebra-in-lean:

=========================
Universal Algebra in Lean
=========================

This section demonstrates the utility of dependent and inductive types by expressing some fundamental concepts of universal algebra in Lean.

In particular, we will formally represent each of the following:  *operation*, *algebra*, *subuniverse*, and *term algebra*.

Our formal representations of these concepts will be clear, concise, and computable. Moreover, we strive to develop a notation and syntax that will feel natural to working algebraists.

Our goal here is to demonstrate the power of Lean's type system for expressing mathematical concepts precisely and constructively, and to show that if we make careful design choices at the start of our development, then our formal theorems *and their proofs* can approximate the efficiency and readability of analogous informal presentations found in the mathematics literature.

Most of the Lean code described in this section can be found in the files ``basic.lean`` and ``subuniverse.lean`` which reside in the ``src`` directory of the lean-ualib_ repository.

-----------------------------------------------------

.. index:: arity, operation
.. index:: airty type, operation symbol type
.. index:: type of; operation symbols
.. index:: type of; arities
.. index:: type of; natural numbers

Arity and Operations 
--------------------

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

------------------------------------------------------

.. _signatures-in-lean:

.. index:: ! signature, ! operation symbol, ! similarity type

.. index:: ! arity

Signature in Lean
-----------------

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

-------------------------------------

.. index:: pair: variety; equational class
.. index:: triple: algebra; structure; universal algebra

.. _universal-algebras-in-lean:

Universal algebras in Lean
--------------------------

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

A :index:`universal algebra` :math:`𝐀 = ⟨A,F^𝐀⟩` is a pair consisting of a :index:`carrier` (or :index:`universe`) :math:`A` along with an set :math:`F^𝐀` of :index:`operations` (i.e., interpretations of the operation symbols in :math:`F`). Thus, the type of the second component of the pair :math:`⟨A,F^𝐀⟩` depends on the first, so it is natural to encode the type of algebras as a :index:`dependent pair`, or :index:`Sigma type`.

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

(See also :numref:`Appendix Section %s <sigma-type>`, for a more technical description of coersions in Lean.)

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

The last two lines are tagged with ``has_coe_to_sort`` and ``has_coe_to_fun``, respectively, because here we are using a very nice feature of Lean called **coercions**. Using coercions allows us to employ a syntax that is similar (though not identical) to the standard syntax of informal mathematics. 

For instance, the standard notation for the interpretation of the operation symbol :math:`f` in the algebra :math:`𝐀 = ⟨A, F^𝐀⟩` is :math:`f^𝐀`. In our Lean implementation, we use ``A f`` to denote :math:`f^𝐀`. Although this syntax doesn't match the informal syntax exactly, it seems equally elegant and adapting to it should not overburden the user.

Another example that demonstrates the utility of coercions is our definition of ``is_subalgebra``, a function that takes as input two algebraic structures and decides whether the second structure is a subalgebra of the first.  Here is the definition.  (See also :numref:`Appendix Section %s <coercions>`, for a more technical description of coersions in Lean.)

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

.. index:: homomorphism

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

-----------------------------------------------------

.. \ref{sec:leans-hierarchy-of-sorts-and-types})

.. index:: ! subalgebra, ! subuniverse

.. _subalgebras-in-lean:

Subalgebras in Lean
--------------------

Two important concepts in universal algebra are **subuniverse** and **subalgebra**.

Our Lean implementation of subuniverse will illustrate one of the underlying themes that motivates our work. Indeed, we demonstrate the power of **inductively defined types**, which are essential for working with infinite objects in a constructive and computable way, and for proving (by induction) properties of these objects. 

A **subuniverse** of an algebra :math:`𝐀 = ⟨A, F^𝐀⟩` is a subset :math:`B ⊆ A` that is closed under the operations in :math:`F^𝐀`.

We denote by S 𝐀 the set of all subuniverses of 𝐀.

If :math:`B` is a subuniverse of 𝐀 and :math:`F^{𝐁|_A} = \{f^𝐀|_B ∣ f ∈ F\}` is the set of basic operations of 𝐀 restricted to the set :math:`B`, then :math:`𝐁 = ⟨B, F^{𝐁|_A}⟩` is a **subalgebra** of 𝐀.

Conversely, all subalgebras are of this form.

If 𝐀 is an algebra and :math:`X ⊆ A` a subset of the universe of 𝐀, then the **subuniverse of** 𝐀 **generated by** :math:`X` is defined as follows:

.. math:: \mathrm{Sg}^{𝐀}(X)  =  ⋂ \{ U ∈ 𝖲 𝐀 ∣ X ⊆ U \}.
  :label: SgDef

To give another exhibition of the efficiency and ease with which we can formalize basic but important mathematical concepts in Lean, we now present a fundamental theorem about subalgebra generation, first in the informal language, and then formally :ref:`below <subalgebras-in-lean>`.

Notice that the added complexity of the Lean implementation of this theorem is not significant, and the proof seems quite readable (especially when compared to the syntax used by other interactive theorem provers).  

The following is a recursive definition of the subuniverse generated by a set. (See :cite:`Bergman:2012`, Thm. 1.14.)

.. _thm-1-14:

.. proof:theorem:: Subuniverse generation

   Let :math:`𝐀 = ⟨A, F^{𝐀}⟩`  be  an  algebra in the signature :math:`σ = (F, ρ)` and let :math:`X ⊆ A`.

   Define, by recursion on :math:`n`, the sets :math:`X_n` as follows:

   .. math:: X_0  &=  X \\
          X_{n+1} &=  X_n ∪ \{ f a  ∣ f ∈ F, \ a ∈ X_n^{ρf}\}.
      :label: subalgebra-inductive

   Then  :math:`\mathrm{Sg}^{𝐀}(X) = ⋃ X_n`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let :math:`Y = ⋃_{n < ω} X_n`. Clearly :math:`X_n ⊆ Y ⊆ A`, for every :math:`n < ω`. In particular :math:`X = X_0 ⊆ Y`.

      Let us show that :math:`Y` is a subuniverse of 𝐀.
   
      Let :math:`f` be a basic :math:`k`-ary operation and :math:`a ∈ Y^k`.
    
      From the construction of :math:`Y`, there is an :math:`n < ω` such that :math:`∀ i,\ a,\ i ∈ X_n`.
    
      From its definition, :math:`f a ∈ X_{n+1} ⊆ Y`.
    
      Thus :math:`Y` is a subuniverse of 𝐀 containing :math:`X`.
    
      By :eq:`SgDef`, :math:`\mathrm{Sg}^{𝐀}(X) ⊆ Y`.
    
      For the opposite inclusion, it is enough to check, by induction on :math:`n`, that :math:`X_n ⊆ \mathrm{Sg}^{𝐀}(X)`.
    
      By definition, :math:`X_0 = X ⊆ \mathrm{Sg}^{𝐀}(X)`.
      
      Assume :math:`X_n ⊆ \mathrm{Sg}^𝐀(X)`.  We show :math:`X_{n+1} ⊆ \mathrm{Sg}^𝐀(X)`.
      
      If :math:`b ∈ X_{n+1} - X_n`, then :math:`b = f a` for a basic :math:`k`-ary operation :math:`f` and some :math:`a ∈ X_n^k`.
      
      But :math:`∀ i, \ a i ∈ \mathrm{Sg}^𝐀(X)` and since this latter object is a subuniverse, :math:`b ∈ \mathrm{Sg}^𝐀(X)` as well.
    
      Therefore, :math:`X_{n+1} ⊆ \mathrm{Sg}^𝐀(X)`, as desired.

The argument in the proof of :numref:`Theorem %s <thm-1-14>` is of a type that one encounters frequently throughout algebra. It has two parts.

  #. Some set :math:`Y` is shown to be a subuniverse of 𝐀 that contains :math:`X`.

  #. Every subuniverse containing :math:`X` is shown to contain :math:`Y` as well.

  #. One concludes that :math:`Y = \mathrm{Sg}^𝐀 (X)`.

We now show how the subalgebra concept and the foregoing argument can be implemented formally in Lean_. [5]_

.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    open set
    parameter {α : Type*}      -- the carrier type 
    parameter {σ : signature}
    parameter (A : algebra_on σ α) 
    parameter {I : Type}       -- a collection of indices
    parameter {R : I → set α}  -- an indexed set of sets of type α
    definition F := σ.F        -- the type of operation symbols
    definition ρ := σ.ρ        -- the operation arity function
    -- END
    end subs
    end subuniverse

.. code-block:: lean

    definition Sub (β : set α) : Prop :=
    ∀ (f : F) (a : ρ f → α), (∀ x, a x in β) → (A f a in β)

.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    definition Sg (X : set α) : set α := ⋂₀ {U | Sub U ∧ X ⊆ U}
    -- END
    end subs
    end subuniverse

Lean syntax for the intersection operation on collections of *sets* is ``⋂₀``. [6]_

Next we need *introduction* and *elimination* rules for arbitrary intersections, plus the useful fact that the intersection of subuniverses is a subuniverse. 

.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    /- Intersection introduction rule -/
    theorem Inter.intro {s : I → set α} : 
    ∀ x, (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
    assume x h t ⟨a, (eq : t = s a)⟩, eq.symm ▸ h a
    -- END
    end subs
    end subuniverse

.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    /- Intersection elimination rule -/
    theorem Inter.elim {x : α} (C : I → set α) : 
    (x ∈ ⋂ i, C i) → (∀ i, x ∈ C i) := 
    assume h : x ∈ ⋂ i, C i, by simp at h; apply h
    -- END
    end subs
    end subuniverse
      
.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    /- Intersection of subuniverses is a subuniverse -/
    lemma sub_of_sub_inter_sub (C : I → set α) : 
    (∀ i, Sub (C i)) → Sub ⋂i, C i :=
    assume h : ∀ i, Sub (C i), show Sub (⋂i, C i), from 
      assume (f : F) (a : ρ f → α) (h₁ : ∀ x, a x ∈ ⋂i, C i), 
      show A f a ∈ ⋂i, C i, from 
        Inter.intro (A f a) 
        (λ j, (h j) f a (λ x, Inter.elim C (h₁ x) j))
    -- END
    end subs
    end subuniverse

The next three lemmas show that :math:`\mathrm{Sg} X` is the smallest subuniverse containing :math:`X`.

.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    -- X is a subset of Sg(X)
    lemma subset_X_of_SgX (X : set α) : X ⊆ Sg X := 
    assume x (h : x ∈ X), 
    show x ∈ ⋂₀ {U | Sub U ∧ X ⊆ U}, from 
      assume W (h₁ : W ∈ {U | Sub U ∧ X ⊆ U}), 
      show x ∈ W, from 
        have h₂ : Sub W ∧ X ⊆ W, from h₁, 
        h₂.right h
    -- END
    end subs
    end subuniverse
      
.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    -- A subuniverse that contains X also contains Sg X
    lemma sInter_mem {X : set α} (x : α) : 
    x ∈ Sg X → ∀ {R : set α }, Sub R → X ⊆ R → x ∈ R := 
    assume (h₁ : x ∈ Sg X) (R : set α) (h₂ : Sub R) (h₃ : X ⊆ R), 
    show x ∈ R, from h₁ R (and.intro h₂ h₃)
    -- END
    end subs
    end subuniverse
      
.. code-block:: lean

    import basic
    import data.set
    namespace subuniverse
    section subs
    -- BEGIN
    -- Sg X is a Sub
    lemma SgX_is_Sub (X : set α) : Sub (Sg X) := 
    assume (f : F) (a : ρ f → α) (h₀ : ∀ i, a i ∈ Sg X), 
    show A f a ∈ Sg X, from 
     assume W (h : Sub W ∧ X ⊆ W), show A f a ∈ W, from 
      have h₁ : Sg X ⊆ W, from 
        assume r (h₂ : r ∈ Sg X), show r ∈ W, from 
         sInter_mem r h₂ h.left h.right,
         have h' : ∀ i, a i ∈ W, from assume i, h₁ (h₀ i),
         (h.left f a h')
    -- END
    end subs
    end subuniverse

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

.. [5]
   See https://github.com/UniversalAlgebra/lean-ualib/blob/master/src/subuniverse.lean

.. [6]
   Technically, ``⋂₀ S`` denotes ``sInter (S : set (set α)) : set α := {λ s, a | ∀ t ∈ s, a ∈ t}`` Given a collection ``S : set (set α)`` of sets of type ``α``, ``⋂₀ S`` is the intersection of the sets in ``S``, as claimed.

.. _Lean: https://leanprover.github.io/

.. _`github.com/UniversalAlgebra/lean-ualib`: https://github.com/UniversalAlgebra/lean-ualib/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

.. The clone of *polynomials} of $\alg A$, denoted by $\Pol \alg A$, is the clone generated by the basic operations of $\alg A$ and the constant unary maps on $A$.

.. The set of  :math:`n`-ary members of $\Pol \alg A$ is sometimes denoted by $\Pol_n \alg A$. The smallest clone on a set $A$ is the set of all projections 

.. $\Proj A := \{\pi^n_i \mid 0\leq i < n < \omega\}$, defined as follows: for $0\leq i < n < \omega$, if $a \colon n \to A$, then $\pi^n_i a = a\, i$.
 
.. .. [9] Lean's built-in sigma type is defined as follows: :math:`structure sigma {α : Type u} (β : α → Type v) := mk :: (fst : α) (snd : β fst)`
