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

Recall, the symbols ℕ, ω, and ``nat`` are synonymous and all denote the **type of natural numbers**.

The Lean code described in this section is found in the following files of the lean-ualib: ``basic.lean``, ``subuniverse.lean``, ``free.lean``, terms.lean``. [3]_

-----------------------------------------------------

.. index:: signature, operation, operation symbol, similarity type, arity, arity type, variety, equational class, algebraic structure 

Arity and Operations 
--------------------------

We start with the **type of operation symbols**, which depends on our semantic notion of **arity**, also captured by a type.

Argument lists that are passed to operations are represented by tuples which are simply functions, say, of type β → α, where β is the **arity type** of the operation to which the tuple will be passed as an argument list.

Heuristically, it's fine to think of | β | as the "number" of arguments the operation takes, but the implementation is much more general than that. In particular, there is no reason to restrict, *a priori*, the arity type to be a finite set.

An **operation** takes a tuple (or, list of "arguments") of type β → α and returns an element of type α.  Here, α is the type on which the operation is defined.

In Lean, if α and β are types, we define the **type of β-ary operations on α**, denoted by ``op``, to be the function type (β → α) → α.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α

An example of an operation of type ``op(βα)`` is the **projection function** π , defined on the type α, as follows:

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    -- BEGIN
    definition π {β α} (i) : op β α := λ t, t i
    -- END

The operation ``π i`` maps a given tuple ``t : β → α`` to ``t i``, its "value" at input ``i``.

For instance, if we have types ``α, β``, and variables ``i:β`` and ``t:β → α``, then the command ``#check π i t`` shows that the type of ``π i t`` is ``α``, as expected, since ``π i t = t i``.

.. code-block:: lean

    import data.set
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ t, t i
    -- BEGIN
    variables (α : Type*) (β : Type*) (i : β) (t : β → α) 
    #check π i f       -- answer: π i f : α 
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

.. _signature:

Signature
---------

A **signature** :math:`σ = (F, ρ)` consists of

  #. :math:`F :=` a set of **operation symbols**;
  #. :math:`ρ: F → N :=` a **similarity type**.
  
..  giving the **arity**, ``ρf``, of each operation symbol ``f:F``.
  
For each operation symbol :math:`f : F`, the value :math:`ρ f` is called the **arity** of :math:`f`.  This value has type :math:`N`, which is the **arity type**.

In classical universal algebra we typically assume :math:`N = ω := ℕ`, but for most of the basic theory this choice is inconsequential. [1]_

.. index:: type of signatures

.. index:: operation symbol, arity function, 

We now given a first pass at implementing signatures and operations in Lean, highlighting the similarity between the formal and the (classical) informal presentation of these concepts.

We define a signature as a structure with two fields, the type ``F`` of **operation symbols** and an **arity function** ``ρ : F → Type*``, which takes each operation symbol ``f`` to its arity ``ρ f``.

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

Next we open up a ``section`` so we can define some parameters (such as the signature ``σ``) that won't change often throughout the development. [4]_

Then we define the **type of interpretations of operations** on the carrier type ``α``. 

First, let us fix a signature ``σ`` and define some convenient notation.

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

The ``local notation`` directive lets us write ``f : F`` (instead of ``f : σ.F``) to indicate that the operation symbol ``f`` has type ``F``.

Similarly, the second notation directive lets us denote the arity of ``f`` by ``ρ f`` (instead of ``σ.ρ f``).

With this notation, the Lean syntax matches our standard informal algebra syntax almost exactly! [5]_ 

-------------------------------------

.. _universal-algebra:

Universal algebra
------------------

Classical universal algebra is the study of **varieties** (or **equational classes**) of algebraic structures. 

An **algebraic structure** is denoted by :math:`𝐀 = ⟨A, F^{𝐀}⟩` and consists of 

  #. :math:`A :=` a set, called the *universe* (or *carrier*) of the algebra,
  #. :math:`F^{𝐀} = \{f^{𝐀} ∣ f ∈ F, f^{𝐀} : (ρf → A) → A\} :=` a set of operations defined on :math:`A`, and
  #. a collection of identities satisfied by the elements and operations of 𝐀.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :math:`\mathbf{Set}`, such as multisorted algebras, higher-type universal algebra, etc. (:cite:`MR2757312`, :cite:`MR3003214`, :cite:`finster:2018`, :cite:`gepner:2018`, :cite:`MR1173632`). These are natural generalizations that we will become part of the ``lean-ualib`` library, but only after we have an easily accessible implementation of the classical core of (single-sorted, set-based) universal algebra.

Suppose :math:`A` is a set and :math:`f` is a :math:`ρ f`-ary operation on :math:`A`. In this case, we often write :math:`f : A^{ρf} → A`.

If the arity type :math:`N` happens to be the set ℕ of natural numbers, then :math:`ρ f` denotes the set :math:`\{0, 1, \dots, ρf-1\}`.

A function :math:`g` of type :math:`ρf → A` is then simply a :math:`ρ f`-tuple of elements from :math:`A`. [2]_

Fix :math:`m : ℕ`.

An :math:`m`-tuple, :math:`𝐚 = (a_0, a_1, \dots , a_{m-1}) : A^m` is (the graph of) the function :math:`𝐚 : m → 𝖠`, defined for each :math:`i < m` by :math:`𝐚 i = 𝖺_i`.

Therefore, if :math:`h : A → B`, then :math:`h ∘ a : m → B` is the tuple whose value at :math:`i` is :math:`(h ∘ a) i = h a i = h a_i`, which has type :math:`B`.

On the other hand, if :math:`g` has type :math:`A^m → A`, then for each :math:`a : A` the value :math:`g a` has type :math:`A`.

Suppose 

  + :math:`f : (ρf → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, 
  + :math:`a : ρf → A` is a :math:`ρ f`-tuple on :math:`A`, and 
  + :math:`h : A → B`. 

Then :math:`h ∘ a : ρf → B`, so :math:`f (h ∘ a) : B`.

.. _universal-algebras-in-lean:

Universal algebras in Lean
~~~~~~~~~~~~~~~~~~~~~~~~~~

To represent the interpretation of an algebra on a carrier type α, we define a type that we call ``algebra_on``.

.. index:: pair: dependent pair type; Sigma type

.. index:: pair: dependent function type; Pi type

Recall, a **Pi type** ``Π(x:A),B x`` generalizes the function type ``A → B`` and represents a **dependent function type** by allowing the codomain ``B x`` to depend on the value ``x`` of the input argument.

Similarly, a **Sigma type** ``Σ(x:A),B x`` generalizes the Cartesian product ``A × B`` by allowing the type ``B x`` of the second argument of the ordered pair to depend on the value ``x`` of the first. Thus, a Sigma type is called a **dependent pair type**.

Our definition of ``algebra_on`` uses the dependent function type, which makes sense because, if we are given a signature σ and a carrier type α, then an σ-algebra over α is determined by its operations on α, and an inhabitant of the type ``algebra_on`` assigns an interpretation to each ``op`` symbol ``f : F``, which yields a function of type ``ρ f → α → α``. [6]_

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

Finally, let us consider how to define a **universal algebra** in Lean.

A universal algebra :math:`𝐀 = ⟨A,F^𝐀⟩` is a pair consisting of a carrier (or universe) :math:`A` along with an set :math:`F^𝐀` of interpretations of the operation symbols in :math:`F`.

Thus, the type of the second component of the pair :math:`⟨A,F^𝐀⟩` depends on the first, so it is natural to encode the type of algebras as a dependent pair (or Sigma) type.

.. , that is, a type of the form ``Σ(x:A), B x``.

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

(For a disection of Lean's ``sigma`` type, see :numref:`Appendix Section %s <sigma-type>`.)

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

The last two lines are tagged with ``has_coe_to_sort`` and ``has_coe_to_fun``, respectively, because here we are using a very nice feature of Lean called **coercions**.

(For a disection of coercions in Lean, see :numref:`Appendix Section %s <coercions>`.)

Using coercions allows us to employ a syntax that is similar (though not identical) to the standard syntax of informal mathematics.

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

.. index:: subalgebra, subuniverse

.. _subalgebra:

Subalgebra
----------

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

.. _subalgebras-in-lean:

Subalgebras in Lean 
~~~~~~~~~~~~~~~~~~~

The argument in the proof of :numref:`Theorem %s <thm-1-14>` is of a type that one encounters frequently throughout algebra. It has two parts.

  #. Some set :math:`Y` is shown to be a subuniverse of 𝐀 that contains :math:`X`.

  #. Every subuniverse containing :math:`X` is shown to contain :math:`Y` as well.

  #. One concludes that :math:`Y = \mathrm{Sg}^𝐀 (X)`.

We now show how the subalgebra concept and the foregoing argument can be implemented formally in Lean_. [7]_

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

Lean syntax for the intersection operation on collections of *sets* is ``⋂₀``. [8]_

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

---------------------------------------------------

.. _inductively-defined-type:

Inductively defined types
-------------------------

A primary motivation for this project was our observation that, on the one hand, many important constructs in universal algebra can be defined inductively, and on the other hand, type theory in general, and Lean in particular, offers excellent support for defining inductive types and powerful tactics for proving their properties.

These two facts suggest that there should be much to gain from implementing universal algebra in an expressive type system that offers powerful tools for proving theorems about inductively defined types.

.. index:: subuniverse generated by a set

As such, we are pleased to present the following inductive type that implements the **subuniverse generated by a set**; cf. the definition :eq:`subalgebra-inductive` given in the informal language.

.. code-block:: lean

    inductive Y (X : set α) : set α
    | var (x : α) : x ∈ X → Y x
    | app (f : F) (a : ρ f → α) : (∀ i, Y (a i)) → Y (A f a)
  
Next we prove that the type ``Y X`` defines a subuniverse, and that it is, in fact, equal to :math:`\mathrm{Sg}^𝐀(X)`.

.. code-block:: lean

    -- Y X is a subuniverse
    lemma Y_is_Sub (X : set α) : Sub (Y X) := 
    assume f a (h: ∀ i, Y X (a i)), show Y X (A f a), from 
    Y.app f a h 
   
    -- Y X is the subuniverse generated by X
    theorem sg_inductive (X : set α) : Sg X = Y X :=
    have h₀ : X ⊆ Y X, from 
      assume x (h : x ∈ X), 
      show x ∈ Y X, from Y.var x h,
    have h₁ : Sub (Y X), from 
      assume f a (h : ∀ x, Y X (a x)), 
      show Y X (A f a), from Y.app f a h,
    have inc_l : Sg X ⊆ Y X, from 
       assume u (h : u ∈ Sg X), 
       show u ∈ Y X, from (sInter_mem u) h h₁ h₀,
    have inc_r : Y X ⊆ Sg X, from
       assume a (h: a ∈ Y X), show a ∈ Sg X, from
         have h' : a ∈ Y X → a ∈ Sg X, from 
           Y.rec
           --base: a = x ∈ X
           ( assume x (h1 : x ∈ X), 
             show x ∈ Sg X, from subset_X_of_SgX X h1 )
           --inductive: a = A f b for some b with ∀ i, b i ∈ Sg X
           ( assume f b (h2 : ∀ i, b i ∈ Y X) (h3 : ∀ i, b i ∈ Sg X),
             show A f b ∈ Sg X, from SgX_is_Sub X f b h3 ),
         h' h,
    subset.antisymm inc_l inc_r

Observe that the last proof proceeds exactly as would a typical informal proof that two sets are equal---prove two subset inclusions and then apply the ``subset.antisymm`` rule, :math:`A ⊆ B → B ⊆ A → A = B`.

.. index:: recursor

We proved ``Y X ⊆ Sg X`` in this case by induction using the **recursor**, ``Y.rec``, which Lean creates for us automatically whenever an inductive type is defined.

The Lean keyword ``assume`` is syntactic sugar for ``λ``; this and other notational conveniences, such as Lean's ``have...from`` and ``show...from`` syntax, make it possible to render formal proofs in a very clear and readable way.

----------------------------------------------

.. index:: variables, word, term, free algebra

.. _terms-and-free-algebra:

Terms and free algebras
-----------------------

Fix a signature :math:`σ = (F, ρ)`, let :math:`X` be a set of **variables** and assume :math:`X ∩ F = ∅`.

For every :math:`n < ω`, let  :math:`F_n = ρ^{-1} \{n\}` be the set of :math:`𝗇`-ary operation symbols.

By a **word** on :math:`X ∪ F` we mean a nonempty, finite sequence of members of :math:`X ∪ T`.

We denote the concatenation of sequences by simple juxtaposition. We define, by recursion on :math:`n`, the sets :math:`T_n` of words on :math:`X ∪ F` by

.. math::      T_0 &= X ∪ F_0;\\
           T_{n+1} &= T_n ∪ \{ f s ∣ f ∈  F, \ s : ρf → T_n \}. 

Define the set of **terms in the signature** σ **over** :math:`X` by :math:`T_ρ(X) = ⋃_{n < ω}T_n`.

The definition of :math:`T_ρ (X)` is recursive, indicating that *the set of terms in a signature can be implemented in Lean using an inductive type*.

We will confirm this in the next subsection, but before doing so, we impose an algebraic structure on :math:`T_ρ(X)`, and then state and prove some basic but important facts about this algebra.

These will also be formalized in the next section, giving us another chance to compare informal language proofs to their formal Lean counterparts, and to show off inductively defined types in Lean.

If :math:`w` is a term, let :math:`|w|` be the least :math:`n` such that :math:`w ∈ T_n`, called the *height* of :math:`w`. [9]_ The height is a useful index for recursion and induction.

Notice that the set :math:`T_ρ (X)` is nonempty iff either :math:`X` or :math:`F_0` is nonempty. As long as :math:`T_ρ (X)` is nonempty, we can impose upon this set an algebraic structure, as follows:

For every basic operation symbol :math:`f ∈ F` let :math:`f^{𝐓_ρ (X)}` be the operation on :math:`𝐓_ρ (X)` that maps each tuple :math:`t : ρf → T_ρ (X)` to the term :math:`ft`.

We define :math:`𝐓_ρ (X)` to be the algebra with universe :math:`T_ρ (X)` and with basic operations :math:`\{f^{𝐓_ρ (X)} | f ∈ F\}`. [10]_

Indeed, Part (2) of :ref:`Theorem 4.21 <thm-4-21>` below asserts that :math:`𝐓_ρ (X)` is *universal for* \sigma-algebras.

To prove this, we need the following basic lemma, which states that a homomorphism is uniquely determined by its restriction to a generating set. (See also :cite:`Bergman:2012`, Ex. 1.16.6.)

.. _ex_1-16-6-brief:

.. proof:lemma::

   Let :math:`f` and :math:`g` be homomorphisms from 𝐀 to 𝐁. If :math:`X ⊆ A` and :math:`X` generates 𝐀 and :math:`f|_X = g|_X`, then :math:`f = g`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Suppose the subset :math:`X ⊆ A` generates 𝐀 and suppose :math:`f|_X = g|_X`. Fix an arbitrary element :math:`a ∈ A`.

      We show :math:`f(a) = g(a)`. Since :math:`X` generates 𝐀, there exists a (say, :math:`n`-ary) term :math:`t` and a tuple :math:`(x_1, \dots, x_n) ∈ X^n` such that :math:`a = t^{𝐀}(x_1, \dots, x_n)`. Therefore,

      .. math:: f(a) = f(t^{𝐀}(x_1, \dots, x_n)) &= t^{𝐁}(f(x_1), \dots, f(x_n)) \\
                                    &= t^{𝐁}(g(x_1), \dots, g(x_n)) = g(t^{𝐀}(x_1, \dots, x_n)) = g(a).

Here is another useful theorem. (See also :cite:`Bergman:2012`, Thm. 4.21.) 

.. _thm-4-21:

.. proof:theorem::

   Let :math:`σ = (F, ρ)` be a signature.

   #. :math:`𝐓_ρ (X)` is generated by X.
   #. For every σ-algebra 𝐀 and every function :math:`h : X → A` there is a unique homomorphism :math:`g : 𝐓_ρ (X) → 𝐀` such that :math:`g|_X = h`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      The definition of :math:`𝐓_ρ (X)` exactly parallels the construction in :ref:`Theorem 1.14 <thm-1-14>`. That accounts for (1).

      For (2), define :math:`g(t)` by induction on :math:`ρt`. Suppose :math:`ρt = 0`. Then :math:`t ∈ X ∪ F`.
      
      If :math:`t ∈ X` then define :math:`g(t) = h(t)`. For :math:`t ∉ X`, :math:`g(t) = t^{𝐀}`.
      
      Note that since 𝐀 is an \sigma-algebra and 𝗍 is a nullary operation symbol, :math:`t^{𝐀}` is defined.
    
      For the inductive step, let :math:`|t| = n + 1`. Then :math:`t = f(s_1, \dots, s_k)` for some :math:`f ∈ F_k` and :math:`s_1, \dots, s_k` each of height at most :math:`n`.
      
      We define :math:`g(t) = f^{𝐀}(g(s_1), \dots, g(s_k))`.
      
      By its very definition, 𝗀 is a homomorphism.
      
      Finally, the uniqueness of 𝗀 follows from :ref:`Lemma 1.16 <ex_1-16-6-brief>`. 

.. _terms-and-free-algebras-in-lean:

Terms and free algebras in Lean [11]_
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As a second demonstration of inductive types in Lean, we define a type representing the (infinite) collection :math:`𝐓(X)` of all terms of a given signature.

.. code-block:: lean

    import basic
    section
      parameters {σ : signature} (X :Type*) 
      local notation `F` := σ.F
      local notation `ρ` := σ.ρ 
    
      inductive term
      | var : X → term
      | app (f : F) : (ρ f → term) → term
  
      def Term : algebra S := ⟨term, term.app⟩
    end

The set of terms along with the operations :math:`F^{𝐓} := \{\mathsf{app} f | f : F\}` forms an algebra :math:`𝐓(X) = ⟨T(X), F^{𝐓}⟩` in the signature :math:`σ = (F, ρ)`.

Suppose :math:`𝐀 = ⟨A, F^{𝐀}⟩` is an algebra in the same signature and :math:`h : X → A` is an arbitrary function.  We will show that :math:`h : X → A` has a unique *extension* (or *lift*) to a homomorphism from :math:`𝐓(X)` to 𝐀.

Since 𝐀 and :math:`h : X → A` are arbitrary, this unique homomorphic lifting property holds universally; accordingly we say that the term algebra :math:`𝐓(X)` is *universal* for σ-algebras. Some authors say, ":math:`𝐓(X)` is *absolutely free* for σ-algebras," in this and only this case.

Before implementing the formal proof of this fact in Lean, let us first define some domain specific syntactic sugar.

.. code-block:: lean

    section
      open term
      parameters {σ : signature} (X :Type*) {A : algebra σ}
      definition F := σ.F         -- operation symbols
      definition ρ := σ.ρ         -- arity function
      definition 𝕋 := @Term σ     -- term algebra over X
      definition 𝕏 := @var σ X    -- generators of the term algebra

If :math:`h : X → A` is a function defined on the generators of the term algebra, then the *lift* (or *extension*) of :math:`h` to all of :math:`𝕋(X)` is defined inductively as follows:

.. code-block:: lean

    definition lift_of (h : X → A) : 𝕋(X) → 
    | (var x) := h x
    | (app f a) := (A f) (λ x, lift_of (a x))

To prove that the term algebra is universal for σ-algebras, we show that the lift of an arbitrary function :math:`h : X → A` is a homomorphism and that this lift is unique.

.. code-block:: lean

      -- The lift is a homomorphism.
      lemma lift_is_hom (h : X → A) : homomorphic (lift_of h) :=
      λ f a, show lift_of h (app f a) = A f (lift_of h ∘ a), from rfl
    
      -- The lift is unique.
      lemma lift_is_unique : ∀ {h h' : 𝕋(X) → A},
      homomorphic h → homomorphic h' → h ∘ 𝕏 = h' ∘ 𝕏 → h = h' :=
      assume (h h' : 𝕋(X) → A) (h₁ : homomorphic h)
        (h₂ : homomorphic h')(h₃ : h ∘ 𝕏 = h' ∘ 𝕏),
        show h = h', from 
          have h₀ : ∀ t : 𝕋(X), h t = h' t, from 
            assume t : 𝕋(X), 
            begin
              induction t with t f a ih₁ ,
              show h (𝕏 t) = h' (𝕏 t),
              { apply congr_fun h₃ t },
    
              show h (app f a) = h' (app f a),
              { have ih₂  : h ∘ a = h' ∘ a, from funext ih₁,
                calc h (app f a) = A f (h ∘ a) : h₁ f a
                             ... = A f (h' ∘ a) : congr_arg (A f) ih₂ 
                             ... = h' (app f a) : (h₂ f a).symm }
            end,
          funext h₀ 
    end

Let :math:`𝐀 = ⟨A, F^{𝐀}⟩` be a \sigma-algebra.

.. with congruence lattice $\Con\<A, \dots \>$.

.. index:: clone

Recall that a **clone** on a nonempty set :math:`A` is a set of operations on :math:`A` that contains the projection operations and is closed under general composition. 

Let :math:`A` denote the set of all clones on :math:`A`.

The **clone of term operations** of an σ-algebra 𝐀, denoted by :math:`\mathrm{Clo} 𝐀`, is the smallest clone on :math:`A` containing the basic operations of 𝐀, that is,

.. math:: \mathrm{Clo} 𝐀 = ⋂ \{ U ∈ 𝖢 A ∣ F^{𝐀} ⊆ U\}.

The set of :math:`n`-ary members of :math:`\mathrm{Clo} 𝐀` is sometimes denoted by :math:`\mathrm{Clo}_n 𝐀` (despite the fact that the latter is obviously not a clone).

We now state a theorem that shows how the clone of term operations of a signature can be defined inductively.

.. _thm-4-3:

.. proof:theorem::

   Let :math:`X` be a set and :math:`σ = (F, ρ)` a signature. Define

   .. math:: F_0 &= X;\\
         F_{n+1} &= F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρ g → X)) \}, \quad n < ω.

   Then :math:`\mathrm{Clo}^X(F) = ⋃_n F_n`.

Thus *the clone of terms operations can be implemented (e.g., in Lean) as an inductive type*. The following theorem makes this precise. (See also :cite:`Bergman:2012`, Thm. 4.32.)

.. _thm-4-32:

.. proof:theorem::

   Let 𝐀 and 𝐁 be algebras of type :math:`ρ`.

   #. For every :math:`n`-ary term :math:`t ∈ T_ρ (X_ω)` and homomorphism :math:`g : 𝐀 → 𝐁`,
      
      .. math:: g(t^{𝐀}(a_1,\dots, a_n)) = t^{𝐁}(g(a_1),\dots, g(a_n)).

   #. For all :math:`t ∈ T_ρ (X_ω)`, :math:`θ ∈ \mathrm{Con} 𝐀`, :math:`𝐚 : ρ t → A` and :math:`𝐛 : ρ t → A`,
   
      .. math:: 𝐚 \mathrel{θ} 𝐛 ⟹ t^{𝐀}(𝐚) \mathrel{θ} t^{𝐀}(𝐛).

   #. For every subset :math:`Y ⊆ A`,

      .. math:: \mathrm{Sg}^{𝐀}(Y) = \{ t^{𝐀}(a_1, \dots, a_n) : t ∈ T(X_n), a_i ∈ Y, i ≤ n < ω\}.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      The first statement is an easy induction on :math:`|t|`.

      The second statement follows from the first by taking :math:`𝐁 = 𝐀/θ` and 𝗀 the canonical homomorphism.
  
      For the third statement, again by induction on the height of 𝗍, every subalgebra must be closed under the action of :math:`t^{𝐀}`. 
  
      Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows.

--------------------------------------------------------------

.. rubric:: Footnotes

.. [1]
   As we will see when implementing general operations in Lean, it is unnecessary to commit in advance to a specific arity type :math:`N`. An exception is the *quotient algebra type* since, unless we restrict ourselves to finitary operations, lifting a basic operation to a quotient requires some form of choice.

.. [2]
   Technically, this assumes we identify :math:`g` with its graph, which is fairly common practice. We will try to identify any situations in which the conflation of a function with its graph might cause problems.

.. [3] 
   The ``lean-ualib`` source code is available from `github.com/UniversalAlgebra/lean-ualib`_.

.. [4]   
   The  ``section`` command allows us to open a section throughout which our signature ``σ`` will be available; ``section`` ends when the keyword ``end`` appears.

.. [5]
   The only exception is that in type theory we make *typing judgments*, denoted by ``:``, rather than set membership judgments, denoted by ``∈``.

.. [6]
   plus whatever equational laws it may models; our handling of *theories* and *models* in Lean is beyond our current scope; for more information, see `github.com/UniversalAlgebra/lean-ualib`_.

.. [7]
   See https://github.com/UniversalAlgebra/lean-ualib/blob/master/src/subuniverse.lean

.. [8]
   Technically, ``⋂₀ S`` denotes ``sInter (S : set (set α)) : set α := {λ s, a | ∀ t ∈ s, a ∈ t}`` Given a collection ``S : set (set α)`` of sets of type ``α``, ``⋂₀ S`` is the intersection of the sets in ``S``, as claimed.

.. [9]
   The **height** of a type is simply type's *level* (see Section ???) and the syntax :math:`Type*` indicates that we do not wish to commit in advance to a specific height.

.. [10]
   The construction of :math:`𝐓_ρ (X)` may seem to be making something out of nothing, but it plays a crucial role in the theory.

.. [11]
   https://github.com/UniversalAlgebra/lean-ualib/blob/master/src/free.lean

.. _Lean: https://leanprover.github.io/

.. _`github.com/UniversalAlgebra/lean-ualib`: https://github.com/UniversalAlgebra/lean-ualib/

.. The clone of *polynomials} of $\alg A$, denoted by $\Pol \alg A$, is the clone generated by the basic operations of $\alg A$ and the constant unary maps on $A$.

.. The set of  :math:`n`-ary members of $\Pol \alg A$ is sometimes denoted by $\Pol_n \alg A$. The smallest clone on a set $A$ is the set of all projections 

.. $\Proj A := \{\pi^n_i \mid 0\leq i < n < \omega\}$, defined as follows: for $0\leq i < n < \omega$, if $a \colon n \to A$, then $\pi^n_i a = a\, i$.
 
.. .. [9] Lean's built-in sigma type is defined as follows: :math:`structure sigma {α : Type u} (β : α → Type v) := mk :: (fst : α) (snd : β fst)`
