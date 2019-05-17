.. _inductively-defined-type:

=========================
Inductively Defined Types
=========================

A primary motivation for this project was our observation that, on the one hand, many important constructs in universal algebra can be defined inductively, and on the other hand, type theory in general, and Lean in particular, offers excellent support for defining inductive types and powerful tactics for proving their properties.

These two facts suggest that there should be much to gain from implementing universal algebra in an expressive type system that offers powerful tools for proving theorems about inductively defined types.  This vision is made manifest in the Lean code described in :numref:`Sections %s <subuniverse-generation>`, :numref:`%s <clones>` and :numref:`%s <terms-and-free-algebras>`.

.. \ref{sec:leans-hierarchy-of-sorts-and-types})

.. index:: ! subalgebra, ! subuniverse

.. _subalgebras-in-lean:

Subalgebras in Lean [1]_
-------------------------

This section describes how the subalgebra concept and :numref:`Subalgebra generation` can be implemented formally in Lean_.

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

(See also :numref:`Appendix Section %s <intersection>`, for a more technical description of the intersection operation coersions ``⋂₀`` in Lean.)

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


.. index:: subuniverse generated by a set

.. _subuniverse-generation:

Subuniverse generation [1]_
----------------------------

We present the following inductive type that implements the **subuniverse generated by a set**; cf. the definition :eq:`subalgebra-inductive` given in the informal language.

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

.. _clones:

Clones
------

.. todo:: complete this section

.. index:: variables, word, term, free algebra

.. _terms-and-free-algebras:

Terms and free algebras [2]_
-----------------------------

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

------------------------

.. rubric:: Footnotes

.. [1]
   The Lean code described in this section can be found in ``subuniverse.lean`` which resides in the ``src`` directory of the lean-ualib_ repository.

.. [2]
   The Lean code described in this section can be found in ``free.lean`` which resides in the ``src`` directory of the lean-ualib_ repository.

.. [2]
   The **height** of a type is simply type's *level* (see Section ???) and the syntax :math:`Type*` indicates that we do not wish to commit in advance to a specific height.

.. [3]
   The construction of :math:`𝐓_ρ (X)` may seem to be making something out of nothing, but it plays a crucial role in the theory.

.. _Lean: https://leanprover.github.io/

.. _`github.com/UniversalAlgebra/lean-ualib`: https://github.com/UniversalAlgebra/lean-ualib/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

