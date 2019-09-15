.. include:: _static/math_macros.rst

.. _inductively-defined-things:

=====================
Inductive Definitions
=====================

One of the primary motivations for the `lean-ualib`_ project was our observation that, on the one hand, many important constructs in universal algebra can be defined inductively, and on the other hand, type theory in general, and Lean in particular, offers excellent support for defining inductive types and powerful tactics for proving their properties.

These two facts suggest that there is much to be gained from implementing universal algebra in an expressive type system that offers powerful tools for proving theorems about inductively defined types. Examples demonstrating how this vision manifests in our Lean library are presented in :numref:`subalgebras-in-lean`, :numref:`terms-in-lean`, and :numref:`clones-in-lean`.

.. In particular, our Lean_ implementation of the notion of :term:`subuniverse` illustrates one of these underlying themes motivating our work.

To exhibit the efficiency and ease with which we can formalize and work with basic but important mathematical objects in Lean_, we will present some fundamental theorems about subalgebras, terms and clones---first in this chapter using the informal language of universal algebra, and then in the next chapter using the formal language of Lean.

The idea is to demonstrate the power and utility of implementing the theory in a formal language that supports dependent and inductively defined types, which are essential for expressing and working with infinite objects in a constructive and computable way, and for proving (by induction) properties of these objects.

-----------------------------------------------

.. _basic-facts:

Basic Facts
-----------

Throughout this section,

+ :math:`𝔸 = ⟨A, F^𝔸⟩, \ 𝔹 = ⟨B, F^𝔹⟩, \ ℂ = ⟨C, F^ℂ⟩\ ` are algebras of the same signature :math:`σ = (F, ρ)`, and

+ :math:`g, h : \hom(𝔸, 𝔹)` are homomorphism from 𝔸 to 𝔹;

.. index:: ! equalizer

The **equalizer** of :math:`g` and :math:`h` is the set

.. math:: 𝖤(g,h) = \{ a : A ∣ g(a) = h(a) \}.

Here is a small collection of basic observations that we will need later. When we refer back to these, we will call them :numref:`Obs %s <obs-one>`, etc.

.. _obs-one:

.. proof:observation::

   :math:`𝖤(g,h)` is a subuniverse of 𝔸.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      Fix arbitrary :math:`f ∈ F` and :math:`a : ρf → 𝖤(g,h)`.

      We show that :math:`g (f^𝔸 ∘ a) = h (f^𝔸 ∘ a)`, as this shows that :math:`𝖤(g, h)` is closed under the operation :math:`f^𝔸` of :math:`𝔸`.

      But this is trivial since, by definition of homomorphism, we have

      .. math:: (g ∘ f^𝔸)(ι_i a) = (f^𝔹 ∘ F g)(ι_i a) = (f^𝔹 ∘ F h)(ι_i a) = (h ∘ f^𝔸)(ι_i a).

      ☐

.. _obs-two:

.. proof:observation::

   If the set :math:`X ⊆ A` generates 𝔸 and :math:`g|_X = h|_X`, then :math:`g = h`.

   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Suppose the subset :math:`X ⊆ A` generates :math:`⟨A, f^𝔸⟩` and suppose :math:`g|_X = h|_X`.
 
      Fix an arbitrary :math:`a : A`. We show :math:`g(a) = h(a)`.
 
      Since :math:`X` generates 𝔸, there exists a term :math:`t` and a tuple :math:`x : ρt → X` of generators such that :math:`a = t^𝔸 x`.
 
      Therefore, since :math:`F g = F h` on :math:`X`, we have
    
      .. math:: g(a) = g(tᴬ x) = (tᴮ ∘ F g)(x) = (tᴮ ∘ F h)(x) = h(tᴬ x) = h(a).

      ☐

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
         :label: hom

      Let :math:`a: ρ f → A` be such that :math:`g ∘ a = b`.  Then the left hand side of :eq:`hom` is :math:`f^ℂ (k ∘ g ∘ a) = f^ℂ (h ∘ a)`, which is equal to :math:`h (f^𝔸 (a))` since :math:`h` is a homomorphism.
   
      Therefore,
   
      .. math:: 
      
         f^ℂ (k ∘ b) &= f^ℂ (k ∘ g ∘ a) = f^ℂ (h ∘ a)\\ 
                 & = h (f^𝔸 (a)) = (k ∘ g)(f^𝔸 (a))\\
                 & = k (f^𝔹 (g ∘ a)) = k (f^𝔹 (b)),

      as desired, where the penultimate equality holds by virtue of the fact that :math:`g` is a homomorphism. ☐

-----------------------------------------

.. index:: ! subuniverse, ! subalgebra

Subalgebras
-----------

We now inductively define the **subuniverse generated by a set** and prove that this new definition is equivalent to the one we gave in :numref:`subalgebras` (cf. :cite:`Bergman:2012` Thm. 1.14).

.. _thm-1-14:

.. proof:theorem:: Subuniverse generation

   Let :math:`𝔸 = ⟨A, F^{𝔸}⟩`  be  an  algebra in the signature :math:`σ = (F, ρ)` and let :math:`X ⊆ A`.

   Define, by recursion on :math:`n`, the sets :math:`X_n` as follows:

   .. math:: X_0  &=  X \\
          X_{n+1} &=  X_n ∪ \{ f a ∣ f ∈ F, \ a ∈ X_n^{ρf}\}.
      :label: subalgebra-inductive

   Then  :math:`\Sg^𝔸(X) = ⋃ X_n`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let :math:`Y = ⋃_{n < ω} X_n`. Clearly :math:`X_n ⊆ Y ⊆ A`, for every :math:`n ∈ ℕ`. In particular :math:`X = X_0 ⊆ Y`.

      Let us show that :math:`Y` is a subuniverse of 𝔸.
   
      Let :math:`f` be a basic :math:`k`-ary operation and :math:`a ∈ Y^k`.
    
      From the construction of :math:`Y`, there is an :math:`n < ω` such that :math:`∀ i,\ a,\ i ∈ X_n`.
    
      From its definition, :math:`f a ∈ X_{n+1} ⊆ Y`.
    
      Thus :math:`Y` is a subuniverse of 𝔸 containing :math:`X`.
    
      By :eq:`SgDef`, :math:`\Sg^𝔸(X) ⊆ Y`.
    
      For the opposite inclusion, it is enough to check, by induction on :math:`n`, that :math:`X_n ⊆ \Sg^𝔸(X)`.
    
      By definition, :math:`X_0 = X ⊆ \Sg^𝔸(X)`.
      
      Assume :math:`X_n ⊆ \Sg^𝔸(X)`.  We show :math:`X_{n+1} ⊆ \Sg^𝔸(X)`.
      
      If :math:`b ∈ X_{n+1} - X_n`, then :math:`b = f a` for a basic :math:`k`-ary operation :math:`f` and some :math:`a ∈ X_n^k`.
      
      But :math:`∀ i, \ a i ∈ \Sg^𝔸(X)` and since this latter object is a subuniverse, :math:`b ∈ \Sg^𝔸(X)` as well.
    
      Therefore, :math:`X_{n+1} ⊆ \Sg^𝔸(X)`, as desired. ☐ 

The argument in the proof of :numref:`Theorem %s <thm-1-14>` is of a type that one encounters frequently throughout algebra. It has two parts.

  #. Some set :math:`Y` is shown to be a subuniverse of 𝔸 that contains :math:`X`.

  #. Every subuniverse containing :math:`X` is shown to contain :math:`Y` as well.

  #. One concludes that :math:`Y = \Sg^𝔸 (X)`.

-----------------------------------------------

.. index:: ! Taylor term, ! term

.. _terms:

Terms
-----

Fix a signature :math:`σ = (F, ρ)`, let :math:`X` be a set of **variables** and assume :math:`X ∩ F = ∅`.

Let :math:`F_0` denote the set of nullary operation symbols.

By a **word** on :math:`X ∪ F` we mean a nonempty, finite sequence of members of :math:`X ∪ F`, and we will denote the concatenation of such sequences by simple juxtaposition.

We *define* by induction on :math:`n` the set :math:`T_n` of words on :math:`X ∪ F` as follows:

.. math::      T_0 &= X ∪ F_0;\\
           T_{n+1} &= T_n ∪ \{ f\, s ∣ f ∈  F, \ s: ρf → T_n \},

and we *define* the collection of **terms of signature** σ **over** :math:`X` by :math:`T_σ(X) = ⋃_{n < ω}T_n`.

The definition of :math:`T_σ (X)` is recursive, indicating that

  *the terms of a given signature can be implemented (in Lean, for example) as an inductive type*.

We will confirm this in :numref:`Chapter %s <inductively-defined-types>`, but before doing so we impose an algebraic structure on :math:`T_σ (X)`, and then state and prove some basic but important facts about this algebra. These will be formalized in :numref:`Chapter %s <inductively-defined-types>`, giving us a chance to show off inductively defined types in Lean and to compare informal language proofs to their formal Lean counterparts.

If :math:`w` is a term, then the **height** of :math:`w` is denoted by :math:`|w|` and defined to be the least :math:`n` such that :math:`w ∈ T_n`. The height is a useful index for recursion and induction.

Notice that :math:`T_σ (X)` is nonempty iff either :math:`X` or :math:`F_0` is nonempty. As long as :math:`T_σ (X)` is nonempty, we can impose upon it an algebraic structure, as follows:

For every basic operation symbol :math:`f ∈ F` let :math:`f^{𝕋_σ (X)}` be the operation on :math:`T_σ (X)` that maps each tuple :math:`s: ρ f → T_σ (X)` to the formal term :math:`f\,s`.

We define :math:`𝕋_σ (X)` to be the algebra with universe :math:`T_σ (X)` and with basic operations :math:`\{f^{𝕋_σ (X)} | f ∈ F\}`. [4]_

Here are some important facts about this algebra.

.. _obs-six:

.. proof:observation::

   Let :math:`σ = (F, ρ)` be a signature.
 
   (a) :math:`𝕋_σ(X)` is generated by :math:`X`.
 
   (b) For every algebra :math:`𝔸 = ⟨A, F^𝔸⟩` of type :math:`σ` and every function :math:`g: X → A` there is a unique homomorphism :math:`h: 𝕋_σ(X) → 𝔸` such that :math:`h|_X = g`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*.
     
      The definition of :math:`𝕋_σ(X)` exactly parallels the construction in :numref:`Theorem %s <thm-1-14>`. That accounts for the first item.
     
      For b, define :math:`h\,t` by induction on the :term:`height` of :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ F_0`. If :math:`t ∈ X`, then define :math:`h\,t = g\,t`. If :math:`t ∈ F_0`, then let :math:`h\,t = t^𝔸`.
     
      For the inductive step, assume :math:`|t| = n + 1`. Then :math:`t = f\,s` for some :math:`f ∈ F` and :math:`s: ρ f → T_n`, where for each :math:`0 ≤ i< ρ f` the term :math:`s\, i` has height at most :math:`n`. We define :math:`h\,t = f^{𝔸}(h ∘ s) = f^{𝔸}(h\,s_1, \dots, h\,s_k)`.
     
      It is easy to see that, by its very definition, :math:`h` is a homomorphism that agrees with :math:`g` on :math:`X`.
      
      Finally, the uniqueness of :math:`h` follows from :numref:`Obs %s <obs-two>`. ☐

.. _obs-seven:

.. proof:observation::

   Let :math:`𝔸 = ⟨A, f^{𝔸}⟩` and :math:`𝔹 = ⟨B, f^{𝔹}⟩` be algebras of type :math:`ρ`.
 
    (a) For every :math:`n`-ary term :math:`t`, homomorphism :math:`g: 𝔸 → 𝔹`, and :math:`n`-tuple :math:`a: n → A`,
    
        .. math:: g(t^{𝔸} a) = t^{𝔹}(g ∘ a).

        where, recall, :math:`t^𝔸 a = t^𝔸 (a_0, a_1, \dots, a_{n-1})` and :math:`(g ∘ a)(i) = g(a_i)`.

    (b) For every term :math:`t ∈ T_ρ(X_ω)` and every :math:`θ ∈ \mathrm{Con}⟨A, fᴬ⟩`,
    
        .. math:: 𝔸 ≡_θ 𝔹 \quad ⟹ \quad t^𝔸(𝔸) ≡_θ t^𝔸(𝔹).

    (c) For every subset :math:`Y` of :math:`A`,

        .. math:: \Sg^{𝔸}(Y) = \{ t^𝔸 \, a ∣ t ∈ T_σ(X_n), a: ρ t → Y, n ∈ ℕ\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      The first statement is an easy induction on :math:`|t|`.
    
      The second statement follows from the first by taking :math:`⟨B, f^{𝔹}⟩ = ⟨A, f^{𝔸}⟩/θ` and :math:`g` the canonical homomorphism.
    
      For the third statement, again by induction on the height of :math:`t`, every subalgebra must be closed under the action of :math:`t^{𝔸}`.
    
      Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows. ☐

.. todo:: complete this section (include material on free algebras)

-----------------------------------------------

.. index:: ! clone
.. index:: ! clone of projections
.. index:: ! clone of polynomial operations
.. index:: ! clone of term operations

.. _clones:

Clones
------

An **operational clone** (or just **clone**) on a nonempty set :math:`A` is a set of operations on :math:`A` that contains the projection operations and is closed under general composition.

Let :math:`𝖢 A` denote the collection of all clones on :math:`A`.

The smallest clone on :math:`A` is the **clone of projections**, which we denote and define as follows:

.. math:: \mathrm{Proj} A = ⋃_{i < n < ω}  \{π^n_i : ∀ a ∈ A^n,\ π^n_i(a) = a(i)\}.

Let us set down some conventions that will help simplify notation.  Recall, the natural number :math:`k< ω` may be constructed as (or at least identified with) the set :math:`\{0,1,\dots, k-1\}`, and this will be helpful here.

For each :math:`k< ω`, denote and define the tuple :math:`\pi^k: k → ((k → A) → A)` of all :math:`k`-ary projections on :math:`A` as follows: for each :math:`0≤ i < k`,  :math:`π^k(i)` is the :math:`i`-th :math:`k`-ary projection operation that takes each :math:`k`-tuple :math:`a: k → A` to its entry at index :math:`i`:

.. math:: π^k (i) a = a(i).

Observe that if :math:`f: (k → A) → A` is a :math:`k`-ary operation on :math:`A`, then 

The **clone of term operations** of a σ-algebra 𝔸 is the smallest clone on :math:`A` containing the basic operations of 𝔸; this is
denoted and defined by

.. math:: \mathrm{Clo}(F^𝔸) = ⋂ \{ U ∈ 𝖢 A ∣ F^𝔸 ⊆ U\}.

The set of :math:`n`-ary members of :math:`\operatorname{Clo}(F^𝔸)` is sometimes denoted by :math:`\operatorname{Clo}_n (F^𝔸)` (despite the fact that the latter is clearly not a clone).

The **clone of polynomial operations** (or **polynomial clone**) of a σ-algebra 𝔸 is denoted by :math:`\operatorname{Pol}(F^𝔸)` and is defined to be the clone generated by the collection consisting of the basic operations (i.e., :math:`F^𝔸`) of 𝔸 along with the **constants** on :math:`A`. [2]_

The set of :math:`n`-ary members of :math:`\operatorname{Pol}(F^𝔸)` is sometimes denoted by :math:`\operatorname{Pol}_n (F^𝔸)`. 

.. .. [9] Lean's built-in sigma type is defined as follows: :math:`structure sigma {α : Type u} (β : α → Type v) := mk :: (fst : α) (snd : β fst)`

The clone :math:`\mathrm{Clo}(F^𝔸)` is associated with the algebra :math:`𝔸` only insofar as the former is constructed out of the basic operations of 𝔸 and the set :math:`A` on which those operations are defined.  However, all that is required when defining a clone is a set :math:`A` and some collection :math:`F` of operations defined on :math:`A`; from only these ingredients, we can construct the clone generated by :math:`F`, which we denote by :math:`\mathrm{Clo}(F)`.

Thus *the clone of terms operations can be implemented (e.g., in Lean) as an inductive type*. The following theorem makes this precise (cf. Theorem 4.32 of :cite:`Bergman:2012`). 

.. We seek a "bottom-up," inductive description of the members of :math:`\mathrm{Clo}(F)`.  By thinking of the clone itself as a kind of algebra, a description analogous to :numref:`Obs %s <thm-1-14>` ought to be possible.  In fact, since function composition is associative, a slightly slicker formulation is available.

..  Theorem  4.3. of Bergman [1].

.. _obs-five:

.. proof:observation::

   Let :math:`A` be a set and let :math:`F ⊆ ⋃_{n<ω} A^{A^n}` be a collection of operations on :math:`A`.
   
   Let :math:`ρ: F → ω` denote the arity function (i.e., :math:`ρ f` is the arity of :math:`f ∈ F`).
 
   Define :math:`F_0 := \mathrm{Proj}(A)` (the set of projections on :math:`A`) and for all :math:`0 ≤ n < ω` let
 
   .. math:: F_{n+1} := F_n ∪ \{ f g \mid f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.
 
   Then :math:`\mathrm{Clo}(F) = ⋃_n F_n`.
 
   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Let :math:`F̄ = ⋃_n F_n`. It is easy to argue by induction that every :math:`F_n` is a subset of :math:`\mathrm{Clo}(F)`. Thus, :math:`F ⊆ \mathrm{Clo}(F)`.
    
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


.. .. _thm-4-3:

.. .. proof:theorem::

..    Let :math:`X` be a set and :math:`σ = (F, ρ)` a signature. Define

..    .. math:: F_0 &= X;\\
..          F_{n+1} &= F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρ g → X)) \}, \quad n < ω.

..    Then :math:`\mathrm{Clo}^X(F) = ⋃_n F_n`.

.. _thm-4-32:

.. proof:theorem::

   Let 𝔸 and 𝔹 be algebras of signature :math:`σ`.

   #. If :math:`t ∈ T (X_ω)` and :math:`g : 𝔸 → 𝔹` is a homomorphism, then
      
      .. math:: g\, t^{𝔸}(a) = t^{𝔹}(g ∘ a), \quad  ∀ a : ρ t → A

   #. If :math:`t ∈ T (X_ω)`, :math:`θ ∈ \operatorname{Con}(𝔸)`, :math:`a : ρ t → A` and :math:`b : ρ t → A`, then
   
      .. math:: a \mathrel{θ} b \implies t^𝔸(a) \mathrel{θ} t^𝔸(b).

   #. If :math:`Y ⊆ A`, then

      .. math:: \operatorname{Sg}^𝔸(Y) = \{ t^𝔸 (a) : t ∈ T(X_n), a : ρ t → Y, i ≤ n < ω\}.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      The first statement is an easy induction on :math:`|t|`.

      The second statement follows from the first by taking :math:`𝔹 = 𝔸/θ` and 𝗀 the canonical homomorphism.
  
      For the third statement, again by induction on the height of :math:`t`, every subalgebra must be closed under the action of :math:`t^{𝔸}`. 
  
      Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows. ☐

.. For a nonempty set :math:`A`, we let :math:`𝖮_A` denote the set of all finitary operations on :math:`A`. That is, :math:`𝖮_A = ⋃_{n∈ ℕ} A^{A^n}` on :math:`A` is a subset of :math:`𝖮_A` that contains all projection operations and is closed under the (partial) operation of :ref:`general composition <general-composition>`.

.. If :math:`𝔸 = ⟨ A, F^𝔸 ⟩` denotes the algebra with universe :math:`A` and set of basic operations :math:`F`, then :math:`\operatorname{Clo} (𝔸)` denotes the clone generated by :math:`F`, which is also known as the **clone of term operations** of :math:`𝔸`.

.. proof:example::

   We will discuss varieties in more detail later, but for now a variety is a collection of algebras of the same signature that is defined by a certain set of identities. [3]_ 
   
   In 1977, Walter Taylor showed in :cite:`Taylor:1977` that a variety :math:`𝕍` satisfies some nontrivial idempotent Malcev condition if and only if it satisfies one of the following form: for some :math:`n`, 𝕍 has an idempotent :math:`n`-ary term  :math:`t` such that for each :math:`i < n` there is an identity of the form 

   .. math:: t(∗, \cdots, ∗, x, ∗, \cdots, ∗) ≈ t(∗, \cdots, ∗, y, ∗, \cdots, ∗)

   true in 𝕍 where distinct variables :math:`x` and :math:`y` appear in the :math:`i`-th position on each side of the identity. Such a term :math:`t` now goes by the name **Taylor term**.


------------------------

.. rubric:: Footnotes

.. [2]
   By "the constants on :math:`A`" we mean the **constant operations**; i.e., functions :math:`f: A → A` such that :math:`∀ a ∈ A, f(a) = c`, for some :math:`c ∈ A`.

.. [3]
   We will also have much to say about Malcev conditions, but for now we ask the reader to trust us when we say that such conditions play an important role in many deep results in universal algebra.

.. [4]
   The construction of :math:`𝕋_ρ (X)` may seem to be making something out of nothing, but it plays a crucial role in the theory.

.. include:: hyperlink_references.rst
