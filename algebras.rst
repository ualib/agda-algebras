.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

=========
Algebras
=========

.. _motivation:

Motivation
----------

Our vision for the `lean-ualib`_ (Lean Universal Algebra Library) originated with our observation that, on the one hand, a number of the most basic and important constructs in universal algebra can be defined recursively, while on the other hand, :term:`type theory` in general, and :term:`dependent <dependent type>` and :term:`inductive types <inductive type>` in particular, facilitates elegant representations of recursively defined objects. Such objects can therefore be implemented in a :term:`proof assistant` such as `Lean`_, a language that not only supports :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`, but also provides powerful :term:`tactics <proof tactic>` for proving properties of objects that inhabit these types.

These observations suggest that there is much to gain from implementing universal algebra in a proof assistant that offers powerful tools for working with :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`. Lean is one such proof assistant.

The goal of the `Lean Universal Algebra Library`_, and this documentation explaining it, is to demonstrate that our vision manifests in a careful (and, whenever possible, :term:`constructive`) presentation of the elementary theory of universal algebra in the language of type theory, along with a formal implementation of this theory in the Lean proof assistant.  Specific examples of this manifestation appear below in :numref:`subalgebras-in-lean`, :numref:`terms-in-lean`, and :numref:`clones-in-lean`.

.. In particular, our Lean_ implementation of the notion of :term:`subuniverse` illustrates one of these underlying themes motivating our work.

Specifically, we present fundamental definitions and theorems about :term:`subalgebras <subalgebra>`, terms, and clones---first in this chapter using the informal language of universal algebra, and then in the next chapter using the formal language of Lean.

The idea is to demonstrate the power and utility of implementing the theory in a formal language that supports :term:`dependent <dependent type>` and :term:`inductive types <inductive type>`, which are essential for expressing and working with infinite objects in a :term:`constructive` and :term:`computable` way, and for proving (by induction) properties of these objects.

-----------------------------------------

.. index:: operation, arity, image
.. index:: ℕ

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

.. index:: pair: algebra; algebraic structure
.. index:: ! σ-algebra 

.. _algebraic-structures:

Algebraic structures
----------------------

An **algebraic structure** in the signature :math:`σ = (F, ρ)` (or, :math:`σ`-**algebra**) is denoted by :math:`𝔸 = ⟨A, F^𝔸⟩` and consists of 

  #. :math:`A` := a set, called the *carrier* (or *universe*) of the algebra,
  #. :math:`F^𝔸 = \{ f^𝔸 ∣ f ∈ F, \ f^𝔸 : (ρ f → A) → A \}` := a set of operations on :math:`A`, and
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝔸`.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`Adamek:2011`, :cite:`Behrisch:2012`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`Meinke:1992`). These are natural generalizations that we will incorporate in our development later. (See :numref:`Chapter %s <postmodern-algebra>`.) But our first goal is to develop a working library for classical (single-sorted, set-based) universal algebra. 

**Formalization**. Our formal implementation (in `Lean`_) of the concept of algebraic structure is described in :numref:`the-algebra-type`, and is included in the `basic.lean`_ file of the `lean-ualib`_ library.

---------------------------

.. index:: ! subuniverse, ! subalgebra
.. index:: 𝖲(𝔸)
.. index:: 𝖲𝗀

.. _subuniverses:

Subuniverses
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


**Formalization**. Our formal implementation (in `Lean`_) of the concept of subalgebra is described in :numref:`Sections %s <subalgebras-in-lean>` and :numref:`%s <subuniverses-in-lean>`, and is included in the `subuniverse.lean`_ file of the `lean-ualib`_ library.

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

.. _homomorphisms:

Homomorphisms
-------------

Let :math:`𝔸 = ⟨ A, F^𝔸 ⟩` and :math:`𝔹 = ⟨ B, F^𝔹 ⟩` be algebras of the same signature, and let :math:`φ : A → B` be a function. Take an :math:`n`-ary operation symbol :math:`f ∈ F`, and suppose that for all :math:`a_1, \dots a_{n} ∈ A` the following equation holds:

.. math:: φ (f^𝔸 (a_1, \dots, a_{n})) = f^𝔹 (φ (a_1), \dots, φ (a_{n})).

Then :math:`φ` is said to **respect the interpretation of** :math:`f`. If :math:`φ` respects the interpretation of every :math:`f ∈ F`, then we call :math:`φ` a **homomorphism** from 𝔸 to 𝔹, and we write :math:`φ \in \operatorname{Hom}(𝔸, 𝔹)`, or simply, :math:`φ : 𝔸 → 𝔹`.

**Formalization**. Our formal implementation (in `Lean`_) of the concept of homomorphism is described in :numref:`Sections %s <subalgebras-in-lean>` and :numref:`%s <basic-facts-in-lean>`, and is included in the `subuniverse.lean`_ file of the `lean-ualib`_ library.

.. .. proof:observation::
..  For groups, to check that a map :math:`φ : G → H` is a homomorphism, it is enough to check that :math:`φ` respects the interpretation of the binary operation. It follows from this that such a function respects the unary and nulary operations as well.

---------------------------------

.. index:: ! epimorphism, ! monomorphism, ! automorphism

Epi, Mono, Auto
-----------------------

.. todo:: complete this section

.. proof:notation:: homo-, epi-, mono-, automorphism

   We adopt the following notation. If :math:`𝔸` and :math:`𝔹` are algebras in the same signature, then

   + :math:`\hom(𝔸, 𝔹) =` the set of homomorphisms from 𝔸 to 𝔹.
   + :math:`\epi(𝔸, 𝔹) =` the set of epimorphisms from 𝔸 onto 𝔹.
   + :math:`\mono(𝔸, 𝔹) =` the set of monomorphisms from 𝔸 into 𝔹.
   + :math:`\aut(𝔸, 𝔹) =` the set of automorphisms from 𝔸 into and onto 𝔹.

**Formalization**. Our formal implementation (in `Lean`_) of these concepts is described in :numref:`factoring-homomorphisms`, and is included in the `birkhoff.lean`_ file of the `lean-ualib`_ library.

----------------------

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

------------------------------

.. index:: ! Taylor term, ! term, ! term algebra, ! σ-term 

.. _terms:

Terms
-----

Fix a signature :math:`σ = (F, ρ)`, let :math:`X` be a set of **variables** and assume :math:`X ∩ F = ∅`.

By a **word** on :math:`X ∪ F` we mean a nonempty, finite sequence of members of :math:`X ∪ F`, and we will denote the concatenation of such sequences by simple juxtaposition.

Let :math:`F_0` denote the set of nullary operation symbols. We define by induction on :math:`n` the sets :math:`T_n` of **terms on** :math:`X ∪ F` as follows:

.. math::      T_0 &= X ∪ F_0;\\
           T_{n+1} &= T_n ∪ \{ f\, s ∣ f ∈  F, \ s: ρf → T_n \},

and we define the collection of **terms of signature** :math:`σ` **over** :math:`X` by :math:`T_σ(X) = ⋃_{n < ω}T_n`.

By a :math:`σ`-**term** we mean a term in the signature :math:`σ`. 

The definition of :math:`T_σ (X)` is recursive, indicating that

  *terms can be implemented as an inductive type*

(in Lean, for example). We confirm this in :numref:`Chapter %s <inductively-defined-types>` below.

Before doing so, let us impose an algebraic structure on :math:`T_σ (X)`, and then state and prove some basic facts about this important algebra. These will be formalized in :numref:`Chapter %s <inductively-defined-types>`, giving us a chance to show off inductively defined types in Lean.

If :math:`t` is a term, then the **height** of :math:`t` is denoted by :math:`|t|` and defined to be the least :math:`n` such that :math:`t ∈ T_n`. The height of is a useful index for recursion and induction.

.. Let :math:`ρ: T_σ(X) → ℕ` denote the **arity function for term**, defined as follows:
.. .. math:: ρ t = \min \{n ∣t ∈ T_n,\; 0≤ n < ω\}.

Notice that :math:`T_σ (X)` is nonempty iff :math:`X ∪ F_0` is nonempty.

If :math:`T_σ (X)` is nonempty, then we can impose upon it an algebraic structure, which we denote by :math:`𝕋_σ (X)` (or :math:`𝕋` when :math:`σ` and :math:`X` are clear from context).

We call :math:`𝕋_σ (X)` the **term algebra in the signature** :math:`σ` **over** :math:`X` (or, the :math:`σ`-**term algebra over** :math:`X`); it is constructed as follows:

  For every basic operation symbol :math:`f ∈ F` let :math:`f^𝕋` be the operation on :math:`T_σ (X)` that maps each tuple :math:`s: ρ f → T_σ (X)` to the formal term :math:`f\,s`; define :math:`𝕋_σ(X)` to be the algebra with universe :math:`T_σ (X)` and basic operations :math:`\{f^𝕋 | f ∈ F\}`. [4]_

Let us now prove a couple of easy but important consequences of these definitions.

.. about the :math:`σ`-term algebra over :math:`X`.

.. _obs-six:

.. proof:observation::

   #. :math:`𝕋 := 𝕋_σ(X)` is generated by :math:`X`.
 
   #. For every :math:`\sigma`-algebra :math:`𝔸 = ⟨A, F^𝔸⟩` and function :math:`g: X → A` there is a unique homomorphism :math:`h: 𝕋 → 𝔸` such that :math:`h|_X = g`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*.
     
      The definition of :math:`𝕋` exactly parallels the construction in :numref:`Theorem %s <thm-1-14>`. That accounts for the first assertion.
     
      For the second assertion, define :math:`h\,t` by induction on the :term:`height` of :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ F_0`.
      
      If :math:`t ∈ X`, then define :math:`h\,t = g\,t`. If :math:`t ∈ F_0`, then let :math:`h\,t = t^𝔸`.
     
      For the inductive step, assume :math:`|t| = n + 1`. Then :math:`t = f\,s` for some :math:`f ∈ F` and :math:`s: ρ f → T_n`, where for each :math:`0 ≤ i< ρ f` the term :math:`s\, i` has height at most :math:`n`. We define :math:`h\,t = f^𝔸(h ∘ s) = f^𝔸(h\,s_1, \dots, h\,s_k)`.
     
      By its very definition, :math:`h` is a homomorphism that agrees with :math:`g` on :math:`X`. The uniqueness of :math:`h` follows from :numref:`Obs %s <obs-two>`. ☐

.. index:: interpretation (of a term), ! arity (of a term)

Interpretation of a term
~~~~~~~~~~~~~~~~~~~~~~~~

..  and let :math:`T_n := T_σ(X_n)` be the subalgebra of :math:`T_σ(X_ω)` generated by :math:`X_n`.  Then, :math:`T_0 ⊆  T_1 ⊆ T_2 ⊆ \cdots` and :math:`T_σ(X_ω) = ⋃_{n<ω}  T_n`.

We denote and define the set :math:`X := \{x_0,x_1,\dots \}` of variable symbols, and for each natural number :math:`n` we let :math:`X_n:=\{x_0,x_1,\dots, x_{n-1}\}`.

Let :math:`σ = (F, ρ)` be a signature, :math:`𝔸` a :math:`σ`-algebra, and :math:`𝕋` the :math:`σ`-term algebra over :math:`X`; that is, 

.. math:: 𝔸 := ⟨A, F^𝔸⟩ \quad \text{ and } \quad 𝕋 := ⟨T_σ(X), F^𝕋⟩. 

Each operation symbol :math:`f ∈ F` gives rise to

#.  a :math:`ρ f`-ary operation on :math:`T_σ(X)`, denoted by :math:`f^𝕋`, which maps each :math:`ρ f`-tuple :math:`s: ρ f → T_σ(X)` to the formal term :math:`f \,s` in :math:`T_σ(X)`, and

#.  a :math:`ρ f`-ary operation on :math:`A`, denoted by :math:`f^𝔸`, which maps each :math:`ρ f`-tuple :math:`a: ρ f → A` to the element :math:`f^𝔸 \,a` in :math:`A`. The operation :math:`f^𝔸` is called the **interpretation of** :math:`f` **in the algebra** :math:`𝔸`.  

In the present section we explain how to define the interpretation of a :math:`σ`-term in a :math:`σ`-algebra.

As usual, for each :math:`0<n<ω` we identify the :math:`n`-tuple :math:`(x_0, x_1, \dots, x_{n-1})` with the function :math:`x: n → X_n` defined by :math:`x\, i = x_i` :math:`(0≤i<n)`.

Recall, a term :math:`t` is either a variable, say, :math:`t = x`, or has the form :math:`t = f \,s` for some operation symbol :math:`f ∈ F`, and some :math:`ρ f`-tuple :math:`s: ρ f → T_σ (X)` of terms.

.. and suppose :math:`|t| = n`.
..  : (n → X_n) → T_n` be an :math:`n`-ary term. 

Let :math:`t ∈ T_σ(X)` be a term. Define the **operation** :math:`t^𝔸` **on** :math:`A` by recursion on the :term:`height` :math:`|t|` of :math:`t` as follows: for each tuple :math:`a: X → A` of :math:`A`, 

#. (:math:`|t| = 0`) if :math:`t` is the variable :math:`x_i ∈ X`, then :math:`t^𝔸 \, a = π^X_i\, a = a\, i`,
#. (:math:`|t| = n+1`) if :math:`t = f\, s` where :math:`f ∈ F` is an operation symbol and :math:`s: ρ f → T_n` is a tuple of terms whose heights are at most :math:`n` (i.e., :math:`∀ i < ρf, |s\, i| ≤ n`), then :math:`t^𝔸 = f^𝔸 \, s^𝔸`.
 
.. .. Let :math:`X_ω := \{x_0, x_1, \dots\}` be a collection of variables and define :math:`X_n:=\{x_0, x_1, \dots, x_{n-1}\}`.

In the next observation, assume :math:`𝔸 = ⟨A, F^𝔸⟩` and :math:`𝔹 = ⟨B, F^𝔹⟩` are algebras in the same signature :math:`σ = (F, ρ)`, and let :math:`t ∈ T_σ (X)` be an :math:`n`-ary term.

In particular, as we just explained, :math:`t` has an interpretation in :math:`𝔸`, denoted by :math:`t^𝔸 a = t^𝔸 (a\, 0, a\, 1, \dots, a\, (n-1))`, where :math:`a: n → A`, as well as an interpretation :math:`t^𝔹: (n → B) → B` in :math:`𝔹`.
    
.. _thm-4-32:

.. _obs-seven:

.. proof:observation:: homomorphisms commute with terms

   #. :math:`g: 𝔸 → 𝔹` is a homomorphism, then :math:`g ∘ a: n → B` is the :math:`n`-tuple whose :math:`i`-th component is :math:`(g ∘ a)\, i = g(a\, i)`, and
  
      .. math:: g(t^𝔸 a) = t^𝔹(g ∘ a).

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      This is an easy induction on :math:`|t|`. ☐
    
.. _obs-eight:

.. proof:observation:: terms respect congruences

   If :math:`θ` is a congruence of :math:`𝔸` and :math:`a, a': n → A` are :math:`n`-tuples over :math:`A`, then
    
   .. math:: (a, a') ∈ θ \; ⟹  \; (t^𝔸\,a, t^𝔸\,a') ∈ θ.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      This follows from :numref:`Obs %s <obs-seven>` by taking :math:`⟨B, F^𝔹⟩ = ⟨A, F^𝔸⟩/θ = ⟨A/θ, F^{𝔸/θ}⟩` and :math:`g=` the canonical homomorphism. ☐
    
.. _obs-nine:

.. proof:observation:: subuniverse generation as image of terms

   If :math:`Y` is a subset of :math:`A`, then

      .. math:: \Sg^{𝔸}(Y) = \{ t^𝔸 \, a ∣ t ∈ T_σ(X_n), \, n ∈ ℕ, \; a: ρ t → Y\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      A straightforward induction on the height of :math:`t` shows that every subuniverse is closed under the action of :math:`t^𝔸`. Thus the right-hand side is contained in the left. On the other hand, the right-hand side is a subuniverse that contains the elements of :math:`Y` (take :math:`t = x_1`), so it contains :math:`\Sg^{𝔸}(Y)` as the latter is the smallest subuniverse containing :math:`Y`. ☐

**Formalization**. Our formal implementation (in `Lean`_) of the concepts and results of this section is described in :numref:`terms-in-lean`, and is included in the `free.lean`_, `term.lean`_, and `birkhoff.lean`_ files of the `lean-ualib`_ library.

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

.. math:: \Proj  A = ⋃_{i < n < ω}  \{π^n_i : ∀ a ∈ A^n,\ π^n_i\, a = a(i)\}.

Let us set down some conventions that will help simplify notation.  Recall, the natural number :math:`k< ω` may be constructed as (or at least identified with) the set :math:`\{0,1,\dots, k-1\}`, and this will be helpful here.

For each :math:`k< ω`, denote and define the tuple :math:`\pi^k: k → ((k → A) → A)` of all :math:`k`-ary projections on :math:`A` as follows: for each :math:`0≤ i < k`,  :math:`π^k(i)` is the :math:`i`-th :math:`k`-ary projection operation that takes each :math:`k`-tuple :math:`a: k → A` to its entry at index :math:`i`:

.. math:: π^k (i) a = a(i).

Observe that if :math:`f: (k → A) → A` is a :math:`k`-ary operation on :math:`A`, then 

The **clone of term operations** of a σ-algebra 𝔸 is the smallest clone on :math:`A` containing the basic operations of 𝔸; this is
denoted and defined by

.. math:: \Clo (F^𝔸) = ⋂ \{ U ∈ 𝖢 A ∣ F^𝔸 ⊆ U\}.

The set of :math:`n`-ary members of :math:`\Clo (F^𝔸)` is sometimes denoted by :math:`\Clo _n (F^𝔸)` (despite the fact that the latter is clearly not a clone).

The **clone of polynomial operations** (or **polynomial clone**) of a σ-algebra 𝔸 is denoted by :math:`\Pol (F^𝔸)` and is defined to be the clone generated by the collection consisting of the basic operations (i.e., :math:`F^𝔸`) of 𝔸 along with the **constants** on :math:`A`. [3]_

The set of :math:`n`-ary members of :math:`\Pol (F^𝔸)` is sometimes denoted by :math:`\Pol _n (F^𝔸)`. 

.. .. [9] Lean's built-in sigma type is defined as follows: :math:`structure sigma {α : Type u} (β : α → Type v) := mk :: (fst : α) (snd : β fst)`

The clone :math:`\Clo (F^𝔸)` is associated with the algebra :math:`𝔸` only insofar as the former is constructed out of the basic operations of 𝔸 and the set :math:`A` on which those operations are defined.  However, all that is required when defining a clone is a set :math:`A` and some collection :math:`F` of operations defined on :math:`A`; from only these ingredients, we can construct the clone generated by :math:`F`, which we denote by :math:`\Clo (F)`.

Thus

  *the clone of terms operations can be implemented (e.g., in Lean) as an inductive type*.
  
The following theorem makes this more precise (cf. Theorem 4.32 of :cite:`Bergman:2012`). (See also :numref:`Chapter %s <inductively-defined-types>`, where we formalize this in Lean.)

.. We seek a "bottom-up," inductive description of the members of :math:`\Clo (F)`.  By thinking of the clone itself as a kind of algebra, a description analogous to :numref:`Obs %s <thm-1-14>` ought to be possible.  In fact, since function composition is associative, a slightly slicker formulation is available.

..  Theorem  4.3. of Bergman [1].

.. _obs-five:

.. proof:observation::

   Let :math:`A` be a set and let :math:`F ⊆ \Op (A):= ⋃_{n<ω} A^{A^n}` be a collection of operations on :math:`A`.
   
   Define :math:`F_0 := \Proj (A)` (the set of projections on :math:`A`) and for all :math:`0 ≤ n < ω` let
 
   .. math:: F_{n+1} := F_n ∪ \{ f g \mid f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.
 
   Then :math:`\Clo (F) = ⋃_n F_n`.
 
   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Let :math:`F̄ = ⋃_n F_n`. It is easy to argue by induction that every :math:`F_n` is a subset of :math:`\Clo (F)`. Thus, :math:`F ⊆ \Clo (F)`.
    
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

**Formalization**. Our formal implementation (in `Lean`_) of the concepts and results of this section is described in :numref:`clones-in-lean`, and is included in the `clone.lean`_ and `birkhoff.lean`_ files of the `lean-ualib`_ library.

------------------------

Special terms
-------------
.. .. _thm-4-3:

.. .. proof:theorem::

..    Let :math:`X` be a set and :math:`σ = (F, ρ)` a signature. Define

..    .. math:: F_0 &= X;\\
..          F_{n+1} &= F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρ g → X)) \}, \quad n < ω.

..    Then :math:`\Clo ^X(F) = ⋃_n F_n`.


.. For a nonempty set :math:`A`, we let :math:`𝖮_A` denote the set of all finitary operations on :math:`A`. That is, :math:`𝖮_A = ⋃_{n∈ ℕ} A^{A^n}` on :math:`A` is a subset of :math:`𝖮_A` that contains all projection operations and is closed under the (partial) operation of :ref:`general composition <general-composition>`.

.. If :math:`𝔸 = ⟨ A, F^𝔸 ⟩` denotes the algebra with universe :math:`A` and set of basic operations :math:`F`, then :math:`\Clo  (𝔸)` denotes the clone generated by :math:`F`, which is also known as the **clone of term operations** of :math:`𝔸`.

.. proof:example::

   We will discuss varieties in more detail later, but for now a variety is a collection of algebras of the same signature that is defined by a certain set of identities. [5]_ 
   
   In 1977, Walter Taylor showed in :cite:`Taylor:1977` that a variety :math:`𝕍` satisfies some nontrivial idempotent Malcev condition if and only if it satisfies one of the following form: for some :math:`n`, 𝕍 has an idempotent :math:`n`-ary term  :math:`t` such that for each :math:`i < n` there is an identity of the form 

   .. math:: t(∗, \cdots, ∗, x, ∗, \cdots, ∗) ≈ t(∗, \cdots, ∗, y, ∗, \cdots, ∗)

   true in 𝕍 where distinct variables :math:`x` and :math:`y` appear in the :math:`i`-th position on each side of the identity. Such a term :math:`t` now goes by the name **Taylor term**.

------------------------

.. rubric:: Footnotes

.. [1]
   For a brief and gentle introduction to type theory see the `section on axiomatic foundations <https://leanprover.github.io/logic_and_proof/axiomatic_foundations.html?highlight=type#type-theory>`_ in `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_.  Alternatively, viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. [3]
   By "the constants on :math:`A`" we mean the **constant operations**; i.e., functions :math:`f: A → A` such that :math:`∀ a ∈ A, f(a) = c`, for some :math:`c ∈ A`.

.. [4]
   The construction of :math:`𝕋_ρ (X)` may seem to be making something out of nothing, but it plays an significant role in the theory.

.. [5]
   We will also have much to say about Malcev conditions, but for now we ask the reader to trust us when we say that such conditions play an important role in many deep results in universal algebra.


.. include:: hyperlink_references.rst
