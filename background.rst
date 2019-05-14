.. .. math:: \newcommand\hom{\operatorname{Hom}} 

.. math:: \newcommand{\Sg}{\mathsf{Sg}} \newcommand\hom{\operatorname{Hom}} \newcommand\epi{\operatorname{Epi}} \newcommand\aut{\operatorname{Aut}} \newcommand\mono{\operatorname{Mono}} \newcommand\Af{\ensuremath{\langle A, f \rangle}} 

.. role:: cat

.. role:: code

.. _background:

==========
Background
==========

Modern algebra
--------------

Notation
~~~~~~~~

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m : ℕ` and say ":math:`m` has type ℕ." [1]_


For :math:`m : ℕ`, we denote and define :math:`\underline m := \{0, 1, \dots, m-1\}`.

Let :math:`a = (a_0, a_1, \dots, a_{m-1})` be an :ref:`mtuple <tuple-functors>` of elements from :math:`A`.

As explained in :numref:`Section %s <general-composition>`, the tuple :math:`a` may be identified with a function of type :math:`\underline m → A`, where :math:`a(i) = a_i`, for each :math:`i < m`.

If :math:`h  : A → A`, then :math:`h ∘ a : \underline m → A` is the function whose i-th coordinate is

.. math:: (h ∘ a)(i) = h(a(i)) = h(a_i), 

and we may formally identify the function :math:`h ∘ a : \underline m → A` with its "image tuple." We denote and define the *image of* :math:`\underline m` *under* :math:`h ∘ a` by

.. math:: (h ∘ a)[\underline m] := (h(a_0), h(a_1), \dots, h(a_{m-1})).

.. index:: signature, arity

Signatures, classically
~~~~~~~~~~~~~~~~~~~~~~~

Classically, a **signature** :math:`σ = (F, ρ)` consists of a set :math:`F` of operation symbols and a function :math:`ρ : F → ℕ`.

For each operation symbol :math:`f ∈ F`, the value :math:`ρf` is the **arity** of :math:`f`. (Intuitively, the arity is the "number of arguments" required to form a single input to the operation.)

If :math:`A` is a set and :math:`f` is a :math:`ρf`-ary function on :math:`A`, then we often write :math:`f : A^{ρf} → A` to indicate this.

On the other hand, the arguments of such a function form a :math:`ρf`-tuple, :math:`(a_0, a_1, \dots, a_{ρf -1})`, which may be viewed as the graph of the function :math:`a : ρf → A`, where :math:`a(i) = a_i`.

Thus, by identifying the :math:`ρf`-th power :math:`A^{ρf}` with the type :math:`ρf → A` of functions from :math:`\{0, 1, \dots, ρf -1\}` to :math:`A`, we identify the function type :math:`A^{ρf} → A` with the (functional) type :math:`(ρf → A) → A`. [2]_

Example
~~~~~~~

The following special cases come up often.

  #. If :math:`g : (\underline m → A) → A` is an :math:`\underline m`-ary operation on :math:`A`, and :math:`a : \underline m → A`, then :math:`g a = g(a_0, a_1, \dots, a_{m-1})` has type :math:`A`.

  #. If :math:`f : (ρf → B) → B` is a :math:`ρf`-ary operation on :math:`B`, and :math:`a : ρf → A` is a :math:`ρf`-tuple on :math:`A`, and :math:`h : A → B`, then :math:`h ∘ a` has type :math:`ρf → B` and :math:`f (h ∘ a)` has type :math:`B`.

It is important to be familiar with the classical notions of signature and arity, since these are used by almost all algebraists. (In :numref:`Section %s <f-algebra>`, we give alternative, category theoretic definitions of these things that are sometimes easier to compute with.)

.. index:: pair: algebra; algebraic structure

Algebraic structures
~~~~~~~~~~~~~~~~~~~~

An **algebraic structure** is denoted by :math:`𝐀 = ⟨ A, F^𝐀⟩` and consists of 

  #. :math:`A` := a set, called the *carrier* (or *universe*) of the algebra,
  #. :math:`F^𝐀 = \{ f^𝐀 ∣ f ∈ F, \ f^𝐀 : (ρf → A) → A \}` := a set of operations on :math:`A`,
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝐀`.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`MR2757312`, :cite:`MR3003214`, :cite:`finster:2018`, :cite:`gepner:2018`, :cite:`MR1173632`). These are natural generalizations that we will incorporate in our development later, once we have a working implementation of the classical (single-sorted, set-based) core of universal algebra. (See :numref:`Section %s <category-theoretic-approach>`.)

Notation for homs, epis, monos, and autos
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If :math:`𝐀 = ⟨A, f^𝐀⟩` and :math:`𝐁 = ⟨B, f^𝐁⟩` are algebras, we denote and define

+ :math:`\hom(𝐀, 𝐁) =` homomorphisms from 𝐀 to 𝐁.
+ :math:`\epi(𝐀, 𝐁) =` epimorphisms from 𝐀 onto 𝐁.
+ :math:`\mono(𝐀, 𝐁) =` monomorphisms from 𝐀 into 𝐁.
+ :math:`\aut(𝐀, 𝐁) =` automorphisms from 𝐀 into and onto 𝐁.

-----------------------------------------------------------------

.. _basic-facts:

Basic facts, classically
------------------------

Throught this section,

+ :math:`𝐀 = ⟨A, F^𝐀⟩, \ 𝐁 = ⟨B, F^𝐁⟩, \ 𝐂 = ⟨C, F^𝐂⟩\ ` are algebras of the same signature :math:`σ = (F, ρ)`, and

+ :math:`g, h : \hom(𝐀, 𝐁)` are homomorphism from 𝐀 to 𝐁;

.. index:: ! equalizer

The **equalizer** of :math:`g` and :math:`h` is the set

.. math:: 𝖤(g,h) = \{ a : A ∣ g(a) = h(a) \}.

Here is a numbered list of basic facts that we need later. We will reference the first fact in the list as :ref:`Fact 1 <fact-one>`, etc.

**Facts**.

.. _fact-one:

#. :math:`𝖤(g,h)` is a subuniverse of 𝐀.

   .. container:: toggle
 
      .. container:: header
 
         *Proof.*

      Fix arbitrary :math:`f ∈ F` and :math:`a : ρf → 𝖤(g,h)`.

      We show that :math:`g (f^𝐀 ∘ a) = h (f^𝐀 ∘ a)`, as this shows that :math:`𝖤(g, h)` is closed under the operation :math:`f^𝐀` of :math:`𝐀`.

      But this is trivial since, by definition of homomorphism, we have

      .. math:: (g ∘ f^𝐀)(ι_i a) = (f^𝐁 ∘ F g)(ι_i a) = (f^𝐁 ∘ F h)(ι_i a) = (h ∘ f^𝐀)(ι_i a).

   |
            
   .. _fact-two:

#. If the set :math:`X ⊆ A` generates 𝐀 and :math:`g|_X = h|_X`, then :math:`g = h`.

   .. container:: toggle
    
      .. container:: header
  
         *Proof*.

      Suppose the subset :math:`X ⊆ A` generates :math:`⟨A, f^𝐀⟩` and suppose :math:`g|_X = h|_X`.
 
      Fix an arbitrary :math:`a : A`. We show :math:`g(a) = h(a)`.
 
      Since :math:`X` generates 𝐀, there exists a term :math:`t` and a tuple :math:`x : ρt → X` of generators such that :math:`a = t^𝐀 x`.
 
      Therefore, since :math:`F g = F h` on :math:`X`, we have
    
      .. math:: g(a) = g(tᴬ x) = (tᴮ ∘ F g)(x) = (tᴮ ∘ F h)(x) = h(tᴬ x) = h(a).
    
   |

   .. _fact-three:

#. If :math:`A, B` are finite and :math:`X` generates 𝐀, then :math:`|\hom(𝐀, 𝐁)| ≤ |B|^{|X|}`.

   .. container:: toggle
    
      .. container:: header
    
         *Proof*.

      By :ref:`Fact 2 <fact-two>`, a homomorphism is uniquely determined by its restriction to a generating set.

      If :math:`X` generates 𝐀, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\hom(𝐀, 𝐁)| ≤ |B|^{|X|}`.
    
   |

   .. _fact-four:

#. If :math:`g : \epi (𝐀, 𝐁)` and :math:`h : \hom (𝐀, 𝐂)` satisfy :math:`\ker g ⊆ \ker h`, then

   .. math:: ∃ k ∈ \hom(𝐁, 𝐂)\ . \ h = k ∘ g.
    
   .. container:: toggle
    
      .. container:: header
    
         *Proof*.

      We define :math:`k ∈ \hom(𝐁, 𝐂)` constructively, as follows:

      Fix :math:`b : B`.

      Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} ⊆ A` is nonempty, and since :math:`\ker g ⊆ \ker h`, we see that every element of :math:`g^{-1}\{b\}` is mapped by :math:`h` to a single element of :math:`C`.

      Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a : g^{-1}\{b\}`.
   
      We define :math:`k(b) = c_b`. Since :math:`b` was arbitrary, :math:`k` is defined on all of :math:`B` in this way.
   
      Now it's easy to see that :math:`k g = h` by construction.
   
      Indeed, for each :math:`a ∈ A`, we have :math:`a ∈ g^{-1}\{g(a)\}`, so :math:`k(g(a)) = h(a)` by definition.
   
      To see that :math:`k` is a homomorphism, let there be :math:`m` operation symbols and let :math:`0≤ i< m` be arbitrary.
   
      Fix :math:`b : \underline{k_i} → B`.
   
      Since :math:`g` is surjective, for each :math:`i : \underline{k_i}`, the subset :math:`g^{-1}\{b(i)\}⊆ A` is nonempty and is mapped by :math:`h` to a single point of :math:`C` (since :math:`\ker g ⊆ \ker h`.
   
      Label this point :math:`c_i` and define :math:`c : \underline{k_i} → C` by :math:`c(i) = c_i`.
   
      We want to show :math:`(f^C ∘ F k) (b) = (k ∘ f^B)(b).`
   
      The left hand side is :math:`f^C c`, which is equal to :math:`(h ∘ fᴬ)(a)` for some :math:`a : \underline{k_i} → A`, since :math:`h` is a homomorphism.
   
      Therefore,
   
      .. math:: (f^C ∘ F k) (b) = (h ∘ f^A) (a) = (k ∘ g ∘ f^A)(a) = (k ∘ f^B ∘ F g)(a) = (k ∘ f^B)(b).
 
   |

#. Let :math:`S = (F, ρ)` be a signature each :math:`f ∈ F` an :math:`(ρf)`-ary operation symbol.
 
    Define :math:`F_0 := \operatorname{Proj}(A)` and for all :math:`n > 0` in :math:`ω` let
 
    .. math:: F_{n+1} := F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.
 
    Then :math:`\mathrm{Clo}^{𝐀}(F) = ⋃_n F_n`.
 
#. Let :math:`f` be a similarity type.
 
    (a) :math:`𝐓_ρ (X)` is generated by :math:`X`.
 
    (b) For every algebra :math:`𝐀 = ⟨A, F⟩` of type :math:`ρ` and every function :math:`h : X → A` there is a unique homomorphism :math:`g : 𝐓_ρ (X) → ⟨A, fᴬ⟩` such that :math:`g|_X = h`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*.
     
      The definition of :math:`𝐓_ρ (X)` exactly parallels the construction in Theorem 1.14 :cite:`Bergman:2012`. That accounts for the first item.
     
      For b, define :math:`g(t)` by induction on :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ \mathcal F_0`.
     
      If :math:`t ∈ X` then define :math:`g(t) = h(t)`. For :math:`t ∈ \mathcal F_0`, :math:`g(t) = t^{𝐀}`.
     
      Note that since :math:`𝐀 = ⟨A, fᴬ⟩` is an algebra of type :math:`f` and :math:`t` is a nullary operation symbol, :math:`t^{𝐀}` is defined.
     
      For the inductive step, let :math:`|t| = n + 1`. Then :math:`t = f(s_1, \dots, s_k)` for some :math:`f ∈ \mathcal F_k` and :math:`s_1, \dots, s_k` each of height at most :math:`n`. We define :math:`g(t) = f^{𝐀}(g(s_1), \dots, g(s_k))`.
     
      By its very definition, :math:`g` is a homomorphism. Finally, the uniqueness of :math:`g` follows from Exercise 1.16.6 in :cite:`Bergman:2012`.
 
   |

#. Let :math:`𝐀 = ⟨A, f^{𝐀}⟩` and :math:`𝐁 = ⟨B, f^{𝐁}⟩` be algebras of type :math:`ρ`.
 
    (a) For every :math:`n`-ary term :math:`t` and homomorphism :math:`g : 𝐀 → 𝐁`, :math:`g(t^{𝐀}(a_1,\dots, a_n)) = t^{𝐁}(g(a_1),\dots, g(a_n))`.

    (b) For every term :math:`t ∈ T_ρ(X_ω)` and every :math:`θ ∈ \mathrm{Con}⟨A, fᴬ⟩`, :math:`𝐀 ≡_θ 𝐁` implies :math:`t^{𝐀}(𝐀) ≡_θ t^{𝐀}(𝐁)`.

    (c) For every subset :math:`Y` of :math:`A`,

        .. math:: \Sg^{𝐀}(Y) = \{ t^{𝐀}(a_1, \dots, a_n) : t ∈ Tᵨ (X_n), a_i ∈ Y, i ≤ n < ω\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*.
    
      The first statement is an easy induction on :math:`|t|`.
    
      The second statement follows from the first by taking :math:`⟨B, f^{𝐁}⟩ = ⟨A, f^{𝐀}⟩/θ` and :math:`g` the canonical homomorphism.
    
      For the third statement, again by induction on the height of :math:`t`, every subalgebra must be closed under the action of :math:`t^{𝐀}`.
    
      Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows.

   |

------------------------------

.. rubric:: Footnotes

.. [1]
   For a brief, gentle introduction to Type Theory see https://leanprover.github.io/logic_and_proof/axiomatic_foundations.html?highlight=type#type-theory. Alternatively, viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. _categorytheory.gitlab.io: https://categorytheory.gitlab.io


.. _Lean: https://leanprover.github.io/
