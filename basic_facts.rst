.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _basic-facts:

===========
Basic Facts
===========

Here is a collection of basic facts that are useful in universal algebra.  Some of them involve homomorphisms, or terms, or clones.  

Throughout this section,

+ :math:`𝔸 = ⟨A, F^𝔸⟩, \ 𝔹 = ⟨B, F^𝔹⟩, \ ℂ = ⟨C, F^ℂ⟩\ ` are algebras of the same signature :math:`σ = (F, ρ)`, and

+ :math:`g, h : \hom(𝔸, 𝔹)` are homomorphism from 𝔸 to 𝔹;

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


Formalization
-------------

Our formal implementation (in `Lean`_) of these objects is described in :numref:`Sections %s <basic-facts-in-lean>`, :numref:`%s <terms-in-lean>`, and :numref:`%s <clones-in-lean>`.


.. include:: hyperlink_references.rst
