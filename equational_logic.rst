.. File: equational_logic.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 2019.10.11
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. _equational-logic:

====================
Equational Logic
====================

.. index:: ! model
.. index:: ! pair: σ-identity; σ-equation
.. index:: ! pair: identity; equation
.. index:: ! pair: equational base; axiomatization
.. index:: ! pair: equational theory; theory
.. index:: ! pair: equational class; variety

.. _models_and_theories:

Models and theories
-------------------

Let :math:`σ = (F, ρ)` be a signature and :math:`X := \{x_0, x_1, \dots\}` a countable collection of variable symbols.

An **identity in the signature** :math:`σ` (or, :math:`σ`-**identity**) is an ordered pair :math:`(t,s)` of terms from :math:`T_σ (X)` of the same arity (:math:`ρ t = ρ s`).

We write :math:`p ≈ q` to indicate such a :math:`σ`-identity; here :math:`p, q ∈ T_σ (X)` and :math:`ρ p = ρ q`. [1]_

**N.B.** We sometimes refer to an identity as an **equation**; in our treatment of the subject the words "identity" and "equation" are synonyms.

Let :math:`𝒜_σ`, resp. :math:`ℰ_σ`, denote the class of all :math:`σ`-algebras, resp. :math:`σ`-identities.

For :math:`𝔸 ∈ 𝒦 ⊆ 𝒜_σ` and :math:`p ≈ q ∈ Σ ⊆ ℰ_σ`, we say

* :math:`𝔸` **models** :math:`p ≈ q`, denoted :math:`𝔸 ⊧ p ≈ q`, just in case :math:`p^𝔸 = q^𝔸` *extensionally* (i.e., :math:`ρ t = ρ s` and :math:`∀ a: ρ p → A, \; p^𝔸 \, a = q^𝔸 \, a`.); [2]_

* :math:`𝔸` **models** :math:`Σ`, denoted :math:`𝔸 ⊧ Σ`, just in case :math:`𝔸 ⊧ p ≈ q` for every :math:`p ≈ q` in :math:`Σ`;

* :math:`𝒦` **models** :math:`p ≈ q`, denoted :math:`𝒦 ⊧ p ≈ q`, just in case :math:`𝔸 ⊧ p ≈ q` for every :math:`𝔸` in :math:`𝒦`;

* :math:`𝒦` **models** :math:`Σ`, denoted :math:`𝒦 ⊧ Σ`, just in case :math:`𝔸 ⊧ Σ` for every :math:`𝔸 ∈ 𝒦`.

The binary relation :math:`⊧` induces an obvious :term:`Galois connection`. Indeed, the :term:`Galois pair` :math:`(\Mod, \Th)` is defined as follows: for all :math:`Σ ⊆ ℰ_σ` and :math:`𝒦 ⊆ 𝒜_σ`, 

.. math:: \Mod(Σ) := \{𝔸: 𝔸 ⊧ Σ \} \quad \text{ and } \quad \Th(𝒦) := \{Σ: 𝒦 ⊧ Σ\}.

The first of these, the class of **models** of :math:`Σ`, contains those and only those algebras modelling :math:`Σ`. It is called an **equational class**, and :math:`Σ` is called an **equational base** for, or an **axiomatization** of, the class.

Dually, :math:`\Th(𝒦)` is the class of identities modelled by all algebras in :math:`𝒦`.  Such a class of identities is called an **equational theory**.

Alternatively and equivalently we could define "equational class" and "equational theory" in terms of the two :term:`closure operators <closure operator>` induced by the Galois pair :math:`(\Mod, \Th)`.  Indeed, :math:`\Mod \Th: 𝒫 (𝒜) → 𝒫(𝒜)` is a closure operator on :math:`𝒜` and :math:`\Th \Mod: 𝒫 (ℰ) → 𝒫(ℰ)` is a closure operator on :math:`ℰ`, and 

* an **equational class** is a :math:`\Mod \Th`-:term:`closed` set of :math:`σ`-algebras;

* an **equational theory** is a :math:`\Th \Mod`-:term:`closed` set of :math:`σ`-identities.

(Here, as usual, :math:`𝒫` denotes the :term:`power set operator`.)

**N.B.** We sometimes refer to an equational class as a **variety**; in our treatment of the subject "equational class" and "variety" are synonyms.

.. _a-variety-of-facts:

A variety of facts
~~~~~~~~~~~~~~~~~~

.. _fact-m1:

.. proof:theorem::

   For every class 𝒦, each of the classes :math:`𝖲(𝒦)`, :math:`𝖧(𝒦)`, :math:`𝖯(𝒦)`, and :math:`𝕍(𝒦)` satisfies exactly the same identities as does 𝒦.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.

      We prove the result for :math:`𝖧(𝒦)` and leave the others as exercises.

      Clearly :math:`𝒦 ⊆ 𝖧(𝒦)`, so :math:`\Th \, 𝖧 (𝒦) ⊆  \Th \,𝒦`. 


.. _fact-m2:

.. proof:theorem:: 

   :math:`𝒦 ⊧ p ≈ q` if and only if :math:`∀ 𝔸 ∈ 𝒦`, :math:`∀ h ∈ \Hom(𝕋(X_ω), 𝔸)`, :math:`h\, p^𝔸 = h\, q^𝔸`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      (⇒) Assume that :math:`𝒦 ⊧ p ≈ q`.
      
          Fix :math:`𝔸 ∈ 𝒦` and :math:`h ∈ \Hom(𝕋(X_ω), 𝔸)`.
      
          We must show :math:`∀ a: ρ p → A` that :math:`h(p^{𝔸}\, a) = h(q^{𝔸}\, a)`.

          Fix :math:`a: ρ p → A`.

          By :math:`𝔸 ⊧ p ≈ q` we have :math:`p^{𝔸} = q^{𝔸}` which implies :math:`p^{𝔸}(h ∘ a) = q^{𝔸}(h ∘ a)`.
      
          Since :math:`h` is a homomorphism, we obtain :math:`h(p^{𝔸}\, a) = h(q^{𝔸}\, a)`, as desired.

      (⇐) Assume :math:`∀ 𝔸 ∈ 𝒦`, :math:`∀ h ∈ \Hom(𝕋(X_ω), 𝔸)`, :math:`h\, p^𝔸 = h\, q^𝔸`.
      
          We must show :math:`𝒦 ⊧ p ≈ q`.
          
          Fix :math:`𝔸 ∈ 𝒦` and :math:`a: ρ p → A`.
          
          We must prove :math:`p^𝔸 \, a = q^𝔸\, a`.
          
          Let :math:`h_0 : X_ω → A` be a function with :math:`h_0\, x\, i = a\, i` for all :math:`0≤ i < ρ p`, for some :math:`x: ρ p → X_ω`.
          
          By :numref:`Obs %s <obs-six>`, :math:`h_0` extends to a homomorphism :math:`h` from :math:`𝕋(X_ω)` to 𝔸.
      
          By assumption :math:`h\, p^𝔸 = h\, q^𝔸`, and since :math:`h` is a homomorphism,
      
          .. math:: p^{𝔸}\, a =  p^{𝔸}(h ∘ x) = h(p^{𝔸} \, x) = h(q^𝔸 \, x) = q^𝔸 (h ∘ x) = q^𝔸 \, a,
      
          so :math:`p^{𝔸}\, a = q^𝔸 \, a`, as desired. ☐

.. _fact-m3:

.. proof:theorem:: 

   Let 𝒦 be a class of algebras and :math:`p ≈ q` an equation. The following are equivalent.

     #. :math:`𝒦 ⊧ p ≈ q`.

     #. :math:`(p, q)` belongs to the congruence :math:`λ_{𝒦}` on :math:`𝕋(X_ω)`.

     #. :math:`𝔽_{𝒦}(X_ω) ⊧ p ≈ q`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      We shall show (1) ⟹ (3) ⟹ (2) ⟹ (1). 
      
      Recall that :math:`𝔽_{𝒦}(X_ω) = 𝕋/λ ∈ 𝖲 𝖯 (𝒦)`.
      
      From (1) and Lemma 4.36 of :cite:`Bergman:2012` we have :math:`𝖲 𝖯 (𝒦) ⊧ p ≈ q`. Thus (3) holds.

      From (3), :math:`p^{𝔽} \, [x] = q^{𝔽} \, [x]`, where :math:`[x]: ρ p → 𝔽_𝒦 (X_ω)` is defined by :math:`[x]\, i = x_i/λ`.
      
      From the definition of 𝔽, :math:`p^{𝕋}\, x ≡_λ q^{𝕋} ×`, from which (2) follows since :math:`p = p^{𝕋}\, x` 
      and :math:`q = q^{𝕋}\, x`.

      Finally assume (2). We wish to apply Lemma 4.37 of :cite:`Bergman:2012`.
      
      Let :math:`𝔸 ∈ 𝒦` and :math:`h ∈ \Hom(𝕋, 𝔸)`.
      
      Then :math:`𝕋/\ker h ∈ 𝖲 (𝔸) ⊆ 𝖲(𝒦)` so :math:`\ker h ⊇ λ`.  Thus, (2) implies :math:`h\, p = h\, q` hence (1) holds, completing the proof. ☐

The last result tells us that we can determine whether an identity is true in a variety by consulting a particular algebra, namely :math:`𝔽(X_ω)`. Sometimes it is convenient to work with algebras free on other generating sets besides :math:`X_ω`. The following corollary takes care of that for us.


.. _fact-m4:

.. proof:theorem:: 

   Let :math:`𝒦` be a class of algebras, :math:`p` and :math:`q` :math:`n`-ary terms, :math:`Y` a set and :math:`y_1, \dots, y_n` distinct elements of :math:`Y`. Then :math:`𝒦 ⊧ p ≈ q` if and only if
   :math:`p^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n) = q^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n)`. In particular, :math:`𝒦 ⊧ p ≈ q` if and only if :math:`𝔽_{𝒦}(X_n) ⊧ p ≈ q`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Since :math:`𝔽_{𝒦}(Y) ∈ 𝖲 𝖯 (𝒦)`, the left-to-right direction uses the same argument as in Theorem 4.38 of :cite:`Bergman:2012`. (See :numref:`Thm %s <fact-m3>` above.)
      
      So assume that :math:`p^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n) = q^{𝔽_{𝒦}(Y)}(y_1, \dots, y_n)`.
      
      To show that :math:`𝒦 ⊧ p ≈ q`, let :math:`𝔸 = ⟨ A, f^{𝔸} ⟩ ∈ 𝒦` and :math:`a_1, \dots, a_n ∈ A`. We must show :math:`p^{𝔸}(a_1, \dots, a_n) = q^{𝔸}(a_1, \dots, a_n)`.

      There is a homomorphism :math:`h : 𝔽_{𝒦}(Y) → (A, f^A)` such that :math:`h(y_i) = a_i` for :math:`i ≤ n`. Then

      .. math:: p^{𝔸}(a_1, \dots, a_n) &= p^{𝔸}(h (y_1), \dots, h (y_n)) = h(p^{𝔽_𝒦(Y)}(y_1, \dots, y_n))\\
                                       &= h(q^{𝔽_𝒦(Y)}(y_1, \dots, y_n)) = q^{𝔸}(h(y_1), \dots, h(y_n))\\
                                       &= q^{𝔸}(a_1, \dots, a_n).

      It now follows from :numref:`Thm %s <fact-m1>` that every equational class is a variety. The converse is **Birkhoff's HSP Theorem**. ☐

----------------------------------

.. _birkhoffs-hsp-theorem:

Birkhoff's HSP theorem
------------------------

The following is Birkhoff's celebrated HSP theorem. (See also :cite:`Bergman:2012`, Thm 4.41.)

.. proof:theorem:: 

   Every variety is an equational class.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let 𝒲 be a variety. We must find a set of equations that axiomatizes 𝒲. The obvious choice is to use the set of all equations that hold in 𝒲.

      To this end, take :math:`Σ = \Th(𝒲)`. Let :math:`𝒲^† := \Mod(Σ)`.  
  
      Clearly, :math:`𝒲 ⊆ 𝒲^†`. We shall prove the reverse inclusion.

      Let :math:`𝔸 ∈ 𝒲^†` and :math:`Y` a set of cardinality :math:`\max(|A|, ω)`. *Choose* a surjection :math:`h_0 : Y → A`. [3]_
  
      By :numref:`Obs %s <obs-six>` (which is essentially Thm. 4.21 of :cite:`Bergman:2012`), :math:`h_0` extends to an epimorphism :math:`h: 𝕋(Y) → 𝔸`.

      Furthermore, since :math:`𝔽_𝒲(Y) = 𝕋(Y)/Θ_𝒲`, there is an epimorphism :math:`g: 𝕋(Y) → 𝔽_𝒲`. [4]_

      We claim that :math:`\ker g ⊆ \ker h`. If the claim is true, then by :numref:`Obs %s <obs-four>` there is a map :math:`f: 𝔽_𝒲(Y) → 𝔸` such that :math:`f ∘ g = h`.
   
      Since :math:`h` is epic, so is :math:`f`. Hence :math:`𝔸 ∈ 𝖧 (𝔽_{𝒲}(Y)) ⊆ 𝒲` completing the proof. ☐

Let :math:`u,v ∈ T(Y)` and assume that :math:`g(u) = g(v)`. Since :math:`𝕋(Y)` is generated by :math:`Y`, then by :numref:`Obs %s <obs-six>` there is an integer :math:`n`, terms :math:`p, q ∈ T(X_n)`, and :math:`y_1, \dots, y_n ∈ Y` such that :math:`u = p^{𝕋(Y)}(y_1, \dots, y_n)` and :math:`v = q^{𝕋(Y)}(y_1,\dots, y_n)`, by Theorem 4.32 of :cite:`Bergman:2012`.

Applying the homomorphism :math:`g`,

.. math:: p^{𝔽_{𝒲}(Y)}(y_1, \dots, y_n) = g(u) = g(v) = q^{𝔽_{𝒲}(Y)}(y_1,\dots, y_n).

Then by :numref:`Thm %s <fact-m4>` above (Corollary 4.39 of :cite:`Bergman:2012`), we have :math:`𝒲 ⊧ p ≈ q`, hence :math:`(p ≈ q) \in Σ`.

Since :math:`𝔸 ∈ 𝒲^† = \Mod(Σ)`, we obtain :math:`𝔸 ⊧ p ≈ q`. Therefore,

.. math:: h(u) = p^{𝔸}(h_0(y_1), \dots, h_0(y_n)) = q^{𝔸}(h_0(y_1), \dots, h_0(y_n)) = h(v),

as desired.

--------------------------

.. rubric:: Footnotes

.. [1]
   Produce ``≈`` with ``\approx``.

.. [2]
   Produce ⊧ with ``\models``.

.. [3]
   **AoC**. Some :term:`Choice` axiom is needed here.

.. [4]
   **AoC**. Some :term:`Choice` axiom is needed here.

.. include:: hyperlink_references.rst
