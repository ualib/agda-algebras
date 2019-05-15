.. _birkhoffs-hsp-theorem:

======================
Birkhoff's HSP Theorem
======================

Let :math:`σ = (F, ρ)` be a signature.

An **identity in the signature** σ is an ordered pair of terms, written :math:`p ≈ q`, from :math:`T_σ (X_ω)`.

Let :math:`𝐀 = ⟨A, F^{𝐀}⟩` be an algebra of signature :math:`S`.

We say that 𝐀 satisfies :math:`p ≈ q`, and write :math:`𝐀 ⊧ p ≈ q`, if :math:`p^{𝐀} = q^{𝐀}`.

If 𝒦 is a class of algebras of signature σ, we write :math:`𝒦 ⊧ p \approx q` if :math:`∀ 𝐀 ∈ 𝒦`, :math:`𝐀 ⊧ p ≈ q`.

Finally, if Σ is a set of equations, we write :math:`𝒦 ⊧ Σ` if every member of 𝒦 satisfies every member of Σ.

Let 𝒦 be a class of algebras and Σ a set of equations in the signature σ. We define :math:`\mathrm{Id}(𝒦) = \{p ≈ q : 𝒦 ⊧ p ≈ q\}`
and :math:`\mathrm{Mod}(Σ) = \{ 𝐀 : 𝐀 ⊧ Σ \}`.

Classes of the form :math:`\mathrm{Mod}(Σ)` are called **equational classes**, and :math:`Σ` is called an **equational base** or an **axiomatization** of the class.

:math:`\mathrm{Mod}(Σ)` is called the class of **models** of Σ.

Dually, a set of identities of the form :math:`\mathrm{Id}(𝒦)` is called an **equational theory**.

.. _a-variety-of-facts:

A variety of theorems
---------------------

.. _fact-m1:

.. proof:theorem::

   For every class 𝒦, each of the classes :math:`𝖲(𝒦)`, :math:`𝖧(𝒦)`, :math:`𝖯(𝒦)`, and :math:`𝕍(𝒦)` satisfies exactly the same identities as does 𝒦.

   *Proof*. Exercise.

   .. _fact-m2:

.. proof:theorem:: 

   :math:`𝒦 ⊧ p ≈ q` if and only if for every :math:`𝐀 ∈ 𝒦` and every :math:`h ∈ \mathrm{Hom}(𝐓(X_ω), 𝐀)`, we have :math:`h(p) = h(q)`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      First assume that :math:`𝒦 ⊧ p ≈ q`. Fix :math:`𝐀∈ 𝒦` and :math:`h ∈ \mathrm{Hom}(𝐓(X_ω), 𝐀)`.
      
      Then :math:`𝐀 ⊧ p ≈ q ⟹ p^{𝐀} = q^{𝐀} ⟹ p^{𝐀}(h(x_1), \dots, h(x_n)) = q^{𝐀}(h(x_1), \dots, h(x_n))`.
      
      Since :math:`h` is a homomorphism, we obtain :math:`h(p^{𝐀}(x_1, \dots, x_n)) = h(q^{𝐀}(x_1, \dots, x_n))`, i.e., :math:`h(p) = h(q)`.

      To prove the converse we must fix a :math:`𝐀 \in 𝒦` and :math:`a_1, \dots, a_n ∈ A` and show that :math:`p^{𝐀}(x_1, \dots, x_n) = q^{𝐀}(x_1, \dots, x_n)`.
   
      Let :math:`h_0 : X_ω → A` be a function with :math:`h_0(x_i) = a_i` for :math:`i ≤ n`.
      
      By Thm. 4.21 in :cite:`Bergman:2012`, :math:`h_0` extends to a homomorphism :math:`h` from :math:`𝐓(X_ω)` to :math:`(A, f^A)`.
      
      By assumption :math:`h(p) = h(q)`. Since :math:`h(p) = h(p^{𝐀}(x_1, \dots, x_n)) = p^{𝐀}(h(x_1), \dots, h(x_n)) = p^{𝐀}(a_1,\dots, a_n)` (and similarly for :math:`q`) the result follows.

   .. _fact-m3:

.. proof:theorem:: 

   Let 𝒦 be a class of algebras and :math:`p ≈ q` an equation. The following are equivalent.

     #. :math:`𝒦 ⊧ p ≈ q`.

     #. :math:`(p, q)` belongs to the congruence :math:`λ_{𝒦}` on :math:`𝐓(X_ω)`.

     #. :math:`𝐅_{𝒦}(X_ω) ⊧ p ≈ q`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      We shall show (a) ⟹ (c) ⟹ (b) ⟹ (a). 
      
      Throughout the proof we write 𝐅 for :math:`𝐅_{𝒦}(X_ω)`, 𝐓 for :math:`𝐓(X_ω)` and :math:`λ` for :math:`λ_{𝒦}`.

      Recall that :math:`𝐅 = 𝐓/λ ∈ 𝖲 𝖯 (𝒦)`.
      
      From (a) and Lemma 4.36 of :cite:`Bergman:2012` we have :math:`𝖲 𝖯 (𝒦) ⊧ p ≈ q`. Thus (c) holds.

      From (c), :math:`p^{𝐅}([x_1], \dots, [x_n]) = q^{𝐅}([x_1], \dots, [x_n])`, where :math:`[x_i] = x_i/λ`.
      
      From the definition of 𝐅, :math:`p^{𝐓}(x_1, \dots, x_n) ≡_λ q^{𝐓}(x_1, \dots, x_n)`, from which (b) follows since :math:`p = p^{𝐓}(x_1, \dots, x_n)` and :math:`q = q^{𝐓}(x_1, \dots, x_n)`.

      Finally assume (b). We wish to apply Lemma 4.37 of :cite:`Bergman:2012`.
      
      Let :math:`𝐀 ∈ 𝒦` and :math:`h ∈ \mathrm{Hom}(𝐓, 𝐀)`.
      
      Then :math:`𝐓/\ker h ∈ 𝖲 (𝐀) ⊆ 𝖲(𝒦)` so :math:`\ker h ⊇ λ`.  Thus, (b) implies :math:`h(p) = h(q)` hence (a) holds, completing the proof.

The last result tells us that we can determine whether an identity is true in a variety by consulting a particular algebra, namely :math:`𝐅(X_ω)`. Sometimes it is convenient to work with algebras free on other generating sets besides :math:`X_ω`. The following corollary takes care of that for us.

.. _fact-m4:

.. proof:theorem:: 

   Let :math:`𝒦` be a class of algebras, :math:`p` and :math:`q` :math:`n`-ary terms, :math:`Y` a set and :math:`y_1, \dots, y_n` distinct elements of :math:`Y`. Then :math:`𝒦 ⊧ p ≈ q` if and only if
   :math:`p^{𝐅_{𝒦}(Y)}(y_1, \dots, y_n) = q^{𝐅_{𝒦}(Y)}(y_1, \dots, y_n)`. In particular, :math:`𝒦 ⊧ p ≈ q` if and only if :math:`𝐅_{𝒦}(X_n) ⊧ p ≈ q`.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Since :math:`𝐅_{𝒦}(Y) ∈ 𝖲 𝖯 (𝒦)`, the left-to-right direction uses the same argument as in Theorem 4.38 of :cite:`Bergman:2012`. (See :ref:`Fact 3 <fact-m3>` above.)
      
      So assume that :math:`p^{𝐅_{𝒦}(Y)}(y_1, \dots, y_n) = q^{𝐅_{𝒦}(Y)}(y_1, \dots, y_n)`.
      
      To show that :math:`𝒦 ⊧ p ≈ q`, let :math:`𝐀 = ⟨ A, f^{𝐀} ⟩ ∈ 𝒦` and :math:`a_1, \dots, a_n ∈ A`. We must show :math:`p^{𝐀}(a_1, \dots, a_n) = q^{𝐀}(a_1, \dots, a_n)`.

      There is a homomorphism :math:`h : 𝐅_{𝒦}(Y) → (A, f^A)` such that :math:`h(y_i) = a_i` for :math:`i ≤ n`. Then

      .. math:: p^{𝐀}(a_1, \dots, a_n) &= p^{𝐀}(h (y_1), \dots, h (y_n)) = h(p^{𝐅_𝒦(Y)}(y_1, \dots, y_n))\\
                                       &= h(q^{𝐅_𝒦(Y)}(y_1, \dots, y_n)) = q^{𝐀}(h(y_1), \dots, h(y_n))\\
                                       &= q^{𝐀}(a_1, \dots, a_n).

      It now follows from :ref:`Fact 1 <fact-m1>` that every equational class is a variety. The converse is **Birkhoff's HSP Theorem**.

.. _the-hsp-theorem:

The HSP theorem
---------------

The following is Birkhoff's celebrated HSP theorem. (See also :cite:`Bergman:2012`, Thm 4.41.)

.. proof:theorem:: 

   Every variety is an equational class.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let 𝒲 be a variety. We must find a set of equations that axiomatizes 𝒲. The obvious choice is to use the set of all equations that hold in 𝒲.

      To this end, take :math:`Σ = \mathrm{Id}(𝒲)`. Let :math:`𝒲^† := \mathrm{Mod}(Σ)`.  
  
      Clearly, :math:`𝒲 ⊆ 𝒲^†`. We shall prove the reverse inclusion.

      Let :math:`𝐀 ∈ 𝒲^†` and :math:`Y` a set of cardinality :math:`\max(|A|, ω)`. *Choose* a surjection :math:`h_0 : Y → A`. [1]_
  
      By :ref:`Theorem 4.21 <thm-4-21>`, :math:`h_0` extends to a (surjective) homomorphism :math:`h : 𝐓(Y) → 𝐀`.

      Furthermore, since :math:`𝐅_{𝒲}(Y) = 𝐓(Y)/Θ_{𝒲}`, there is a surjective homomorphism :math:`g : 𝐓(Y) → 𝐅_{𝒲}`. [2]_

      We claim that :math:`\ker g ⊆ \ker h`. If the claim is true then by Lemma [ex:1.26.8] there is a map :math:`f : 𝐅_{𝒲}(Y) → 𝐀` such that :math:`f ∘ g = h`.
   
      Since :math:`h` is surjective, so is :math:`f`. Hence :math:`𝐀 ∈ 𝖧 (𝐅_{𝒲}(Y)) ⊆ 𝒲` completing the proof.

Let :math:`u,v ∈ T(Y)` and assume that :math:`g(u) = g(v)`. Since :math:`𝐓(Y)` is generated by :math:`Y`, by :ref:`Theorem 4.21 <thm-4-21>`, there is an integer :math:`n`, terms :math:`p, q ∈ T(X_n)`, and :math:`y_1, \dots, y_n ∈ Y` such that :math:`u = p^{𝐓(Y)}(y_1, \dots, y_n)` and :math:`v = q^{𝐓(Y)}(y_1,\dots, y_n)`, by Theorem [thm:4.32].

Applying the homomorphism :math:`g`,

.. math:: p^{𝐅_{𝒲}(Y)}(y_1, \dots, y_n) = g(u) = g(v) = q^{𝐅_{𝒲}(Y)}(y_1,\dots, y_n).

Then by :ref:`Fact 4 <fact-m4>` above (Corollary 4.39 of :cite:`Bergman:2012`), we have :math:`𝒲 ⊧ p ≈ q`, hence :math:`(p ≈ q) \in Σ`.

Since :math:`𝐀 ∈ 𝒲^† = \mathrm{Mod}(Σ)`, we obtain :math:`𝐀 ⊧ p ≈ q`. Therefore,

.. math:: h(u) = p^{𝐀}(h_0(y_1), \dots, h_0(y_n)) = q^{𝐀}(h_0(y_1), \dots, h_0(y_n)) = h(v),

as desired.

---------------------------

.. rubric:: Footnotes

.. [1]
   **AoC**. It seems we need the Axiom of Choice here.

.. [2]
   **AoC**. *ditto*