.. FILE: birkhoff.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 23 Feb 2020
.. UPDATE: 27 Jun 2020
.. REF: Based on the file `birkhoff.agda` (23 Jan 2020).

.. _birkhoffs theorem in agda:

============================
Birkhoff's Theorem in Agda
============================

Here we give a formal proof in Agda of :ref:`Birkhoff's theorem <birkhoffs theorem>` (:numref:`%s <birkhoffs theorem>`), which says that a variety is an equational class. In other terms, if a class 𝒦 of algebras is closed under the operators 𝑯, 𝑺, 𝑷, then 𝒦 is an equational class (i.e., 𝒦 is the class of algebras that model a particular set of identities).  The sections below contain (literate) Agda code that formalizes each step of the (informal) proof we saw above in :numref:`birkhoffs theorem`.

Preliminaries
-----------------

As usual, we start with the imports we will need below.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import prelude
  open import basic using (Signature; Algebra; Π')
  open import relations using (ker-pred; Rel; con; _//_)
  open import homomorphisms using (HOM; Hom; hom; is-homomorphism)

  open import terms using (Term; generator; 𝔉; _̇_; comm-hom-term';
                           lift-hom; interp-prod)

  open import subuniverses using (Subuniverse; mksub; var; app; Sg;
                                  _is-subalgebra-of_; Subalgebra)

The Birkhoff module
----------------------

We start the ``birkhoff`` module with a fixed signature and a type ``X``.  As in the ``terms`` module, ``X`` represents an arbitrary (infinite) collection of "variables" (which will serve as the generators of the :term:`term algebra` 𝔉).

::

  module birkhoff {S : Signature 𝓞 𝓥} {X : 𝓧 ̇ }  where

.. _obs 1 in agda:

Equalizers
~~~~~~~~~~~~~~

The equalizer of two functions (resp., homomorphisms) ``g h : A → B`` is the subset of ``A`` on which the values of the functions ``g`` and ``h`` agree.  We formalize this notion in Agda as follows.

::

  --Equalizers of functions
  𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
  𝑬 g h x = g x ≡ h x

  --Equalizers of homomorphisms
  𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 S} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
  𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x
  --cf. definition 𝓔 in the homomorphisms module

It turns out that the equalizer of two homomorphisms is closed under the operations of ``𝑨`` and is therefore a subalgebra of the common domain, as we now prove.

::

  𝑬𝑯-is-closed : funext 𝓥 𝓤
   →      {𝑓 : ∣ S ∣ } {𝑨 𝑩 : Algebra 𝓤 S}
          (g h : hom 𝑨 𝑩)  (𝒂 : (∥ S ∥ 𝑓) → ∣ 𝑨 ∣)
   →      ((x : ∥ S ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
          --------------------------------------------------
   →       ∣ g ∣ (∥ 𝑨 ∥ 𝑓 𝒂) ≡ ∣ h ∣ (∥ 𝑨 ∥ 𝑓 𝒂)

  𝑬𝑯-is-closed fe {𝑓 = 𝑓}{𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ}
   (g , ghom)(h , hhom) 𝒂 p =
     g (Fᴬ 𝑓 𝒂)    ≡⟨ ghom 𝑓 𝒂 ⟩
     Fᴮ 𝑓 (g ∘ 𝒂)  ≡⟨ ap (Fᴮ _ )(fe p) ⟩
     Fᴮ 𝑓 (h ∘ 𝒂)  ≡⟨ (hhom 𝑓 𝒂)⁻¹ ⟩
     h (Fᴬ 𝑓 𝒂)    ∎

Thus, ``𝑬𝑯`` is a subuniverse of ``𝑨``.

::

  -- Equalizer of homs is a subuniverse.
  𝑬𝑯-is-subuniverse : funext 𝓥 𝓤
   →  {𝑨 𝑩 : Algebra 𝓤 S}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
  𝑬𝑯-is-subuniverse fe {𝑨 = 𝑨} {𝑩 = 𝑩} g h =
   mksub (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h)
    λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑨 = 𝑨} {𝑩 = 𝑩} g h 𝒂 x

.. _obs 3 in agda:

Homomorphisms
~~~~~~~~~~~~~~

The :numref:`homomorphisms module (Section %s) <homomorphisms module>` formalizes the notion of homomorphism and proves some basic facts about them. Here we show that homomorphisms are determined by their values on a generating set, as stated and proved informally in :numref:`Obs %s <obs 3>`.  This is proved here, and not in :numref:`homomorphisms module` because we need ``Sg`` from the ``subuniverses`` module (see :numref:`subuniverses in agda`).

::

  HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
             (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
   →         (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
           ---------------------------------------------------
   →        (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ g ∣ a ≡ ∣ h ∣ a)

  HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x
  HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
   (g , ghom) (h , hhom) gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
    g (Fᴬ 𝑓 𝒂)     ≡⟨ ghom 𝑓 𝒂 ⟩
    Fᴮ 𝑓 (g ∘ 𝒂 )   ≡⟨ ap (Fᴮ 𝑓) (fe induction-hypothesis) ⟩
    Fᴮ 𝑓 (h ∘ 𝒂)    ≡⟨ ( hhom 𝑓 𝒂 )⁻¹ ⟩
    h ( Fᴬ 𝑓 𝒂 )   ∎
   where
    induction-hypothesis =
      λ x → HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
      (g , ghom)(h , hhom) gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

**Obs**. If 𝐴, 𝐵 are finite and 𝑋 generates 𝑨, then ∣Hom(𝑨, 𝑩)∣ ≤ :math:`∣B∣^{∣X∣}`.
Proof. By ``HomUnique``, a homomorphism is uniquely determined by its restriction to a generating set. If 𝑋 generates 𝑨, then since there are exactly :math:`∣B∣^∣X∣` functions from 𝑋 to 𝐵, the result holds. □

.. todo:: formalize **Obs**.

.. _obs 14 in agda:

Identities preserved by homs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recall (:numref:`Obs %s <obs 14>`) that an identity is satisfied by all algebras in a class if and only if that identity is compatible with all homomorphisms from the term algebra 𝔉 into algebras of the class.  More precisely, if𝓚 is a class of 𝑆-algebras and 𝑝, 𝑞 terms in the language of 𝑆, then,

.. math:: 𝒦 ⊧ p ≈ q \; ⇔ \; ∀ 𝑨 ∈ 𝒦, ∀ h ∈ \mathrm{Hom}(𝔉, 𝑨), h ∘ p^𝔉 = h ∘ q^𝔉.

We now formalize this result in Agda.

::

  module _
   (gfe : global-dfunext)
   (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
   { X : 𝓧 ̇ } where

   -- ⇒ (the "only if" direction)
   identities-are-compatible-with-homs : (p q : Term)
    →                𝓚 ⊧ p ≋ q
         ----------------------------------------------------
    →     ∀ 𝑨 KA h → ∣ h ∣ ∘ (p ̇ (𝔉{X = X})) ≡ ∣ h ∣ ∘ (q ̇ 𝔉)
   -- Here, the inferred types are
   -- 𝑨 : Algebra 𝓤 S, KA : 𝓚 𝑨, h : hom (𝔉{X = X}) 𝑨

   identities-are-compatible-with-homs p q 𝓚⊧p≋q 𝑨 KA h = γ
    where
     pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
     pA≡qA = 𝓚⊧p≋q KA

     pAh≡qAh : ∀(𝒂 : X → ∣ 𝔉 ∣)
      →        (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
     pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

     hpa≡hqa : ∀(𝒂 : X → ∣ 𝔉 ∣)
      →        ∣ h ∣ ((p ̇ 𝔉) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝔉) 𝒂)
     hpa≡hqa 𝒂 =
      ∣ h ∣ ((p ̇ 𝔉) 𝒂)  ≡⟨ comm-hom-term' gfe 𝔉 𝑨 h p 𝒂 ⟩
      (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
      (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term' gfe 𝔉 𝑨 h q 𝒂)⁻¹ ⟩
      ∣ h ∣ ((q ̇ 𝔉) 𝒂)  ∎

     γ : ∣ h ∣ ∘ (p ̇ 𝔉) ≡ ∣ h ∣ ∘ (q ̇ 𝔉)
     γ = gfe hpa≡hqa

   -- ⇐ (the "if" direction)
   homs-are-compatible-with-identities : (p q : Term)
    →    (∀ 𝑨 KA h  →  ∣ h ∣ ∘ (p ̇ 𝔉) ≡ ∣ h ∣ ∘ (q ̇ 𝔉))
         -----------------------------------------------
    →                𝓚 ⊧ p ≋ q
   --Inferred types: 𝑨 : Algebra 𝓤 S, KA : 𝑨 ∈ 𝓚, h : hom 𝔉 𝑨

   homs-are-compatible-with-identities p q all-hp≡hq {A = 𝑨} KA = γ
    where
     h : (𝒂 : X → ∣ 𝑨 ∣) → hom 𝔉 𝑨
     h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

     γ : 𝑨 ⊧ p ≈ q
     γ = gfe λ 𝒂 →
      (p ̇ 𝑨) 𝒂
        ≡⟨ refl _ ⟩
      (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ generator)
        ≡⟨(comm-hom-term' gfe 𝔉 𝑨 (h 𝒂) p generator)⁻¹ ⟩
      (∣ h 𝒂 ∣ ∘ (p ̇ 𝔉)) generator
        ≡⟨ ap (λ - → - generator) (all-hp≡hq 𝑨 KA (h 𝒂)) ⟩
      (∣ h 𝒂 ∣ ∘ (q ̇ 𝔉)) generator
        ≡⟨ (comm-hom-term' gfe 𝔉 𝑨 (h 𝒂) q generator) ⟩
      (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ generator)
        ≡⟨ refl _ ⟩
      (q ̇ 𝑨) 𝒂
        ∎

   compatibility-of-identities-and-homs : (p q : Term)
    →  (𝓚 ⊧ p ≋ q)
        ⇔ (∀ 𝑨 KA hh → ∣ hh ∣ ∘ (p ̇ 𝔉) ≡ ∣ hh ∣ ∘ (q ̇ 𝔉))
   --inferred types: 𝑨 : Algebra 𝓤 S, KA : 𝑨 ∈ 𝓚, hh : hom 𝔉 𝑨.

   compatibility-of-identities-and-homs p q =
     identities-are-compatible-with-homs p q ,
     homs-are-compatible-with-identities p q

   Th : ? ̇
   Th = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝓚 ⊧ p ≋ q


      --    To this end, take Σ = Th(𝒲). Let :math:`𝒲^† :=` Mod(Σ).

      -- Clearly, :math:`𝒲 ⊆ 𝒲^†`. We shall prove the reverse inclusion.

      -- Let :math:`𝑨 ∈ 𝒲^†` and 𝑌 a set of cardinality max(∣𝐴∣, ω). Choose a surjection ℎ₀ : 𝑌 → 𝐴.

      -- By :numref:`Obs %s <obs 9>`, ℎ₀ extends to an epimorphism ℎ : 𝔉(𝑌) → 𝑨`.

      -- Furthermore, since :math:`𝔽_𝒲(Y) = 𝑻(Y)/Θ_𝒲`, there is an epimorphism :math:`g: 𝑻(Y) → 𝔽_𝒲`.

      -- We claim that :math:`\ker g ⊆ \ker h`. If the claim is true, then by :numref:`Obs %s <obs 5>` there is a map 𝑓 : 𝔽_𝒲(𝑌) → 𝐴 such that :math:`f ∘ g = h`.

      -- Since ℎ is epic, so is 𝑓. Hence :math:`𝑨 ∈ 𝑯(𝔽_{𝒲}(Y)) ⊆ 𝒲` completing the proof.

------------------

.. include:: hyperlink_references.rst

