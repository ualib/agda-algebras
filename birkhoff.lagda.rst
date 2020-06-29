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

The equalizer of two functions (resp., homomorphisms) ``f g : A → B`` is the subset of ``A`` on which the values of the functions ``f`` and ``g`` agree.  We formalize this notion in Agda as follows.

::

  --Equalizers of functions
  𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (f g : A → B) → Pred A 𝓦
  𝑬 f g x = f x ≡ g x

  --Equalizers of homomorphisms (see also the definition 𝓔 in the ``homomorphisms`` module)
  𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 S} (f g : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
  𝑬𝑯 f g x = ∣ f ∣ x ≡ ∣ g ∣ x

It turns out that the equalizer of two homomorphisms ``f g : hom 𝑨 𝑩`` is a subalgebra of their common domain ``∣ 𝑨 ∣`` since it is closed under the operations of ``𝑨``, as we now prove.

::

  𝑬𝑯-is-closed : funext 𝓥 𝓤
   →       {𝓸 : ∣ S ∣ } {𝑨 𝑩 : Algebra 𝓤 S}
           (f g : hom 𝑨 𝑩)   (𝒂 : (∥ S ∥ 𝓸) → ∣ 𝑨 ∣)
   →       ((x : ∥ S ∥ 𝓸) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} f g))
           --------------------------------------------------
   →        ∣ f ∣ (∥ 𝑨 ∥ 𝓸 𝒂) ≡ ∣ g ∣ (∥ 𝑨 ∥ 𝓸 𝒂)

  𝑬𝑯-is-closed fe {𝓸 = 𝓸}{𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ}
   (f , fhom)(g , ghom) 𝒂 p =
     f (Fᴬ 𝓸 𝒂)    ≡⟨ fhom 𝓸 𝒂 ⟩
     Fᴮ 𝓸 (f ∘ 𝒂)  ≡⟨ ap (Fᴮ _ )(fe p) ⟩
     Fᴮ 𝓸 (g ∘ 𝒂)  ≡⟨ (ghom 𝓸 𝒂)⁻¹ ⟩
     g (Fᴬ 𝓸 𝒂)    ∎

Thus, ``𝑬𝑯`` is a subuniverse of ``𝑨``.

::

  -- Equalizer of homs is a subuniverse.
  𝑬𝑯-is-subuniverse : funext 𝓥 𝓤
   →  {𝑨 𝑩 : Algebra 𝓤 S}(f g : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
  𝑬𝑯-is-subuniverse fe {𝑨 = 𝑨} {𝑩 = 𝑩} f g =
   mksub (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} f g)
    λ 𝓸 𝒂 x → 𝑬𝑯-is-closed fe {𝑨 = 𝑨} {𝑩 = 𝑩} f g 𝒂 x

.. _obs 3 in agda:

Homomorphisms
~~~~~~~~~~~~~~

The :numref:`homomorphisms module (Section %s) <homomorphisms module>` formalizes the notion of homomorphism and proves some basic facts about them. Here we show that homomorphisms are determined by their values on a generating set, as stated and proved informally in :numref:`Obs %s <obs 3>`.  This is proved here, and not in :numref:`homomorphisms module` because we need ``Sg`` from the ``subuniverses`` module (see :numref:`subuniverses in agda`).

::

  HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
             (X : Pred ∣ 𝑨 ∣ 𝓤)  (f g : hom 𝑨 𝑩)
   →         (∀ ( x : ∣ 𝑨 ∣ )  →  x ∈ X  →  ∣ f ∣ x ≡ ∣ g ∣ x)
           ---------------------------------------------------
   →        (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ f ∣ a ≡ ∣ g ∣ a)

  HomUnique _ _ _ _ fx≡gx a (var x) = (fx≡gx) a x
  HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
   (f , fhom) (g , ghom) fx≡gx a (app 𝓸 {𝒂} im𝒂⊆SgX) =
    f (Fᴬ 𝓸 𝒂)     ≡⟨ fhom 𝓸 𝒂 ⟩
    Fᴮ 𝓸 (f ∘ 𝒂 )   ≡⟨ ap (Fᴮ 𝓸) (fe induction-hypothesis) ⟩
    Fᴮ 𝓸 (g ∘ 𝒂)    ≡⟨ ( ghom 𝓸 𝒂 )⁻¹ ⟩
    g ( Fᴬ 𝓸 𝒂 )   ∎
   where
    induction-hypothesis =
      λ x → HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
      (f , fhom)(g , ghom) fx≡gx (𝒂 x) ( im𝒂⊆SgX x )

Obs 2.3. If A, B are finite and X generates 𝑨, then ∣Hom(𝑨, 𝑩)∣ ≤ :math:`∣B∣^{∣X∣}`.
Proof. By Obs 2, a hom is uniquely determined by its restriction to a generating set. If X generates 𝑨, then since there are exactly |B|^|X| functions from X to B, the result holds. □

(todo) formalize Obs 2.3.

Obs 2.4. Factorization of homs. (This is proved in the `morphisms` module.)


The closure operators 𝑯, 𝑺, 𝑷
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Fix a signature 𝑆.

Let 𝓚 be a class of 𝑆-algebras. Define

  * 𝑯(𝓚) = homomorphic images of members of 𝓚;
  * 𝑺(𝓚) = algebras isomorphic to a subalgebra of a member of 𝓚;
  * 𝑷(𝓚) = algebras isomorphic to a direct product of members of 𝓚;

It is not hard to check that 𝑯, 𝑺, and 𝑷 are closure operators. A class 𝓚 of 𝑆-algebras is said to be *closed under the formation of homomorphic images* if 𝑯(𝓚) ⊆ 𝓚. Similarly, 𝓚 is *closed under the formation of subalgebras* (resp., *products*) provided 𝑺(𝓚) ⊆ 𝓚 (resp., 𝑷(𝓚) ⊆ 𝓚).

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class 𝑯(𝓚) (resp., S(𝓚); resp., P(𝓚)) is closed under isomorphism.

The operators 𝑯, 𝑺, and 𝑷 can be composed with one another repeatedly, forming yet more closure operators. If C₁ and C₂ are closure operators on classes of structures, let us say that C₁ ≤ C₂ if for every class 𝓚 we have C₁(𝓚) ⊆ C₂(𝓚).

.. _lem 3.41:

.. proof:lemma:: Lem. 3.41 of :cite:`Bergman:2012`

   𝑺𝑯 ≤ 𝑯𝑺, 𝑷𝑺 ≤ 𝑺𝑷.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let 𝑪 ∈ 𝑺𝑯(𝓚). Then 𝑪 ≤ 𝑩 for some 𝑩 ∈ 𝑯(𝑨), where 𝑨 ∈ 𝓚.  Let θ be such that 𝑩 ≅ 𝑨/θ.  Then 𝑪 is isomorphic to a subalgebra, say, 𝑻, of 𝑨/θ.  By the correspondence theorem, there is a subalgebra 𝑺 ≤ 𝑨 such that 𝑺/θ = 𝑻.  Thus, 𝑪 ∈ 𝑯𝑺(𝑨) ⊆ 𝑯𝑺(𝓚), as desired.

      Let 𝑪 ∈ 𝑷𝑺(𝓚). Then 𝑪 = Π 𝑩ᵢ for some 𝑩ᵢ ≤ 𝑨ᵢ ∈ 𝓚. Clearly, 𝑪 = Π 𝑩ᵢ ≤ Π 𝑨ᵢ, so 𝑪 ∈ 𝑺𝑷(𝓚), as desired. ∎


Varieties
-------------

A class 𝓚 of 𝑆-algebras is called a **variety** if it is closed under each of the closure operators 𝑯, 𝑺, and 𝑷 introduced above; the corresponding closure operator is often denoted 𝕍. Thus, if 𝓚 is a class of similar algebras, then the **variety generated by** 𝓚 is denoted by 𝕍(𝓚) and defined to be the smallest class that contains 𝓚 and is closed under 𝑯, 𝑺, and 𝑷.

.. The class of all varieties of 𝑆-algebras is ordered by inclusion, and closed under arbitrary intersection; thus, the class of varieties is a complete lattice.

We would like to know how to construct 𝕍(𝓚) directly from 𝓚, but it's not immediately obvious how many times we would have to apply the operators 𝑯, 𝑺, 𝑷 before the result stabilizes to form a variety---the **variety generated by** 𝓚.  Fortunately, Garrett Birkhoff proved that if we apply the operators in the correct order, then it suffices to apply each one only once.

.. proof:theorem:: Thm 3.43 of :cite:`Bergman:2012`

   𝕍 = 𝑯𝑺𝑷.

   .. container:: toggle

      .. container:: header

         *Proof*.

      Let 𝓚 be a class of algebras. To see that 𝑯𝑺𝑷(𝓚) is a variety, we use :numref:`Lemma %s <lem 3.41>` to compute 𝑯(𝑯𝑺𝑷) = 𝑯𝑺𝑷, 𝑺(𝑯𝑺𝑷) ≤ 𝑯𝑺²𝑷 = 𝑯𝑺𝑷, P(𝑯𝑺𝑷) ≤ 𝑯𝑺𝑷² = 𝑯𝑺𝑷. Thus 𝑯𝑺𝑷 ≥ 𝕍.

      On the other hand, 𝑯𝑺𝑷(𝓚) ⊆ 𝑯𝑺𝑷(𝕍(𝓚)) = 𝕍(𝓚) so 𝑯𝑺𝑷 ≤ 𝕍.

Equational classes
~~~~~~~~~~~~~~~~~~~~~~

In his treatment of Birhoff's HSP theorem, Cliff Bergman (at the start of Section 4.4 of his universal algebra textbook :cite:`Bergman:2012`) proclaims, "Now, finally, we can formalize the idea we have been using since the first page of this text."  He then proceeds to define **identities of terms** as follows (paraphrasing for notational consistency):

Let 𝑆 be a signature.  An **identity** or **equation** in 𝑆 is an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝔉. If 𝑨 is an 𝑆-algebra we say that 𝑨 **satisfies** 𝑝 ≈ 𝑞 if 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨.  In this  situation,  we  write 𝑨 ⊧ 𝑝 ≈ 𝑞.

If 𝓚 is a class of 𝑆-algebras, we write 𝓚 ⊧ 𝑝 ≋ 𝑞 if, for every 𝑨 ∈ 𝓚, 𝑨 ⊧ 𝑝 ≈ 𝑞. Finally, if 𝓔 is a set of equations, we write 𝓚 ⊨ 𝓔 if every member of 𝓚 satisfies every member of 𝓔.

We formalize these notions in Agda as follows.

::

  _⊧_≈_ : {X : 𝓧 ̇ } → Algebra 𝓤 S
   →      Term{X = X} → Term → 𝓧 ⊔ 𝓤 ̇

  𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

  _⊧_≋_ : {X : 𝓧 ̇ } → Pred (Algebra 𝓤 S) 𝓦
   →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇

  _⊧_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊧ p ≈ q

Identities are compatible with the formation of subalgebras, homomorphic images and products. More precisely,
for every class 𝒦 of structures, each of the classes 𝑺(𝒦), 𝑯(𝒦), 𝑷(𝒦), 𝕍(𝒦) satisfies the same set of identities as does 𝒦.

We formalize the notion of closure under the taking of homomorphic images in the `morphisms` module.  Here we will formalize closure under the taking of products and subuniverses, and prove that these closures preserve identities.

.. _obs 13 in agda:

Identities in products
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let ℙ (𝓚) denote the class of algebras isomorphic to a direct product of members of 𝓚.

::

  ℙ-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ) )
   →      (𝓘 : Universe )  ( I : 𝓘 ̇ )  ( 𝓐 : I → Algebra 𝓘 S )
   →      (( i : I ) → 𝓐 i ∈ 𝓛𝓚 𝓘 ) → 𝓘 ⁺ ̇
  ℙ-closed 𝓛𝓚 = λ 𝓘 I 𝓐 𝓐i∈𝓛𝓚 →  Π' 𝓐  ∈ ( 𝓛𝓚 𝓘 )

  module _
    (gfe : global-dfunext)
    (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))) { X : 𝓧 ̇ } where

    products-preserve-identities : (p q : Term{X = X})
          (I : 𝓤 ̇ ) (𝓐 : I → Algebra 𝓤 S)
     →    𝓚 ⊧ p ≋ q  →  ((i : I) → 𝓐 i ∈ 𝓚)
     →    Π' 𝓐 ⊧ p ≈ q
    products-preserve-identities p q I 𝓐 𝓚⊧p≋q all𝓐i∈𝓚 = γ
     where
      all𝓐⊧p≈q : ∀ i → (𝓐 i) ⊧ p ≈ q
      all𝓐⊧p≈q i = 𝓚⊧p≋q (all𝓐i∈𝓚 i)

      γ : (p ̇ Π' 𝓐) ≡ (q ̇ Π' 𝓐)
      γ = gfe λ 𝒂 →
       (p ̇ Π' 𝓐) 𝒂
         ≡⟨ interp-prod gfe p 𝓐 𝒂 ⟩
       (λ i → ((p ̇ (𝓐 i)) (λ x → (𝒂 x) i)))
         ≡⟨ gfe (λ i → cong-app (all𝓐⊧p≈q i) (λ x → (𝒂 x) i)) ⟩
       (λ i → ((q ̇ (𝓐 i)) (λ x → (𝒂 x) i)))
         ≡⟨ (interp-prod gfe q 𝓐 𝒂)⁻¹ ⟩
       (q ̇ Π' 𝓐) 𝒂
         ∎



Identities in subalgebras
~~~~~~~~~~~~~~~~~~~~~~~~~~

Let 𝑺(𝓚) denote the class of algebras isomorphic to a subalgebra of a member of 𝓚. We show that every term equation, 𝑝 ≈ 𝑞, that is satisfied by all 𝑨 ∈ 𝓚 is also satisfied by all 𝑩 ∈ 𝑺(𝓚).

::

  _is-subalgebra-of-class_ : {𝓤 : Universe}(𝑩 : Algebra 𝓤 S)
   →                         Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  𝑩 is-subalgebra-of-class 𝓚 =
   Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × (𝑩 is-subalgebra-of 𝑨)

  module _
   (𝓚 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ))
   (𝓚' : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))){X : 𝓧 ̇ }
   (𝓤★ : Univalence) where

   gfe : global-dfunext
   gfe = univalence-gives-global-dfunext 𝓤★

   SubalgebrasOfClass : Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   SubalgebrasOfClass 𝓚 =
    Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × Subalgebra{𝑨 = 𝑨} 𝓤★

   𝕊-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
    →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   𝕊-closed 𝓛𝓚 =
    λ 𝓤 𝑩 → (𝑩 is-subalgebra-of-class (𝓛𝓚 𝓤)) → (𝑩 ∈ 𝓛𝓚 𝓤)

   subalgebras-preserve-identities : (p q : Term{X = X})
    →  (𝓚 ⊧ p ≋ q) → (SAK : SubalgebrasOfClass 𝓚)
    →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q
   subalgebras-preserve-identities p q 𝓚⊧p≋q SAK = γ
    where

     𝑨 : Algebra 𝓤 S
     𝑨 = ∣ SAK ∣

     𝑨∈𝓚 : 𝑨 ∈ 𝓚
     𝑨∈𝓚 = ∣ pr₂ SAK ∣

     𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
     𝑨⊧p≈q = 𝓚⊧p≋q 𝑨∈𝓚

     subalg : Subalgebra{𝑨 = 𝑨} 𝓤★
     subalg = ∥ pr₂ SAK ∥

     𝑩 : Algebra 𝓤 S
     𝑩 = pr₁ subalg

     h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
     h = ∣ pr₂ subalg ∣

     h-emb : is-embedding h
     h-emb = pr₁ ∥ pr₂ subalg ∥

     h-hom : is-homomorphism 𝑩 𝑨 h
     h-hom = pr₂ ∥ pr₂ subalg ∥

     ξ : (𝒃 : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) 𝒃) ≡ h ((q ̇ 𝑩) 𝒃)
     ξ 𝒃 =
      h ((p ̇ 𝑩) 𝒃)  ≡⟨ comm-hom-term' gfe 𝑩 𝑨 (h , h-hom) p 𝒃 ⟩
      (p ̇ 𝑨)(h ∘ 𝒃) ≡⟨ intensionality 𝑨⊧p≈q (h ∘ 𝒃) ⟩
      (q ̇ 𝑨)(h ∘ 𝒃) ≡⟨ (comm-hom-term' gfe 𝑩 𝑨 (h , h-hom) q 𝒃)⁻¹ ⟩
      h ((q ̇ 𝑩) 𝒃)  ∎

     hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
     hlc hb≡hb' = (embeddings-are-lc h h-emb) hb≡hb'

     γ : 𝑩 ⊧ p ≈ q
     γ = gfe λ 𝒃 → hlc (ξ 𝒃)


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

------------------

.. include:: hyperlink_references.rst

