.. File      : homomorphisms.lagda.rst
.. Author    : William DeMeo and Siva Somayyajula
.. Date      : 20 Feb 2020
.. Updated   : 21 Jul 2020
.. COPYRIGHT : (c) 2020 William DeMeo


.. _homomorphisms in agda:

========================
Homomorphisms in Agda
========================

This chapter describes the `homomorphisms module`_ of the `agda-ualib`_.

Preliminaries
-------------

As usual, we start with the imports we will need below.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import prelude
  open import basic using (Signature; Algebra; Op; _̂_)
  open import relations using (ker; ker-pred; Rel; 𝟎; con; _//_)

.. _homomorphisms extensionally:

Homomorphisms extensionally
---------------------------

We start the ``homomorphisms`` module with a fixed signature ``𝑆``.

::

  module homomorphisms {𝑆 : Signature 𝓞 𝓥} where


Our implementation of the notion of homomorphisms in the agda-ualib_ is an `extensional` one.  What this means will become clear once we have presented the definitions (cf. :ref:`Homomorphisms intensionally <homomorphisms intensionally>`).

Here we say what it means for an operation 𝑓, interpreted in the algebras 𝑨 and 𝑩, to commute with a function :math:`g : A → B`.

::

  op_interpreted-in_and_commutes-with :
   (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g =
   ∀( 𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣ ) → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)

  all-ops-in_and_commute-with :
   (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
    →   (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  all-ops-in 𝑨 and 𝑩 commute-with g = ∀ (𝑓 : ∣ 𝑆 ∣)
   → op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g

  is-homomorphism : (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
   →                (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  is-homomorphism 𝑨 𝑩 g =
   all-ops-in 𝑨 and 𝑩 commute-with g

And now we define the type of homomorphisms.

::

  hom : Algebra 𝓤 𝑆 → Algebra 𝓦 𝑆  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
  hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

An example of such a homomorphism is the identity map.

::

  𝒾𝒹 :  (A : Algebra 𝓤 𝑆) → hom A A
  𝒾𝒹 _ = (λ x → x) , λ _ _ → refl _


.. _obs 2 in agda:

Compositions of homomorphisms
--------------------------------

As we asserted in :numref:`Obs %s <obs 2>`, the composition of homomorphisms is again a homomorphism.

::

  HCompClosed : {𝑨 : Algebra 𝓤 𝑆}
                {𝑩 : Algebra 𝓦 𝑆}
                {𝑪 : Algebra 𝓣 𝑆}
   →            hom 𝑨 𝑩   →   hom 𝑩 𝑪
               ------------------------
   →                   hom 𝑨 𝑪

  HCompClosed {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪}
   (g , ghom) (h , hhom) = h ∘ g , γ
    where
     γ : (𝑓 : ∣ 𝑆 ∣) (𝒂 : ∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣)
      →  (h ∘ g) ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ 𝒂)

     γ 𝑓 𝒂 = (h ∘ g) ((𝑓 ̂ 𝑨) 𝒂) ≡⟨ ap h (ghom 𝑓 𝒂) ⟩
            h ((𝑓 ̂ 𝑩)(g ∘ 𝒂))  ≡⟨ hhom 𝑓 (g ∘ 𝒂) ⟩
            (𝑓 ̂ 𝑪)(h ∘ g ∘ 𝒂)     ∎

  --Alternative notation for hom composition
  module _ {𝑨 : Algebra 𝓤 𝑆}
           {𝑩 : Algebra 𝓦 𝑆}
           {𝑪 : Algebra 𝓣 𝑆} where

   _>>>_ : hom 𝑨 𝑩  → hom 𝑩 𝑪 → hom 𝑨 𝑪

   (g , ghom) >>> (h , hhom) = h ∘ g , γ
    where
     γ :      (𝑓 : ∣ 𝑆 ∣ ) → (𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)
          -------------------------------------------
      →    (h ∘ g) ((𝑓 ̂ 𝑨) 𝒂)  ≡  (𝑓 ̂ 𝑪)(h ∘ g ∘ 𝒂)

     γ 𝑓 𝒂 =
      (h ∘ g)((𝑓 ̂ 𝑨) 𝒂)  ≡⟨ ap (λ - → h -)(ghom 𝑓 𝒂) ⟩
      h ((𝑓 ̂ 𝑩) (g ∘ 𝒂)) ≡⟨ hhom 𝑓 (g ∘ 𝒂) ⟩
      (𝑓 ̂ 𝑪) (h ∘ g ∘ 𝒂)  ∎


.. _obs 5 in agda:

Factorization of homomorphisms
-----------------------------------

As we saw in :numref:`Obs %s <obs 5>`, if

* ``g : hom 𝑨 𝑩``,
* ``h : hom 𝑨 𝑪``,
* ``h`` is surjective, and
* ``ker h ⊆ ker g``,

then there exists ``ϕ : hom 𝑪 𝑩`` such that ``g = ϕ ∘ h``, that is, such that the following diagram commutes;

.. code-block::

        𝑨---- h -->>𝑪
         \         /
          \       /
         g \     / ∃ϕ
            \   /
             \ /
              V
              𝑩

We now formalize the statement and proof of this basic fact. (Notice that the proof is fully constructive.)

::

  homFactor : funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
              (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
   →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
             ---------------------------------------------
   →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

  homFactor fe {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪}
   (g , ghom) (h , hhom) Kh⊆Kg hEpic = (ϕ , ϕIsHomCB) , g≡ϕ∘h
    where
     hInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
     hInv = λ c → (EpicInv h hEpic) c

     ϕ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
     ϕ = λ c → g ( hInv c )

     ξ : (x : ∣ 𝑨 ∣) → ker-pred h (x , hInv (h x))
     ξ x =  ( cong-app (EInvIsRInv fe h hEpic) ( h x ) )⁻¹

     g≡ϕ∘h : g ≡ ϕ ∘ h
     g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

     ζ : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)(x : ∥ 𝑆 ∥ 𝑓)
      →  𝒄 x ≡ (h ∘ hInv)(𝒄 x)

     ζ 𝑓 𝒄 x = (cong-app (EInvIsRInv fe h hEpic) (𝒄 x))⁻¹

     ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)
      →  (λ x → 𝒄 x) ≡ (λ x → h (hInv (𝒄 x)))

     ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EInvIsRInv fe h hEpic)⁻¹

     useker : (𝑓 : ∣ 𝑆 ∣)  (𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)
      → g (hInv (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄)))) ≡ g ((𝑓 ̂ 𝑨) (hInv ∘ 𝒄))

     useker = λ 𝑓 𝒄
      → Kh⊆Kg (cong-app
               (EInvIsRInv fe h hEpic)
               (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))))


     ϕIsHomCB : (𝑓 : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)
      →         ϕ ((𝑓 ̂ 𝑪) 𝒂)  ≡  (𝑓 ̂ 𝑩)(ϕ ∘ 𝒂)

     ϕIsHomCB 𝑓 𝒄 =
      g (hInv ((𝑓 ̂ 𝑪) 𝒄))                ≡⟨ i   ⟩
      g (hInv ((𝑓 ̂ 𝑪) (h ∘ (hInv ∘ 𝒄)))) ≡⟨ ii  ⟩
      g (hInv (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))))   ≡⟨ iii ⟩
      g ((𝑓 ̂ 𝑨) (hInv ∘ 𝒄))              ≡⟨ iv  ⟩
      (𝑓 ̂ 𝑩)(λ x → g (hInv (𝒄 x)))      ∎
      where
       i   = ap (g ∘ hInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
       ii  = ap (λ - → g (hInv -)) (hhom 𝑓 (hInv ∘ 𝒄))⁻¹
       iii = useker 𝑓 𝒄
       iv  = ghom 𝑓 (hInv ∘ 𝒄)

-----------------------------------------

Isomorphism
-----------


For algebras, an isomorphism is simply a homomorphism with a trivial kernel.

::

  module _ {𝓤 : Universe} where

::

   _≅_ : (𝑨 𝑩 : Algebra 𝓤 𝑆) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
   𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) ,
            (∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝒾𝒹 𝑩 ∣) × (∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝒾𝒹 𝑨 ∣)

   is-algebra-iso : {𝑨 𝑩 : Algebra 𝓤 𝑆} (f : hom 𝑨 𝑩) → 𝓤 ⁺ ̇
   is-algebra-iso {𝑨} f = ker ∣ f ∣ ≡ 𝟎 {A = ∣ 𝑨 ∣}

   AlgebraIsos : (𝑨 𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   AlgebraIsos 𝑨 𝑩 = Σ f ꞉ (hom 𝑨 𝑩) , is-algebra-iso {𝑨}{𝑩} f

   _≈_ : Rel (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
   𝑨 ≈ 𝑩 = is-singleton (AlgebraIsos 𝑨 𝑩)


-----------------------------------------------------

.. _types for homomorphic imageshom images:

Types for homomorphic images
-----------------------------

The following seem to be (for our purposes) the two most useful types for representing homomomrphic images of an algebra.

::

  HomImage : {𝑨 : Algebra 𝓤 𝑆}
   (𝑩 : Algebra 𝓤 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓤 ̇

  HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b


  HomImagesOf : {𝓤 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

  HomImagesOf {𝓤} 𝑨 =
    Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
                            is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

Here are some further definitions, derived from the one above, that will come in handy later.

::

  _is-hom-image-of_ : (𝑩 : Algebra 𝓤 𝑆)
    →                (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

  𝑩 is-hom-image-of 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf 𝑨) , 𝑩 ≅ ∣ 𝑪ϕ ∣

  _is-hom-image-of-class_ : {𝓤 : Universe}
   →                       Algebra 𝓤 𝑆
   →                       Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)
   →                       𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

  _is-hom-image-of-class_ {𝓤} 𝑩 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
                             (𝑨 ∈ 𝒦) × (𝑩 is-hom-image-of 𝑨)

  HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

  HomImagesOfClass 𝒦 = Σ 𝑩 ꞉ (Algebra _ 𝑆) ,
                     (𝑩 is-hom-image-of-class 𝒦)

  H : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  H 𝒦 = HomImagesOfClass 𝒦

In the following definition ℒ𝒦 represents a (universe-indexed) collection of classes.

::

  H-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
   →         (𝓤 : Universe) → Algebra 𝓤 𝑆
   →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

  H-closed ℒ𝒦 =
   λ 𝓤 𝑩 → _is-hom-image-of-class_ {𝓤 = 𝓤} 𝑩 (ℒ𝒦 𝓤) → 𝑩 ∈ (ℒ𝒦 𝓤)

------------------------------------------

Unicode Hints
---------------

Table of some special characters used in the `homomorphisms module`_.

  +--------+------------------------+
  | To get | Type                   |
  +--------+------------------------+
  | 𝒂, 𝒃   | ``\MIa``, ``\MIb``     |
  +--------+------------------------+
  | 𝑓 ̂ 𝑨  |  ``\Mif \^ \MIA``      |
  +--------+------------------------+
  | ≅      | ``≅`` or ``\cong``     |
  +--------+------------------------+
  | ∘      | ``\comp`` or ``\circ`` |
  +--------+------------------------+
  | 𝒾𝒹     | ``\Mci\Mcd``           |
  +--------+------------------------+
  | ℒ𝒦     | ``\McL\McK``           |
  +--------+------------------------+
  | ϕ      | ``\phi``               |
  +--------+------------------------+

For a more complete list of symbols used in the agda-ualib_, see :numref:`unicode hints`.

Emacs commands for retrieving information about characters or the input method:

  * ``M-x describe-char`` (or ``M-m h d c``) with the cursor on the character of interest

  * ``M-x desscribe-input-method`` (or ``C-h I``) (for a list of unicode characters available in agda2-mode_)

------------------

.. include:: hyperlink_references.rst

