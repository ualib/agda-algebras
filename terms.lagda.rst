.. FILE: terms.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 20 Feb 2020
.. UPDATE: 27 Jun 2020

.. open import UF-Extensionality using (propext; dfunext; funext; _∈_; global-funext; hfunext; intensionality)
.. open import Relation.Unary using (Pred)

.. _types for terms:

===============
Types for Terms
===============

Preliminaries
-------------

As usual, we start with the imports we will need below.

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import prelude
   open import basic using (Signature; Algebra; Π')
   open import homomorphisms using (HOM; Hom; hom)
   open import relations using (Con; compatible-fun)

Terms in Agda
------------------------

We developed the notion of a term in a signature informally in :numref:`terms`.  Here we formalize this concept in an Agda module called ``terms``. We start by defining a datatype called ``Term`` which, not surprisingly, represents the type of terms.

::

   module terms {S : Signature 𝓞 𝓥} where  -- 𝓞 ⊔ 𝓥 ⊔ 𝓤

   module _ where
     data Term {X : 𝓧 ̇}  :  𝓞 ⊔ 𝓥 ⊔ 𝓧 ̇  where
       generator : X → Term {X = X}
       node : ( 𝓸 : ∣ S ∣ )  →  ( 𝒕 : ∥ S ∥ 𝓸 → Term {X = X} )  →  Term {X = X}

     open Term

The term algebra
~~~~~~~~~~~~~~~~~~

The term algebra was described informally in :numref:`terms`.  Here is how we implement this important algebra in Agda.

::

     𝔉 : {X : 𝓧 ̇} → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧) S
     𝔉 {X = X} = Term{X = X} , node

The universal property of 𝔉
~~~~~~~~~~~~~~~~~~~~~~~~~~~

We prove

  #. every `ℎ : X → ∥ 𝑨 ∥  lifts to a hom from 𝔉 to 𝑨.
  #. the induced homomorphism is unique.

::

   module _ {𝑨 : Algebra 𝓤 S} { X : 𝓧 ̇} where

    --1.a. Every map  (X → A)  "lifts".
    free-lift : (h : X → ∣ 𝑨 ∣)  →   ∣ 𝔉 ∣ → ∣ 𝑨 ∣
    free-lift h (generator x) = h x
    free-lift h (node 𝓸 args) = (∥ 𝑨 ∥ 𝓸) λ{i → free-lift  h (args i)}

    --I. Extensional proofs (using hom's)
    --1.b.' The lift is (extensionally) a hom
    lift-hom : (h : X → ∣ 𝑨 ∣) →  hom 𝔉 𝑨
    lift-hom h = free-lift h , λ 𝓸 𝒂 → ap (∥ 𝑨 ∥ _) (refl _)

    --2.' The lift to  (free → A)  is (extensionally) unique.
    free-unique : funext 𝓥 𝓤 → ( f g : hom (𝔉 {X = X}) 𝑨 )
     →             ( ∀ x  →  ∣ f ∣ (generator x) ≡ ∣ g ∣ (generator x) )
     →             (t : Term )
                   ---------------------------
     →              ∣ f ∣ t ≡ ∣ g ∣ t

    free-unique fe f g p (generator x) = p x
    free-unique fe f g p (node 𝓸 args) =
       (∣ f ∣)(node 𝓸 args)            ≡⟨ ∥ f ∥ 𝓸 args ⟩
       (∥ 𝑨 ∥ 𝓸)(λ i → ∣ f ∣ (args i))  ≡⟨ ap (∥ 𝑨 ∥ _) (fe (λ i → free-unique fe f g p (args i))) ⟩
       (∥ 𝑨 ∥ 𝓸)(λ i → ∣ g ∣ (args i))  ≡⟨ (∥ g ∥ 𝓸 args)⁻¹ ⟩
       ∣ g ∣ (node 𝓸 args)             ∎


Intensional proofs
~~~~~~~~~~~~~~~~~~~

Here we use `HOM` instead of `hom`. N.B. using this "intensional" definition of hom, we don't need function extensionality to prove uniqueness of the hom extension.

::

    --1.b. that free-lift is (intensionally) a hom.
    lift-HOM : (h : X → ∣ 𝑨 ∣) →  HOM 𝔉 𝑨
    lift-HOM  h = free-lift h , refl _

    --2. The lift to  (free → A)  is (intensionally) unique.

    free-intensionally-unique : funext 𝓥 𝓤 → ( f g : HOM (𝔉{X = X}) 𝑨 )
     →             ( ∣ f ∣ ∘ generator ) ≡ ( ∣ g ∣ ∘ generator )
     →             (t : Term)
                   --------------------------------
     →              ∣ f ∣ t ≡ ∣ g ∣ t

    free-intensionally-unique fe f g p (generator x) = intensionality p x
    free-intensionally-unique fe f g p (node 𝓸 args) =
       ( ∣ f ∣ )(node 𝓸 args)       ≡⟨ ap (λ - → - 𝓸 args) ∥ f ∥  ⟩
       (∥ 𝑨 ∥ 𝓸) ( ∣ f ∣ ∘ args )   ≡⟨ ap (∥ 𝑨 ∥ _) (fe (λ i → free-intensionally-unique fe f g p (args i)) ) ⟩
       (∥ 𝑨 ∥ 𝓸) ( ∣ g ∣ ∘ args )   ≡⟨ (ap (λ - → - 𝓸 args) ∥ g ∥ ) ⁻¹ ⟩
       ∣ g ∣ (node 𝓸 args)         ∎

Interpretations
-------------------

Syntactic sugar:  `𝓸 ̂ 𝑨  ≡  ⟦ 𝑨 ⟧ 𝓸`

Before proceding, we define some syntactic sugar that allows us to replace `⟦ 𝑨 ⟧ 𝓸` with (the more standard-looking) `𝓸 ̂ 𝑨`.

::

   _̂_ :  (𝓸 : ∣ S ∣ ) → (𝑨 : Algebra 𝓤 S)
    →       ( ∥ S ∥ 𝓸  →  ∣ 𝑨 ∣ ) → ∣ 𝑨 ∣
   𝓸 ̂ 𝑨 = λ x → (∥ 𝑨 ∥ 𝓸) x

We can now write `𝓸 ̂ 𝑨` for the interpretation of the basic operation `𝓸` in the algebra `𝑨`. N.B. below, we will write `𝒕 ̇ 𝑨` for the interpretation of a *term* `𝒕` in `𝑨`.

(todo: probably we should figure out how to use the same notation for both, if possible)

Interpretation of terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(cf Def 4.31 of Bergman)

Let `𝒕 : Term` be a term and `𝑨` an S-algebra. We define the n-ary operation `𝒕 ̇ 𝑨` on `𝑨` by structural recursion on `𝒕`.

  #. if `𝒕 = x ∈ X` (a variable) and `𝒂 : X → ∣ 𝑨 ∣` is a tuple from `A`, then `(t ̇ 𝑨) 𝒂 = 𝒂 x`.
  #. if `𝒕 = 𝓸 args`, where `𝓸 ∈ ∣ S ∣` is an op symbol and `args : ⟦ S ⟧ 𝓸 → Term` is an (`⟦ S ⟧ 𝓸`)-tuple of terms and `𝒂 : X → ∣ A ∣` is a tuple from `A`, then `(𝒕 ̇ 𝑨) 𝒂 = ((𝓸 args) ̇ 𝑨) 𝒂 = (𝓸 ̂ 𝑨) λ{ i → ((args i) ̇ 𝑨) 𝒂 }`

::

   _̇_ : { X : 𝓧 ̇ } → Term{X = X}  → (𝑨 : Algebra 𝓤 S) →  ( X → ∣ 𝑨 ∣ ) → ∣ 𝑨 ∣
   ((generator x)̇ 𝑨) 𝒂 = 𝒂 x
   ((node 𝓸 args)̇ 𝑨) 𝒂 = (𝓸 ̂ 𝑨) λ{x → (args x ̇ 𝑨) 𝒂 }

   𝔉-interp : { X : 𝓧 ̇ } → Term{X = X} →  ( X → Term{X = X} ) → Term{X = X}
   𝔉-interp (generator x) 𝒂 = 𝒂 x
   𝔉-interp (node 𝓸 args) 𝒂 = node 𝓸 (λ (i : ∥ S ∥ 𝓸 ) →   (𝔉-interp (args i) 𝒂) )

   interp-prod : funext 𝓥 𝓤 → { X : 𝓧 ̇}{I : 𝓤 ̇} (p : Term{X = X})  (𝓐 : I → Algebra 𝓤 S) ( x : X → ∀ i → ∣ (𝓐 i) ∣ )
    →              (p ̇ (Π' 𝓐)) x  ≡   (λ i → (p ̇ 𝓐 i) (λ j -> x j i))
   interp-prod fe (generator x₁) 𝓐 x = refl _
   interp-prod fe (node 𝓸 𝒕) 𝓐 x =
     let IH = λ x₁ → interp-prod fe (𝒕 x₁) 𝓐 x in
         ∥ Π' 𝓐 ∥ 𝓸 (λ x₁ → (𝒕 x₁ ̇ Π' 𝓐) x)                         ≡⟨ ap (∥ Π' 𝓐 ∥ 𝓸 ) (fe IH) ⟩
         ∥ Π' 𝓐 ∥ 𝓸 (λ x₁ → (λ i₁ → (𝒕 x₁ ̇ 𝓐 i₁) (λ j₁ → x j₁ i₁))) ≡⟨ refl _ ⟩   -- refl _ ⟩
         (λ i₁ → ∥ 𝓐 i₁ ∥ 𝓸 (λ x₁ → (𝒕 x₁ ̇ 𝓐 i₁) (λ j₁ → x j₁ i₁)))  ∎

   interp-prod2 : global-dfunext → { X : 𝓧 ̇}{I : 𝓤 ̇} (p : Term{X = X}) ( A : I → Algebra 𝓤 S )
    →              (p ̇ Π' A)  ≡  λ (args : X → ∣ Π' A ∣ ) → ( λ ᵢ → (p ̇ A ᵢ ) ( λ x → args x ᵢ ) )
   interp-prod2 fe (generator x₁) A = refl _
   interp-prod2 fe {X = X} (node 𝓸 𝒕) A = fe λ ( tup : X → ∣ Π' A ∣ ) →
     let IH = λ x → interp-prod fe (𝒕 x) A  in
     let tᴬ = λ z → 𝒕 z ̇ Π' A in
       ( 𝓸 ̂ Π' A )  ( λ s → tᴬ s tup )                 ≡⟨ refl _ ⟩
       ∥ Π' A ∥ 𝓸 ( λ s →  tᴬ s tup )                    ≡⟨ ap ( ∥ Π' A ∥ 𝓸 ) (fe  λ x → IH x tup) ⟩
       ∥ Π' A ∥ 𝓸 (λ s → (λ ⱼ → (𝒕 s ̇ A ⱼ ) (λ ℓ → tup ℓ ⱼ )))    ≡⟨ refl _ ⟩
       (λ ᵢ → (𝓸 ̂ A ᵢ ) (λ s → (𝒕 s ̇ A ᵢ ) (λ ℓ → tup ℓ ᵢ )))       ∎

.. _obs 10 agda:

Compatibility of homs and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this section we present the formal proof of the fact that homomorphisms commute with terms.  More precisely, if 𝑨 and 𝑩 are 𝑆-algebras, 𝑓 : 𝑨 → 𝑩 a homomorphism, and 𝑡 a term in the language of 𝑆, then for all 𝒂 : X → ∣ 𝑨 ∣ we have :math:`𝑓 (𝑡^𝑨 𝒂) = 𝑡^𝑩 (𝑓 ∘ 𝒂)`.


::

   -- Proof of 1. (homomorphisms commute with terms).
   comm-hom-term : global-dfunext
    →              {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
                   (g : HOM 𝑨 𝑩) (𝒕 : Term{X = X})
                  ---------------------------------------------
    →              ∣ g ∣ ∘ (𝒕 ̇ 𝑨) ≡ (𝒕 ̇ 𝑩) ∘ (λ 𝒂 → ∣ g ∣ ∘ 𝒂 )
   comm-hom-term gfe 𝑨 𝑩 g (generator x) = refl _
   comm-hom-term gfe {X = X}𝑨 𝑩 g (node 𝓸 args) = γ
    where
     γ : ∣ g ∣ ∘ (λ 𝒂 → (𝓸 ̂ 𝑨) (λ i → (args i ̇ 𝑨) 𝒂))     ≡ (λ 𝒂 → (𝓸 ̂ 𝑩)(λ i → (args i ̇ 𝑩) 𝒂)) ∘ _∘_ ∣ g ∣
     γ =  ∣ g ∣ ∘ (λ 𝒂 → (𝓸 ̂ 𝑨) (λ i → (args i ̇ 𝑨) 𝒂))    ≡⟨ ap (λ - → (λ 𝒂 → - 𝓸 (λ i → (args i ̇ 𝑨) 𝒂))) ∥ g ∥ ⟩
         (λ 𝒂 → (𝓸 ̂ 𝑩)(∣ g ∣ ∘ (λ i →  (args i ̇ 𝑨) 𝒂)))   ≡⟨ refl _ ⟩
         (λ 𝒂 → (𝓸 ̂ 𝑩)(λ i → ∣ g ∣ ((args i ̇ 𝑨) 𝒂)))      ≡⟨ ap (λ - → (λ 𝒂 → (𝓸 ̂ 𝑩)(- 𝒂))) ih ⟩
         ((λ 𝒂 → (𝓸 ̂ 𝑩)(λ i → (args i ̇ 𝑩) 𝒂)) ∘ _∘_ ∣ g ∣) ∎
       where
        IH : (𝒂 : X → ∣ 𝑨 ∣)(i : ∥ S ∥ 𝓸) → ((∣ g ∣ ∘ (args i ̇ 𝑨)) 𝒂) ≡ (((args i ̇ 𝑩) ∘ _∘_ ∣ g ∣) 𝒂)
        IH 𝒂 i = intensionality (comm-hom-term gfe 𝑨 𝑩 g (args i)) 𝒂

        IH' : (i : ∥ S ∥ 𝓸) → ((∣ g ∣ ∘ (args i ̇ 𝑨))) ≡ ((args i ̇ 𝑩) ∘ _∘_ ∣ g ∣)
        IH' i = (comm-hom-term gfe 𝑨 𝑩 g (args i))

        ih : (λ 𝒂 → (λ i → ∣ g ∣ ((args i ̇ 𝑨) 𝒂))) ≡ (λ 𝒂 → (λ i → ((args i ̇ 𝑩) ∘ _∘_ ∣ g ∣) 𝒂))
        ih = gfe λ 𝒂 → gfe λ i → IH 𝒂 i

        ih' : (λ i → ∣ g ∣ ∘ (args i ̇ 𝑨)) ≡ (λ i → ((args i ̇ 𝑩) ∘ _∘_ ∣ g ∣))
        ih' = gfe λ i → IH' i


.. _obs 11 agda:

Compatibility of congruences and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we present an Agda proof of the fact that terms respect congruences. More precisely, we show that for every term 𝑡, every θ ∈ Con(𝑨), and all tuples 𝒂, 𝒃 : 𝑋 → 𝑨, we have (∀ i, 𝒂(i) θ 𝒃(i)) → (t^𝑨 𝒂) θ (t^𝑨 𝒃).

::

   compatible-term : {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 S)
                     ( 𝒕 : Term{X = X} ) (θ : Con 𝑨)
                    ----------------------------------
    →                  compatible-fun (𝒕 ̇ 𝑨) ∣ θ ∣

   compatible-term 𝑨 (generator x) θ p = p x
   compatible-term 𝑨 (node 𝓸 args) θ p = ∥ ∥ θ ∥ ∥ 𝓸 λ{ x → (compatible-term 𝑨 (args x) θ) p }

   -- For proof of 3, see `TermImageSub` in Subuniverse.agda.


Extensional versions
~~~~~~~~~~~~~~~~~~~~~~~~~

::

   -- Proof of 1. (homomorphisms commute with terms).
   comm-hom-term' : global-dfunext --  𝓥 𝓤
    →               {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
    →               (g : hom 𝑨 𝑩) (𝒕 : Term{X = X}) (𝒂 : X → ∣ 𝑨 ∣)
                  --------------------------------------------
    →               ∣ g ∣ ((𝒕 ̇ 𝑨) 𝒂) ≡ (𝒕 ̇ 𝑩) (∣ g ∣ ∘ 𝒂)

   comm-hom-term' fe 𝑨 𝑩 g (generator x) 𝒂 = refl _
   comm-hom-term' fe 𝑨 𝑩 g (node 𝓸 args) 𝒂 =
       ∣ g ∣ ((𝓸 ̂ 𝑨)  (λ i₁ → (args i₁ ̇ 𝑨) 𝒂))     ≡⟨ ∥ g ∥ 𝓸 ( λ r → (args r ̇ 𝑨) 𝒂 ) ⟩
       (𝓸 ̂ 𝑩) ( λ i₁ →  ∣ g ∣ ((args i₁ ̇ 𝑨) 𝒂) )    ≡⟨ ap (_ ̂ 𝑩) ( fe (λ i₁ → comm-hom-term' fe 𝑨 𝑩 g (args i₁) 𝒂) ) ⟩
       (𝓸 ̂ 𝑩) ( λ r → (args r ̇ 𝑩) (∣ g ∣ ∘ 𝒂) )        ∎


   -- Proof of 2.  (If t : Term, θ : Con A, then a θ b  →  t(a) θ t(b). )
   compatible-term' :  {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 S) ( 𝒕 : Term{X = X}  ) (θ : Con 𝑨)
                            ------------------------------------------------------
    →                              compatible-fun (𝒕 ̇ 𝑨) ∣ θ ∣

   compatible-term' 𝑨 (generator x) θ p = p x
   compatible-term' 𝑨 (node 𝓸 args) θ p = ∥ ∥ θ ∥ ∥ 𝓸 λ{ x → (compatible-term' 𝑨 (args x) θ) p }

For proof of 3, see `TermImageSub` in Subuniverse.agda.

..    #. For every subset Y of A,  Sg ( Y ) = { t (a₁, ..., aₙ ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.




------------------

.. include:: hyperlink_references.rst

