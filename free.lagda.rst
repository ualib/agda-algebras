.. File: free.lagda.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 25 Dec 2019
.. Updated: 29 Jan 2020
.. Note: This was used for the second part of my talk at JMM Special Session.
.. Copyright (c) 2019 William DeMeo

.. _Datatypes for Terms:

Datatypes for Terms 
======================

(The code described in this chapter resides in ``free.agda``.)

As usual, we begin by setting some options and importing a few things from the Agda std lib (as well as our definitions from the ``basic.agda`` file).

.. code-block:: agda
		
    {-# OPTIONS --without-K --exact-split #-}

    open import Level
    open import basic 
    open algebra
    open signature

    module free {S : signature}{X : Set} where

    open import preliminaries  using (_⊎_ ; ∀-extensionality; ∑)
    open import Function using (_∘_)
    open import Relation.Unary
    open import Relation.Binary hiding (Total)
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; sym)
    open Eq.≡-Reasoning
    import Relation.Binary.EqReasoning as EqR

--------------------------------------------

Terms
-------

We define the inductive family of terms in ``signature S`` as follows: 


.. code-block:: agda

    data Term : Set where

      generator : X -> Term

      node : ∀ (𝓸 : ⟨ S ⟩ₒ)
        ->   (Fin (⟨ S ⟩ₐ 𝓸) -> Term)
            -------------------------
	->    Term


-----------------------------------------------

The term algebra
-----------------

Here is a datatype for the term algebra in ``signature S``.

.. code-block:: agda
		
    open Term

    free : algebra S

    free = record { ⟦_⟧ᵤ = Term ; _⟦_⟧ = node }


-----------------------------------------------

The universal property
-----------------------------------

We now come to our first proof.

We wish to show that the term algebra is **aboslutely free**.

That is, we must show

1. every ``h : X -> ⟦ A ⟧ᵤ`` lifts to a hom from ``free`` to ``A``;

2. the induced hom is unique.


Here is the Agda code proving these facts.

1.
   a. Every map  ``(X -> A)``  "lifts".

      .. code-block:: agda
		
          free-lift : {A : algebra  S}
	              (h : X -> ⟦ A ⟧ᵤ)
                    ---------------------
            ->        ⟦ free ⟧ᵤ -> ⟦ A ⟧ᵤ

          free-lift h (generator x) = h x

          free-lift {A} h (node 𝓸 args) =
	    (A ⟦ 𝓸 ⟧) λ{i -> free-lift {A} h (args i)}


   b. The lift is a hom.

      .. code-block:: agda
		
          open Hom

          lift-hom : {A : algebra S}
	             (h : X -> ⟦ A ⟧ᵤ)
                    ------------------
	    ->        Hom free A

          lift-hom {A} h =
            record
              {
              ⟦_⟧ₕ = free-lift {A} h;
              homo = λ args -> refl
              }


2. The lift to  ``(free -> A)``  is unique.

   We need `function extensionality`_ for this, which we import from our ``preliminaries.agda`` file (see the agda-ualib_ gitlab repository).

   .. code-block:: agda

       free-unique : {A : algebra S}
         ->    ( f g : Hom free A )
         ->    ( ∀ x  ->  ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x) )
         ->    (t : Term)
              ---------------------------
         ->    ⟦ f ⟧ₕ t ≡ ⟦ g ⟧ₕ t

       free-unique {A} f g p (generator x) = p x

       free-unique {A} f g p (node 𝓸 args) =
          begin
            ⟦ f ⟧ₕ (node 𝓸 args)
          ≡⟨ homo f args  ⟩
            (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
          ≡⟨ cong ((A ⟦_⟧)_) (∀-extensionality (induct f g p args)) ⟩
            (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
          ≡⟨ sym (homo g args) ⟩
            ⟦ g ⟧ₕ (node 𝓸 args)
          ∎
          where
           induct : {A : algebra S}
             ->     (f g : Hom free A)
             ->     (∀ x -> ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x))
             ->     (args : Fin (⟨ S ⟩ₐ 𝓸) → Term)
             ->     (i : Fin (⟨ S ⟩ₐ 𝓸))
                   --------------------------------------- (IH)
             ->     ⟦ f ⟧ₕ (args i) ≡ ⟦ g ⟧ₕ (args i)
           induct f' g' h' args' i' = free-unique f' g' h' (args' i')


   Now that we have seen exactly where and how induction is used, let's clean up the proof by inserting the induction step within the angle brackets inside the calculational proof.

   .. code-block:: agda

       free-unique : {A : algebra S}
         ->    ( f g : Hom free A )
         ->    ( ∀ x  ->  ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x) )
         ->    (t : Term)
              ---------------------------
         ->    ⟦ f ⟧ₕ t ≡ ⟦ g ⟧ₕ t

       free-unique {A} f g p (generator x) = p x

       free-unique {A} f g p (node 𝓸 args) =
          begin
	    ⟦ f ⟧ₕ (node 𝓸 args)
	  ≡⟨ homo f args  ⟩
	    (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
	  ≡⟨ cong ((A ⟦_⟧)_)
	     ( ∀-extensionality λ i -> free-unique f g p (args i) ) ⟩
	    (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
	  ≡⟨ sym (homo g args) ⟩
	    ⟦ g ⟧ₕ (node 𝓸 args)
	  ∎


----------------------------

Interpretation of a term
-------------------------

**TODO** This section needs to be rewritten.

Given a set ``X`` and an algebra ``𝐀 = ⟨A,...⟩``, we call a function ``ctx : X → A`` a **context**.

.. proof:definition:: cf. 4.31 of Bergman

   Let  and 𝐀 be an algebra of signature :math:`S`.

   Let :math:`t` be an :math:`(ρ t)`-ary term of signature :math:`S`.

   The **interpretation** of :math:`t` in 𝐀---often denoted in the literature by :math:`t^𝚨`---is the :math:`(ρ t)`-ary operation on :math:`A` defined by recursion on the structure of :math:`t`, as follows:

     #. if :math:`t` is the variable :math:`x ∈ X`, then in the context ``ctx`` we take :math:`t^𝚨` to be the projection onto the coordinate containing ``ctx x``.

     #. if :math:`t = 𝓸 𝐟`, where 𝓸 is a basic operation symbol with interpretation :math:`𝓸^𝚨` in 𝚨 and :math:`𝐟 : (ρ 𝓸) →` Term is a (ρ 𝓸)-tuple of terms, each with interpretation :math:`(𝐟 i)^𝚨`, then we take :math:`t^𝐀(𝐟)` to be :math:`𝓸^𝐀 \bigl( λ \{ (i : ρ 𝓸) . (𝐟 i)^𝐀\}\bigr)`.


Let's translate this definition into the Agda syntax developed above.

#. If ``t`` is a variable, say, ``x : X``, then we define ``(t ̂ A) : ⟦ A ⟧ᵤ -> ⟦ A ⟧ᵤ`` for each ``a : ⟦ A ⟧ᵤ`` by ``(t ̂ A) a = a``.

#. If ``t = 𝓸 𝐟``, where ``𝓸 : ⟨ S ⟩ₒ`` is a basic operation symbol with interpretation ``A ⟦ 𝓸 ⟧`` in 𝚨, and if ``𝐟 : ⟨ S ⟩ₐ 𝓸 -> Term`` is a ``(⟨ S ⟩ₐ 𝓸)``-tuple of terms with interpretations ``(𝐟 i) ̂ A`` for each ``i : ⟨ S ⟩ₐ 𝓸``, then we define

   ``(t ̂ A) = (𝓸 𝐟) ̂ A = (A ⟦ 𝓸 ⟧) λ{i -> (𝐟 i) ̂ A}``

Here's how we could implement this in Agda.


.. code-block:: agda

    _̂_ : Term -> (A : algebra S) -> (X -> ⟦ A ⟧ᵤ) -> ⟦ A ⟧ᵤ

    ((generator x) ̂ A) tup = tup x

    ((node 𝓸 args) ̂ A) tup = (A ⟦ 𝓸 ⟧) λ{i -> (args i ̂ A) tup }


Recall (:cite:`Bergman:2012` Theorem 4.32),

.. proof:theorem::

   Let 𝔸 and 𝔹be algebras of signature :math:`S`. The following hold:

     #. For every :math:`n`-ary term :math:`t` and homomorphism :math:`g : A \to B`, we have

	.. math:: g(tᴬ(a₁,...,aₙ)) = tᴮ(g(a₁),...,g(aₙ)).

     #. For every term :math:`t ∈ T(X)` and every :math:`θ ∈ Con()`, we have

	.. math:: a θ b \implies t(a) θ t(b).

     #. For every subset :math:`Y` of :math:`A`, we have

       .. math:: \mathrm{Sg}(Y) = \{ t(a₁,\dots ,aₙ) : t ∈ T(Xₙ), n < ω, \text{ and } aᵢ ∈ Y, for i ≤ n\}.

Rewriting the three assertions in Agda syntax, 

     #. For every ``n``-ary term ``t`` and homomorphism ``g : hom A B``, we have

	  ``⟦ g ⟧ₕ ((t ̂ A) a)  ≡ (t ̂ B)(⟦ g ⟧ₕ ∘ a)``

	for each ``n``-tuple ``a``.

     #. For every term ``t ∈ T(X)`` and congruence ``θ ∈ con A``, we have

	  ``⟦ θ ⟧ᵣ a b => ⟦ θ ⟧ᵣ t(a) t(b)``.

     #. For every subset ``Y`` of ``A``, we have

	  ``Sg(Y) = {(t ̂ A) a : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y (∀ i ≤ n)}``.

Let's prove the first of the assertions in Agda.

**Claim**. Homomorphisms commute with terms.

   .. code-block:: agda

      comm-hom-term : {A B : algebra S}
        ->            (g : Hom A B) -> (t : Term)
	->            (tup : X -> ⟦ A ⟧ᵤ)
               ----------------------------------------------
	->       ⟦ g ⟧ₕ ((t ̂ A) tup) ≡ (t ̂ B) (⟦ g ⟧ₕ ∘ tup)

      comm-hom-term g (generator x) tup = refl

      comm-hom-term {A} {B} g (node 𝓸 args) tup =  

      -- Goal: ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup })) ≡
      --  (B ⟦ 𝓸 ⟧) (λ { i → (args i ̂ B) ((λ {.x} → ⟦ g ⟧ₕ) ∘ tup) })

        begin

	  ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup }))

	≡⟨ homo g (λ { i → (args i ̂ A) tup }) ⟩

	  (B ⟦ 𝓸 ⟧) (λ { i → ⟦ g ⟧ₕ ((args i ̂ A) tup) })

	≡⟨ cong ((B ⟦_⟧)_) (∀-extensionality (induct g tup args)) ⟩

	  (B ⟦ 𝓸 ⟧) (λ { i → (args i ̂ B) (⟦ g ⟧ₕ ∘ tup)})

	∎

	where

	  induct : {A B : algebra S}
	    ->     (g : Hom A B)
            ->     (tup : X -> ⟦ A ⟧ᵤ)
            ->     (args : ⟨ S ⟩ₐ 𝓸 → Term)
            ->     (i : ⟨ S ⟩ₐ 𝓸)
               ---------------------------------------------------------
            ->    ⟦ g ⟧ₕ ((args i ̂ A) tup) ≡ (args i ̂ B) (⟦ g ⟧ₕ ∘ tup)

	  induct g' tup' args' i' = comm-hom-term g' (args' i') tup' 


   Now that we have seen exactly where and how induction is used, let's clean up the proof by inserting the induction step within the angle brackets inside the calculational proof.

.. code-block:: agda

   comm-hom-term : {A B : algebra S}
     ->    (g : hom A B) -> (t : Term)
     ->    (tup : X -> ⟦ A ⟧ᵤ)
          ------------------------------
     ->     ⟦ g ⟧ₕ ((t ̂ A) tup) ≡ (t ̂ B) (⟦ g ⟧ₕ ∘ tup)

   comm-hom-term g (generator x) tup = refl
   comm-hom-term {A} {B} g (node 𝓸 args) tup =  
   -- Goal: ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup })) ≡
   --       (B ⟦ 𝓸 ⟧) (λ { i → (args i ̂ B) ((λ {.x} → ⟦ g ⟧ₕ) ∘ tup) })
     begin
       ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup }))
     ≡⟨ homo g ( λ i → (args i ̂ A) tup )⟩
       (B ⟦ 𝓸 ⟧) ( λ i → ⟦ g ⟧ₕ ((args i ̂ A) tup) )
     ≡⟨ cong ((B ⟦_⟧)_)
        ( ∀-extensionality  λ i -> comm-hom-term g (args i) tup  ) ⟩
       (B ⟦ 𝓸 ⟧) ( λ i → (args i ̂ B) (⟦ g ⟧ₕ ∘ tup) )
     ∎

-----------------------------------------------

.. include:: hyperlink_references.rst

