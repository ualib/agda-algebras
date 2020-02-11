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

Essential arity
------------------

The definition of arity of an operation or term is a bit nuanced as the next example demonstrates.

.. proof:example:: arity of a term

   Suppose 𝑓 is a binary term, and 𝑝 and 𝑞 are ternary terms.

   What is the arity of the following term?

   .. math:: 𝑡(𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧) = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))
     :label: arity1

   On the face of it, it seems safe to say that 𝑡 has arity 6, since it is expressible as a function
   of 6 variables.

   But what if we decided to throw in some useless (or "dummy") variables, like so,

   .. math:: t'(𝑢', 𝑣', 𝑢, 𝑣, 𝑤, 𝑥, 𝑦, 𝑧, 𝑧') = 𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))?
     :label: arity2

   And what happens if :math:`𝑝(𝑥, 𝑦, 𝑧) = 𝑧`, so that 𝑝 depends on just one of its arguments? Then we could replace it with :math:`𝑝'(𝑧) = 𝑝(𝑥, 𝑦, 𝑧)`, and 𝑡 could be expressed as,

   .. math:: 𝑡''(𝑢, 𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))).
     :label: arity3
	     
   The respective arities of :math:`𝑡, 𝑡'` and :math:`𝑡''` are 6, 9, and 5, yet :eq:`arity1`--:eq:`arity3` merely give three different ways to present the term :math:`𝑓(𝑝(𝑥, 𝑦, 𝑧), 𝑓(𝑤, 𝑥), 𝑞(𝑢, 𝑣, 𝑤))`.
   
As the example demonstrates, the notion of arity of a term is not uniquely defined (modulo equivalence of terms). As such, it is sometimes useful to speak of the **essential arity** of a term, which is defined to be the minimum number of variables required to express that term; it should be clear that this is equal to the number of arguments with respect to which the term is not constant.

.. proof:example:: essential arity of a term

   It is impossible to know the essential arity of a term until we know that of each of its subterms.

   Picking up where we left off in the previous example, suppose 𝑓 depends on both of its arguments and :math:`𝑞(𝑢, 𝑣, 𝑤) = 𝑓(𝑣, 𝑤)`. Then 𝑡 is expressible as

   .. math:: s(𝑣, 𝑤, 𝑥, 𝑧) = 𝑓(𝑝'(𝑧), 𝑓(𝑤, 𝑥), 𝑓(𝑣, 𝑤))

   and we finally see the lower bound on the number of variables required to express 𝑡, namely 4.  Therefore, 𝑡 has essential arity 4.


------------------------------------------------------------------

Interpretation of terms
-----------------------

.. 𝐀 = ⟨𝐴,...⟩ be an algebra
   
.. proof:definition:: cf. 4.31 of Bergman

   Let 𝑿 be an infinite set (of variables), and let 𝑨 = ⟨𝐴,...⟩ be an algebra of signature :math:`S`.

   .. , and let 𝑐 : ω → 𝑿 be an injective function. (We might call 𝑐 a "choice function" or "indexing function".)

   If :math:`t` is a :math:`(ρ t)`-ary term symbol in the signature :math:`S`, and if we select a :math:`(ρ t)`-tuple of variables, say :math:`x : (ρ t) → X`, then the term associated with the symbols :math:`t` and :math:`x` is :math:`t(x)`.

   The **interpretation** of :math:`t(x)` in 𝑨, often denoted by :math:`t^𝑨(x)`, is the :math:`(ρ t)`-ary operation on :math:`A` defined by recursion on the structure of :math:`t`, as follows:

     #. if :math:`t(x)` is simply the variable :math:`x i ∈ X`, and if 𝑎 is a :math:`(ρ t)`-tuple of :math:`A`, then :math:`t^𝑨(a) = a i`; that is, :math:`t^𝑨(a)` is the projection of the input tuple onto its :math:`i`-th coordinate.

     #. if :math:`t = 𝓸 𝑓`, where 𝓸 is a basic operation symbol with interpretation :math:`𝓸^𝑨` in 𝑨 and :math:`𝑓 : (ρ 𝓸) →` Term is a (ρ 𝓸)-tuple of terms, each with interpretation :math:`(𝑓 i)^𝑨`, then :math:`t^𝑨(𝑓)` is :math:`𝓸^𝑨 \bigl( λ (i : ρ 𝓸) . (𝑓 i)^𝑨\bigr)`.


Let's translate this definition into the Agda syntax developed above.

#. If ``t x`` is a variable, say, ``x i : X``, then we define ``(t ̂ A) : (Fin ⟨ S ⟩ₐ tFin ⟦ A ⟧ᵤ -> ⟦ A ⟧ᵤ`` for each ``a : ⟦ A ⟧ᵤ`` by ``(t ̂ A) a = a``.

#. If ``t = 𝓸 𝐟``, where ``𝓸 : ⟨ S ⟩ₒ`` is a basic operation symbol with interpretation ``A ⟦ 𝓸 ⟧`` in 𝚨, and if ``𝐟 : Fin ⟨ S ⟩ₐ 𝓸 -> Term`` is a ``(⟨ S ⟩ₐ 𝓸)``-tuple of terms with interpretations ``(𝐟 i) ̂ A`` for each ``i : ⟨ S ⟩ₐ 𝓸``, then we define

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

