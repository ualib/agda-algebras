.. FILE      : terms.lagda.rst
.. AUTHOR    : William DeMeo and Siva Somayyajula
.. DATE      : 20 Feb 2020
.. UPDATE    : 21 Jul 2020
.. COPYRIGHT : (c) 2020 William DeMeo


.. _terms in agda:

===============
Terms in Agda
===============

This chapter describes the `terms module`_ of the `agda-ualib`_.

------------------------------------------

.. _types for terms:

Types for terms
------------------------

We developed the notion of a term in a signature informally in :numref:`terms`.  Here we formalize this concept in an Agda module called `terms <terms module>`_.

We start by declaring the module and importing the required dependencies.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import basic

  module terms {𝑆 : Signature 𝓞 𝓥} where

  open import congruences
  open import homomorphisms {𝑆 = 𝑆}
  open import prelude using
   (intensionality; global-dfunext; 𝓇ℯ𝒻𝓁; pr₂; Inv; InvIsInv;
    eq; _∙_; fst; snd) public

Next, we define a datatype called ``Term`` which, not surprisingly, represents the type of terms.  The type ``X :  𝒰 ̇`` represents an arbitrary collection of "variables."

::

  data Term {X : 𝓤 ̇}  :  𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇  where
    generator : X → Term {X = X}
    node : (f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term {X = X}) → Term

  open Term

The term algebra 𝑻(X)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The term algebra was described informally in :numref:`terms`.  We denote this important algebra by 𝑻(X) and we implement it in Agda as follows.

::

  --The term algebra 𝑻(X).
  𝑻 : 𝓤 ̇ → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤) 𝑆
  𝑻 X = Term{X = X} , node

  term-op : {X : 𝓤 ̇}(f : ∣ 𝑆 ∣)(args : ∥ 𝑆 ∥ f → Term {X = X}) → Term
  term-op f args = node f args


-----------------------------------------------

.. _obs 9 in agda:

The universal property
----------------------

We prove

  #. every map ``h : 𝑋 → ∣ 𝑨 ∣`` lifts to a homomorphism from 𝑻(X) to 𝑨, and
  #. the induced homomorphism is unique.

::

  module _ {𝑨 : Algebra 𝓤 𝑆} {X : 𝓤 ̇ } where

First, every map ``X → ∣ 𝑨 ∣`` lifts to a homomorphism.

::

   free-lift : (h : X → ∣ 𝑨 ∣)  →  ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
   free-lift h (generator x) = h x
   free-lift h (node f args) = (f ̂ 𝑨) λ i → free-lift h (args i)

   lift-hom : (h : X → ∣ 𝑨 ∣) →  hom  (𝑻 X) 𝑨
   lift-hom h = free-lift h , λ f a → ap (_ ̂ 𝑨) (refl _)

Next, the lift to (𝑻 X → 𝑨) is unique.

::

   free-unique : funext 𝓥 𝓤 → (g h : hom (𝑻 X) 𝑨)
    →           (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
    →           (t : Term )
               ---------------------------
    →            ∣ g ∣ t ≡ ∣ h ∣ t

   free-unique fe g h p (generator x) = p x
   free-unique fe g h p (node f args) =
    ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
    (f ̂ 𝑨)(λ i → ∣ g ∣ (args i))  ≡⟨ ap (∥ 𝑨 ∥ _) γ ⟩
    (f ̂ 𝑨)(λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
    ∣ h ∣ (node f args)             ∎
     where γ = fe λ i → free-unique fe g h p (args i)

Next we note the easy fact that the lift induced by ``h₀`` agrees with ``h₀`` on ``X`` and that the lift is surjective if the ``h₀`` is.

::

   --lift agrees on X
   lift-agrees-on-X : (h₀ : X → ∣ 𝑨 ∣)(x : X)
                   ------------------------------------
    →               h₀ x ≡ ∣ lift-hom h₀ ∣ (generator x)

   lift-agrees-on-X h₀ x = refl _

   --Of course, the lift of a surjective map is surjective.
   lift-of-epic-is-epic : (h₀ : X → ∣ 𝑨 ∣) →  Epic h₀
                         ---------------------------
    →                     Epic ∣ lift-hom h₀ ∣

   lift-of-epic-is-epic h₀ hE y = γ
    where
     h₀pre : Image h₀ ∋ y
     h₀pre = hE y

     h₀⁻¹y : X
     h₀⁻¹y = Inv h₀ y (hE y)

     η : y ≡ ∣ lift-hom h₀ ∣ (generator h₀⁻¹y)
     η =
      y                               ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
      h₀ h₀⁻¹y                        ≡⟨ lift-agrees-on-X h₀ h₀⁻¹y ⟩
      ∣ lift-hom h₀ ∣ (generator h₀⁻¹y) ∎

     γ : Image ∣ lift-hom h₀ ∣ ∋ y
     γ = eq y (generator h₀⁻¹y) η


----------------------------------------------

.. _interpretation:

Interpretation
--------------

Let ``t : Term`` be a term and ``𝑨`` an 𝑆-algebra. We define the 𝑛-ary operation ``t ̇ 𝑨`` on ``𝑨`` by structural recursion on ``t``.

  #. if ``t = x ∈ X`` (a variable) and ``a : X → ∣ 𝑨 ∣`` is a tuple of elements of ``∣ 𝑨 ∣``, then ``(t ̇ 𝑨) a = a x``.
  #. if ``t = f args``, where ``f ∈ ∣ 𝑆 ∣`` is an op symbol and ``args : ∥ 𝑆 ∥ f → Term`` is an (``∥ 𝑆 ∥ f``)-tuple of terms and ``a : X → ∣ 𝑨 ∣`` is a tuple from ``𝑨``, then ``(t ̇ 𝑨) a = ((f args) ̇ 𝑨) a = (f ̂ 𝑨) λ{ i → ((args i) ̇ 𝑨) a }``

::

  _̇_ : {X : 𝓧 ̇ } → Term{X = X}
   →   (𝑨 : Algebra 𝓤 𝑆) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

  ((generator x)̇ 𝑨) 𝒂 = 𝒂 x

  ((node f args)̇ 𝑨) 𝒂 = (f ̂ 𝑨) λ i → (args i ̇ 𝑨) 𝒂


Next we show that if ``p : ∣ 𝑻(X) ∣`` is a term, then there exists ``𝓅 : ∣ 𝑻(X) ∣`` and ``𝒕 : X → ∣ 𝑻(X) ∣`` such that ``p ≡ (𝓅 ̇ 𝑻(X)) 𝒕``. We prove this fact in the following module:

::

  module _ {X : 𝓤 ̇} {gfe : global-dfunext} where

   term-op-interp : (f : ∣ 𝑆 ∣)
                     {a1 a2 : ∥ 𝑆 ∥ f → Term {X = X}}
    →                a1 ≡ a2
    →                node f a1 ≡ (f ̂ 𝑻(X)) a2
   term-op-interp f {a1}{a2} a1≡a2 = (ap (node f) a1≡a2) ∙ 𝓇ℯ𝒻𝓁

   term-gen : (p : ∣ 𝑻(X) ∣)
    →         Σ 𝓅 ꞉ ∣ 𝑻(X) ∣ , p ≡ (𝓅 ̇ 𝑻(X)) generator

   term-gen (generator x) = (generator x) , 𝓇ℯ𝒻𝓁
   term-gen (node f args) =
     node f (λ i → ∣ term-gen (args i) ∣ ) ,
       term-op-interp f (gfe λ i → ∥ term-gen (args i) ∥)

   tg : (p : ∣ 𝑻(X) ∣) → Σ 𝓅 ꞉ ∣ 𝑻(X) ∣ , p ≡ (𝓅 ̇ 𝑻(X)) generator
   tg p = term-gen p

   term-gen-agreement : (p : ∣ 𝑻(X) ∣)
    →      (p ̇ 𝑻(X)) generator  ≡  (∣ term-gen p ∣ ̇ 𝑻(X)) generator
   term-gen-agreement (generator x) = 𝓇ℯ𝒻𝓁
   term-gen-agreement (node f args) = ap (f ̂ 𝑻 X) (gfe λ x → term-gen-agreement (args x))

   term-agreement : (p : ∣ 𝑻(X) ∣) → p ≡ (p ̇ 𝑻(X)) generator
   term-agreement p = snd (tg p) ∙ (term-gen-agreement p)⁻¹

Next we have some definitions that are sometimes useful when dealing with the interpretations of terms in a product structure.

::

  interp-prod : funext 𝓥 𝓤
   →            {X : 𝓧 ̇}{I : 𝓤 ̇}(p : Term{X = X})
                (𝒜 : I → Algebra 𝓤 𝑆)
                (x : X → ∀ i → ∣ (𝒜 i) ∣)
   →            (p ̇ (⨅ 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

  interp-prod fe (generator x₁) 𝒜 x = refl _

  interp-prod fe (node f t) 𝒜 x =
   let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
    (f ̂ ⨅ 𝒜)(λ x₁ → (t x₁ ̇ ⨅ 𝒜) x)
        ≡⟨ ap (f ̂ ⨅ 𝒜 ) (fe IH) ⟩
    (f ̂ ⨅ 𝒜 )(λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
        ≡⟨ refl _ ⟩
    (λ i₁ → (f ̂ 𝒜 i₁) (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
        ∎

  interp-prod2 : global-dfunext
   →             {X : 𝓧 ̇ }{I : 𝓤 ̇ }
                 (p : Term{X = X}) (𝒜 : I → Algebra 𝓤 𝑆)
    -----------------------------------------------------------
   → (p ̇ ⨅ 𝒜) ≡ λ(args : X → ∣ ⨅ 𝒜 ∣)
                    → (λ i → (p ̇ 𝒜 i)(λ x → args x i))

  interp-prod2 fe (generator x₁) 𝒜 = refl _

  interp-prod2 fe {X = X} (node f t) 𝒜 =
   fe λ (tup : X → ∣ ⨅ 𝒜 ∣) →
    let IH = λ x → interp-prod fe (t x) 𝒜  in
    let tA = λ z → t z ̇ ⨅ 𝒜 in
     (f ̂ ⨅ 𝒜) (λ s → tA s tup)
        ≡⟨ refl _ ⟩
     (f ̂ ⨅ 𝒜) (λ s →  tA s tup)
        ≡⟨ ap (f ̂ ⨅ 𝒜) (fe  λ x → IH x tup) ⟩
     (f ̂ ⨅ 𝒜) (λ s → (λ j → (t s ̇ 𝒜 j)(λ l → tup l j)))
        ≡⟨ refl _ ⟩
     (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ l → tup l i)))
        ∎

-----------------------------------------------

.. _obs 10 in agda:

Compatibility of terms
-------------------------

In this section we present the formal proof of the fact that homomorphisms commute with terms.  More precisely, if 𝑨 and 𝑩 are 𝑆-algebras, h : 𝑨 → 𝑩 a homomorphism, and t a term in the language of 𝑆, then for all a : X → ∣ 𝑨 ∣ we have :math:`h (t^𝑨 a) = t^𝑩 (h ∘ a)`.


.. _obs 11 in agda:

Homomorphisms commute with terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

  comm-hom-term : global-dfunext
   →     {X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
   →     (h : hom 𝑨 𝑩) (t : Term{X = X}) (a : X → ∣ 𝑨 ∣)
         -----------------------------------------------
   →     ∣ h ∣ ((t ̇ 𝑨) a) ≡ (t ̇ 𝑩) (∣ h ∣ ∘ a)

  comm-hom-term fe 𝑨 𝑩 h (generator x) a = refl _

  comm-hom-term fe 𝑨 𝑩 h (node f args) a =
   ∣ h ∣ ((f ̂ 𝑨)  (λ i₁ → (args i₁ ̇ 𝑨) a))
     ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ 𝑨) a ) ⟩
   (f ̂ 𝑩) (λ i₁ →  ∣ h ∣ ((args i₁ ̇ 𝑨) a))
     ≡⟨ ap (_ ̂ 𝑩)(fe (λ i₁ → comm-hom-term fe 𝑨 𝑩 h (args i₁) a))⟩
   (f ̂ 𝑩) (λ r → (args r ̇ 𝑩) (∣ h ∣ ∘ a))
     ∎

Congruences commute with terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Rounding out this chapter is an formal proof of the fact that terms respect congruences.

More precisely, we show that for every term ``t``, every ``θ ∈ Con(𝑨)``, and all tuples ``a, b : 𝑋 → A``, we have ``(∀ i, a(i) θ b(i)) → (t ̇ 𝑨) a θ (t ̇ 𝑨) b.

::

  -- If t : Term, θ : Con 𝑨, then a θ b → t(a) θ t(b)
  compatible-term : {X : 𝓧 ̇}
        (𝑨 : Algebra 𝓤 𝑆) (t : Term{X = X}) (θ : Con 𝑨)
       --------------------------------------------------
   →         compatible-fun (t ̇ 𝑨) ∣ θ ∣

  compatible-term 𝑨 (generator x) θ p = p x

  compatible-term 𝑨 (node f args) θ p =
   pr₂( ∥ θ ∥ ) f λ{x → (compatible-term 𝑨 (args x) θ) p}

(For proof of 3, see `TermImageSub` in the `subuniverses module`_.)



------------------------------------------

Unicode Hints
---------------

Table of some special characters used in the `terms module`_.

  +--------+------------------------+
  | To get | Type                   |
  +--------+------------------------+
  | 𝑻      | ``\MIT``               |
  +--------+------------------------+
  | t ̇ 𝑨  | ``t \^. \MIA``         |
  +--------+------------------------+
  | 𝑓 ̂ 𝑨  |  ``\Mif \^ \MIA``      |
  +--------+------------------------+
  | pr₂    | ``pr\_2``              |
  +--------+------------------------+
  | ∘      | ``\comp`` or ``\circ`` |
  +--------+------------------------+
  | 𝒾𝒹     | ``\Mci\Mcd``           |
  +--------+------------------------+
  | ℒ𝒦     | ``\McL\McK``           |
  +--------+------------------------+
  | ϕ      | ``\phi``               |
  +--------+------------------------+

See :numref:`unicode hints` for a longer list of symbols used in the agda-ualib_, or better yet, use these

  **Emacs commands providing information about special characters/input methods**:

  * ``M-x describe-char`` (or ``M-m h d c``) with the cursor on the character of interest

  * ``M-x describe-input-method`` (or ``C-h I``)

------------------

.. include:: hyperlink_references.rst

