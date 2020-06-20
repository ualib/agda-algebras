.. FILE: UF-Birkhoff.agda
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 27 Oct 2019
.. UPDATE: 20 Jun 2020
.. COPYRIGHT: (c) 2019 William DeMeo and Siva Somayyajula

.. open import UF-Extensionality using (funext; global-funext; EInvIsRInv; dfunext; intensionality)

.. _birkhoffs-hsp-theorem:

=============================
Birkhoff's HSP theorem
=============================

The following is Birkhoff's celebrated HSP theorem. The proof we give here (and formalize in Agda) is the same one that appears in Cliff Bergman's excellent textbook on universal algebra (see :cite:`Bergman:2012`, Thm 4.41).

.. proof:theorem:: 

   Every variety is an equational class.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*.
      
      Let 𝒲 be a variety. We must find a set of equations that axiomatizes 𝒲. The obvious choice is to use the set of all equations that hold in 𝒲.

      To this end, take :math:`Σ = \mathsf{Th}(𝒲)`. Let :math:`𝒲^† := \mathsf{Mod}(Σ)`.  
  
      Clearly, :math:`𝒲 ⊆ 𝒲^†`. We shall prove the reverse inclusion.

      Let :math:`𝔸 ∈ 𝒲^†` and :math:`Y` a set of cardinality :math:`\max(|A|, ω)`. *Choose* a surjection :math:`h_0 : Y → A`. [1]_
  
      By :numref:`Obs %s <obs 6>` (which is essentially Thm. 4.21 of :cite:`Bergman:2012`), :math:`h_0` extends to an epimorphism :math:`h: 𝕋(Y) → 𝔸`.

      Furthermore, since :math:`𝔽_𝒲(Y) = 𝕋(Y)/Θ_𝒲`, there is an epimorphism :math:`g: 𝕋(Y) → 𝔽_𝒲`. [2]_

      We claim that :math:`\ker g ⊆ \ker h`. If the claim is true, then by :numref:`Obs %s <obs 4>` there is a map :math:`f: 𝔽_𝒲(Y) → 𝔸` such that :math:`f ∘ g = h`.
   
      Since :math:`h` is epic, so is :math:`f`. Hence :math:`𝔸 ∈ 𝖧 (𝔽_{𝒲}(Y)) ⊆ 𝒲` completing the proof. ☐

In the ``birkhoff`` module of ``agda-ualib`` we formalize the above proof.  The sections below contain literate Agda code that implement and describe our formalization of Birkhoff's HSP theorem.


Preliminaries
-----------------

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import prelude
   open import basic using (Signature; Algebra; Π')
   open import morphisms using (HOM; Hom; hom)
   open import relations using (ker-pred; Rel)
   open import congruences using (con; _//_)
   open import terms using (Term; 𝔉; _̇_; comm-hom-term'; _⊢_≈_; _⊢_≋_; 𝔉-interp )
   open import subuniverses using (Subuniverse; mksub; Sg; _is-subalgebra-of_; var; app)

   module birkhoff  {S : Signature 𝓞 𝓥}  where

   ----------------------------------------------------------------------------------------
   --Theories and Models.
   -- _⊢_≈_ : Algebra 𝓤 S → Term → Term → 𝓤 ̇
   -- 𝑨 ⊢ p ≈ q = p ̇ 𝑨 ≡ q ̇ 𝑨

   -- _⊢_≋_ : Pred (Algebra 𝓤 S) 𝓦 → Term {X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇
   -- _⊢_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊢ p ≈ q

Equalizers
-------------

::

   --...of functions
   𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (f g : A → B) → Pred A 𝓦
   𝑬 f g x = f x ≡ g x

   --..of homs  (see also definition 𝓔 in UF-Hom)
   𝑬𝑯 : {A B : Algebra 𝓤 S} (f g : hom A B) → Pred ∣ A ∣ 𝓤
   𝑬𝑯 f g x = ∣ f ∣ x ≡ ∣ g ∣ x

   𝑬𝑯-is-closed : funext 𝓥 𝓤 → {𝓸 : ∣ S ∣ } {𝑨 𝑩 : Algebra 𝓤 S}
                 (f g : hom 𝑨 𝑩)     (𝒂 : ( ∥ S ∥ 𝓸 )  → ∣ 𝑨 ∣ )
    →          ( ( x : ∥ S ∥ 𝓸 ) → ( 𝒂 x ) ∈ ( 𝑬𝑯 {A = 𝑨} {B = 𝑩} f g ) )
               ----------------------------------------
    →          ∣ f ∣ ( ∥ 𝑨 ∥ 𝓸 𝒂 ) ≡ ∣ g ∣ ( ∥ 𝑨 ∥ 𝓸 𝒂 )

   𝑬𝑯-is-closed fe {𝓸 = 𝓸} {𝑨 = A , Fᴬ} {𝑩 = B , Fᴮ} (f , fhom) (g , ghom) 𝒂 p =
      f ( Fᴬ 𝓸 𝒂)                     ≡⟨ fhom 𝓸 𝒂 ⟩
      Fᴮ 𝓸 ( λ i  →  f ( 𝒂 i ) )    ≡⟨ ap ( Fᴮ _ ) ( fe p ) ⟩
      Fᴮ 𝓸 ( λ i →  g  ( 𝒂 i ) )    ≡⟨ (ghom 𝓸 𝒂)⁻¹ ⟩
      g ( Fᴬ 𝓸 𝒂)                     ∎

   -- Obs 2.0. Equalizer of homs is a subuniverse.
   -- Equalizer `𝑬𝑯 f g`  of `f g : Hom 𝑨 𝑩` is a subuniverse of 𝑨.
   𝑬𝑯-is-subuniverse :  funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S} (f g : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
   𝑬𝑯-is-subuniverse fe {𝑨 = 𝑨} {𝑩 = 𝑩} f g =
    mksub ( 𝑬𝑯 {A = 𝑨}{B = 𝑩} f g ) λ 𝓸 𝒂 x → 𝑬𝑯-is-closed fe {𝑨 = 𝑨} {𝑩 = 𝑩}  f g 𝒂 x

Composition of homs
---------------------

Obs 2.1. Composing homs gives a hom.  (This is proved in the ``morphisms`` module.)

Obs 2.3. Homs are determined by their values on a generating set (UAFST Ex. 1.4.6.b)

If :math:`f, g : \mathrm{Hom}(𝑨,𝑩), X ⊆ A` generates 𝑨, and :math:`f|_X = g|_X`, then :math:`f = g`.

(This is proved here, and not in the ``morphisms`` module because we use ``Sg`` from the ``subuniverses`` module.)

Here is the informal proof.  Suppose the 𝑋 ⊆ 𝐴 generates 𝑨 and :math:`f|_X = g|_X`. Fix an arbitrary 𝑎 : 𝐴.  We show 𝑓 𝑎 = 𝑔 𝑎. Since 𝑋 generates 𝑨, there is a term 𝑡 (of arity 𝑛, say) and a tuple 𝑥 : 𝑛 → 𝑋 of generators such that :math:`a = t^𝑨 x`. Since :math:`f|_X = g|_X`,

.. math:: f ∘ x = (f x₀, ..., f xₙ) = (g x₀,...,g xₙ) = g ∘ x, \text{ so}

.. math:: f a = f(t^𝑨 x) = t^𝑩 (f ∘ x) = t^𝑩 (g ∘ x) = g(t^𝑨 x) = g a.

::

   HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
              (X : Pred ∣ 𝑨 ∣ 𝓤)  (f g : hom 𝑨 𝑩)
    →          (∀ ( x : ∣ 𝑨 ∣ )  →  x ∈ X  →  ∣ f ∣ x ≡ ∣ g ∣ x)
              -------------------------------------------------
    →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ f ∣ a ≡ ∣ g ∣ a)

   HomUnique _ _ _ _ fx≡gx a (var x) = (fx≡gx) a x
   HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
    (f , fhom) (g , ghom) fx≡gx a (app 𝓸 {𝒂} im𝒂⊆SgX) =
     f ( Fᴬ 𝓸 𝒂)        ≡⟨ fhom 𝓸 𝒂 ⟩
     Fᴮ 𝓸 ( f ∘ 𝒂 )     ≡⟨ ap (Fᴮ 𝓸) (fe induction-hypothesis) ⟩
     Fᴮ 𝓸 ( g ∘ 𝒂)      ≡⟨ ( ghom 𝓸 𝒂 )⁻¹ ⟩
     g ( Fᴬ 𝓸 𝒂 )       ∎
     where
      induction-hypothesis =
       λ x → HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
        (f , fhom) (g , ghom) fx≡gx (𝒂 x)(im𝒂⊆SgX x)


Obs 2.3. If A, B are finite and X generates 𝑨, then :math:`∣\mathrm{Hom}(𝑨, 𝑩)∣ ≤ ∣B∣^∣X∣`.

*Proof*. By Obs 2, a hom is uniquely determined by its restriction to a generating set. If X generates 𝑨, then since there are exactly :math:`∣B∣^∣X∣` functions from *X* to *B*, the result holds. □

.. todo:: formalize Obs 2.3.

Obs 2.4. Factorization of homs. (This is proved in the `morphisms` module.)

Varieties
-------------

(cf. Def 1.10 of Bergman) Let 𝓚 be a class of similar algebras. We write

  * H(𝓚) for the class of all homomorphic images of members of 𝓚;
  * S(𝓚) for the class of all algebras isomorphic to a subalgebra of a member of 𝓚;
  * P(𝓚) for the class of all algebras isomorphic to a direct product of members of 𝓚;

We say that 𝓚 is closed under the formation of homomorphic images if H(𝓚) ⊆ 𝓚, and similarly for subalgebras and products.

Notice that all three of these "class operators" are designed so that for any class 𝓚, H(𝓚), S(𝓚), P(𝓚) are closed under isomorphic images. On those rare occasions that we need it, we can write I(𝓚) for the class of algebras isomorphic to a member of 𝓚. Finally, we call 𝓚 a **variety** if it is closed under each of H, S and P.

Homomorphic Images (moved to the `morphisms` module)

Products
----------

Let ℙ (𝓚) denote the class of algebras isomorphic to a direct product of members of 𝓚.

::

   ℙ-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ) )
     →      (𝓘 : Universe )  ( I : 𝓘 ̇ )  ( 𝓐 : I → Algebra 𝓘 S )
     →      (( i : I ) → 𝓐 i ∈ 𝓛𝓚 𝓘 ) → 𝓘 ⁺ ̇
   ℙ-closed 𝓛𝓚 = λ 𝓘 I 𝓐 𝓐i∈𝓛𝓚 →  Π' 𝓐  ∈ ( 𝓛𝓚 𝓘 )

Subalgebras
----------------

Let 𝕊(𝓚) denote the class of algebras isomorphic to a subalgebra of a member of 𝓚.

::

   _is-subalgebra-of-class_ : {𝓤 : Universe}(𝑩 : Algebra 𝓤 S)
    →                         Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   𝑩 is-subalgebra-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × (𝑩 is-subalgebra-of 𝑨)

   SubalgebraOfClass-pred_ : {𝓤 : Universe}
    →   Pred (Algebra 𝓤 S)(𝓤 ⁺) → Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺))
   SubalgebraOfClass-pred 𝓚 = λ 𝑩 → Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × (𝑩 is-subalgebra-of 𝑨)

   -- SubalgebrasOfClass 𝕊: {𝓤 : Universe} → Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   -- SubalgebrasOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ S) , (𝑩 is-subalgebra-of-class 𝓚)
   -- 𝕊 = SubalgebrasOfClass

   𝕊-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
    →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   𝕊-closed 𝓛𝓚 = λ 𝓤 𝑩 → (𝑩 is-subalgebra-of-class (𝓛𝓚 𝓤)) → (𝑩 ∈ 𝓛𝓚 𝓤)

Obs 2.12. ∀ 𝒦 (classes of structures) each of the classes 𝖲(𝒦), 𝖧(𝒦), 𝖯(𝒦), 𝕍(𝒦) satisfies exaxtly the same set of identities as does 𝒦.

Recall, Th𝓚 denotes the set of identities satisfied by all A ∈ 𝓚. 
`𝑻𝒉 : {𝓤 : Universe} → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`


::

   module _ (gfe : global-dfunext) { X : 𝓧 ̇ } (𝓚 : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)) ) where
   -- Recall, `𝑨 ⊢ p ≈ q = p ̇ 𝑨 ≡ q ̇ 𝑨`
   --         `𝓚 ⊢ p ≋ q = {A : Algebra _ S} → 𝓚 A → A ⊢ p ≈ q`

   -- Obs 2.13. 𝒦 ⊧ p ≈ q iff ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom 𝔉 𝑨 , h p = h q`. (UAFST Lem 4.37)
    identity-implies-preserved-by-homs :  (p q : Term {X = X})
     →                                 𝓚 ⊢ p ≋ q
                 ---------------------------------------------------------
     →         (𝑨 : Algebra 𝓤 S) (KA : 𝓚 𝑨) (h : hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q
    identity-implies-preserved-by-homs p q 𝓚⊢p≋q  𝑨  KA h = γ
     -- let cht = comm-hom-term' fe 𝔉 𝑨 h p in {!!}
     where
     pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
     pA≡qA = 𝓚⊢p≋q KA

     pAh≡qAh : ∀ (𝒂 : X → ∣ 𝔉 ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
     pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

     hpa≡hqa :  ∀ (𝒂 : X → ∣ 𝔉 ∣ ) →  ∣ h ∣ (𝔉-interp p 𝒂)  ≡ ∣ h ∣ (𝔉-interp q 𝒂)
     hpa≡hqa = {!!}
     -- hp≡hq : ∣ h ∣ ∘ (p ̇ 𝔉)  ≡ ∣ h ∣ ∘ (q ̇ 𝔉)
     -- hp≡hq = ?

     -- Since h is a hom, we obtain h ((p ̇ 𝔉) 𝒂) = h ((q ̇ 𝔉) 𝒂), as desired.
     γ :  ∣ h ∣ p ≡ ∣ h ∣ q
     γ = {!!}

    preserved-by-homs-implies-identity : (p q : Term{X = X} ) →
            (∀(𝑨 : Algebra 𝓤 S)(KA : 𝑨 ∈ 𝓚) (hh : hom 𝔉 𝑨) → ∣ hh ∣ p ≡ ∣ hh ∣ q)
            -----------------------------------------------------------------
     →                              𝓚 ⊢ p ≋ q
    preserved-by-homs-implies-identity p q all-hp≡hq {A = 𝑨} KA = γ
     where
      γ : 𝑨 ⊢ p ≈ q
      γ = {!!}

    identity-iff-preserved-by-homs :  (p q : Term {X = X})
     →    (𝓚 ⊢ p ≋ q) ⇔ (∀ (𝑨 : Algebra 𝓤 S)(KA : 𝓚 𝑨)(hh : hom 𝔉 𝑨) → ∣ hh ∣ p ≡ ∣ hh ∣ q)
    identity-iff-preserved-by-homs p q =
     (identity-implies-preserved-by-homs p q , preserved-by-homs-implies-identity p q)
  
Here's the pencil-and-paper proof:

  ⇒ Assume 𝒦 ⊧ p ≈ q. Fix 𝑨 ∈ 𝒦 and h : hom 𝔉 𝑨.  We must show h p ≡ h q.
    Fix 𝒂 : X → Term.   By 𝑨 ⊧ p ≈ q we have p ̇ 𝑨 = q ̇ 𝑨 which implies (p ̇ 𝑨)(h ∘ 𝒂) = (q ̇ 𝑨)(h ∘ 𝒂).
    Since h is a hom, we obtain h ((p ̇ 𝔉) 𝒂) = h ((q ̇ 𝔉) 𝒂), as desired.

  ⇐ Assume ∀ 𝑨 ∈ 𝒦, ∀ h : hom 𝔉 𝑨, h p ≡ h q.  We must show 𝒦 ⊧ p ≈ q.
    Fix 𝑨 ∈ 𝒦 and 𝒂 : (ρ p) → ∣ 𝑨 ∣.  We must prove (p ̇ 𝑨) 𝒂 = (q ̇ 𝑨) 𝒂.
    Define h₀ : X → A so that ∀i → ∃ x → h₀ x = 𝒂 i.  Let 𝒙 : (ρ p) → X be such that h₀ (𝒙 i) = 𝒂 i.
    By Obs 6, h₀ extends to a homomorphism h : hom 𝔉 𝑨.  By assumption h p = h q, and since h is a hom,
    (p ̇ 𝑨) 𝒂 =  (p ̇ 𝑨) (h ∘ 𝒙) = h (p ̇ 𝔉) 𝒙 = h p = h q = h (q ̇ 𝔉) 𝒙 = (q ̇ 𝑨) (h ∘ 𝒙) = (q ̇ 𝑨) 𝒂

--------------------------------------------------------------------------------------------------

Notes on homomorphic images and their types
--------------------------------------------

The homomorphic image of `f : Hom 𝑨 𝑩` is the image of `∣ 𝑨 ∣` under `f`, which, in "set-builder" notation, is simply `Im f = {f a : a ∈ ∣ 𝑨 ∣ }`.

As we have proved, `Im f` is a subuniverse of `𝑩`.

However, there is another means of representing the collection "H 𝑨" of all homomorphic images of 𝑨 without ever referring to codomain algebras (like 𝑩 above).

Here's how: by the first isomorphism theorem, for each `f : Hom 𝑨 𝑩`, there exists a congruence `θ` of `𝑨` (which is the kernel of `f`) that satisfies `𝑨 / θ ≅ Im f`.

Therefore, we have a handle on the collection `H 𝑨` of all homomorphic images of `𝑨` if we simply consider the collection `Con 𝑨` of all congruence relations of `𝑨`.  Indeed, by the above remark, we have

  `H 𝑨 = { 𝑨 / θ : θ ∈ Con 𝑨 }`.

So, we could define the following:

.. code-block::

   hom-closed : (𝓚 : Pred (Algebra (𝓤 ⁺) S) l) → Pred (Algebra 𝓤 S) _
   hom-closed 𝓚 = λ 𝑨 → (𝓚 (𝑨 / (∥𝟎∥ 𝑨)))
      →     (∃ θ : Congruence 𝑨) → (∃ 𝑪 : Algebra (𝓤 ⁺) S) → (𝓚 𝑪) × ((𝑨 / θ) ≅ 𝑪)

To get this to type check, we have an apparent problem, and we need a trick to resolve it. The class 𝓚 is a collection of algebras whose universes live at some level. (Above we use `𝓤 ⁺`.)

However, if `𝑨` is an algebra with `∣ 𝑨 ∣ : 𝓤 ̇`, then the quotient structure  (as it is now defined in Con.agda), has type `𝑨 / θ : 𝓤 ⁺ ̇`. So, in order for the class `𝓚` to contain both `𝑨` and all its quotients `𝑨 / θ` (i.e. all its homomorphic images), we need to somehow define a class of algebras that have different universe levels.

Can we define a data type with such "universe level polymorphism"?

Without that, we use a trick to get around the problem. Instead of assuming that `𝑨` itself belongs to `𝓚`, we could instead take the "quotient" `𝑨 / ∥𝟎∥` (which is isomorphic to `𝑨`) as belonging to `𝓚`.

This is a hack and, worse, it won't do for us. We need something inductive because we will also need that if `𝑪 ≅ 𝑨 / θ ∈ 𝓚`, then also `𝑪 / ψ ≅ (𝑨 / θ) / ψ ∈ 𝓚`.

So, if we want `𝓚` to be closed under all quotients, we cannot determine in advance the universe levels of the algebras that belong to `𝓚`.

We are trying to come up with a datatype for classes of algebras that has some sort of inductive notion of the universe levels involved.

It seems we may be testing the limits of Agda's universe level paradigm. Maybe we can invent a new type to solve the problem, or we may have to try to extend Agda's capabilities.

-- ::
--    record AlgebraClass (𝓤 : Universe) : 𝓤 ̇ where
--     algebras : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ )
--     nextclass : AlgebraClass ( 𝓤 ⁺ )

--    record AlgebraClass : Set _ where
--     algebras : (ℓ : Level) -> Pred (Algebra ℓ S) (lsuc ℓ)

--    module _ {S : Signature 𝓞 𝓥} where

--     hom-closed : Pred (AlgebraClass lzero) _
--     hom-closed 𝓚 = ∀ 𝑨 -> (algebras 𝓚) 𝑨 -- (𝓚 (𝑨 / (⟦𝟎⟧ 𝑨)))
--      -> ∀ (θ : Congruence 𝑨) -> (∃ 𝑪 : Algebra lsuc ℓ S)
--           ------------------------------
--      ->     (𝓚 𝑪) × ((𝑨 / θ) ≅ 𝑪)

Obs 2.12. ∀ 𝒦 (classes of structures) each of the classes 𝖲(𝒦), 𝖧(𝒦), 𝖯(𝒦), 𝕍(𝒦) satisfies exaxtly the same set of identities as does 𝒦.

-- ::
--    module _  {S : Signature 𝓞 𝓥}  where
--     open AlgebraClass

--     data HomClo {ℓ : Level} (𝓚 : AlgebraClass) : Pred AlgebraClass _ where
--      hombase : {𝑨 : Algebra ℓ S} → 𝑨 ∈ (algebras 𝓚) ℓ  → 𝑨 ∈ HomClo 𝓚
--      homstep : {𝑨 : Algebra ℓ S} ->  𝑨 ∈ HomClo 𝓚
--        ->     (∃ θ : Congruence 𝑨)
--        ->     (𝑪 : Algebra (lsuc ℓ) S)
--              ------------------------------
--        ->     𝑪 ∈ (algebras (lsuc ℓ) 𝓚) × ((𝑨 / θ) ≅ 𝑪)


**Obs 2.13**. 𝒦 ⊧ p ≈ q iff ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom(𝑻(X_ω), 𝑨), h p^𝑨 = h q^𝑨`. (UAFST Lem 4.37)

**Obs 2.14**. Let 𝒦 be a class of algebras and p ≈ q an equation. The following are equivalent.

  #. 𝒦 ⊧ p ≈ q.
  #. (p, q) belongs to the congruence λ_𝒦 on 𝑻(X_ω).
  #. 𝑭_𝒦(X_ω) ⊧ p ≈ q.

**Obs 2.15**. Let 𝒦 be a class of algebras, p, q terms (say, n-ary), Y a set, and y₁,..., yₙ distinct elements of Y. Then 𝒦 ⊧ p ≈ q iff p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦}(Y)(y₁, ..., yₙ). In particular, 𝒦 ⊧ p ≈ q iff 𝑭_𝒦(Xₙ) ⊧ p ≈ q.

-- ::
--    contains : {A : Set} -> (L : List A) -> A -> Prp
--    contains [] a = ⊥
--    contains (h :: tail) a = (h ≡ a) ⋁ (contains tail a)

----------------------------------------------------------------------------------------

**Obs 2.5**. (proved in subuniverses.agda; see `sub-inter-is-sub`)
Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨.

**Obs 2.6**. Inductive version of :math:`\mathrm{Sg}^𝑨`.  (proved in subuniverse.agda; see `Sg`)
Let 𝑨 be an algebra in the signature S and A₀ a subset of A. Define, by recursion on n, the sets Aₙ as follows:

  If A₀ = ∅, then Aₙ = ∅ for all n<ω.

  If A₀ ≠ ∅, then A_{n+1} = Aₙ ∪ { f a ∣ f ∈ F, a ∈ Fin(ρ f) -> Aₙ}.

Then the subuniverse of 𝑨 generated by A₀ is Sg^𝑨(A₀) = ⋃ₙ Aₙ.

*Proof*. Let Y := ⋃ₙ Aₙ. Clearly Aₙ ⊆ Y ⊆ A, for every n < ω. In particular A = A₀ ⊆ Y. We first show that  Y is a subuniverse of 𝑨. Let f be a basic k-ary operation and let a: Fin(k) -> Y be a k-tuple of elements of Y. From the construction of Y, ∃ n < ω, ∀ i, (a i) ∈ Aₙ. From its definition, f a ∈ A_{n+1} ⊆ Y. Since f was arbitrary, Y is a subuniverse of 𝑨 containing A₀. Thus, Sg^𝑨(A₀) ⊆ Y. For the opposite inclusion, we check that Aₙ ⊆ Sg^𝑨(A₀), for each n. Clearly, A₀ ⊆ Sg^𝑨(A₀). Assume Aₙ ⊆ Sg^𝑨(A₀). We must show A_{n+1} ⊆ Sg^𝑨(A₀). If b ∈ A_{n+1} - Aₙ, then b = f a for a basic k-ary operation f and some a: Fin(k) -> Aₙ.  But ∀ i, a i ∈ Sg^𝑨(A₀), and this latter object is a subuniverse, so b ∈ Sg^𝑨(X) as well. Therefore,  A_{n+1} ⊆ Sg^𝑨(A₀), as desired.    ☐ 

**Obs 2.7**. Inductive version of Clo(F).  (UAFST Thm 4.3)
Let A be a set and let F ⊆ Op(A):= ⋃ₙ A^Aⁿ be a collection of operations on A. Define

  F_0 := Proj(A) (the set of projection operations on A), and for all 0 ≤ n < ω,

  F_{n+1} := Fₙ ∪ {f g | f ∈ F, g : Fin(ρ f) -> Fₙ ∩ (Fin(ρg) -> A)}.

Then Clo(F) = ⋃ₙ Fₙ.

*Proof*. Let F̄ = ⋃ₙ Fₙ. By induction, every Fₙ is a subset of Clo(F). Thus, F ⊆ Clo(F). For the converse inclusion, we must show F` is a clone that contains F. Obviously F contains the projection operations, F₀ ⊆ F̄. For every f ∈ F, we have f πᵏ ∈ F₁ ⊆ F̄, where k := ρ f. We must show that F̄ is closed under generalized composition. This follows from the following subclaim.

  *Subclaim*. If f ∈ Fₙ and all entries of g := (g₀, ..., g_{ρf - 1} ∈ Fₘ are k-ary, then f g ∈ F_{n+m},
  where we have defined g: Fin(ρ f) -> (k -> A) -> A to be the tuple given by g i = gᵢ for
  each 0 ≤ i < ρ f.

By induction on n: If n = 0 then f is a projection, so f g = gᵢ ∈ Fₘ for some 0 ≤ i < ρ f. Assume (IH) claim holds for n and f ∈ F_{n+1} - Fₙ.  By def, ∃ t-ary op fᵢ ∈ F, ∃ t-tuple, h = (h₀, ..., h_{t-1}) ∈ t -> Fₙ, such that f = fᵢ h. (N.B. h: Fin(t) → (Fin(ρ f) → A) → A is given by h(j) = hⱼ, and the arity of each hᵢ must be equal to that of f, namely ρ f.) By (IH) for each i ≤ k, hᵢ = hᵢ g ∈ F_{n+m}, where as above g = (g₀,...,g_{k-1}). By def, f₁ h' ∈ F_{n+m+1} = F_{(n+1)+m}. Since f₁ h' = f₁ ∘ (h₁ g, ..., hₜ g) = f g, the claim is proved. □

**Obs 2.8**. The Lift of a map h : X → A extends uniquely to a hom 𝑻(X) → 𝑨.  (UAFST Thm 4.21)

  #. 𝑻 := 𝑻_σ(X) is generated by X.
  #. ∀ 𝑨 = ⟨A, F^𝑨⟩, ∀ g: X → A, ∃! hom h: 𝑻 → 𝑨,  h|_X = g.

(This is proved in the `terms` module; see `free-unique`)

*Proof*. The def of 𝑻 exactly parallels the construction in Obs 6 above. That accounts for the 1st assertion. For the 2nd assertion, define h t by induction on the height, ∣𝑡∣, of 𝑡. Suppose ∣𝑡∣ = 0.  Then 𝑡 ∈ 𝑋 ∪ 𝐹₀. If 𝑡 ∈ 𝑋, then define ℎ 𝑡 = 𝑔 𝑡. If 𝑡 ∈ 𝐹₀, then let ℎ 𝑡 = :math:`t^𝑨`. For the inductive step, assume ∣𝑡∣ = 𝑛+1. Then 𝑡 = 𝑓 𝑠 for some 𝑓 ∈ 𝐹 and 𝑠 : ρ 𝑓 → 𝑇ₙ, where for each 0 ≤ 𝑖 < ρ 𝑓 the term 𝑠 𝑖 has height at most 𝑛. Define ℎ 𝑡 = :math:`f^𝑨(h ∘ s) = f^𝑨(h s₁, ..., h sₖ)`. Then ℎ is a hom that agrees with 𝑔 on 𝑋. The uniqueness of ℎ follows from Obs 2.? ☐

**Obs 2.9**. Homs commute with terms. (UAFST Thm 4.32)
(This is proved in the `terms` module; see `comm-hom-term`)

**Obs 2.10**. Terms respect congruences. (This is proved in the `terms` module; see `compatible-term`)

**Obs 2.11**. On subuniverse generation as image of terms. If 𝑌 is a subset of 𝑨, then :math:`\mathrm{Sg}^{𝑨}(Y) = \{t^𝑨 a : t ∈ T_σ(X_n), n ∈ ℕ, a: ρt → Y \}`.

(This is proved in the `subuniverses` module; see `TermImageIsSub`.) 

*Proof*. Induction on the height of *t* shows that every subuniverse is closed under the action of :math:`t^𝑨`. Thus the right-hand side is contained in the left. On the other hand, the right-hand side is a subuniverse that contains the elements of 𝑌 (take 𝑡 = 𝑥₁), so it contains :math:`\mathrm{Sg}^{𝑨}(Y)`, as the latter is the smallest subuniverse containing 𝑌. ☐

**Obs 2.12**. ∀ 𝒦 (classes of structures) each of the classes 𝖲(𝒦), 𝖧(𝒦), 𝖯(𝒦), 𝕍(𝒦) satisfies the same set of identities as does 𝒦.

*Proof*. We prove the result for 𝖧(𝒦). 𝒦 ⊆ 𝖧(𝒦), so Th 𝖧 (𝒦) ⊆  Th 𝒦.... 

**Obs 2.13**. 𝒦 ⊧ p ≈ q iff ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom(𝑻(X_ω), 𝑨), h p^𝑨 = h q^𝑨`. (UAFST Lem 4.37)

*Proof*.

  ⇒ Assume 𝒦 ⊧ p ≈ q. Fix 𝑨 ∈ 𝒦 and h ∈ Hom(𝑻(X_ω), 𝑨). We must show ∀ a: Fin(ρ p) -> A that h(p^𝑨 a) = h(q^𝑨 a). Fix a: Fin(ρ p) -> A`. By 𝑨 ⊧ p ≈ q we have p^𝑨 = q^𝑨 which implies p^𝑨(h ∘ a) = q^𝑨(h ∘ a). Since h is a hom, we obtain h(p^𝑨 a) = h(q^𝑨 a), as desired.

  ⇐ Assume ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom(𝑻(X_ω), 𝑨), h p^𝑨 = h q^𝑨. We must show 𝒦 ⊧ p ≈ q. Fix 𝑨 ∈ 𝒦 and a: Fin(ρ p) -> A. We must prove p^𝑨 a = q^𝑨 a`. Let h₀ : X_ω -> A be a function with h₀ x i = a i for all 0≤ i < ρ p, for some x: Fin(ρ p) -> X_ω. By Obs 6, h₀ extends to a homomorphism h from 𝑻(X_ω) to 𝑨. By assumption h p^𝑨 = h q^𝑨, and since h is a homomorphism, p^𝑨 a =  p^𝑨(h ∘ x) = h(p^𝑨 x) = h(q^𝑨 x) = q^𝑨 (h ∘ x) = q^𝑨 a, so p^𝑨 a = q^𝑨 a. ☐

**Obs 2.14**. Let 𝒦 be a class of algebras and p ≈ q an equation. The following are equivalent.

  #. 𝒦 ⊧ p ≈ q.
  #. (p, q) belongs to the congruence λ_𝒦 on 𝑻(X_ω).
  #. 𝑭_𝒦(X_ω) ⊧ p ≈ q.

*Proof*. We shall show (1) ⟹ (3) ⟹ (2) ⟹ (1).  Recall that 𝑭_𝒦(X_ω) = 𝑻/λ ∈ 𝖲 𝖯 (𝒦).  From (1) and Lemma 4.36 of :term:`UAFST` we have 𝖲 𝖯 (𝒦) ⊧ p ≈ q. Thus (3) holds. From (3), p^𝑭 [x] = q^𝑭 [x], where [x]: Fin(ρ p) → 𝑭_𝒦 (X_ω) is defined by [x] i = xᵢ/λ. From the def of 𝑭, p^𝑻 x ≡λ q^𝑻 x, from which (2) follows since p = p^𝑻 x and q = q^𝑻 x.  Finally assume (2). We wish to apply Lemma 4.37 of UAFST. Let 𝑨 ∈ 𝒦 and h ∈ Hom(𝑻, 𝑨). Then 𝑻/ker h ∈ 𝖲 (𝑨) ⊆ 𝖲(𝒦) so ker h ⊇ λ.  Thus, (2) implies h p = h q hence (1) holds. ☐

The last result tells us that we can determine whether an identity is true in a variety by consulting a particular algebra, namely 𝑭(X_ω). Sometimes it is convenient to work with algebras free on other generating sets besides X_ω. The following corollary takes care of that for us.

**Obs 2.15**. Let 𝒦 be a class of algebras, p, q terms (say, n-ary), Y a set, and y₁,..., yₙ distinct elements of Y. Then 𝒦 ⊧ p ≈ q iff p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦}(Y)(y₁, ..., yₙ). In particular, 𝒦 ⊧ p ≈ q iff 𝑭_𝒦(Xₙ) ⊧ p ≈ q.

*Proof*. Since 𝑭_𝒦(Y) ∈ 𝖲 𝖯 (𝒦), the left-to-right direction uses the same argument as in Thm 4.38 of UAFST. (See Obs 14 above.) So assume that p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦(Y)}(y₁,..., yₙ). To show that 𝒦 ⊧ p ≈ q, let 𝑨= ⟨ A, f^𝑨 ⟩ ∈ 𝒦 and a₁, ..., aₙ ∈ A. We must show p^𝑨(a₁,..., aₙ) = q^𝑨(a₁,...,aₙ)`. There is a hom h: 𝔽_𝒦(Y) -> (A, f^𝑨) such that h(yᵢ) = aᵢ for i ≤ n. Then p^𝑨(a₁, ..., aₙ) = p^𝑨(h(y₁), ..., h(yₙ)) = h(p^{𝑭_𝒦(Y)}(y₁, ...,yₙ)) = h(q^{𝑭_𝒦(Y)}(y₁, ...,yₙ)) = q^𝑨(h(y₁), ..., h(yₙ)) = q^𝑨(a₁, ..., aₙ). It now follows from Obs 12 that every equational class is a variety.  ☐

The converse of Obs 2.15 is **Birkhoff's HSP Theorem**.

**Obs 2.16**. Every  finitely  generated  variety  is  locally finite. (UAFST Thm 3.49)

(This is not needed for the HSP theorem, but we might want to prove it next.)

The converse of the last theorem is false.  That is, ∃ loc fin varieties that are not finitely generated(e.g., the variety of p-algebras; see UAFSt Cor. 4.55).


--------------------------

.. rubric:: Footnotes

.. [1]
   **AoC**. Some :term:`Choice` axiom is needed here.

.. [2]
   **AoC**. Some :term:`Choice` axiom is needed here.

.. include:: hyperlink_references.rst



.. I'm not sure where the material below is from or where it should go... saving it for now, in case it was accidentally deleted from some section.

.. Let :math:`u,v ∈ T(Y)` and assume that :math:`g(u) = g(v)`. Since :math:`𝕋(Y)` is generated by :math:`Y`, then by :numref:`Obs %s <obs 6>` there is an integer :math:`n`, terms :math:`p, q ∈ T(X_n)`, and :math:`y_1, \dots, y_n ∈ Y` such that :math:`u = p^{𝕋(Y)}(y_1, \dots, y_n)` and :math:`v = q^{𝕋(Y)}(y_1,\dots, y_n)`, by Theorem 4.32 of :cite:`Bergman:2012`.

.. Applying the homomorphism :math:`g`,

.. .. math:: p^{𝔽_{𝒲}(Y)}(y_1, \dots, y_n) = g(u) = g(v) = q^{𝔽_{𝒲}(Y)}(y_1,\dots, y_n).

.. Then by :numref:`Obs %s <obs 15>` above (Corollary 4.39 of :cite:`Bergman:2012`), we have :math:`𝒲 ⊧ p ≈ q`, hence :math:`(p ≈ q) \in Σ`.

.. Since :math:`𝔸 ∈ 𝒲^† = \mathsf{Mod}(Σ)`, we obtain :math:`𝔸 ⊧ p ≈ q`. Therefore,

.. .. math:: h(u) = p^{𝔸}(h_0(y_1), \dots, h_0(y_n)) = q^{𝔸}(h_0(y_1), \dots, h_0(y_n)) = h(v),

.. as desired.
