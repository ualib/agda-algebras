---
layout: default
title : UALib.Varieties.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="equational-logic-types">Equational Logic Types</a>

This section presents the [UALib.Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][].

We prove closure properties, or "invariance," of the models relation defined in [UALib.Varieties.ModelTheory][] module .  Proofs are given of the following facts (which are needed, for example, in the proof the Birkhoff HSP Theorem).

* [Algebraic invariance of ⊧](#algebraic-invariance-of-⊧). The ⊧ relation is an *algebraic invariant* (stable under isomorphism).

* [Product invariance of ⊧](#product-invariance-of-⊧). Identities modeled by a class of algebras are also modeled by all products of algebras in the class.

* [Subalgebra invariance of ⊧](#subalgebra-invariance-of-⊧). Identities modeled by a class of algebras are also modeled by all subalgebras of algebras in the class;

* [Homomorphism invariance of ⊧](#homomorphism-invariance-of-⊧). Identities modeled by a class of algebras are also modeled by all homomorphic images (equivalently, all quotients) of algebras in the class;

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Varieties.EquationalLogic
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Varieties.ModelTheory {𝑆 = 𝑆}{gfe}{𝕏} public
open import UALib.Prelude.Preliminaries using (∘-embedding; domain; embeddings-are-lc) public

\end{code}

-------------------------------------

#### <a id="computing-with-⊧">Computing with ⊧</a>

We have formally defined 𝑨 ⊧ 𝑝 ≈ 𝑞, which represents the assertion that p ≈  q holds when this identity is interpreted in the algebra  𝑨; syntactically,  𝑝 ̇  𝑨 ≡  𝑞 ̇  𝑨.  It should be emphasized that the expression  𝑝 ̇  𝑨 ≡  𝑞 ̇  𝑨 is interpreted computationally as an \emph{extensional equality}, by which we mean that for each *assignment function*  𝒂 :  X → ∣ 𝑨 ∣, assigning values in the domain of  𝑨 to the variable symbols in  X, we have (𝑝 ̇  𝑨)  𝒂 ≡ (𝑞 ̇  𝑨)  𝒂.

---------------------------------

#### <a id="algebraic-invariance-of-⊧I">Algebraic invariance of ⊧</a>

The binary relation ⊧ would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism).

\begin{code}

⊧-I-invariance : {𝓠 𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
                 (p q : Term{𝓧}{X}) → (𝑨 ⊧ p ≈ q) → (𝑨 ≅ 𝑩) → 𝑩 ⊧ p ≈ q
⊧-I-invariance {𝓠}{𝓤}{𝓧}{X}{𝑨}{𝑩} p q Apq (f , g , f∼g , g∼f) = γ
 where
  γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
  γ = gfe λ x →
      (p ̇ 𝑩) x ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      (p ̇ 𝑩) (∣ 𝒾𝒹 𝑩 ∣ ∘ x) ≡⟨ ap (λ - → (p ̇ 𝑩) -) (gfe λ i → ((f∼g)(x i))⁻¹)  ⟩
      (p ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘ x) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 f p (∣ g ∣ ∘ x))⁻¹ ⟩
      ∣ f ∣ ((p ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ ap (λ - → ∣ f ∣ (- (∣ g ∣ ∘ x))) Apq ⟩
      ∣ f ∣ ((q ̇ 𝑨) (∣ g ∣ ∘ x)) ≡⟨ comm-hom-term gfe 𝑨 𝑩 f q (∣ g ∣ ∘ x) ⟩
      (q ̇ 𝑩) ((∣ f ∣ ∘ ∣ g ∣) ∘  x) ≡⟨ ap (λ - → (q ̇ 𝑩) -) (gfe λ i → (f∼g) (x i)) ⟩
      (q ̇ 𝑩) x ∎

\end{code}

As the proof makes clear, we show 𝑩 ⊧ p ≈ q by showing that p ̇ 𝑩 ≡ q ̇ 𝑩 holds *extensionally*, that is, `∀ x, (p ̇ 𝑩) x ≡ (q ̇ 𝑩) x`.

--------------------------------------

#### <a id="Lift-invariance-of-⊧">Lift-invariance of ⊧</a>

The ⊧ relation is also invariant under the algebraic lift and lower operations.

\begin{code}

⊧-lift-alg-invariance : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
       (𝑨 : Algebra 𝓤 𝑆)(p q : Term{𝓧}{X})
  →    𝑨 ⊧ p ≈ q → (lift-alg 𝑨 𝓦) ⊧ p ≈ q
⊧-lift-alg-invariance 𝑨 p q Apq = ⊧-I-invariance p q Apq lift-alg-≅

⊧-lower-alg-invariance : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓤 𝑆)
                             (p q : Term{𝓧}{X})
 →                           lift-alg 𝑨 𝓦 ⊧ p ≈ q → 𝑨 ⊧ p ≈ q
⊧-lower-alg-invariance {𝓤}{𝓦}{𝓧}{X} 𝑨 p q lApq = ⊧-I-invariance p q lApq (sym-≅ lift-alg-≅)

\end{code}

---------------------------------------------

#### <a id="product-invariance-of-⊧">Product-invariance of ⊧</a>

Identities satisfied by all factors of a product are also satisfied by the product.

\begin{code}
⊧-P-invariance : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X})
                 (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →               ((i : I) → (𝒜 i) ⊧ p ≈ q)
                 --------------------------
 →               ⨅ 𝒜 ⊧ p ≈ q

⊧-P-invariance p q I 𝒜 𝒜pq = γ
  where
   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = gfe λ a →
    (p ̇ ⨅ 𝒜) a                           ≡⟨ interp-prod gfe p 𝒜 a ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ gfe (λ i → cong-app (𝒜pq i) (λ x → (a x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i))) ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
    (q ̇ ⨅ 𝒜) a                           ∎

⊧-P-lift-invariance : {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}(p q : Term{𝓧}{X})
                      (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →                    ((i : I) → (lift-alg (𝒜 i) 𝓦) ⊧ p ≈ q)
                      ---------------------------------------
 →                    ⨅ 𝒜 ⊧ p ≈ q

⊧-P-lift-invariance {𝓤}{𝓦} p q I 𝒜 lApq = ⊧-P-invariance p q I 𝒜 Aipq
  where
   Aipq : (i : I) → (𝒜 i) ⊧ p ≈ q
   Aipq i = ⊧-I-invariance p q (lApq i) (sym-≅ lift-alg-≅)

⊧-class-P-invariance : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                       (p q : Term{𝓧}{X})
                       (I : 𝓤 ̇)(𝒜 : I → Algebra 𝓤 𝑆)
 →                     𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
                       ----------------------------------
 →                     ⨅ 𝒜 ⊧ p ≈ q

⊧-class-P-invariance p q I 𝒜 α K𝒜 = γ
  where
   β : ∀ i → (𝒜 i) ⊧ p ≈ q
   β i = α (K𝒜 i)

   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = ⊧-P-invariance p q I 𝒜 β
\end{code}

--------------------------------------------

#### <a id="subalgebra-invariance-of-⊧">Subalgebra invariance of ⊧</a>
We show that identities modeled by a class of algebras is also modeled by all subalgebras of the class.  In other terms, every term equation `p ≈ q` that is satisfied by all `𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of 𝒦.

\begin{code}

⊧-S-invariance : {𝓤 𝓠 𝓧 : Universe}{X : 𝓧 ̇}
                 {𝒦 : Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
                 (p q : Term{𝓧}{X})
                 (𝑩 : SubalgebraOfClass{𝓤}{𝓠} 𝒦)
 →               𝒦 ⊧ p ≋ q
                -----------------
 →               ∣ 𝑩 ∣ ⊧ p ≈ q

⊧-S-invariance {𝓤}{X = X} p q (𝑩 , 𝑨 , SA , (KA , BisSA)) Kpq = γ
 where
  𝑩' : Algebra 𝓤 𝑆
  𝑩' = ∣ SA ∣

  h' : hom 𝑩' 𝑨
  h' = (∣ snd SA ∣ , snd ∥ snd SA ∥ )

  f : hom 𝑩 𝑩'
  f = ∣ BisSA ∣

  h : hom 𝑩 𝑨
  h = HCompClosed 𝑩 𝑩' 𝑨 f h'

  hem : is-embedding ∣ h ∣
  hem = ∘-embedding h'em fem
   where
    h'em : is-embedding ∣ h' ∣
    h'em = fst ∥ snd SA ∥

    fem : is-embedding ∣ f ∣
    fem = iso→embedding BisSA

  β : 𝑨 ⊧ p ≈ q
  β = Kpq KA

  ξ : (b : X → ∣ 𝑩 ∣ ) → ∣ h ∣ ((p ̇ 𝑩) b) ≡ ∣ h ∣ ((q ̇ 𝑩) b)
  ξ b =
   ∣ h ∣((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 h p b ⟩
   (p ̇ 𝑨)(∣ h ∣ ∘ b) ≡⟨ intensionality β (∣ h ∣ ∘ b) ⟩
   (q ̇ 𝑨)(∣ h ∣ ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 h q b)⁻¹ ⟩
   ∣ h ∣((q ̇ 𝑩) b)  ∎

  hlc : {b b' : domain ∣ h ∣} → ∣ h ∣ b ≡ ∣ h ∣ b' → b ≡ b'
  hlc hb≡hb' = (embeddings-are-lc ∣ h ∣ hem) hb≡hb'

  γ : 𝑩 ⊧ p ≈ q
  γ = gfe λ b → hlc (ξ b)

\end{code}

------------------------------------------------------------

#### <a id="homomorphism-invariance-of-⊧">Homomorphism-invariance of ⊧</a>

Below we will prove that a class models an identity if and only if all homomorphic images of algebras in the class model the same identity.  But first we prove the slightly simpler special case involving just a single algebra, rather than a class of algebras.

\begin{code}

⊧-H-invariance : {𝓤 𝓧 : Universe}{X : 𝓧 ̇} (p q : Term{𝓧}{X})
                 (𝑨 : Algebra 𝓤 𝑆)(φ : hom (𝑻 X) 𝑨)
 →               𝑨 ⊧ p ≈ q
                 ------------------
 →               ∣ φ ∣ p ≡ ∣ φ ∣ q

⊧-H-invariance {X = X} p q 𝑨 φ β =
  ∣ φ ∣ p              ≡⟨ ap ∣ φ ∣ (term-agreement p) ⟩
  ∣ φ ∣ ((p ̇ 𝑻 X) ℊ )   ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 φ p ℊ ) ⟩
  (p ̇ 𝑨) (∣ φ ∣ ∘ ℊ ) ≡⟨ intensionality β (∣ φ ∣ ∘ ℊ ) ⟩
  (q ̇ 𝑨) (∣ φ ∣ ∘ ℊ ) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 φ q ℊ )⁻¹ ⟩
  ∣ φ ∣ ((q ̇ 𝑻 X) ℊ ) ≡⟨ (ap ∣ φ ∣ (term-agreement q))⁻¹ ⟩
  ∣ φ ∣ q              ∎

\end{code}

Recall that an identity is satisfied by all algebras in a class if and only if that identity is compatible with all homomorphisms from the term algebra `𝑻 X` into algebras of the class. More precisely, if 𝓚 is a class of 𝑆-algebras and 𝑝, 𝑞 terms in the language of 𝑆, then,

𝒦 ⊧ p ≈ q  ⇔  ∀ 𝑨 ∈ 𝒦,  ∀ h : hom (𝑻 X) 𝑨,  h ∘ (𝑝 ̇ (𝑻 X)) = h ∘ (𝑞 ̇ (𝑻 X)).

\begin{code}

-- ⇒ (the "only if" direction)
⊧-class-H-invariance : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                       {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                       (p q : Term) →  𝒦 ⊧ p ≋ q
                       ------------------------------------
 →                      ∀ (𝑨 : Algebra 𝓤 𝑆)(KA : 𝒦 𝑨)(h : hom (𝑻 X) 𝑨)
                           →     ∣ h ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ h ∣ ∘ (q ̇ 𝑻 X)

⊧-class-H-invariance {X = X} p q α 𝑨 KA h = γ
 where
  β : ∀(𝒂 : X → ∣ 𝑻 X ∣ ) → (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
  β 𝒂 = intensionality (α KA) (∣ h ∣ ∘ 𝒂)

  ξ : ∀(𝒂 : X → ∣ 𝑻 X ∣ ) → ∣ h ∣ ((p ̇ 𝑻 X) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻 X) 𝒂)
  ξ 𝒂 =
   ∣ h ∣ ((p ̇ 𝑻 X) 𝒂)  ≡⟨ comm-hom-term gfe (𝑻 X) 𝑨 h p 𝒂 ⟩
   (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ β 𝒂 ⟩
   (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 h q 𝒂)⁻¹ ⟩
   ∣ h ∣ ((q ̇ 𝑻 X) 𝒂)  ∎

  γ : ∣ h ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ h ∣ ∘ (q ̇ 𝑻 X)
  γ = gfe ξ

-- ⇐ (the "if" direction)
⊧-class-H-coinvariance : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                         {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                         (p q : Term)
 →                       ( (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦) (h : hom (𝑻 X) 𝑨)
                                    → ∣ h ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ h ∣ ∘ (q ̇ 𝑻 X) )
                         ----------------------------------------------------
 →                       𝒦 ⊧ p ≋ q

⊧-class-H-coinvariance {X = X} p q β {𝑨} KA = γ
  where
   h : (𝒂 : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
   h 𝒂 = lift-hom 𝑨 𝒂

   γ : 𝑨 ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ 𝑨) 𝒂            ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨(comm-hom-term gfe (𝑻 X) 𝑨 (h 𝒂) p ℊ)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻 X)) ℊ  ≡⟨ ap (λ - → - ℊ) (β 𝑨 KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻 X)) ℊ  ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 (h 𝒂) q ℊ) ⟩
    (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ ℊ)   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
    (q ̇ 𝑨) 𝒂             ∎

⊧-class-H-compatibility : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
                    {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
                    (p q : Term{𝓧}{X})
                    ----------------------------------------
 →                  (𝒦 ⊧ p ≋ q) ⇔ ( (𝑨 : Algebra 𝓤 𝑆)(KA : 𝑨 ∈ 𝒦)(hh : hom (𝑻 X) 𝑨)
                                           →   ∣ hh ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻 X) )

⊧-class-H-compatibility p q = ⊧-class-H-invariance p q , ⊧-class-H-coinvariance p q

\end{code}

-------------------------------------

[← UALib.Varieties.ModelTheory](UALib.Varieties.ModelTheory.html)
<span style="float:right;">[UALib.Varieties.Varieties →](UALib.Varieties.Varieties.html)</span>

{% include UALib.Links.md %}

<!-- #### Term operations preserve identities -->

