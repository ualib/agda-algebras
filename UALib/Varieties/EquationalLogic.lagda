---
layout: default
title : Varieties.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="model-theory-and-equational-logic-types">Model Theory and Equational Logic</a>

This section presents the [Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][] where the binary "models" relation ⊧, relating algebras (or classes of algebras) to the identities that they satisfy, is defined.

Agda supports the definition of infix operations and relations, and we use this to define ⊧ so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊧ p ≋ q`.

We also prove some closure and invariance properties of ⊧.  In particular, we prove the following facts (which are needed, for example, in the proof the Birkhoff HSP Theorem).

* [Algebraic invariance](#algebraic-invariance). The ⊧ relation is an *algebraic invariant* (stable under isomorphism).

* [Subalgebraic invariance](#subalgebraic-invariance). Identities modeled by a class of algebras are also modeled by all subalgebras of algebras in the class.

* [Product invariance](#product-invariance). Identities modeled by a class of algebras are also modeled by all products of algebras in the class.



**Notation**. In the [Agda UALib][], because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊧ p ≋ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

**Unicode Hints**. To produce the symbols ≈, ⊧, and ≋ in [agda2-mode][], type `\~~`, `\models`, and `\~~~`, respectively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import Universes using (Universe; _̇)

module Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥}{𝓧 : Universe}{X : 𝓧 ̇} where

open import Subalgebras.Subalgebras{𝑆 = 𝑆} hiding (Universe; _̇) public
open import MGS-MLTT using (_⇔_) public
open import MGS-Embeddings using (embeddings-are-lc) public


\end{code}


#### <a id="the-models-relation">The models relation</a>

We define the binary "models" relation ⊧ using infix syntax so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊧ p ≋ q`, relating algebras (or classes of algebras) to the identities that they satisfy. We also prove a coupld of useful facts about ⊧.  More will be proved about ⊧ in the next module, [Varieties.EquationalLogic](Varieties.EquationalLogic.html).

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇} where

 _⊧_≈_ : Algebra 𝓤 𝑆 → Term X → Term X → 𝓤 ⊔ 𝓧 ̇
 𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≡ 𝑨 ⟦ q ⟧


 _⊧_≋_ : Pred(Algebra 𝓤 𝑆)(ov 𝓤) → Term X → Term X → 𝓧 ⊔ ov 𝓤 ̇
 𝒦 ⊧ p ≋ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}

##### <a id="semantics-of-⊧">Syntax and semantics of ⊧</a>
The expression `𝑨 ⊧ 𝑝 ≈ 𝑞` represents the assertion that the identity `p ≈ q` holds when interpreted in the algebra 𝑨; syntactically, `𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨`.  It should be emphasized that the expression  `𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨` is interpreted computationally as an *extensional equality*, by which we mean that for each *assignment function*  `𝒂 :  X → ∣ 𝑨 ∣`, assigning values in the domain of `𝑨` to the variable symbols in `X`, we have `(𝑝 ̇ 𝑨) 𝒂 ≡ (𝑞 ̇ 𝑨) 𝒂`.




#### <a id="equational-theories-and-classes">Equational theories and models</a>

Here we define a type `Th` so that, if 𝒦 denotes a class of algebras, then `Th 𝒦` represents the set of identities modeled by all members of 𝒦.

\begin{code}

 Th : Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Pred(Term X × Term X)(𝓧 ⊔ ov 𝓤)
 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

\end{code}

If ℰ denotes a set of identities, then the class of algebras satisfying all identities in ℰ is represented by `Mod ℰ`, which we define in the following natural way.

\begin{code}

 Mod : Pred(Term X × Term X)(𝓧 ⊔ ov 𝓤) → Pred(Algebra 𝓤 𝑆)(ov (𝓧 ⊔ 𝓤))
 Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

\end{code}




#### <a id="algebraic-invariance-of-models">Algebraic invariance of ⊧</a>

The binary relation ⊧ would be practically useless if it were not an *algebraic invariant* (i.e., invariant under isomorphism).

\begin{code}

module _ {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇} where

 ⊧-I-invar : dfunext 𝓧 𝓦 → dfunext 𝓥 𝓦 → dfunext (𝓦 ⊔ 𝓧) 𝓦
  →          {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(p q : Term X)
  →          𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q

 ⊧-I-invar fxw fvw fwxw {𝑨} 𝑩 p q Apq (f , g , f∼g , g∼f) = fwxw λ x →
  (𝑩 ⟦ p ⟧) x                      ≡⟨ refl ⟩
  (𝑩 ⟦ p ⟧) (∣ 𝒾𝒹 𝑩 ∣ ∘ x)         ≡⟨ ap (𝑩 ⟦ p ⟧) (fxw λ i → ((f∼g)(x i))⁻¹)⟩
  (𝑩 ⟦ p ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘ x)  ≡⟨ (comm-hom-term fvw 𝑩 f p (∣ g ∣ ∘ x))⁻¹ ⟩
  ∣ f ∣ ((𝑨 ⟦ p ⟧) (∣ g ∣ ∘ x))    ≡⟨ ap (λ - → ∣ f ∣ (- (∣ g ∣ ∘ x))) Apq ⟩
  ∣ f ∣ ((𝑨 ⟦ q ⟧) (∣ g ∣ ∘ x))    ≡⟨ comm-hom-term fvw 𝑩 f q (∣ g ∣ ∘ x) ⟩
  (𝑩 ⟦ q ⟧) ((∣ f ∣ ∘ ∣ g ∣) ∘  x) ≡⟨ ap (𝑩 ⟦ q ⟧) (fxw λ i → (f∼g) (x i)) ⟩
  (𝑩 ⟦ q ⟧) x                      ∎

\end{code}

As the proof makes clear, we show 𝑩 ⊧ p ≈ q by showing that p ̇ 𝑩 ≡ q ̇ 𝑩 holds *extensionally*, that is, `∀ x, (𝑩 ⟦ p ⟧) x ≡ (q ̇ 𝑩) x`.

#### <a id="lift-invariance">Lift-invariance of ⊧</a>
The ⊧ relation is also invariant under the algebraic lift and lower operations.

\begin{code}

module _ {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇} where

 ⊧-Lift-invar : dfunext 𝓧 (𝓤 ⊔ 𝓦) → dfunext 𝓥 (𝓤 ⊔ 𝓦) → dfunext (𝓤 ⊔ 𝓦 ⊔ 𝓧) (𝓤 ⊔ 𝓦)
  →             {𝑨 : Algebra 𝓤 𝑆}(p q : Term X) → 𝑨 ⊧ p ≈ q → Lift-alg 𝑨 𝓦 ⊧ p ≈ q
 ⊧-Lift-invar fxuw fvuw fuwxuw {𝑨} p q Apq = ⊧-I-invar fxuw fvuw fuwxuw (Lift-alg 𝑨 _) p q Apq Lift-≅

 ⊧-lower-invar : dfunext 𝓧 𝓤 → dfunext 𝓥 𝓤 → dfunext (𝓤 ⊔ 𝓧) 𝓤
  →              {𝑨 : Algebra 𝓤 𝑆}(p q : Term X) → Lift-alg 𝑨 𝓦 ⊧ p ≈ q  →  𝑨 ⊧ p ≈ q
 ⊧-lower-invar fxu fvu fuxu {𝑨} p q lApq = ⊧-I-invar fxu fvu fuxu 𝑨 p q lApq (≅-sym Lift-≅)

\end{code}





#### <a id="subalgebraic-invariance">Subalgebraic invariance of ⊧</a>

Identities modeled by an algebra 𝑨 are also modeled by every subalgebra of 𝑨, which fact can be formalized as follows.

\begin{code}

module _ {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
         (fwxw : dfunext (𝓦 ⊔ 𝓧) 𝓦)(fvu : dfunext 𝓥 𝓤)
 where

 ⊧-S-invar : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆){p q : Term X} → 𝑨 ⊧ p ≈ q  →  𝑩 ≤ 𝑨  →  𝑩 ⊧ p ≈ q
 ⊧-S-invar {𝑨} 𝑩 {p}{q} Apq B≤A = fwxw λ b → (embeddings-are-lc ∣ h ∣ ∥ B≤A ∥) (ξ b)
  where
  h : hom 𝑩 𝑨
  h = ∣ B≤A ∣

  ξ : ∀ b → ∣ h ∣ ((𝑩 ⟦ p ⟧) b) ≡ ∣ h ∣ ((𝑩 ⟦ q ⟧) b)
  ξ b = ∣ h ∣((𝑩 ⟦ p ⟧) b)   ≡⟨ comm-hom-term fvu 𝑨 h p b ⟩
        (𝑨 ⟦ p ⟧)(∣ h ∣ ∘ b) ≡⟨ extfun Apq (∣ h ∣ ∘ b) ⟩
        (𝑨 ⟦ q ⟧)(∣ h ∣ ∘ b) ≡⟨ (comm-hom-term fvu 𝑨 h q b)⁻¹ ⟩
        ∣ h ∣((𝑩 ⟦ q ⟧) b)   ∎

\end{code}

Next, identities modeled by a class of algebras is also modeled by all subalgebras of the class.  In other terms, every term equation `p ≈ q` that is satisfied by all `𝑨 ∈ 𝒦` is also satisfied by every subalgebra of a member of 𝒦.

\begin{code}

 ⊧-S-class-invar : {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}(p q : Term X)
  →                𝒦 ⊧ p ≋ q → (𝑩 : SubalgebraOfClass{𝓦} 𝒦) → ∣ 𝑩 ∣ ⊧ p ≈ q
 ⊧-S-class-invar p q Kpq (𝑩 , 𝑨 , SA , (ka , BisSA)) = ⊧-S-invar 𝑩 {p}{q}((Kpq ka)) (h , hem)
   where
   h : hom 𝑩 𝑨
   h = ∘-hom 𝑩 𝑨 (∣ BisSA ∣) ∣ snd SA ∣
   hem : is-embedding ∣ h ∣
   hem = ∘-embedding (∥ snd SA ∥) (iso→embedding BisSA)
\end{code}





#### <a id="product-invariance">Product invariance of ⊧</a>

An identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in that collection.

\begin{code}

module _ {𝓤 𝓦 𝓧 : Universe}{X : 𝓧 ̇}
         {fwu : dfunext 𝓦 𝓤}{fvuw : dfunext 𝓥 (𝓤 ⊔ 𝓦)}{fxuwuw : dfunext (𝓧 ⊔ 𝓤 ⊔ 𝓦)(𝓤 ⊔ 𝓦)}
 where

 ⊧-P-invar : (I : 𝓦 ̇)(𝒜 : I → Algebra 𝓤 𝑆){p q : Term X} → (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar I 𝒜 {p}{q} 𝒜pq = γ
  where
   γ : ⨅ 𝒜 ⟦ p ⟧  ≡  ⨅ 𝒜 ⟦ q ⟧
   γ = fxuwuw λ a → (⨅ 𝒜 ⟦ p ⟧) a            ≡⟨ interp-prod fvuw p 𝒜 a ⟩
       (λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x)i)) ≡⟨ fwu (λ i → cong-app (𝒜pq i) (λ x → (a x) i)) ⟩
       (λ i → (𝒜 i ⟦ q ⟧)(λ x → (a x)i)) ≡⟨ (interp-prod fvuw q 𝒜 a)⁻¹ ⟩
       (⨅ 𝒜 ⟦ q ⟧) a                     ∎

\end{code}

An identity satisfied by all algebras in a class is also satisfied by the product of algebras in the class.

\begin{code}

 ⊧-P-class-invar : (I : 𝓦 ̇)(𝒜 : I → Algebra 𝓤 𝑆){𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}{p q : Term X}
  →                𝒦 ⊧ p ≋ q → (∀ i → 𝒜 i ∈ 𝒦) → ⨅ 𝒜 ⊧ p ≈ q

 ⊧-P-class-invar I 𝒜 {𝒦}{p}{q}α K𝒜 = ⊧-P-invar I 𝒜 {p}{q}λ i → α (K𝒜 i)

\end{code}

Another fact that will turn out to be useful is that a product of a collection of algebras models p ≈ q if the lift of each algebra in the collection models p ≈ q.

\begin{code}

 ⊧-P-lift-invar : dfunext 𝓧 𝓤 → dfunext 𝓥 𝓤 → dfunext (𝓤 ⊔ 𝓧) 𝓤
  →               (I : 𝓦 ̇)(𝒜 : I → Algebra 𝓤 𝑆){p q : Term X}
  →               (∀ i → (Lift-alg (𝒜 i) 𝓦) ⊧ p ≈ q)  →  ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-lift-invar fxu fvu fuxu I 𝒜 {p}{q} α = ⊧-P-invar I 𝒜 {p}{q}Aipq
   where
    Aipq : ∀ i → (𝒜 i) ⊧ p ≈ q
    Aipq i = ⊧-lower-invar fxu fvu fuxu p q (α i) --  (≅-sym Lift-≅)

\end{code}


#### <a id="homomorphisc-invariance">Homomorphic invariance of ⊧</a>

If an algebra 𝑨 models an identity p ≈ q, then the pair (p , q) belongs to the kernel of every homomorphism φ : hom (𝑻 X) 𝑨 from the term algebra to 𝑨; that is, every homomorphism from 𝑻 X to 𝑨 maps p and q to the same element of 𝑨.

\begin{code}

module _ {fe : dfunext 𝓥 (ov 𝓧)}
         (𝑨 : Algebra 𝓤 𝑆)(p q : Term X)
 where

 ⊧-H-invar : dfunext 𝓥 (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⁺)) → dfunext 𝓥 𝓤 → (φ : hom (𝑻 X) 𝑨) → 𝑨 ⊧ p ≈ q  →  ∣ φ ∣ p ≡ ∣ φ ∣ q

 ⊧-H-invar fe few φ β = ∣ φ ∣ p                ≡⟨ ap ∣ φ ∣ (term-agreement {fe = fe} p) ⟩
                 ∣ φ ∣((𝑻 X ⟦ p ⟧) ℊ)   ≡⟨ (comm-hom-term few 𝑨 φ p ℊ ) ⟩
                 (𝑨 ⟦ p ⟧) (∣ φ ∣ ∘ ℊ)  ≡⟨ extfun β (∣ φ ∣ ∘ ℊ ) ⟩
                 (𝑨 ⟦ q ⟧) (∣ φ ∣ ∘ ℊ)  ≡⟨ (comm-hom-term few 𝑨 φ q ℊ )⁻¹ ⟩
                 ∣ φ ∣ ((𝑻 X ⟦ q ⟧) ℊ)  ≡⟨(ap ∣ φ ∣ (term-agreement {fe = fe} q))⁻¹ ⟩
                 ∣ φ ∣ q             ∎

\end{code}

More generally, an identity is satisfied by all algebras in a class if and only if that identity is invariant under all homomorphisms from the term algebra `𝑻 X` into algebras of the class. More precisely, if `𝒦` is a class of `𝑆`-algebras and `𝑝`, `𝑞` terms in the language of `𝑆`, then,

`𝒦 ⊧ p ≈ q  ⇔  ∀ 𝑨 ∈ 𝒦,  ∀ φ : hom (𝑻 X) 𝑨,  φ ∘ (𝑝 ̇ (𝑻 X)) = φ ∘ (𝑞 ̇ (𝑻 X))`.

\begin{code}

module _ {fe : dfunext 𝓥 (ov 𝓧)}
         {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}(p q : Term X)
 where
 -- ⇒ (the "only if" direction)
 ⊧-H-class-invar : dfunext (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⁺)) 𝓤 → dfunext 𝓥 𝓤
  →                𝒦 ⊧ p ≋ q → ∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘ (𝑻 X ⟦ q ⟧)
 ⊧-H-class-invar fe few α 𝑨 φ ka = fe ξ
  where
   ξ : ∀(𝒂 : X → ∣ 𝑻 X ∣ ) → ∣ φ ∣ ((𝑻 X ⟦ p ⟧) 𝒂) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) 𝒂)
   ξ 𝒂 = ∣ φ ∣ ((𝑻 X ⟦ p ⟧) 𝒂)  ≡⟨ comm-hom-term few 𝑨 φ p 𝒂 ⟩
         (𝑨 ⟦ p ⟧)(∣ φ ∣ ∘ 𝒂)   ≡⟨ extfun (α ka) (∣ φ ∣ ∘ 𝒂) ⟩
         (𝑨 ⟦ q ⟧)(∣ φ ∣ ∘ 𝒂)   ≡⟨ (comm-hom-term few 𝑨 φ q 𝒂)⁻¹ ⟩
         ∣ φ ∣ ((𝑻 X ⟦ q ⟧) 𝒂)  ∎


-- ⇐ (the "if" direction)
 ⊧-H-class-coinvar : dfunext (𝓤 ⊔ 𝓧) 𝓤 → dfunext 𝓥 𝓤
  →  (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘ (𝑻 X ⟦ q ⟧)) → 𝒦 ⊧ p ≋ q

 ⊧-H-class-coinvar fe few β {𝑨} ka = γ
  where
  φ : (𝒂 : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
  φ 𝒂 = lift-hom 𝑨 𝒂

  γ : 𝑨 ⊧ p ≈ q
  γ = fe λ 𝒂 → (𝑨 ⟦ p ⟧)(∣ φ 𝒂 ∣ ∘ ℊ)     ≡⟨(comm-hom-term few 𝑨 (φ 𝒂) p ℊ)⁻¹ ⟩
               (∣ φ 𝒂 ∣ ∘ (𝑻 X ⟦ p ⟧)) ℊ  ≡⟨ cong-app (β 𝑨 (φ 𝒂) ka) ℊ ⟩
               (∣ φ 𝒂 ∣ ∘ (𝑻 X ⟦ q ⟧)) ℊ  ≡⟨ (comm-hom-term few 𝑨 (φ 𝒂) q ℊ) ⟩
               (𝑨 ⟦ q ⟧)(∣ φ 𝒂 ∣ ∘ ℊ)     ∎


 ⊧-H : dfunext (𝓞 ⊔ 𝓥 ⊔ (𝓧 ⁺)) 𝓤 → dfunext 𝓥 𝓤 → dfunext (𝓤 ⊔ 𝓧) 𝓤 → dfunext 𝓥 𝓤
  →    𝒦 ⊧ p ≋ q ⇔ (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘(𝑻 X ⟦ q ⟧))
 ⊧-H fe few fe' few' = ⊧-H-class-invar fe few , ⊧-H-class-coinvar fe' few'

\end{code}




-------------------------------------

[↑ Varieties](Varieties.html)
<span style="float:right;">[Varieties.Varieties →](Varieties.Varieties.html)</span>

{% include UALib.Links.md %}







<!--
 γ --
  where
  ζ : ∣ φ ∣ p ≡ ∣ φ ∣ q
  ζ = ⊧-H-invar{fe = fe} 𝑨 p q φ (α ka)

  γ' : ∣ φ ∣ ((𝑻 X ⟦ p ⟧) ℊ) ≡ ∣ φ ∣ ((𝑻 X ⟦ q ⟧) ℊ)
  γ' = ∣ φ ∣ ((𝑻 X ⟦ p ⟧) ℊ) ≡⟨ (ap ∣ φ ∣ (term-agreement {fe = fe} p))⁻¹ ⟩
       ∣ φ ∣ p  ≡⟨ ζ ⟩
       ∣ φ ∣ q  ≡⟨ ap ∣ φ ∣ (term-agreement {fe = fe} q) ⟩
       ∣ φ ∣ ((𝑻 X ⟦ q ⟧)ℊ ) ∎

  γ : ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘ (𝑻 X ⟦ q ⟧)
  γ = ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡⟨ {!!} ⟩
      (𝑨 ⟦ p ⟧) (λ (𝑎 : X → ∣ 𝑻 X ∣) → ∣ φ ∣ ∘ 𝑎)  ≡⟨ ?  ⟩
      (𝑨 ⟦ q ⟧) ∣ φ ∣  ≡⟨ ? ⟩
      ∣ φ ∣ ∘ (𝑻 X ⟦ q ⟧) ∎

-->
