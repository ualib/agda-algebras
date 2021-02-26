---
layout: default
title : UALib.Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [UALib.Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Quotients where

open import Relations.Binary public
-- open import UALib.Prelude.Preliminaries using (_⇔_; id) public

\end{code}


#### <a id="properties-of-binary-relations">Properties of binary relations</a>

Let `𝓤 : Universe` be a universe and `A : 𝓤 ̇` a type.  In [Relations.Binary][] we defined a type representing a binary relation on A.  In this module we will define types for binary relations that have special properties. The most important special properties of relations are the ones we now define.

\begin{code}

module _ {𝓤 : Universe} where

 reflexive : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 reflexive _≈_ = ∀ x → x ≈ x

 symmetric : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 antisymmetric : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 antisymmetric _≈_ = ∀ x y → x ≈ y → y ≈ x → x ≡ y

 transitive : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

 open import MGS-Subsingleton-Theorems using (is-subsingleton)


 is-subsingleton-valued : {𝓡 : Universe}{A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)

\end{code}



#### <a id="equivalence-classes">Equivalence classes</a>

A binary relation is called a **preorder** if it is reflexive and transitive. An **equivalence relation** is a symmetric preorder.


\begin{code}

module _ {𝓤 𝓡 : Universe} where

 is-preorder : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-preorder _≈_ = is-subsingleton-valued _≈_ × reflexive _≈_ × transitive _≈_

 record IsEquivalence {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
  field
   rfl   : reflexive _≈_
   sym   : symmetric _≈_
   trans : transitive _≈_

 is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-equivalence-relation _≈_ = is-preorder _≈_ × symmetric _≈_

\end{code}

An easy first example of an equivalence relation is the kernel of any function.

\begin{code}

map-kernel-IsEquivalence : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}
                            (f : A → B) → IsEquivalence (KER-rel{𝓤}{𝓦} f)

map-kernel-IsEquivalence {𝓤}{𝓦} f =
 record { rfl = λ x → 𝓇ℯ𝒻𝓁
        ; sym = λ x y x₁ → ≡-sym{𝓦} (f x) (f y) x₁
        ; trans = λ x y z x₁ x₂ → ≡-trans (f x) (f y) (f z) x₁ x₂ }

\end{code}




#### <a id="equivalence-classes">Equivalence classes</a>

If R is an equivalence relation on A, then for each `𝑎 : A`, there is an **equivalence class** containing 𝑎, which we denote and define by [ 𝑎 ] R := all `𝑏 : A` such that R 𝑎 𝑏. We often refer to [ 𝑎 ] R as the *R-class containing* 𝑎.

\begin{code}
module _ {𝓤 𝓡 : Universe} where

 [_]_ : {A : 𝓤 ̇ } → A → Rel A 𝓡 → Pred A 𝓡
 [ 𝑎 ] R = λ x → R 𝑎 x

 infix 60 [_]_
\end{code}

So, `x ∈ [ a ] R` if and only if `R a x`, as desired.

We define type of all R-classes of the relation `R` as follows.

\begin{code}

 𝒞 : {A : 𝓤 ̇}{R : Rel A 𝓡} → Pred A 𝓡 → (𝓤 ⊔ 𝓡 ⁺) ̇
 𝒞 {A}{R} = λ (C : Pred A _) → Σ a ꞉ A , C ≡ ( [ a ] R)

\end{code}

If `R` is an equivalence relation on `A`, then the **quotient** of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ 𝑎 ] R ∣  𝑎 : A}` of all equivalence classes of `R`. There are a few ways we could define the quotient with respect to a relation, but we find the following to be the most useful.

\begin{code}

 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → 𝓤 ⊔ (𝓡 ⁺) ̇
 A / R = Σ C ꞉ Pred A _ ,  𝒞{A}{R} C

 infix -1 _/_
\end{code}

We define the following introduction rule for an R-class with a designated representative.

\begin{code}

 ⟦_⟧ : {A : 𝓤 ̇} → A → {R : Rel A 𝓡} → A / R
 ⟦ a ⟧ {R} = [ a ] R , a , 𝓇ℯ𝒻𝓁

 infix 60 ⟦_⟧
\end{code}

If the relation is reflexive, then we have the following elimination rules.

\begin{code}

 /-refl : {A : 𝓤 ̇}(a a' : A){R : Rel A 𝓡} → reflexive R → [ a ] R ≡ [ a' ] R → R a a'

 /-refl a a' rfl x  = cong-app-pred a' (rfl a') (x ⁻¹)


 ⌜_⌝ : {A : 𝓤 ̇}{R : Rel A 𝓡} → A / R  → A

 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

\end{code}

Later we will need the following additional quotient tools.

\begin{code}

module _ {𝓤 𝓡 : Universe}{A : 𝓤 ̇} where

 open IsEquivalence{𝓤}{𝓡}

 /-subset : {a a' : A}{R : Rel A 𝓡} → IsEquivalence R → R a a' →  [ a ] R  ⊆  [ a' ] R
 /-subset {a}{a'} Req Raa' {x} Rax = (trans Req) a' a x (sym Req a a' Raa') Rax

 /-supset : {a a' : A}{R : Rel A 𝓡} → IsEquivalence R → R a a' →  [ a ] R  ⊇  [ a' ] R
 /-supset {a}{a'} Req Raa' {x} Ra'x = (trans Req) a a' x Raa' Ra'x

 /-=̇ : {a a' : A}{R : Rel A 𝓡} → IsEquivalence R → R a a' →  [ a ] R  ≐  [ a' ] R
 /-=̇ Req Raa' = /-subset Req Raa' , /-supset Req Raa'

\end{code}


#### <a id="compatibility-of-lifts-and-functions">Compatibility of lifts and functions</a>

Finally, we define some types that are useful for asserting and proving facts about *compatibility* of relations and functions.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe} {γ : 𝓥 ̇} {Z : 𝓤 ̇} where

 lift-rel : Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R f g = ∀ x → R (f x) (g x)

 compatible-fun : (f : (γ → Z) → Z)(R : Rel Z 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

\end{code}

We used the slick implication notation in the definition of `compatible-fun`, but we could have defined it more explicitly, like so.

\begin{code}

 compatible-fun' : (f : (γ → Z) → Z)(R : Rel Z 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun' f R  = ∀ x y → (lift-rel R) x y → R (f x) (f y)

\end{code}

However, this is a rare case in which the more elegant syntax may result in simpler proofs when applying the definition. (See, for example, `compatible-term` in the [Terms.Operations][] module.)

--------------------------------------

[← Relations.Binary](Relations.Binary.html)
<span style="float:right;">[Relations.Truncation →](Relations.Truncation.html)</span>

{% include UALib.Links.md %}

