---
layout: default
title : UALib.Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="quotient-types">Quotient Types</a>

This section presents the [UALib.Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Relations.Quotients where

open import UALib.Relations.Equivalences public
open import UALib.Prelude.Preliminaries using (_⇔_; id) public

module _ {𝓤 𝓡 : Universe} where

 -- relation class
 [_] : {A : 𝓤 ̇ } → A → Rel A 𝓡 → Pred A 𝓡
 [ a ] R = λ x → R a x

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 []-elim : {A : 𝓤 ̇ }{a x : A}{R : Rel A 𝓡}
  →         R a x ⇔ (x ∈ [ a ] R)
 []-elim = id , id

 -- The type of R-classes
 𝒞 : {A : 𝓤 ̇}{R : Rel A 𝓡} → Pred A 𝓡 → (𝓤 ⊔ 𝓡 ⁺) ̇
 𝒞 {A}{R} = λ (C : Pred A 𝓡) → Σ a ꞉ A , C ≡ ( [ a ] R)

 -- relation quotient (predicate version)
 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → 𝓤 ⊔ (𝓡 ⁺) ̇
 A / R = Σ C ꞉ Pred A 𝓡 ,  𝒞{A}{R} C
 -- old version:  A / R = Σ C ꞉ Pred A 𝓡 ,  Σ a ꞉ A ,  C ≡ ( [ a ] R )

 -- For a reflexive relation, we have the following elimination rule.
 /-refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   reflexive R → [ a ] R ≡ [ a' ] R → R a a'
 /-refl{A = A}{a}{a'}{R} rfl x  = γ
  where
   a'in : a' ∈ [ a' ] R
   a'in = rfl a'
   γ : a' ∈ [ a ] R
   γ = cong-app-pred a' a'in (x ⁻¹)

 /-refl' : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   transitive R → R a' a → ([ a ] R) ⊆ ([ a' ] R)
 /-refl'{A = A}{a}{a'}{R} trn Ra'a {x} aRx = trn a' a x Ra'a aRx

 ⌜_⌝ : {A : 𝓤 ̇}{R : Rel A 𝓡} → A / R  → A
 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- introduction rule for relation class with designated representative
 ⟦_⟧ : {A : 𝓤 ̇} → A → {R : Rel A 𝓡} → A / R
 ⟦ a ⟧ {R} = ([ a ] R) , a , 𝓇ℯ𝒻𝓁

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 ⟦⟧-elim : {A : 𝓤 ̇ }{a x : A}{R : Rel A 𝓡}
  →         R a x ⇔ (x ∈ [ a ] R)
 ⟦⟧-elim = id , id

 -- elimination rule for relation class representative
 /-Refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   reflexive R → ⟦ a ⟧{R} ≡ ⟦ a' ⟧ → R a a'
 /-Refl rfl (refl _)  = rfl _

 open IsEquivalence{𝓤}{𝓡}

 /-subset : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) ⊆ ([ a' ] R)
 /-subset {A = A}{a}{a'}{R} Req Raa' {x} Rax = (trans Req) a' a x (sym Req a a' Raa') Rax

 /-supset : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) ⊇ ([ a' ] R)
 /-supset {A = A}{a}{a'}{R} Req Raa' {x} Ra'x = (trans Req) a a' x Raa' Ra'x

 /-=̇ : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) =̇ ([ a' ] R)
 /-=̇ {A = A}{a}{a'}{R} Req Raa' = /-subset Req Raa' , /-supset Req Raa'
\end{code}

#### Quotient extensionality

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  For this we assume that our relations are on sets, rather than arbitrary types.  For us, this is equivalent to assuming that there is at most one proof that two elements of a set are the same.  In other words, a set is a type with *unique identity proofs*. As a general principle, this is sometimes referred to as "proof irrelevance"---two proofs of a single identity are equal.

\begin{code}
 class-extensionality : propext 𝓡 → global-dfunext
  →       {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →       (∀ a x → is-subsingleton (R a x))
  →       IsEquivalence R
         ---------------------------------------
  →        R a a' → ([ a ] R) ≡ ([ a' ] R)

 class-extensionality pe gfe {A = A}{a}{a'}{R} ssR Req Raa' =
  Pred-=̇-≡ pe gfe {A}{[ a ] R}{[ a' ] R} (ssR a) (ssR a') (/-=̇ Req Raa')

 to-subtype-⟦⟧ : {A : 𝓤 ̇}{R : Rel A 𝓡}{C D : Pred A 𝓡}
                 {c : 𝒞 C}{d : 𝒞 D}
  →              (∀ C → is-subsingleton (𝒞{A}{R} C))
  →              C ≡ D  →  (C , c) ≡ (D , d)

 to-subtype-⟦⟧ {D = D}{c}{d} ssA CD = to-Σ-≡ (CD , ssA D (transport 𝒞 CD c) d)

 class-extensionality' : propext 𝓡 → global-dfunext
  →       {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →       (∀ a x → is-subsingleton (R a x))
  →       (∀ C → is-subsingleton (𝒞 C))
  →       IsEquivalence R
         ---------------------------------------
  →        R a a' → (⟦ a ⟧ {R}) ≡ (⟦ a' ⟧ {R})

 class-extensionality' pe gfe {A = A}{a}{a'}{R} ssR ssA Req Raa' = γ
  where
   CD : ([ a ] R) ≡ ([ a' ] R)
   CD = class-extensionality pe gfe {A}{a}{a'}{R} ssR Req Raa'

   γ : (⟦ a ⟧ {R}) ≡ (⟦ a' ⟧ {R})
   γ = to-subtype-⟦⟧ ssA CD

\end{code}

#### Compatibility

The following definitions and lemmas are useful for asserting and proving facts about compatibility of relations and functions.

\begin{code}
module _ {𝓤 𝓥 𝓦 : Universe} {γ : 𝓥 ̇ } {Z : 𝓤 ̇ } where

 lift-rel : Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R f g = ∀ x → R (f x) (g x)

 compatible-fun : (f : (γ → Z) → Z)(R : Rel Z 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

-- relation compatible with an operation
module _ {𝓤 𝓦 : Universe} {𝑆 : Signature 𝓞 𝓥} where
 compatible-op : {𝑨 : Algebra 𝓤 𝑆} → ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 compatible-op {𝑨} f R = ∀{𝒂}{𝒃} → (lift-rel R) 𝒂 𝒃  → R ((f ̂ 𝑨) 𝒂) ((f ̂ 𝑨) 𝒃)
 -- alternative notation: (lift-rel R) =[ f ̂ 𝑨 ]⇒ R

--The given relation is compatible with all ops of an algebra.
 compatible :(𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 compatible  𝑨 R = ∀ f → compatible-op{𝑨} f R
\end{code}

#### Examples

\begin{code}
module _ {𝓤 : Universe} {𝑆 : Signature 𝓞 𝓥} where

 𝟎-compatible-op : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} (f : ∣ 𝑆 ∣)
  →                   compatible-op {𝓤 = 𝓤}{𝑨 = 𝑨} f 𝟎-rel
 𝟎-compatible-op fe {𝑨} f ptws0  = ap (f ̂ 𝑨) (fe (λ x → ptws0 x))

 𝟎-compatible : funext 𝓥 𝓤 → {A : Algebra 𝓤 𝑆} → compatible A 𝟎-rel
 𝟎-compatible fe {A} = λ f args → 𝟎-compatible-op fe {A} f args
\end{code}


--------------------------------------

[← UALib.Relations.Equivalences](UALib.Relations.Equivalences.html)
<span style="float:right;">[UALib.Relations.Congruences →](UALib.Relations.Congruences.html)</span>

{% include UALib.Links.md %}
