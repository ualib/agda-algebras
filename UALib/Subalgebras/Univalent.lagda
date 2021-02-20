---
layout: default
title : UALib.Subalgebras.Univalent module (The Agda Universal Algebra Library)
date : 2021-02-20
author: William DeMeo
---

### <a id="univalent-subalgebras">Univalent Subalgebras</a>

This section presents the [UALib.Subalgebras.Univalent][] module of the [Agda Universal Algebra Library][].

In his Type Topology library, Martin Escardo gives a nice formalization of the notion of subgroup and its properties.  In this module we merely do for algebras what Martin did for groups.


This is our first foray into univalent foundations, and our first chance to put Voevodsky's univalence axiom to work.

As one can see from the import statement that starts with `open import Prelude.Preliminaries`, there are many new definitions and theorems imported from Escardo's Type Topology library.  Most of these will not be discussed here.

This module can be safely skipped, or even left out of the Agda Universal Algebra Library, as it plays no role in other modules.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Subalgebras.Univalent {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Subalgebras.Subalgebras {𝑆 = 𝑆}{gfe} public

open import UALib.Prelude.Preliminaries using (∘-embedding; id-is-embedding; Univalence;
 Π-is-subsingleton; ∈₀-is-subsingleton; pr₁-embedding; embedding-gives-ap-is-equiv; _●_; _≃_;
 equiv-to-subsingleton; powersets-are-sets'; lr-implication; rl-implication; inverse;
 subset-extensionality'; ×-is-subsingleton; logically-equivalent-subsingletons-are-equivalent)

module mhe_subgroup_generalization {𝓦 : Universe} {𝑨 : Algebra 𝓦 𝑆} (ua : Univalence) where

 op-closed : (∣ 𝑨 ∣ → 𝓦 ̇) → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ̇
 op-closed B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → ((i : ∥ 𝑆 ∥ f) → B (a i)) → B ((f ̂ 𝑨) a)


 subuniverse : 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 subuniverse = Σ B ꞉ (𝓟 ∣ 𝑨 ∣) , op-closed ( _∈₀ B)


 being-op-closed-is-subsingleton : (B : 𝓟 ∣ 𝑨 ∣) → is-subsingleton (op-closed ( _∈₀ B ))

 being-op-closed-is-subsingleton B = Π-is-subsingleton gfe
  (λ f → Π-is-subsingleton gfe
   (λ a → Π-is-subsingleton gfe
    (λ _ → ∈₀-is-subsingleton B ((f ̂ 𝑨) a))))


 pr₁-is-embedding : is-embedding ∣_∣
 pr₁-is-embedding = pr₁-embedding being-op-closed-is-subsingleton


 --so equality of subalgebras is equality of their underlying subsets in the powerset:
 ap-pr₁ : (B C : subuniverse) → B ≡ C → ∣ B ∣ ≡ ∣ C ∣
 ap-pr₁ B C = ap ∣_∣

 ap-pr₁-is-equiv : (B C : subuniverse) → is-equiv (ap-pr₁ B C)
 ap-pr₁-is-equiv = embedding-gives-ap-is-equiv ∣_∣ pr₁-is-embedding



 subuniverse-is-a-set : is-set subuniverse
 subuniverse-is-a-set B C = equiv-to-subsingleton
                            (ap-pr₁ B C , ap-pr₁-is-equiv B C)
                            (powersets-are-sets' ua ∣ B ∣ ∣ C ∣)


 subuniverse-equality-gives-membership-equiv : (B C : subuniverse)
  →                                  B ≡ C
                      ----------------------------------------
  →                   ( x : ∣ 𝑨 ∣ ) → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣)
 subuniverse-equality-gives-membership-equiv B C B≡C x =
  transport (λ - → x ∈₀ ∣ - ∣) B≡C ,
   transport (λ - → x ∈₀ ∣ - ∣ ) ( B≡C ⁻¹ )


 membership-equiv-gives-carrier-equality : (B C : subuniverse)
  →          ((x : ∣ 𝑨 ∣) →  x ∈₀ ∣ B ∣  ⇔  x ∈₀ ∣ C ∣)
             --------------------------------------
  →                       ∣ B ∣ ≡ ∣ C ∣

 membership-equiv-gives-carrier-equality B C φ =
  subset-extensionality' ua α β
   where
    α :  ∣ B ∣ ⊆₀ ∣ C ∣
    α x = lr-implication (φ x)

    β : ∣ C ∣ ⊆₀ ∣ B ∣
    β x = rl-implication (φ x)


 membership-equiv-gives-subuniverse-equality : (B C : subuniverse)
  →            (( x : ∣ 𝑨 ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
               ---------------------------------------
  →                          B ≡ C
 membership-equiv-gives-subuniverse-equality B C =
  inverse (ap-pr₁ B C)
  (ap-pr₁-is-equiv B C)
     ∘ (membership-equiv-gives-carrier-equality B C)


 membership-equiv-is-subsingleton : (B C : subuniverse)
  →                                 is-subsingleton (( x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)

 membership-equiv-is-subsingleton B C =
  Π-is-subsingleton gfe
   (λ x → ×-is-subsingleton
    (Π-is-subsingleton gfe (λ _ → ∈₀-is-subsingleton ∣ C ∣ x ))
      (Π-is-subsingleton gfe (λ _ → ∈₀-is-subsingleton ∣ B ∣ x )))


 subuniverse-equality : (B C : subuniverse)
  →                     (B ≡ C)  ≃  ((x : ∣ 𝑨 ∣) → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣))

 subuniverse-equality B C =
  logically-equivalent-subsingletons-are-equivalent _ _
    (subuniverse-is-a-set B C)
     (membership-equiv-is-subsingleton B C)
      (subuniverse-equality-gives-membership-equiv B C ,
        membership-equiv-gives-subuniverse-equality B C)


 carrier-equality-gives-membership-equiv : (B C : subuniverse)
  →                          ∣ B ∣ ≡ ∣ C ∣
                 --------------------------------------
  →              ((x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣  ⇔  x ∈₀ ∣ C ∣)

 carrier-equality-gives-membership-equiv B C (refl _) x = id , id


 --so we have...
 carrier-equiv : (B C : subuniverse)
  →              ((x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣) ≃ (∣ B ∣ ≡ ∣ C ∣)

 carrier-equiv B C =
  logically-equivalent-subsingletons-are-equivalent _ _
   (membership-equiv-is-subsingleton B C)
    (powersets-are-sets' ua ∣ B ∣ ∣ C ∣)
     (membership-equiv-gives-carrier-equality B C ,
       carrier-equality-gives-membership-equiv B C)

 -- ...which yields an alternative subuniverse equality lemma.
 subuniverse-equality' : (B C : subuniverse) → (B ≡ C) ≃ (∣ B ∣ ≡ ∣ C ∣)

 subuniverse-equality' B C = (subuniverse-equality B C) ● (carrier-equiv B C)

\end{code}

---------------------------------

[← UALib.Subalgebras.Subalgebras](UALib.Subalgebras.Subalgebras.html)
<span style="float:right;">[UALib.Varieties →](UALib.Varieties.html)</span>

{% include UALib.Links.md %}

