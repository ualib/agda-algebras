---
layout: default
title : "Base.Terms.Operations module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

### <a id="term-operations">Term Operations</a>

This section presents the [Base.Terms.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a
particular algebra, and we prove some compatibility properties of term operations.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Terms.Operations {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive  using ()  renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; Σ )
open import Function        using ( _∘_ )
open import Level           using ( Level ; _⊔_ )
open import Relation.Binary.PropositionalEquality as ≡
                            using ( _≡_ ; module ≡-Reasoning )
open import Axiom.Extensionality.Propositional
                            using () renaming (Extensionality to funext)

-- Imports from Agda Universal Algebra Library ----------------------------------------------
open import Overture        using ( _∙_ ; _⁻¹ ; ∣_∣ ; ∥_∥ ; Π ; Π-syntax ; _≈_ )
open import Legacy.Base.Relations  using ( _|:_ )
open import Legacy.Base.Equality   using ( swelldef )

open import Legacy.Base.Algebras          {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; ov ; ⨅ )
                                            using ( IsCongruence ; Con )
open import Legacy.Base.Homomorphisms     {𝑆 = 𝑆}  using ( hom )
open import Legacy.Base.Terms.Basic       {𝑆 = 𝑆}  using ( Term ; 𝑻 )
open import Legacy.Base.Terms.Properties  {𝑆 = 𝑆}  using ( free-lift )

open Term
private variable α β γ ρ χ : Level
```


When we interpret a term in an algebra we call the resulting function a
*term operation*. Given a term `p` and an algebra `𝑨`, we denote by `𝑨 ⟦ p ⟧`
the *interpretation* of `p` in `𝑨`.  This is defined inductively as follows.

1.  If `p` is a variable symbol `x : X` and if `a : X → ∣ 𝑨 ∣` is a tuple of
    elements of `∣ 𝑨 ∣`, then `𝑨 ⟦ p ⟧ a := a x`.

2.  If `p = f t`, where `f : ∣ 𝑆 ∣` is an operation symbol, if `t : ∥ 𝑆 ∥ f → 𝑻 X`
    is a tuple of terms, and if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we
    define `𝑨 ⟦ p ⟧ a = 𝑨 ⟦ f t ⟧ a := (f ̂ 𝑨) (λ i → 𝑨 ⟦ t i ⟧ a)`.

Thus the interpretation of a term is defined by induction on the structure of the
term, and the definition is formally implemented in the [agda-algebras][]
library as follows.


```agda


_⟦_⟧ : (𝑨 : Algebra α){X : Type χ } → Term X → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
𝑨 ⟦ ℊ x ⟧ = λ η → η x
𝑨 ⟦ node f t ⟧ = λ η → (f ̂ 𝑨) (λ i → (𝑨 ⟦ t i ⟧) η)
```


It turns out that the intepretation of a term is the same as the `free-lift`
(modulo argument order and assuming function extensionality).


```agda


free-lift-interp :  swelldef 𝓥 α → (𝑨 : Algebra α){X : Type χ }
                    (η : X → ∣ 𝑨 ∣)(p : Term X) → (𝑨 ⟦ p ⟧) η ≡ (free-lift 𝑨 η) p

free-lift-interp _ 𝑨 η (ℊ x) = ≡.refl
free-lift-interp wd 𝑨 η (node f t) =
 wd (f ̂ 𝑨) (λ z → (𝑨 ⟦ t z ⟧) η)
 ((free-lift 𝑨 η) ∘ t)((free-lift-interp wd 𝑨 η) ∘ t)
```


If the algebra in question happens to be `𝑻 X`, then we expect that `∀ s`
we have `(𝑻 X)⟦ p ⟧ s ≡ p s`. But what is `(𝑻 X)⟦ p ⟧ s` exactly? By
definition, it depends on the form of `p` as follows:

*  if `p = ℊ x`, then `(𝑻 X)⟦ p ⟧ s := (𝑻 X)⟦ ℊ x ⟧ s ≡ s x`

*  if `p = node f t`, then
   `(𝑻 X)⟦ p ⟧ s := (𝑻 X)⟦ node f t ⟧ s = (f ̂ 𝑻 X) λ i → (𝑻 X)⟦ t i ⟧ s`

Now, assume `ϕ : hom 𝑻 𝑨`. Then by `comm-hom-term`, we have
`∣ ϕ ∣ (𝑻 X)⟦ p ⟧ s = 𝑨 ⟦ p ⟧ ∣ ϕ ∣ ∘ s`.

* if `p = ℊ x` (and `t : X → ∣ 𝑻 X ∣`), then

  `∣ ϕ ∣ p ≡ ∣ ϕ ∣ (ℊ x) ≡ ∣ ϕ ∣ (λ t → h t) ≡ λ t → (∣ ϕ ∣ ∘ t) x`

* if `p = node f t`, then

   `∣ ϕ ∣ p ≡ ∣ ϕ ∣ (𝑻 X)⟦ p ⟧ s = (𝑻 X)⟦ node f t ⟧ s = (f ̂ 𝑻 X) λ i → (𝑻 X)⟦ t i ⟧ s`

We claim that for all `p : Term X` there exists `q : Term X` and `t : X → ∣ 𝑻 X ∣`
such that `p ≡ (𝑻 X)⟦ q ⟧ t`. We prove this fact as follows.


```agda


term-interp :  {X : Type χ} (f : ∣ 𝑆 ∣){s t : ∥ 𝑆 ∥ f → Term X}
 →             s ≡ t → node f s ≡ (f ̂ 𝑻 X) t

term-interp f {s}{t} st = ≡.cong (node f) st


term-interp' :  swelldef 𝓥 (ov χ) → {X : Type χ} (f : ∣ 𝑆 ∣){s t : ∥ 𝑆 ∥ f → Term X}
 →              (∀ i → s i ≡ t i) → node f s ≡ (f ̂ 𝑻 X) t

term-interp' wd f {s}{t} st = wd (node f) s t st


term-gen :  swelldef 𝓥 (ov χ) → {X : Type χ}(p : ∣ 𝑻 X ∣)
 →          Σ[ q ∈ ∣ 𝑻 X ∣ ] p ≡ (𝑻 X ⟦ q ⟧) ℊ

term-gen _ (ℊ x) = (ℊ x) , ≡.refl
term-gen wd (node f t) =  (node f (λ i → ∣ term-gen wd (t i) ∣)) ,
                          term-interp' wd f λ i → ∥ term-gen wd (t i) ∥

term-gen-agreement :  (wd : swelldef 𝓥 (ov χ)){X : Type χ}(p : ∣ 𝑻 X ∣)
 →                    (𝑻 X ⟦ p ⟧) ℊ ≡ (𝑻 X ⟦ ∣ term-gen wd p ∣ ⟧) ℊ
term-gen-agreement _ (ℊ x) = ≡.refl
term-gen-agreement wd {X} (node f t) = wd  ( f ̂ 𝑻 X) (λ x → (𝑻 X ⟦ t x ⟧) ℊ)
                                           (λ x → (𝑻 X ⟦ ∣ term-gen wd (t x) ∣ ⟧) ℊ)
                                           λ i → term-gen-agreement wd (t i)

term-agreement : swelldef 𝓥 (ov χ) → {X : Type χ}(p : ∣ 𝑻 X ∣) → p ≡  (𝑻 X ⟦ p ⟧) ℊ
term-agreement wd {X} p = ∥ term-gen wd p ∥ ∙ (term-gen-agreement wd p)⁻¹
```



#### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>


```agda


module _ (wd : swelldef 𝓥 (β ⊔ α)){X : Type χ }{I : Type β} where

 interp-prod :  (p : Term X)(𝒜 : I → Algebra α)(a : X → Π[ i ∈ I ] ∣ 𝒜 i ∣)
  →             (⨅ 𝒜 ⟦ p ⟧) a ≡ λ i → (𝒜 i ⟦ p ⟧)(λ x → (a x) i)

 interp-prod (ℊ _) 𝒜 a = ≡.refl
 interp-prod (node f t) 𝒜 a = wd ((f ̂ ⨅ 𝒜)) u v IH
  where
  u : ∀ x → ∣ ⨅ 𝒜 ∣
  u = λ x → (⨅ 𝒜 ⟦ t x ⟧) a
  v : ∀ x i → ∣ 𝒜 i ∣
  v = λ x i → (𝒜 i ⟦ t x ⟧)(λ j → a j i)
  IH : ∀ i → u i ≡ v i
  IH = λ x → interp-prod (t x) 𝒜 a

 interp-prod2 :  funext (α ⊔ β ⊔ χ) (α ⊔ β) → (p : Term X)(𝒜 : I → Algebra α)
  →              ⨅ 𝒜 ⟦ p ⟧ ≡ (λ a i → (𝒜 i ⟦ p ⟧) λ x → a x i)

 interp-prod2 _ (ℊ x₁) 𝒜 = ≡.refl
 interp-prod2 fe (node f t) 𝒜 = fe λ a → wd (f ̂ ⨅ 𝒜)(u a) (v a) (IH a)
  where
  u : ∀ a x → ∣ ⨅ 𝒜 ∣
  u a = λ x → (⨅ 𝒜 ⟦ t x ⟧) a
  v : ∀ (a : X → ∣ ⨅ 𝒜 ∣) → ∀ x i → ∣ 𝒜 i ∣
  v a = λ x i → (𝒜 i ⟦ t x ⟧)(λ z → (a z) i)
  IH : ∀ a x → (⨅ 𝒜 ⟦ t x ⟧) a ≡ λ i → (𝒜 i ⟦ t x ⟧)(λ z → (a z) i)
  IH a = λ x → interp-prod (t x) 𝒜 a
```



#### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which
is used very often in the sequel, asserts that every term commutes with every
homomorphism.


```agda


open ≡-Reasoning

comm-hom-term :  swelldef 𝓥 β → {𝑨 : Algebra α} (𝑩 : Algebra β)
                 (h : hom 𝑨 𝑩){X : Type χ}(t : Term X)(a : X → ∣ 𝑨 ∣)
                 ------------------------------------------------------
  →              ∣ h ∣ ((𝑨 ⟦ t ⟧) a) ≡ (𝑩 ⟦ t ⟧) (∣ h ∣ ∘ a)

comm-hom-term _ 𝑩 h (ℊ x) a = ≡.refl
comm-hom-term wd {𝑨} 𝑩 h (node f t) a =
 ∣ h ∣((f ̂ 𝑨) λ i →  (𝑨 ⟦ t i ⟧) a)      ≡⟨ i  ⟩
 (f ̂ 𝑩)(λ i →  ∣ h ∣ ((𝑨 ⟦ t i ⟧) a))   ≡⟨ ii ⟩
 (f ̂ 𝑩)(λ r → (𝑩 ⟦ t r ⟧) (∣ h ∣ ∘ a))  ∎
 where i  = ∥ h ∥ f λ r → (𝑨 ⟦ t r ⟧) a
       ii = wd (f ̂ 𝑩)  ( λ i₁ → ∣ h ∣ ((𝑨 ⟦ t i₁ ⟧) a) )
                       ( λ r → (𝑩 ⟦ t r ⟧) (λ x → ∣ h ∣ (a x)) )
                       λ j → comm-hom-term wd 𝑩 h (t j) a
```


To conclude this module, we prove that every term is compatible with every
congruence relation. That is, if `t : Term X` and `θ : Con 𝑨`, then
`a θ b → t(a) θ t(b)`. (Recall, the compatibility relation `|:` was defined in
[Relations.Discrete][].)


```agda



module _ {α β : Level}{X : Type α} where

 open IsCongruence

 _∣:_ : {𝑨 : Algebra α}(t : Term X)(θ : Con{α}{β} 𝑨) → (𝑨 ⟦ t ⟧) |: ∣ θ ∣
 ((ℊ x) ∣: θ) p = p x
 ((node f t) ∣: θ) p = (is-compatible ∥ θ ∥) f λ x → ((t x) ∣: θ) p
```


**WARNING!** The compatibility relation for terms `∣:` is typed as \|:, whereas
the compatibility type for functions `|:` (defined in the
[Base.Relations.Discrete][] module) is typed as `|:`.



#### <a id="substitution">Substitution</a>

A substitution from `Y` to `X` is simply a function from `Y` to `X`, and the
application of a substitution is represented as follows.


```agda


_[_] : {χ : Level}{X Y : Type χ} → Term Y → (Y → X) → Term X
(ℊ y) [ σ ] = ℊ (σ y)
(node f t)  [ σ ] = node f λ i → t i [ σ ]
```


Alternatively, we may want a substitution that replaces each variable symbol in
`Y`, not with an element of `X`, but with a term from `Term X`.


```agda


-- Substerm X Y, an inhabitant of which replaces each variable symbol in Y
-- with a term from Term X.
Substerm : (X Y : Type χ) → Type (ov χ)
Substerm X Y = (y : Y) → Term X

-- Application of a Substerm.
_[_]t : {X Y : Type χ } → Term Y → Substerm X Y → Term X
(ℊ y) [ σ ]t = σ y
(node f t) [ σ ]t = node f (λ z → (t z) [ σ ]t )
```


Next we prove the important Substitution Theorem which asserts that an identity `p
≈ q` holds in an algebra `𝑨` iff it holds in `𝑨` after applying any substitution.


```agda


subst-lemma :  swelldef 𝓥 α → {X Y : Type χ }(p : Term Y)(σ : Y → X)
               (𝑨 : Algebra α)(η : X → ∣ 𝑨 ∣)
 →             (𝑨 ⟦ p [ σ ] ⟧) η ≡ (𝑨 ⟦ p ⟧) (η ∘ σ)

subst-lemma _ (ℊ x) σ 𝑨 η = ≡.refl
subst-lemma wd (node f t) σ 𝑨 η = wd (f ̂ 𝑨)  ( λ i → (𝑨 ⟦ (t i) [ σ ] ⟧) η )
                                             ( λ i → (𝑨 ⟦ t i ⟧) (η ∘ σ) )
                                             λ i → subst-lemma wd (t i) σ 𝑨 η

subst-theorem :  swelldef 𝓥 α → {X Y : Type χ }
                 (p q : Term Y)(σ : Y → X)(𝑨 : Algebra α)
 →               𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧ → 𝑨 ⟦ p [ σ ] ⟧ ≈ 𝑨 ⟦ q [ σ ] ⟧

subst-theorem wd p q σ 𝑨 Apq η =
 (𝑨 ⟦ p [ σ ] ⟧) η  ≡⟨ subst-lemma wd p σ 𝑨 η ⟩
 (𝑨 ⟦ p ⟧) (η ∘ σ)  ≡⟨ Apq (η ∘ σ) ⟩
 (𝑨 ⟦ q ⟧) (η ∘ σ)  ≡⟨ ≡.sym (subst-lemma wd q σ 𝑨 η) ⟩
 (𝑨 ⟦ q [ σ ] ⟧) η  ∎
```


----------------------------------

<span style="float:left;">[← Base.Terms.Properties](Base.Terms.Properties.html)</span>
<span style="float:right;">[Base.Subalgebras →](Base.Subalgebras.html)</span>

{% include UALib.Links.md %}
