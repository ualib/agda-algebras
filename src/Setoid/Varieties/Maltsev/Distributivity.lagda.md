---
layout: default
file: "src/Setoid/Varieties/Maltsev/Distributivity.lagda.md"
title: "Setoid.Varieties.Maltsev.Distributivity module (The Agda Universal Algebra Library)"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Maltsev conditions: congruence distributivity

This is the [Setoid.Varieties.Maltsev.Distributivity][] module of the [Agda Universal Algebra Library][].

This module records the encoding of congruence distributivity (CD) — the Jónsson identities, as
a theory interpretation `Th-Jonsson n ≼ ℰ` — and states Jónsson's theorem.

#### Distributivity of the congruence lattice

CD is a property of the congruence *lattice*, defined in
[Setoid.Congruences.Properties][] as `CongruenceDistributive` (at the absorbing relation
level, so that meet and join are operations on a single type).  We use it here to phrase
the Jónsson variety condition below.


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev.Distributivity where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Bool.Base       using  ( true ; false ; if_then_else_ )
open import Data.Fin.Base        using  ( Fin ; toℕ ; fromℕ ; inject₁ ; zero )
                                 renaming ( suc to fsuc )
open import Data.Fin.Induction   using  ( <-weakInduction )
open import Data.Fin.Patterns    using  ( 0F ; 1F ; 2F )
open import Data.Nat.Base        using  ( ℕ ; suc )
open import Data.Product         using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Data.Sum.Base        using  ( inj₁ ; inj₂ )
open import Level                using  ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary      using  ( Setoid ; IsEquivalence )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Basic                   using  ( _⇔_ )
open import Overture.Signatures              using  ( Signature )
open import Overture.Terms                   using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation    using  ( Interpretation )
open import Setoid.Algebras.Basic            using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic         using  ( Con ; reflexive ; is-equivalence )
open import Setoid.Congruences.Generation    using  ( _∨_ ; _∪ᵣ_ ; ∨-upperˡ
                                                    ; ∨-upperʳ ; ∨-least )
open import Setoid.Congruences.ChainJoin     using  ( Chain ; nil ; cons ; JoinIsChain
                                                    ; Finitary ; finitary⇒JoinIsChain )
open import Setoid.Congruences.Lattice       using  ( _∧_ ; _⊆_ )
open import Setoid.Congruences.Properties    using  ( CongruenceDistributive )
open import Setoid.Terms.Basic               using  ( _[_] ; module Environment )
open import Setoid.Varieties.Interpretation  using  ( reductᴵ ; _⊨ₑ_ ; module Interpret )
open import Setoid.Varieties.Maltsev.Basic   using  ( tri ; even? ; term-compatible )

open import Function using ( Func )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α ρ χ ι ℓ : Level
```

#### Jónsson terms (congruence distributivity)

Where a single ternary term characterizes CP, a *chain* of ternary terms
`d₀ , … , dₙ` — the **Jónsson terms** — characterizes CD.[^jonsson]
They are encoded exactly as the Maltsev term was: a signature `Sig-Jonsson n` of
`n+1` ternary symbols, and a theory `Th-Jonsson n` of the Jónsson identities
(Burris–Sankappanavar, Def. 12.5),

    d₀(x,y,z) ≈ x,    dₙ(x,y,z) ≈ z,    dᵢ(x,y,x) ≈ x   (all i),
    dᵢ(x,x,z) ≈ dᵢ₊₁(x,x,z)   (i even),  dᵢ(x,y,y) ≈ dᵢ₊₁(x,y,y)   (i odd).

`HasJonssonTerms n ℰ = Th-Jonsson n ≼ ℰ` — `ℰ` admits `n+1` Jónsson terms iff the
Jónsson theory interprets into it, the same `Th-X ≼ ℰ` shape as `HasMaltsevTerm`.

```agda
module _ (n : ℕ) where

  -- n+1 ternary operation symbols.
  Sig-Jonsson : Signature 0ℓ 0ℓ
  Sig-Jonsson = Fin (suc n) , (λ _ → Fin 3)

  private
    -- the i-th Jónsson term applied to three arguments
    d : Fin (suc n) → (a b c : Term (Fin 3)) → Term (Fin 3)
    d i a b c = node i (tri a b c)

    x y z : Term {𝑆 = Sig-Jonsson} (Fin 3)
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F

  -- the index of the Jónsson identities: endpoints, the "x,y,x" family, and the forks
  data Eq-Jonsson : Type where
    dxyz≈x  : Eq-Jonsson                 -- d₀(x,y,z) ≈ x
    dxyz≈z  : Eq-Jonsson                 -- dₙ(x,y,z) ≈ z
    dxyx≈x  : Fin (suc n) → Eq-Jonsson   -- dᵢ(x,y,x) ≈ x
    d-fork  : Fin n → Eq-Jonsson         -- consecutive dᵢ, dᵢ₊₁ agree (parity-dependent)

  Th-Jonsson : Eq-Jonsson → Term {𝑆 = Sig-Jonsson} (Fin 3) × Term {𝑆 = Sig-Jonsson} (Fin 3)
  Th-Jonsson dxyz≈x      = d zero x y z , x
  Th-Jonsson (dxyx≈x i)  = d i x y x , x
  Th-Jonsson dxyz≈z      = d (fromℕ n) x y z , z
  Th-Jonsson (d-fork i) = if even? (toℕ i)
    then ( d (inject₁ i) x x z , d (fsuc i) x x z )   -- i even: agree on (x,x,z)
    else ( d (inject₁ i) x y y , d (fsuc i) x y y )   -- i odd:  agree on (x,y,y)

HasJonssonTerms : (n : ℕ) (α ρ : Level) {𝑆 : Signature 0ℓ 0ℓ} {X : Type χ} {Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
HasJonssonTerms n α ρ ℰ = Th-Jonsson n ≼ ℰ
  where open Interpret α ρ
```

#### Jónsson terms imply distributivity along chains

The forward direction of Jónsson's theorem (Burris–Sankappanavar, Thm. II.12.6) runs the
Jónsson terms along a **finite alternating walk** from `a` to `b` whose steps lie in `φ` or
in `ψ`.  Classically such a walk witnesses `(a , b) ∈ φ ∨ ψ`; here the join `φ ∨ ψ` is the
*inductively generated* congruence `Cg (φ ∪ ψ)`, whose `comp` closure makes it strictly
larger than the walk relation for an **infinitary** signature.  So the walk relation is
isolated as the type `Chain` ([Setoid.Congruences.ChainJoin][]), the staircase is proved
against it in full generality, and the two are identified — `JoinIsChain`,
`finitary⇒JoinIsChain`{.AgdaFunction} — exactly for the **finitary** signatures of ordinary
universal algebra.

Fix a model `𝑩` of a theory `ℰ` with `n+1` Jónsson terms.  The witnessing
interpretation `Iⱼ`{.AgdaFunction} sends the `i`-th Jónsson symbol to a derived
`𝑆`-term, whose evaluation against the named triple is the curried operation
`d𝑩 i`{.AgdaFunction}.  The single evaluation lemma `eval-d`{.AgdaFunction} rewrites a
Jónsson application in the reduct to `d𝑩`, and the Jónsson identities fall out by
instantiating the reduct's satisfaction of `Th-Jonsson n` — the same
`eval`/`sat` division of labour as the Maltsev `eval-m`{.AgdaFunction} /
`satM`{.AgdaFunction}, now over the `Fin (n+1)` chain.

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  {ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X}{n : ℕ}
  (jt : HasJonssonTerms n α ρ ℰ)(𝑩 : Algebra {𝑆 = 𝑆} α ρ)(B⊨ : 𝑩 ⊨ₑ ℰ)
  where
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ )
    renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Environment 𝑩 using ( ⟦_⟧ )
  open Environment (reductᴵ 𝑩 (proj₁ jt)) using () renaming ( ⟦_⟧ to ⟦_⟧ᴿ )

  -- the witnessing interpretation and the reduct's satisfaction of the Jónsson theory
  Iⱼ : Interpretation (Sig-Jonsson n) 𝑆
  Iⱼ = proj₁ jt

  satⱼ : reductᴵ 𝑩 Iⱼ ⊨ₑ Th-Jonsson n
  satⱼ = proj₂ jt 𝑩 B⊨

  -- the curried i-th Jónsson term operation
  d𝑩 : Fin (suc n) → 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ]
  d𝑩 i a b c = ⟦ Iⱼ i ⟧ ⟨$⟩ tri a b c

  -- evaluating a Jónsson application in the reduct lands on the curried d𝑩
  eval-d : (i : Fin (suc n))(i₀ i₁ i₂ : Fin 3)(η : Fin 3 → 𝕌[ 𝑩 ])
    → ⟦ node i (tri (ℊ i₀) (ℊ i₁) (ℊ i₂)) ⟧ᴿ ⟨$⟩ η ≈ d𝑩 i (η i₀) (η i₁) (η i₂)
  eval-d i i₀ i₁ i₂ η = cong ⟦ Iⱼ i ⟧ λ { 0F → ≈refl ; 1F → ≈refl ; 2F → ≈refl }

  -- the two endpoint identities and the "x,y,x" family, curried, from satⱼ
  d-fst : (a b c : 𝕌[ 𝑩 ]) → d𝑩 zero a b c ≈ a
  d-fst a b c = ≈trans (≈sym (eval-d zero 0F 1F 2F (tri a b c))) (satⱼ dxyz≈x (tri a b c))

  d-lst : (a b c : 𝕌[ 𝑩 ]) → d𝑩 (fromℕ n) a b c ≈ c
  d-lst a b c = ≈trans (≈sym (eval-d (fromℕ n) 0F 1F 2F (tri a b c))) (satⱼ dxyz≈z (tri a b c))

  d-mid : (i : Fin (suc n))(a b : 𝕌[ 𝑩 ]) → d𝑩 i a b a ≈ a
  d-mid i a b = ≈trans (≈sym (eval-d i 0F 1F 0F (tri a b a))) (satⱼ (dxyx≈x i) (tri a b a))

  -- d𝑩 i is a term operation, hence compatible with every congruence
  d-compat : (μ : Con 𝑩 ℓ)(i : Fin (suc n)){a a′ b b′ c c′ : 𝕌[ 𝑩 ]}
    → proj₁ μ a a′ → proj₁ μ b b′ → proj₁ μ c c′ → proj₁ μ (d𝑩 i a b c) (d𝑩 i a′ b′ c′)
  d-compat μ i {a}{a′}{b}{b′}{c}{c′} pa pb pc =
    term-compatible μ (Iⱼ i) {tri a b c}{tri a′ b′ c′} λ { 0F → pa ; 1F → pb ; 2F → pc }
```

The staircase has two halves.  The **horizontal** lemma walks one chain: for every `i`,
`dᵢ(a,u,b)` and `dᵢ(a,v,b)` are `γ = (θ∧φ)∨(θ∧ψ)`-related whenever `u`, `v` are joined by
a φ/ψ-chain.  The θ-component is automatic — `dᵢ(a,·,b)` is θ-tied to `a` because
`dᵢ(a,c,a) ≈ a` and `a θ b` (`dpin`{.AgdaFunction}) — and each single step contributes its
φ- or ψ-component, landing the step in `θ∧φ` or `θ∧ψ`.  The **vertical** induction then
climbs the rungs `i = 0 … n`: the fork identities glue consecutive rungs and the endpoints
`d₀(a,a,b) ≈ a`, `dₙ(a,a,b) ≈ b` close the walk, so `a γ b`.

```agda
  module _ (θ φ ψ : Con 𝑩 ℓ)(a b : 𝕌[ 𝑩 ])(aθb : proj₁ θ a b) where
    -- the target join, at the absorbing level 𝒈 ℓ = α ⊔ ρ ⊔ ℓ (since 𝓞 = 𝓥 = 0ℓ)
    γ : Con 𝑩 (α ⊔ ρ ⊔ ℓ)
    γ = (θ ∧ φ) ∨ (θ ∧ ψ)

    open IsEquivalence (is-equivalence (proj₂ θ)) using ()
      renaming ( refl to θ-refl ; sym to θ-sym ; trans to θ-trans )
    open IsEquivalence (is-equivalence (proj₂ φ)) using () renaming ( refl to φ-refl )
    open IsEquivalence (is-equivalence (proj₂ ψ)) using () renaming ( refl to ψ-refl )
    open IsEquivalence (is-equivalence (proj₂ γ)) using ()
      renaming ( sym to γ-sym ; trans to γ-trans )

    -- every dᵢ(a,u,b) is θ-tied to a (using a θ b and dᵢ(x,y,x) ≈ x)
    dpin : (i : Fin (suc n))(u : 𝕌[ 𝑩 ]) → proj₁ θ (d𝑩 i a u b) a
    dpin i u = θ-trans (d-compat θ i θ-refl θ-refl (θ-sym aθb))
                       (reflexive (proj₂ θ) (d-mid i a u))

    -- horizontal: along a φ/ψ-chain from u to v, dᵢ(a,u,b) γ dᵢ(a,v,b) for every i
    horiz : (u v : 𝕌[ 𝑩 ]) → Chain 𝑩 (φ ∪ᵣ ψ) u v → (i : Fin (suc n))
      → proj₁ γ (d𝑩 i a u b) (d𝑩 i a v b)
    horiz u v (nil u≈v) i =
      reflexive (proj₂ γ) (cong ⟦ Iⱼ i ⟧ λ { 0F → ≈refl ; 1F → u≈v ; 2F → ≈refl })
    horiz u v (cons {y = w} r c) i = γ-trans (step r) (horiz w v c i)
      where
      θ-eq : proj₁ θ (d𝑩 i a u b) (d𝑩 i a w b)
      θ-eq = θ-trans (dpin i u) (θ-sym (dpin i w))
      step : (φ ∪ᵣ ψ) u w → proj₁ γ (d𝑩 i a u b) (d𝑩 i a w b)
      step (inj₁ uφw) = ∨-upperˡ (θ ∧ φ) (θ ∧ ψ) (θ-eq , d-compat φ i φ-refl uφw φ-refl)
      step (inj₂ uψw) = ∨-upperʳ (θ ∧ φ) (θ ∧ ψ) (θ-eq , d-compat ψ i ψ-refl uψw ψ-refl)

    -- the rung predicate: a is γ-below both columns of the i-th rung
    Rung : Fin (suc n) → Type (α ⊔ ρ ⊔ ℓ)
    Rung i = proj₁ γ a (d𝑩 i a a b) × proj₁ γ a (d𝑩 i a b b)

    chainDist : Chain 𝑩 (φ ∪ᵣ ψ) a b → proj₁ γ a b
    chainDist chn = γ-trans (proj₁ (rungs (fromℕ n))) (reflexive (proj₂ γ) (d-lst a a b))
      where
      -- the horizontal step at every rung, read off the given chain a → b
      hz : (i : Fin (suc n)) → proj₁ γ (d𝑩 i a a b) (d𝑩 i a b b)
      hz i = horiz a b chn i

      base-rung : Rung zero
      base-rung =   reflexive (proj₂ γ) (≈sym (d-fst a a b))
                  , reflexive (proj₂ γ) (≈sym (d-fst a b b))

      -- climb one rung; the fork identity (parity-split) glues to the next index
      step-rung : (i : Fin n) → Rung (inject₁ i) → Rung (fsuc i)
      step-rung i (aP , aQ) with even? (toℕ i) | satⱼ (d-fork i)
      ... | true  | fk = aP′ , γ-trans aP′ (hz (fsuc i))
        where
        feq : d𝑩 (inject₁ i) a a b ≈ d𝑩 (fsuc i) a a b
        feq = ≈trans (≈sym (eval-d (inject₁ i) 0F 0F 2F (tri a a b)))
                     (≈trans (fk (tri a a b)) (eval-d (fsuc i) 0F 0F 2F (tri a a b)))
        aP′ : proj₁ γ a (d𝑩 (fsuc i) a a b)
        aP′ = γ-trans aP (reflexive (proj₂ γ) feq)
      ... | false | fk = γ-trans aQ′ (γ-sym (hz (fsuc i))) , aQ′
        where
        feq : d𝑩 (inject₁ i) a b b ≈ d𝑩 (fsuc i) a b b
        feq = ≈trans (≈sym (eval-d (inject₁ i) 0F 1F 1F (tri a b b)))
                     (≈trans (fk (tri a b b)) (eval-d (fsuc i) 0F 1F 1F (tri a b b)))
        aQ′ : proj₁ γ a (d𝑩 (fsuc i) a b b)
        aQ′ = γ-trans aQ (reflexive (proj₂ γ) feq)

      rungs : (i : Fin (suc n)) → Rung i
      rungs = <-weakInduction Rung base-rung step-rung
```

Packaging the staircase as a forward statement: a variety with Jónsson terms satisfies
the distributive inclusion `θ ∧ (φ ∨ ψ) ⊆ (θ∧φ) ∨ (θ∧ψ)` **along every φ/ψ-chain**.  This
is the finiteness-free content of Jónsson's theorem (Burris–Sankappanavar, Thm. II.12.6);
composing it with `Gen ⊆ Chain` (the collapse of the generated join `Cg(φ ∪ ψ)` to finite
chains, valid for finitary signatures) upgrades it to the literal
`CongruenceDistributive`{.AgdaFunction}.  The converse identification
`Chain⊆Gen`{.AgdaFunction} ([Setoid.Congruences.ChainJoin][]) shows the chain form is a
genuine sub-statement of that inclusion.

```agda
jonsson⇒chainDistributive :
  {𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  {ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X}
  → ( Σ[ n ∈ ℕ ] HasJonssonTerms n α ρ ℰ ) → (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ
  → (θ φ ψ : Con 𝑩 ℓ)(a b : 𝕌[ 𝑩 ]) → proj₁ θ a b
  → Chain 𝑩 (φ ∪ᵣ ψ) a b → proj₁ ((θ ∧ φ) ∨ (θ ∧ ψ)) a b
jonsson⇒chainDistributive {ℰ = ℰ} (n , jt) 𝑩 B⊨ θ φ ψ a b aθb chn =
  chainDist {ℰ = ℰ}{n = n} jt 𝑩 B⊨ θ φ ψ a b aθb chn
```

To land the staircase in the *literal* `CongruenceDistributive`{.AgdaFunction} (whose join
is the generated congruence `Cg(φ ∪ ψ)`), the one extra ingredient is that membership in
that join is witnessed by a finite chain — the `JoinIsChain`{.AgdaFunction} hypothesis from
[Setoid.Congruences.ChainJoin][].  For a **finitary** signature this is *automatic*
(`finitary⇒JoinIsChain`{.AgdaFunction}, proved there by a coordinate-by-coordinate fold); we
take it as a hypothesis here rather than bake a finiteness assumption into the whole
development, and discharge it in the featured finitary theorem below.

```agda
-- Jónsson terms ⟹ congruence distributivity (the forward half of Jónsson's theorem),
-- modulo the hypothesis JoinIsChain.  The forward inclusion is the staircase;
-- the reverse inclusion is the automatic semidistributive law of any lattice.
jonsson⇒CongruenceDistributive :
  {𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  {ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X}
  → ( Σ[ n ∈ ℕ ] HasJonssonTerms n α ρ ℰ ) → (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ
  → JoinIsChain 𝑩 (α ⊔ ρ ⊔ ℓ) → CongruenceDistributive 𝑩 ℓ
jonsson⇒CongruenceDistributive {ℰ = ℰ} jh 𝑩 B⊨ jic θ φ ψ = fwd , bwd
  where
  fwd : (θ ∧ (φ ∨ ψ)) ⊆ ((θ ∧ φ) ∨ (θ ∧ ψ))
  fwd {x}{y} (xθy , xφ∨ψy) =
    jonsson⇒chainDistributive {ℰ = ℰ} jh 𝑩 B⊨ θ φ ψ x y xθy (jic φ ψ xφ∨ψy)
  bwd : ((θ ∧ φ) ∨ (θ ∧ ψ)) ⊆ (θ ∧ (φ ∨ ψ))
  bwd = ∨-least (θ ∧ φ) (θ ∧ ψ) (θ ∧ (φ ∨ ψ))
          (λ (xθy , xφy) → xθy , ∨-upperˡ φ ψ xφy)
          (λ (xθy , xψy) → xθy , ∨-upperʳ φ ψ xψy)
```


#### The condition as a property of a variety

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.
A *congruence-distributive variety* is one in which all models are
congruence-distributive.  Jónsson's characterization of CD varieties is the iff statement
`Jonsson-Statement`{.AgdaFunction}.  The **forward** (term ⟹ lattice-property) half is now
proved — `jonsson⇒CongruenceDistributiveVariety`{.AgdaFunction} below — leaving the reverse
half (CD ⟹ terms, #413).  The companion modularity development — the Day terms and the
`Day-Statement`, whose forward direction is deferred for a substantive reason — lives in
[Setoid.Varieties.Maltsev.Modularity][] and the design note.

```agda
module _ {α ρ ℓ : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  -- "Every model is congruence-distributive / -modular."
  CongruenceDistributiveVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceDistributiveVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceDistributive 𝑩 ℓ
  -- Jónsson's theorem, the full iff.  The reverse half (CD ⟹ terms) is #413; the forward
  -- half is PROVED — `jonsson⇒CongruenceDistributiveVariety` below (and, finiteness-free,
  -- `jonsson⇒chainDistributive`) — so only the reverse keeps the whole `⇔` deferred.
  Jonsson-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Jonsson-Statement = CongruenceDistributiveVariety ⇔ ( Σ[ n ∈ ℕ ] HasJonssonTerms n α ρ ℰ )

  -- Forward Jónsson at the variety level: with Jónsson terms — and `JoinIsChain`, the
  -- finitary collapse of the generated join `Cg(φ ∪ ψ)` to finite chains — every model is
  -- congruence-distributive.  This is the proj₂ (term ⟹ CD) direction of `Jonsson-Statement`,
  -- modulo `JoinIsChain`.
  jonsson⇒CongruenceDistributiveVariety :
    ( Σ[ n ∈ ℕ ] HasJonssonTerms n α ρ ℰ )
    → ( (𝑩 : Algebra α ρ) → JoinIsChain 𝑩 (α ⊔ ρ ⊔ ℓ) )
    → CongruenceDistributiveVariety
  jonsson⇒CongruenceDistributiveVariety jh jic 𝑩 B⊨ =
    jonsson⇒CongruenceDistributive {ℓ = ℓ}{ℰ = ℰ} jh 𝑩 B⊨ (jic 𝑩)

  -- ★ The finitary Jónsson theorem.  For a finitary signature the JoinIsChain hypothesis is
  -- automatic (`finitary⇒JoinIsChain`), so a variety with Jónsson terms is
  -- congruence-distributive outright — the term ⟹ CD direction of `Jonsson-Statement` with
  -- no residual side condition.  The finiteness witness `fin` is `λ _ → _ , ↔-id _` for every
  -- signature whose arities are `Fin`s, which is every signature of the library; supplying it
  -- is therefore a one-liner, never a hoop (see `Examples.Setoid.FinitarySignatures`).
  jonsson-finitary⇒CongruenceDistributiveVariety :
    Finitary {𝑆 = 𝑆} → ( Σ[ n ∈ ℕ ] HasJonssonTerms n α ρ ℰ ) → CongruenceDistributiveVariety
  jonsson-finitary⇒CongruenceDistributiveVariety fin jh =
    jonsson⇒CongruenceDistributiveVariety jh (λ 𝑩 → finitary⇒JoinIsChain {ℓ = α ⊔ ρ ⊔ ℓ} fin)
```

---

[^jonsson]: B. Jónsson, *Algebras whose congruence lattices are distributive*, Math. Scand. **21** (1967), 110–121.  [doi:10.7146/math.scand.a-10850](https://doi.org/10.7146/math.scand.a-10850) (open access; mirror at [EUDML](https://eudml.org/doc/166010)).

