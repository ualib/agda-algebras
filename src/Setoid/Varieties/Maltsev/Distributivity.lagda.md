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
a theory interpretation `Th-Jonsson n ≼ ℰ` — and proves **Jónsson's theorem** in both
directions: terms ⟹ CD (the staircase, with the finitary collapse of the join), and
CD ⟹ terms (the converse, which extracts the chain of Jónsson terms from a congruence
of the free algebra `𝔽[ Fin 3 ]`).  For a finitary signature the two halves assemble
into the complete iff `jonsson-theorem`{.AgdaFunction}.

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
                                 renaming ( Rel to BinRel )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; subst ) renaming ( refl to ≡refl ; sym to ≡sym )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Basic                    using  ( _⇔_ )
open import Overture.Signatures               using  ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Terms                    using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation     using  ( Interpretation ; _✦_ )
open import Setoid.Algebras.Basic             using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic          using  ( Con ; reflexive ; is-equivalence )
open import Setoid.Congruences.Generation     using  ( Cg ; base ; tran ; _∨_ ; _∪ᵣ_
                                                     ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
open import Setoid.Congruences.ChainJoin      using  ( Chain ; nil ; cons ; JoinIsChain
                                                     ; Finitary ; finitary⇒JoinIsChain )
open import Setoid.Congruences.Lattice        using  ( _∧_ ; _⊆_ )
open import Setoid.Congruences.Properties     using  ( CongruenceDistributive )
open import Setoid.Terms.Basic                using  ( Sub ; _[_] ; module Environment )
open import Setoid.Terms.Interpretation       using  ( graft≐[] )
open import Setoid.Varieties.FreeBridge       using  ( ❴_,_❵ ; pᵣ ; cg-pair→⊢ ; toEq )
open import Setoid.Varieties.FreeSubstitution using  ( ≐→⊢ )
open import Setoid.Varieties.Interpretation   using  ( reductᴵ ; _⊨ₑ_ ; ⊧-interp
                                                     ; module Interpret )
open import Setoid.Varieties.Maltsev.Basic    using  ( tri ; even? ; term-compatible )
open import Setoid.Varieties.SoundAndComplete using  ( Eq ; _⊢_▹_≈_
                                                     ; module FreeAlgebra
                                                     ; module Soundness )

open import Function using ( Func )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )
open _⊢_▹_≈_ using ( sub ; refl ; sym ; trans )

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
`Jonsson-Statement`{.AgdaFunction}.  The **forward** (term ⟹ lattice-property) half is
proved just below — `jonsson⇒CongruenceDistributiveVariety`{.AgdaFunction} — and the
**reverse** half (CD ⟹ terms) is proved at the end of this module
(`CD⇒jonsson`{.AgdaFunction}), so for finitary signatures the two halves assemble into
the complete iff `jonsson-theorem`{.AgdaFunction}.  The companion modularity
development — the Day terms and the `Day-Statement`, whose forward direction is deferred
for a substantive reason — lives in [Setoid.Varieties.Maltsev.Modularity][] and the
design note.

```agda
module _ {α ρ ℓ : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  -- "Every model is congruence-distributive / -modular."
  CongruenceDistributiveVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceDistributiveVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceDistributive 𝑩 ℓ
  -- Jónsson's theorem, the full iff.  Both halves are PROVED: the forward (term ⟹ CD)
  -- half is `jonsson⇒CongruenceDistributiveVariety` below (and, finiteness-free,
  -- `jonsson⇒chainDistributive`); the reverse (CD ⟹ terms) half is `CD⇒jonsson` at the
  -- end of this module.  `jonsson-theorem` assembles the iff for finitary signatures.
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

#### Parity-normalized chains

The converse direction of Jónsson's theorem reads the terms `d₀ , … , dₙ` off a finite
alternating chain in the free algebra, and it needs that chain in a *parity-normal*
form: the fork identities of `Th-Jonsson`{.AgdaFunction} are parity-split, so the step
from element `i` to element `i + 1` must lie in the first relation when `i` is even and
in the second when `i` is odd.  The chain that `finitary⇒JoinIsChain`{.AgdaFunction}
produces carries its steps in whatever order the join membership dictates.  The
normalization is elementary — wherever a step's tag disagrees with its position's
parity, insert a trivial step of the expected relation, using that every congruence is
reflexive — but it is exactly the bookkeeping that turns "some chain" into "the Jónsson
chain", so we package it once, as data.

A `ParityChain 𝑩 P Q x z`{.AgdaRecord} is a chain from `x` to `z` presented as an
*indexed family* `elt : Fin (suc len) → 𝕌[ 𝑩 ]`{.AgdaField} — the shape in which the
elements will become the interpretation of the `len + 1` Jónsson symbols — whose head is
*exactly* `x` (propositional equality, so the head can be rewritten silently), whose
last element is `≈`-tied to `z` (in the free algebra the setoid equality is
derivability, which is all the endpoint identity needs), and whose `i`-th step lies in
`P` for even `i` and in `Q` for odd `i`.

```agda
record ParityChain {𝑆 : Signature 𝓞 𝓥}(𝑩 : Algebra {𝑆 = 𝑆} α ρ)
                   (P Q : BinRel 𝕌[ 𝑩 ] ℓ)(x z : 𝕌[ 𝑩 ]) : Type (α ⊔ ρ ⊔ ℓ) where
  field
    len      : ℕ
    elt      : Fin (suc len) → 𝕌[ 𝑩 ]
    elt-fst  : elt zero ≡ x
    elt-lst  : Setoid._≈_ 𝔻[ 𝑩 ] (elt (fromℕ len)) z
    step     : (i : Fin len)
             → (if even? (toℕ i) then P else Q) (elt (inject₁ i)) (elt (fsuc i))
```

The two constructors of the normal form.  The empty chain is a single element.  Consing
a `P`-step onto a chain *swaps the roles of `P` and `Q` in the tail* — prepending one
element shifts every position's parity by one — which is why the record is parameterized
by the ordered pair `(P , Q)` rather than by a single tagged relation.  The parity
arithmetic is silent: `even? (suc k)`{.AgdaFunction} is definitionally
`not (even? k)`{.AgdaFunction}, so the shifted `step`{.AgdaField} field transports by a
two-case Boolean split, with no numeric lemmas.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}{𝑩 : Algebra {𝑆 = 𝑆} α ρ}{P Q : BinRel 𝕌[ 𝑩 ] ℓ} where

  -- the singleton chain (no steps)
  pnil : {x z : 𝕌[ 𝑩 ]} → Setoid._≈_ 𝔻[ 𝑩 ] x z → ParityChain 𝑩 P Q x z
  pnil {x = x} x≈z = record
    { len = 0 ; elt = λ _ → x ; elt-fst = ≡refl ; elt-lst = x≈z ; step = λ () }

  -- prepend a P-step; the tail is a chain with the two relations swapped
  pcons : {x y z : 𝕌[ 𝑩 ]} → P x y → ParityChain 𝑩 Q P y z → ParityChain 𝑩 P Q x z
  pcons {x = x} pxy c = record
    { len = suc len ; elt = elt′ ; elt-fst = ≡refl ; elt-lst = elt-lst ; step = step′ }
    where
    open ParityChain c

    elt′ : Fin (suc (suc len)) → 𝕌[ 𝑩 ]
    elt′ zero      = x
    elt′ (fsuc i)  = elt i

    step′ : (i : Fin (suc len))
          → (if even? (toℕ i) then P else Q) (elt′ (inject₁ i)) (elt′ (fsuc i))
    step′ zero = subst (P x) (≡sym elt-fst) pxy
    step′ (fsuc j) with even? (toℕ j) | step j
    ... | true   | s = s
    ... | false  | s = s
```

Normalization.  Given two congruences `μ`, `ν` and a `Chain`{.AgdaDatatype} whose steps
are tagged `μ`-or-`ν` in arbitrary order, produce a parity chain whose even steps are
`μ`-steps and whose odd steps are `ν`-steps.  The two mutually recursive passes track
which relation the current position expects (`chain→parityᵒ`{.AgdaFunction} is the
off-phase pass, expecting a `ν`-step first): a step whose tag matches the expectation is
consed directly; a mismatched step is preceded by a trivial step of the expected
relation (congruence reflexivity), which flips the expectation so that the real step
then matches.  Both passes are structural in the chain.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}{𝑩 : Algebra {𝑆 = 𝑆} α ρ}(μ ν : Con 𝑩 ℓ) where
  private
    μ-refl : (u : 𝕌[ 𝑩 ]) → proj₁ μ u u
    μ-refl u = IsEquivalence.refl (is-equivalence (proj₂ μ))

    ν-refl : (u : 𝕌[ 𝑩 ]) → proj₁ ν u u
    ν-refl u = IsEquivalence.refl (is-equivalence (proj₂ ν))

  chain→parity   : {x z : 𝕌[ 𝑩 ]}
    → Chain 𝑩 (μ ∪ᵣ ν) x z → ParityChain 𝑩 (proj₁ μ) (proj₁ ν) x z
  chain→parityᵒ  : {x z : 𝕌[ 𝑩 ]}
    → Chain 𝑩 (μ ∪ᵣ ν) x z → ParityChain 𝑩 (proj₁ ν) (proj₁ μ) x z

  chain→parity (nil x≈z)          = pnil x≈z
  chain→parity (cons (inj₁ p) c)  = pcons p (chain→parityᵒ c)
  chain→parity (cons (inj₂ q) c)  = pcons (μ-refl _) (pcons q (chain→parity c))

  chain→parityᵒ (nil x≈z)          = pnil x≈z
  chain→parityᵒ (cons (inj₁ p) c)  = pcons (ν-refl _) (pcons p (chain→parityᵒ c))
  chain→parityᵒ (cons (inj₂ q) c)  = pcons q (chain→parity c)
```

#### The converse of Jónsson's theorem: CD ⟹ Jónsson terms

The construction is the classical one (Burris–Sankappanavar, Thm. II.12.6, the
(1) ⟹ (2) direction[^bs]), run through the free-algebra congruence/derivability bridge
of [Setoid.Varieties.FreeBridge][], exactly as the converse of Maltsev's theorem
(`CP⇒maltsev`{.AgdaFunction}, [Setoid.Varieties.Maltsev.Permutability][]) is.

+  Work in `𝔽 = 𝔽[ Fin 3 ]`{.AgdaFunction}, the relatively free algebra on three
   generators `x , y , z`.  It is a model of the theory (`satisfies`{.AgdaFunction}),
   hence congruence-distributive by hypothesis.

+  Take the principal congruences `θ = Cg ❴ x , z ❵`{.AgdaFunction},
   `φ = Cg ❴ x , y ❵`{.AgdaFunction}, and `ψ = Cg ❴ y , z ❵`{.AgdaFunction}.  Then
   `(x , z)` lies in `θ` (a generator pair) and in `φ ∨ ψ` (one `φ`-step to `y`, one
   `ψ`-step to `z`), so distributivity moves it into `(θ ∧ φ) ∨ (θ ∧ ψ)`.

+  For a **finitary** signature that join membership is witnessed by a finite
   alternating chain (`finitary⇒JoinIsChain`{.AgdaFunction}), which
   `chain→parity`{.AgdaFunction} normalizes: `(θ∧φ)`-steps at even positions,
   `(θ∧ψ)`-steps at odd ones.  Its `n + 1` elements are *terms* — the carrier of `𝔽`
   *is* `Term (Fin 3)` — and they are the Jónsson terms `d₀ , … , dₙ`, packaged as the
   interpretation `I i = tᵢ`.  The chain length is the `n` of the
   `Σ[ n ∈ ℕ ]` in `Jonsson-Statement`{.AgdaFunction}; this extraction is exactly where
   it comes from.

+  Each Jónsson identity is a principal-congruence membership pushed through a
   collapsing substitution (the bridge `cg-pair→⊢`{.AgdaFunction}).  The endpoint
   identities are the chain's endpoints (`d₀` is *exactly* `x`; `dₙ` is derivably `z`).
   The middle family `dᵢ(x,y,x) ≈ x` collapses `z ↦ x` — the `θ`-pair — using that
   every chain element is `θ`-tied to `x` (both step relations have a `θ`-component, so
   the walk never leaves the `θ`-class of `x`).  The fork at `i` collapses `y ↦ x` (the
   `φ`-pair) when `i` is even and `z ↦ y` (the `ψ`-pair) when `i` is odd — precisely the
   parity of the normalized chain's `i`-th step.

+  As in the Maltsev converse, the collapsing substitutions are chosen to be exactly the
   position maps `I ✦_`{.AgdaFunction} uses on a Jónsson application, so each bridge
   output is *definitionally* the interpreted identity, modulo the one term-level shim
   `graft≐[]`{.AgdaFunction}; `⊧-interp`{.AgdaFunction} and `sound`{.AgdaFunction}ness
   then discharge the satisfaction obligation in an arbitrary model.

Because the free algebra is built on the variable type `Fin 3 : Type 0ℓ`, and the free
construction shares one universe level between the equations' variables and the free
generators, the theory's variable type is taken at level `0ℓ` (`X : Type 0ℓ`), and the
converse inhabits the `proj₁` direction of `Jonsson-Statement`{.AgdaFunction} at the
levels of `𝔽[ Fin 3 ] : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)` — the same instantiation as
`CP⇒maltsev`{.AgdaFunction}, and no restriction for the finitary algebraic theories the
condition concerns.

```agda
module _ {𝑆 : Signature 0ℓ 0ℓ}{X : Type 0ℓ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  -- The converse (hard) half of Jónsson's theorem: a congruence-distributive variety
  -- over a finitary signature has a chain of Jónsson terms.
  CD⇒jonsson : Finitary {𝑆 = 𝑆}
    → CongruenceDistributiveVariety {α = lsuc 0ℓ}{ρ = ι ⊔ lsuc 0ℓ}{ℓ = 0ℓ} ℰ
    → Σ[ n ∈ ℕ ] HasJonssonTerms n (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ) ℰ
  CD⇒jonsson fin cdv = n , I , red
    where
    -- the theory in the `I → Eq` shape that the free algebra consumes
    E : Idx → Eq
    E = toEq ℰ

    open FreeAlgebra E using ( 𝔽[_] ; satisfies )

    -- the relatively free algebra on three generators, and its generators
    𝔽 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)
    𝔽 = 𝔽[ Fin 3 ]

    x y z : 𝕌[ 𝔽 ]
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F

    -- 𝔽 is a model, hence congruence-distributive by hypothesis
    𝔽cd : CongruenceDistributive 𝔽 0ℓ
    𝔽cd = cdv 𝔽 satisfies

    -- the three principal congruences of the construction
    θ φ ψ : Con 𝔽 (ι ⊔ lsuc 0ℓ)
    θ = Cg ❴ x , z ❵
    φ = Cg ❴ x , y ❵
    ψ = Cg ❴ y , z ❵

    -- (x , z) lies in θ ∧ (φ ∨ ψ): the θ-pair is a generator, and φ ∨ ψ walks through y
    xθz : proj₁ θ x z
    xθz = base pᵣ

    xφ∨ψz : proj₁ (φ ∨ ψ) x z
    xφ∨ψz = tran (base (inj₁ (base pᵣ))) (base (inj₂ (base pᵣ)))

    -- distributivity moves the pair into (θ ∧ φ) ∨ (θ ∧ ψ)
    xγz : proj₁ ((θ ∧ φ) ∨ (θ ∧ ψ)) x z
    xγz = proj₁ (𝔽cd θ φ ψ) (xθz , xφ∨ψz)

    -- the finite chain (the signature is finitary), parity-normalized:
    -- (θ∧φ)-steps at even positions, (θ∧ψ)-steps at odd positions
    pc : ParityChain 𝔽 (proj₁ (θ ∧ φ)) (proj₁ (θ ∧ ψ)) x z
    pc = chain→parity (θ ∧ φ) (θ ∧ ψ)
           (finitary⇒JoinIsChain {𝑩 = 𝔽} fin (θ ∧ φ) (θ ∧ ψ) xγz)

    open ParityChain pc renaming
      ( len to n ; elt to t ; elt-fst to t-fst ; elt-lst to t-lst ; step to t-step )

    -- the chain elements are terms — the carrier of 𝔽 is Term (Fin 3) — and they are
    -- the Jónsson terms: the i-th element interprets the i-th Jónsson symbol
    I : Interpretation (Sig-Jonsson n) 𝑆
    I i = t i

    -- the generators of the Jónsson signature (the source side of I)
    xJ yJ zJ : Term {𝑆 = Sig-Jonsson n} (Fin 3)
    xJ = ℊ 0F ; yJ = ℊ 1F ; zJ = ℊ 2F

    -- the collapsing substitutions: exactly the position maps `I ✦_` uses on a
    -- Jónsson application, so `graft (t i) σ` is definitionally `I ✦ dᵢ(_,_,_)`
    σxyz σxyx σxxz σxyy : Sub {𝑆 = 𝑆} (Fin 3) (Fin 3)
    σxyz j = I ✦ tri xJ yJ zJ j    -- the identity positions (no collapse)
    σxyx j = I ✦ tri xJ yJ xJ j    -- z ↦ x : collapses the θ-pair (x , z)
    σxxz j = I ✦ tri xJ xJ zJ j    -- y ↦ x : collapses the φ-pair (x , y)
    σxyy j = I ✦ tri xJ yJ yJ j    -- z ↦ y : collapses the ψ-pair (y , z)

    open IsEquivalence (is-equivalence (proj₂ θ)) using ()
      renaming ( refl to θ-refl ; trans to θ-trans )

    -- every chain element is θ-tied to x: the head is x, and both step relations
    -- carry a θ-component, so the walk never leaves the θ-class of x
    xθt : (i : Fin (suc n)) → proj₁ θ x (t i)
    xθt = <-weakInduction (λ i → proj₁ θ x (t i)) tie₀ tie₊
      where
      tie₀ : proj₁ θ x (t zero)
      tie₀ = subst (proj₁ θ x) (≡sym t-fst) θ-refl

      tie₊ : (i : Fin n) → proj₁ θ x (t (inject₁ i)) → proj₁ θ x (t (fsuc i))
      tie₊ i prev with even? (toℕ i) | t-step i
      ... | true   | s = θ-trans prev (proj₁ s)
      ... | false  | s = θ-trans prev (proj₁ s)

    -- the bridge at the θ-pair: collapsing z ↦ x turns "x θ tᵢ" into a derivable
    -- equation; x[σxyx] and z[σxyx] are both literally ℊ 0F, so the collapse is refl
    bridge-mid : (i : Fin (suc n)) → E ⊢ Fin 3 ▹ (x [ σxyx ]) ≈ (t i [ σxyx ])
    bridge-mid i = cg-pair→⊢ E σxyx x z refl (xθt i)

    -- every model of ℰ satisfies the interpreted Jónsson identities
    red : (𝑩 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)) → 𝑩 ⊨ₑ ℰ → reductᴵ 𝑩 I ⊨ₑ Th-Jonsson n

    -- d₀(x,y,z) ≈ x : the chain starts exactly at x (t-fst)
    red 𝑩 B⊨ dxyz≈x =
      ⊧-interp 𝑩 I {s = node zero (tri xJ yJ zJ)} {t = xJ}
        (Soundness.sound E 𝑩 B⊨
          (trans (≐→⊢ (graft≐[] (t zero) σxyz))
                 (subst (λ u → E ⊢ Fin 3 ▹ (u [ σxyz ]) ≈ (ℊ 0F)) (≡sym t-fst) refl)))

    -- dₙ(x,y,z) ≈ z : the chain ends derivably at z (t-lst); the setoid equality of 𝔽
    -- *is* derivability, so t-lst feeds the substitution rule `sub` directly
    red 𝑩 B⊨ dxyz≈z =
      ⊧-interp 𝑩 I {s = node (fromℕ n) (tri xJ yJ zJ)} {t = zJ}
        (Soundness.sound E 𝑩 B⊨
          (trans (≐→⊢ (graft≐[] (t (fromℕ n)) σxyz)) (sub t-lst σxyz)))

    -- dᵢ(x,y,x) ≈ x : collapse the θ-pair (x , z); every chain element is θ-tied to x
    red 𝑩 B⊨ (dxyx≈x i) =
      ⊧-interp 𝑩 I {s = node i (tri xJ yJ xJ)} {t = xJ}
        (Soundness.sound E 𝑩 B⊨
          (trans (≐→⊢ (graft≐[] (t i) σxyx)) (sym (bridge-mid i))))

    -- the forks: the i-th step of the parity chain is a (θ∧φ)-step when i is even and
    -- a (θ∧ψ)-step when i is odd — exactly the parity split of Th-Jonsson's forks
    red 𝑩 B⊨ (d-fork i) with even? (toℕ i) | t-step i
    ... | true  | s =
      ⊧-interp 𝑩 I {s = node (inject₁ i) (tri xJ xJ zJ)}
                   {t = node (fsuc i) (tri xJ xJ zJ)}
        (Soundness.sound E 𝑩 B⊨
          (trans (≐→⊢ (graft≐[] (t (inject₁ i)) σxxz))
            (trans (cg-pair→⊢ E σxxz x y refl (proj₂ s))
                   (sym (≐→⊢ (graft≐[] (t (fsuc i)) σxxz))))))
    ... | false | s =
      ⊧-interp 𝑩 I {s = node (inject₁ i) (tri xJ yJ yJ)}
                   {t = node (fsuc i) (tri xJ yJ yJ)}
        (Soundness.sound E 𝑩 B⊨
          (trans (≐→⊢ (graft≐[] (t (inject₁ i)) σxyy))
            (trans (cg-pair→⊢ E σxyy y z refl (proj₂ s))
                   (sym (≐→⊢ (graft≐[] (t (fsuc i)) σxyy))))))
```

#### Jónsson's theorem, the complete iff

With both halves in hand, `Jonsson-Statement`{.AgdaFunction} itself is inhabited for
every finitary signature, at the levels of the free-algebra construction: a variety over
a finitary signature is congruence-distributive **exactly when** it has a chain of
Jónsson terms.  (As everywhere in this development, the `Finitary` witness is a
one-liner for every `Fin`-arity signature; see `Examples.Setoid.FinitarySignatures`.)

```agda
  -- ★ Jónsson's theorem (Burris–Sankappanavar, Thm. II.12.6), as a complete iff.
  jonsson-theorem : Finitary {𝑆 = 𝑆}
    → Jonsson-Statement {α = lsuc 0ℓ}{ρ = ι ⊔ lsuc 0ℓ}{ℓ = 0ℓ} ℰ
  jonsson-theorem fin =
    CD⇒jonsson fin , jonsson-finitary⇒CongruenceDistributiveVariety {ℓ = 0ℓ} ℰ fin
```

---

[^jonsson]: B. Jónsson, *Algebras whose congruence lattices are distributive*, Math. Scand. **21** (1967), 110–121.  [doi:10.7146/math.scand.a-10850](https://doi.org/10.7146/math.scand.a-10850) (open access; mirror at [EUDML](https://eudml.org/doc/166010)).

[^bs]: S. Burris and H. P. Sankappanavar, *A Course in Universal Algebra*, Graduate Texts in Mathematics 78, Springer (1981), Thm. II.12.6.  [Free online edition](https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html).

