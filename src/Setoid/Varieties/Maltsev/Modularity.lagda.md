---
layout: default
file: "src/Setoid/Varieties/Maltsev/Modularity.lagda.md"
title: "Setoid.Varieties.Maltsev.Modularity module (The Agda Universal Algebra Library)"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Day's theorem

This is the [Setoid.Varieties.Maltsev.Modularity][] module of the [Agda Universal Algebra Library][].

This module records the Maltsev term condition for **congruence modularity** (CM) — the *Day
identities*, as a theory interpretation `Th-Day n ≼ ℰ` — and proves **Day's theorem**:

1.  Day terms ⟹ CM: the two-column ladder of Freese–McKenzie's Lemma 2.3,[^fm] run
    along finite alternating chains by induction on the number of `φ`-steps, with the
    finitary collapse of the join;
2.  CM ⟹ Day terms: the converse, which extracts the chain of Day terms from a
    congruence of the free algebra `𝔽[ Fin 4 ]`.

For a finitary signature the two halves assemble into the complete iff
`day-theorem`{.AgdaFunction}.  Although this is exactly what
`jonsson-theorem`{.AgdaFunction} does for distributivity in
[Setoid.Varieties.Maltsev.Distributivity][], the forward half here is *not*
a mechanical mirror of the Jónsson staircase.

The construction that does work is explained below and in
[design note `m6-6-forward-jonsson-day.md`](https://github.com/ualib/agda-algebras/blob/master/docs/notes/m6-6-forward-jonsson-day.md).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev.Modularity where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Bool.Base                     using  ( true ; false ; if_then_else_ )
open import Data.Fin.Base                      using  ( Fin ; toℕ ; fromℕ ; inject₁ )
                                               renaming ( zero to fzero ; suc to fsuc )
open import Data.Fin.Induction                 using  ( <-weakInduction )
open import Data.Fin.Patterns                  using  ( 0F ; 1F ; 2F ; 3F )
open import Data.Nat.Base                      using  ( ℕ ; zero ; suc ; _≤_ ; s≤s⁻¹ )
open import Data.Nat.Properties                using  ( ≤-refl ; ≤-reflexive ; ≤-trans
                                                      ; n≤1+n )
open import Data.Product                       using  ( _×_ ; _,_ ; Σ-syntax
                                                      ; proj₁ ; proj₂ )
open import Data.Sum.Base                      using  ( inj₁ ; inj₂ )
open import Level                              using  ( Level ; 0ℓ ; _⊔_ )
                                               renaming ( suc to lsuc )
open import Relation.Binary                    using  ( Setoid ; IsEquivalence )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ) renaming ( refl to ≡refl ; cong to ≡cong )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Basic                     using  ( _⇔_ )
open import Overture.Signatures                using  ( Signature )
open import Overture.Terms                     using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation      using  ( Interpretation ; graft ; _✦_ )
open import Setoid.Algebras.Basic              using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic           using  ( Con ; reflexive ; is-equivalence )
open import Setoid.Congruences.Generation      using  ( Cg ; base ; transitive ; _∨_ ; _∪ᵣ_
                                                      ; ∨-upperˡ ; ∨-upperʳ ; ∨-least
                                                      ; module principal )
open import Setoid.Congruences.ChainJoin       using  ( Chain ; nil ; cons ; JoinIsChain
                                                      ; Finitary ; finitary⇒JoinIsChain )
open import Setoid.Congruences.Lattice         using  ( _∧_ ; _⊆_ )
open import Setoid.Congruences.Properties      using  ( CongruenceModular )
open import Setoid.Terms.Basic                 using  ( Sub ; _[_] ; module Environment )
open import Setoid.Terms.Interpretation        using  ( graft≐[] )
open import Setoid.Varieties.EquationalLogic   using  ( _⊧_≈_ )
open import Setoid.Varieties.FreeSubstitution  using  ( ≐→⊢ ; cg-pair→⊢ ; cg-pairs→⊢ )
open import Setoid.Varieties.Interpretation    using  ( reductᴵ ; _⊨ₑ_ ; ⊧-interp
                                                      ; module Interpret )
open import Setoid.Varieties.Maltsev.Basic     using  ( even? ; term-compatible )
open import Setoid.Varieties.Maltsev.Distributivity
                                               using  ( ParityChain ; chain→parityᵒ
                                                      ; head-linked )
open import Setoid.Varieties.SoundAndComplete  using  ( Eq ; toEq ; _⊢_▹_≈_
                                                      ; module FreeAlgebra
                                                      ; module Soundness )
open import Function using ( Func )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )
open _⊢_▹_≈_ using ( sub ; refl ; sym ; trans )

private variable α ρ χ ι ℓ : Level
```
-->

#### Modularity of the congruence lattice

**Congruence modularity** (CM) is a property of the congruence lattice of an algebra,
defined in [Setoid.Congruences.Properties][] as `CongruenceModular` (at the absorbing
relation level, so that meet and join are operations on a single type).  We use it
here to phrase the Day variety condition below.

#### Day terms

Congruence modularity is characterized by a chain of *quaternary* terms `m₀ , … , mₙ`,
the **Day terms** (Day 1969; Burris–Sankappanavar, Thm. 12.4), with identities[^day]

    m₀(x, y, z, u)  ≈ x,
    mᵢ(x, y, y, x)  ≈ x                 (all i),
    mᵢ(x, x, u, u)  ≈ mᵢ₊₁(x, x, u, u)  (i even),
    mᵢ(x, y, y, u)  ≈ mᵢ₊₁(x, y, y, u)  (i odd),
    mₙ(x, y, z, u)  ≈ u.

```agda
-- the canonical 4-element tuple over the variable carrier Fin 4
quad : {ℓ : Level}{A : Type ℓ}(a b c d : A) → Fin 4 → A
quad a b c d 0F = a
quad a b c d 1F = b
quad a b c d 2F = c
quad a b c d 3F = d

-- n+1 quaternary operation symbols.
Sig-Day : {n : ℕ} → Signature 0ℓ 0ℓ
Sig-Day {n} = Fin (suc n) , (λ _ → Fin 4)

data Eq-Day {n : ℕ} : Type where
  mxyzu≈x  : Eq-Day                 -- m₀(x,y,z,u) ≈ x
  mxyyx≈x  : Fin (suc n) → Eq-Day   -- mᵢ(x,y,y,x) ≈ x
  mxyzu≈u  : Eq-Day                 -- mₙ(x,y,z,u) ≈ u
  m-fork   : Fin n → Eq-Day         -- consecutive mᵢ, mᵢ₊₁ agree (parity-dependent)

private
  d : {n : ℕ} → Fin (suc n) → (a b c d : Term (Fin 4)) → Term (Fin 4)
  d i a b c d = node i (quad a b c d)

module _ {n : ℕ} where
  private
    x y z u : Term {𝑆 = Sig-Day{n}} (Fin 4)
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F ; u = ℊ 3F

  Th-Day : Eq-Day → Term (Fin 4) × Term (Fin 4)
  Th-Day mxyzu≈x      = d fzero x y z u , x
  Th-Day mxyzu≈u      = d (fromℕ n) x y z u , u
  Th-Day (mxyyx≈x i)  = d i x y y x , x
  Th-Day (m-fork i)   = if even? (toℕ i)
    then ( d (inject₁ i) x x u u , d (fsuc i) x x u u )   -- i even: agree on (x,x,u,u)
    else ( d (inject₁ i) x y y u , d (fsuc i) x y y u )   -- i odd:  agree on (x,y,y,u)

HasDayTerms : (n : ℕ){α ρ : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
HasDayTerms n {α} {ρ} ℰ = Th-Day {n} ≼ ℰ
  where open Interpret α ρ
```

#### Day terms imply modularity along chains

The forward direction of Day's theorem runs the Day terms along a
**finite alternating walk** from `a` to `b` whose steps lie in `θ` or in `φ`.
As in the Jónsson development, the walk relation is the type `Chain`
([Setoid.Congruences.ChainJoin][]), the theorem is proved against it in full
generality, and the identification with the library's generated join `Cg(θ ∪ φ)` —
`JoinIsChain`, `finitary⇒JoinIsChain`{.AgdaFunction} — is paid exactly once, for the
**finitary** signatures, which is the usual setting in "ordinary" universal algebra.

The *argument* along the chain, however, is **not** the Jónsson staircase.  Jónsson's
θ-pinning holds at every element `dᵢ(a, u, b)` because `dᵢ(x, y, x) ≈ x` leaves the middle
argument free; Day's pinning `mᵢ(x, y, y, x) ≈ x` requires the two middle arguments to be
*equal*, so the even-fork column `mᵢ(a, a, b, b)` is not pinnable and the two-column
staircase has no analogue.  (This dead end is recorded in the design note.[^1])  What works
instead is the classical two-part construction of Day (1969),[^day] in the streamlined
form of Freese–McKenzie:[^fm]

+  **A collector lemma** (Freese–McKenzie, Lemma 2.3): for every congruence `μ` and
   pair `b μ d`, if the two ladder columns `mᵢ(a, a, c, c)` and `mᵢ(a, b, d, c)` are
   `μ`-related rung by rung, then `a μ c`.  The climb alternates: even forks advance the
   first column directly (`mᵢ(x, x, u, u) ≈ mᵢ₊₁(x, x, u, u)` at `(a, c)`), odd forks advance
   the second (`mᵢ(x, y, y, u) ≈ mᵢ₊₁(x, y, y, u)` at `(a, b, c)`, reachable because `b μ d`
   moves the third slot).

+  **An induction on the number of `φ`-steps** in the chain, which manufactures the
   collector's hypotheses at the join `δ = θ ∨ (φ ∧ ψ)`.  θ-steps absorb for free.  At
   the first genuine alternation `a φ t₁ θ t₂ φ t₃ ⋯ c` the collector is applied with
   the θ-pair `(t₁ , t₂) ∈ δ`, and its rung hypothesis is the induction hypothesis at
   the pair `(mᵢ(a,t₁,t₂,c) , mᵢ(a,a,c,c))`: the two flanking φ-steps `a φ t₁` and
   `t₂ φ t₃` **fuse into a single simultaneous move** in the second and third slots of
   `mᵢ`, the remaining chain pushes through the third slot coordinatewise
   (`m-compat`{.AgdaFunction}), and the fused chain has *strictly fewer* φ-steps.  Both
   elements of the pair are `ψ`-tied to `a` by the pinning identity (using `a ψ c` and
   `θ ⊆ ψ`), which is what lets the induction hypothesis — whose statement demands a
   `ψ`-tie — apply to them.

The fusion step is precisely where modularity differs from distributivity: it has no
single-column analogue, and it is what the `mᵢ(x, y, y, x) ≈ x` pinning buys.

##### The curried extraction

Fix a model `𝑩` of a theory `ℰ` with `n+1` Day terms.  The witnessing interpretation
`Iₘ`{.AgdaFunction} sends the `i`-th Day symbol to a derived `𝑆`-term, whose evaluation
against the named quadruple is the curried operation `m𝑩 i`{.AgdaFunction}.  The single
evaluation lemma `eval-m`{.AgdaFunction} rewrites a Day application in the reduct to
`m𝑩`, and the endpoint, pinning, and compatibility facts fall out by instantiating the
reduct's satisfaction of `Th-Day` — the verbatim quaternary analogue of the Jónsson
`d𝑩`{.AgdaFunction} / `eval-d`{.AgdaFunction} block (over `quad`{.AgdaFunction} in place
of `tri`{.AgdaFunction}).

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  {ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X}{n : ℕ}
  (dt : HasDayTerms n {α} {ρ} ℰ)(𝑩 : Algebra {𝑆 = 𝑆} α ρ)(B⊨ : 𝑩 ⊨ₑ ℰ)
  where
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ )
    renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Environment 𝑩 using ( ⟦_⟧ )
  open Environment (reductᴵ 𝑩 (proj₁ dt)) using () renaming ( ⟦_⟧ to ⟦_⟧ᴿ )

  -- the witnessing interpretation and the reduct's satisfaction of the Day theory
  Iₘ : Interpretation (Sig-Day {n}) 𝑆
  Iₘ = proj₁ dt

  satₘ : reductᴵ 𝑩 Iₘ ⊨ₑ Th-Day
  satₘ = proj₂ dt 𝑩 B⊨

  -- the curried i-th Day term operation
  m𝑩 : Fin (suc n) → (a b c d : 𝕌[ 𝑩 ]) → 𝕌[ 𝑩 ]
  m𝑩 i a b c d = ⟦ Iₘ i ⟧ ⟨$⟩ quad a b c d

  -- evaluating a Day application in the reduct lands on the curried m𝑩
  eval-m : (i : Fin (suc n)){i₀ i₁ i₂ i₃ : Fin 4}(η : Fin 4 → 𝕌[ 𝑩 ])
    → ⟦ node i (quad (ℊ i₀) (ℊ i₁) (ℊ i₂) (ℊ i₃)) ⟧ᴿ ⟨$⟩ η
      ≈ m𝑩 i (η i₀) (η i₁) (η i₂) (η i₃)
  eval-m i η = cong ⟦ Iₘ i ⟧ λ { 0F → ≈refl ; 1F → ≈refl ; 2F → ≈refl ; 3F → ≈refl }

  -- the two endpoint identities and the pinning family, curried, from satₘ
  m-fst : {a b c d : 𝕌[ 𝑩 ]} → m𝑩 fzero a b c d ≈ a
  m-fst = ≈trans (≈sym (eval-m fzero (quad _ _ _ _))) (satₘ mxyzu≈x (quad _ _ _ _))

  m-lst : {a b c d : 𝕌[ 𝑩 ]} → m𝑩 (fromℕ n) a b c d ≈ d
  m-lst = ≈trans (≈sym (eval-m (fromℕ n) (quad _ _ _ _))) (satₘ mxyzu≈u (quad _ _ _ _))

  m-mid : (i : Fin (suc n)){a b : 𝕌[ 𝑩 ]} → m𝑩 i a b b a ≈ a
  m-mid i {a} {b} = ≈trans (≈sym (eval-m i (quad a b b a))) (satₘ (mxyyx≈x i) (quad a b b a))

  -- m𝑩 i is a term operation, hence compatible with every congruence
  m-compat : (μ : Con 𝑩 ℓ)(i : Fin (suc n)){a a′ b b′ c c′ d d′ : 𝕌[ 𝑩 ]}
    → proj₁ μ a a′ → proj₁ μ b b′ → proj₁ μ c c′ → proj₁ μ d d′
    → proj₁ μ (m𝑩 i a b c d) (m𝑩 i a′ b′ c′ d′)
  m-compat μ i pa pb pc pd = term-compatible μ (Iₘ i) λ  { 0F → pa ; 1F → pb
                                                         ; 2F → pc ; 3F → pd }
```

##### The collector

`m-collect`{.AgdaFunction} is the substantive direction of Lemma 2.3 in
Freese–McKenzie[^fm] for an arbitrary congruence `μ`: given a pair `b μ d`, if the
columns `mᵢ(a, a, c, c)` and `mᵢ(a, b, d, c)` are `μ`-related at every rung, then
`a μ c`.

The climb is `<-weakInduction`{.AgdaFunction} on the rung predicate
`a μ mᵢ(a, a, c, c)`:

+  the base is the **endpoint identity** `m₀(a, a, c, c) ≈ a`;
+  an **even** fork advances the first column by the `(x, x, u, u)` identity alone;
+  an **odd** fork crosses to the second column by the hypothesis, advances it — moving
   the third slot `d → b` (`b μ d`), applying the `(x, y, y, u)` fork, and moving
   `b → d` back — and crosses home by the hypothesis at the next rung;
+  the final **endpoint identity** `mₙ(a, a, c, c) ≈ c` closes the walk.

The walk it produces, spelled out for the first few rungs (`≈` from the identities,
`μ` from the hypothesis, the pair `b μ d`, and their composites):

    a ≈ m₀(a,a,c,c)          -- m-fst
      ≈ m₁(a,a,c,c)          -- even fork at 0
      μ m₁(a,b,d,c)          -- hypothesis at 1
      μ m₂(a,b,d,c)          -- odd fork at 1 (b μ d moves slot three there and back)
      μ m₂(a,a,c,c)          -- hypothesis at 2
      ≈ m₃(a,a,c,c)          -- even fork at 2
      ⋮
        mₙ(a,a,c,c) ≈ c      -- m-lst

Nothing here mentions `θ`, `φ`, `ψ`, or chains; the lemma is a fact about a single
congruence.

```agda
  m-collect : (μ : Con 𝑩 ℓ){a c b d : 𝕌[ 𝑩 ]} → proj₁ μ b d
    → ((i : Fin (suc n)) → proj₁ μ (m𝑩 i a a c c) (m𝑩 i a b d c))
    → proj₁ μ a c
  m-collect {ℓ = ℓ} μ {a} {c} {b} {d} bμd hyp =
    μ-trans (rungs (fromℕ n)) (reflexive (proj₂ μ) m-lst)
    where
    open IsEquivalence (is-equivalence (proj₂ μ)) using ()
      renaming ( refl to μ-refl ; sym to μ-sym ; trans to μ-trans )

    -- the rung predicate: a is μ-below the first ladder column
    Rung : Fin (suc n) → Type ℓ
    Rung i = proj₁ μ a (m𝑩 i a a c c)

    base-rung : Rung fzero
    base-rung = reflexive (proj₂ μ) (≈sym m-fst)

    -- climb one rung; the fork identity (parity-split) glues to the next index
    step-rung : (i : Fin n) → Rung (inject₁ i) → Rung (fsuc i)
    step-rung i aμu with even? (toℕ i) | satₘ (m-fork i)
    ... | true  | fk = μ-trans aμu (reflexive (proj₂ μ) feq)
      where
      feq : m𝑩 (inject₁ i) a a c c ≈ m𝑩 (fsuc i) a a c c
      feq = ≈trans (≈sym (eval-m (inject₁ i) (quad a a c c)))
                   (≈trans (fk (quad a a c c)) (eval-m (fsuc i) (quad a a c c)))
    ... | false | fk =
      μ-trans aμu (μ-trans (hyp (inject₁ i)) (μ-trans odd-step (μ-sym (hyp (fsuc i)))))
      where
      feq : m𝑩 (inject₁ i) a b b c ≈ m𝑩 (fsuc i) a b b c
      feq = ≈trans (≈sym (eval-m (inject₁ i) (quad a b b c)))
                   (≈trans (fk (quad a b b c)) (eval-m (fsuc i) (quad a b b c)))
      -- advance the second column: move slot three d → b, fork, move back
      odd-step : proj₁ μ (m𝑩 (inject₁ i) a b d c) (m𝑩 (fsuc i) a b d c)
      odd-step =
        μ-trans (m-compat μ (inject₁ i) μ-refl μ-refl (μ-sym bμd) μ-refl)
        (μ-trans (reflexive (proj₂ μ) feq)
                 (m-compat μ (fsuc i) μ-refl μ-refl bμd μ-refl))

    rungs : (i : Fin (suc n)) → Rung i
    rungs = <-weakInduction Rung base-rung step-rung
```

##### The chain induction

Fix congruences `θ, φ, ψ` with `θ ⊆ ψ` and write `δ = θ ∨ (φ ∧ ψ)` for the join of
the modular law's conclusion.  Two joins are in play and they must be kept straight:
the *hypothesis* join `θ ∨ φ` is what gets decomposed — that is why the theorem
consumes a `Chain` — while the *conclusion* join `δ` is only ever introduced
(`∨-upperˡ/ʳ` and the transitivity of the join congruence), never eliminated.

The induction is on the number of φ-steps in the chain (`countφ`{.AgdaFunction}),
with an inner structural recursion that normalizes the head of the chain:

+  `absorb-θ`{.AgdaFunction} absorbs θ-steps (a θ-step lands in `δ` outright, and `θ ⊆ ψ`
   re-ties the new head to the far end);
+  `onφ`{.AgdaFunction} holds one open φ-step and merges any φ-steps that follow it
   (φ is transitive, so merging only lowers the count);
+  `onφθ`{.AgdaFunction} holds an open `φ`-then-`θ` head and merges subsequent
   θ-steps likewise.

The bases are degenerate chains:

+  a pure-θ chain collapses into `θ` (`θ-collapse`{.AgdaFunction});
+  a lone φ-step meets the `ψ`-tie in `φ ∧ ψ`;
+  a `φ`-then-`θ` chain splits as `(φ ∧ ψ) ∘ θ`.

The genuine case is a head `a φ t₁ θ t₂ φ t₃` followed by the rest of the chain.
There `m-collect`{.AgdaFunction} is applied at `μ = δ` with the θ-pair `(t₁ , t₂)`,
and its rung hypotheses come from the induction hypothesis at the pair
`(mᵢ(a,t₁,t₂,c) , mᵢ(a,a,c,c))`:

+  **the ψ-tie** (`m-rail`{.AgdaFunction}): `mᵢ(a, b, c, d)` is ψ-tied to `a` whenever
   the outer pair `(a, d)` and the inner pair `(b, c)` are each ψ-related — the pinning
   `m-mid`{.AgdaFunction}, reached by ψ-moves in the third and fourth slots.  Both
   columns qualify: for `mᵢ(a, t₁, t₂, c)` the inner move is `θ ⊆ ψ` at `t₁ θ t₂` and
   the outer is the ambient `a ψ c`; for `mᵢ(a, a, c, c)` both are `a ψ c`;

+  **the crossing chain**: its first step moves slots two and three *simultaneously*
   (`t₁ → a` by the opening φ-step reversed, `t₂ → t₃` by the closing one) — the fusion
   of two φ-steps of the original chain into one — and the remaining chain pushes
   through slot three by `m-push`{.AgdaFunction}, preserving step tags
   (`m-push-countφ`{.AgdaFunction}).  The fused chain therefore has strictly fewer
   φ-steps, and the outer induction applies.

```agda
  module _ (θ φ ψ : Con 𝑩 ℓ)(θ⊆ψ : θ ⊆ ψ) where
    -- the conclusion join, at the absorbing level 𝒈 ℓ = α ⊔ ρ ⊔ ℓ (since 𝓞 = 𝓥 = 0ℓ)
    δ : Con 𝑩 (α ⊔ ρ ⊔ ℓ)
    δ = θ ∨ (φ ∧ ψ)

    open IsEquivalence (is-equivalence (proj₂ θ)) using () renaming  ( refl  to θ-refl
                                                                     ; trans to θ-trans )
    open IsEquivalence (is-equivalence (proj₂ φ)) using () renaming  ( refl  to φ-refl
                                                                     ; sym   to φ-sym
                                                                     ; trans to φ-trans )
    open IsEquivalence (is-equivalence (proj₂ ψ)) using () renaming  ( refl  to ψ-refl
                                                                     ; sym   to ψ-sym
                                                                     ; trans to ψ-trans )
    open IsEquivalence (is-equivalence (proj₂ δ)) using () renaming  ( sym   to δ-sym
                                                                     ; trans to δ-trans )

    -- the induction measure: the number of φ-steps in a chain
    countφ : {x y : 𝕌[ 𝑩 ]} → Chain 𝑩 (θ ∪ᵣ φ) x y → ℕ
    countφ (nil _)           = 0
    countφ (cons (inj₁ _) C) = countφ C
    countφ (cons (inj₂ _) C) = suc (countφ C)

    -- a chain with no φ-steps collapses into θ
    θ-collapse : {x y : 𝕌[ 𝑩 ]}(C : Chain 𝑩 (θ ∪ᵣ φ) x y) → countφ C ≤ 0 → proj₁ θ x y
    θ-collapse (nil x≈y)         _  = reflexive (proj₂ θ) x≈y
    θ-collapse (cons (inj₁ s) C) le = θ-trans s (θ-collapse C le)
    θ-collapse (cons (inj₂ _) C) ()

    -- push a chain through the third slot of m𝑩 i, coordinatewise and tag-preserving
    m-push : (i : Fin (suc n)) {a c u v : 𝕌[ 𝑩 ]}
      → Chain 𝑩 (θ ∪ᵣ φ) u v → Chain 𝑩 (θ ∪ᵣ φ) (m𝑩 i a a u c) (m𝑩 i a a v c)
    m-push i (nil u≈v) = nil (cong ⟦ Iₘ i ⟧ λ  { 0F → ≈refl ; 1F → ≈refl ; 2F → u≈v ; 3F → ≈refl })
    m-push i (cons (inj₁ s) C) = cons (inj₁ (m-compat θ i θ-refl θ-refl s θ-refl)) (m-push i C)
    m-push i (cons (inj₂ s) C) = cons (inj₂ (m-compat φ i φ-refl φ-refl s φ-refl)) (m-push i C)

    -- the push preserves the φ-count
    m-push-countφ : (i : Fin (suc n)) {a c u v : 𝕌[ 𝑩 ]}
      → (C : Chain 𝑩 (θ ∪ᵣ φ) u v) → countφ (m-push i {a} {c} C) ≡ countφ C
    m-push-countφ i (nil _)           = ≡refl
    m-push-countφ i (cons (inj₁ _) C) = m-push-countφ i C
    m-push-countφ i (cons (inj₂ _) C) = ≡cong suc (m-push-countφ i C)

    -- the ψ-rail: mᵢ(a, b, c, d) is ψ-tied to a whenever the outer pair (a, d) and
    -- the inner pair (b, c) are each ψ-related — the pinning mᵢ(a, b, b, a) ≈ a,
    -- reached by ψ-moves in the third and fourth slots.  Both ladder columns qualify
    m-rail : (i : Fin (suc n)){a b c d : 𝕌[ 𝑩 ]}
      → proj₁ ψ a d → proj₁ ψ b c → proj₁ ψ (m𝑩 i a b c d) a
    m-rail i aψd bψc = ψ-trans  (m-compat ψ i ψ-refl ψ-refl (ψ-sym bψc) (ψ-sym aψd))
                                (reflexive (proj₂ ψ) (m-mid i))

    -- one round of the induction: the outer hypothesis `ih` covers chains with at
    -- most K φ-steps; the inner recursion is structural in the chain
    chainModStep : (K : ℕ)
      → ( {x y : 𝕌[ 𝑩 ]} → proj₁ ψ x y → (C : Chain 𝑩 (θ ∪ᵣ φ) x y)
          → countφ C ≤ K → proj₁ δ x y )
      → {a c : 𝕌[ 𝑩 ]} → proj₁ ψ a c → (C : Chain 𝑩 (θ ∪ᵣ φ) a c)
      → countφ C ≤ suc K → proj₁ δ a c
    chainModStep K ih = absorb-θ
      where
      onφ  : {x w y : 𝕌[ 𝑩 ]} → proj₁ ψ x y → proj₁ φ x w
        → (C : Chain 𝑩 (θ ∪ᵣ φ) w y) → suc (countφ C) ≤ suc K → proj₁ δ x y
      onφθ : {x t₁ t₂ y : 𝕌[ 𝑩 ]} → proj₁ ψ x y → proj₁ φ x t₁ → proj₁ θ t₁ t₂
        → (C : Chain 𝑩 (θ ∪ᵣ φ) t₂ y) → suc (countφ C) ≤ suc K → proj₁ δ x y

      -- one open φ-step: merge following φ-steps; a lone φ-step meets the ψ-tie
      onφ pψ xφw (nil w≈y) _ = ∨-upperʳ θ (φ ∧ ψ) (φ-trans xφw (reflexive (proj₂ φ) w≈y) , pψ)
      onφ pψ xφw (cons (inj₂ s) C) le = onφ pψ (φ-trans xφw s) C (≤-trans (n≤1+n _) le)
      onφ pψ xφw (cons (inj₁ s) C) le = onφθ pψ xφw s C le

      -- an open φ-then-θ head: merge following θ-steps; a φ∘θ chain splits as
      -- (φ ∧ ψ) ∘ θ; a further φ-step is the collector case
      onφθ pψ xφt₁ t₁θt₂ (nil t₂≈y) _ =
        δ-trans  (∨-upperʳ θ (φ ∧ ψ) (xφt₁ , ψ-trans pψ (ψ-sym (θ⊆ψ t₁θy))))
                 (∨-upperˡ θ (φ ∧ ψ) t₁θy)
          where
          t₁θy : proj₁ θ _ _
          t₁θy = θ-trans t₁θt₂ (reflexive (proj₂ θ) t₂≈y)
      onφθ pψ xφt₁ t₁θt₂ (cons (inj₁ s) C)  le = onφθ pψ xφt₁ (θ-trans t₁θt₂ s) C le
      onφθ {x}{t₁}{t₂}{y} pψ xφt₁ t₁θt₂ (cons (inj₂ t₂φt₃) C) le =
        m-collect δ (∨-upperˡ θ (φ ∧ ψ) t₁θt₂) hyps
        where
        -- the induction hypothesis, at the ψ-railed pair of ladder columns; the
        -- crossing chain fuses the two flanking φ-steps into its first step and
        -- pushes the remaining chain through the third slot
        sδr : (i : Fin (suc n)) → proj₁ δ (m𝑩 i x t₁ t₂ y) (m𝑩 i x x y y)
        sδr i = ih sψr crossing le′
          where
          sψr : proj₁ ψ (m𝑩 i x t₁ t₂ y) (m𝑩 i x x y y)
          sψr = ψ-trans (m-rail i pψ (θ⊆ψ t₁θt₂)) (ψ-sym (m-rail i pψ pψ))
          crossing : Chain 𝑩 (θ ∪ᵣ φ) (m𝑩 i x t₁ t₂ y) (m𝑩 i x x y y)
          crossing = cons (inj₂ (m-compat φ i φ-refl (φ-sym xφt₁) t₂φt₃ φ-refl))
                          (m-push i C)
          le′ : countφ crossing ≤ K
          le′ = ≤-trans (≤-reflexive (≡cong suc (m-push-countφ i C))) (s≤s⁻¹ le)

        hyps : (i : Fin (suc n)) → proj₁ δ (m𝑩 i x x y y) (m𝑩 i x t₁ t₂ y)
        hyps i = δ-sym (sδr i)

      -- absorb θ-steps; a θ-step is a δ-step, and θ ⊆ ψ re-ties the head
      absorb-θ : {x y : 𝕌[ 𝑩 ]} → proj₁ ψ x y
        → (C : Chain 𝑩 (θ ∪ᵣ φ) x y) → countφ C ≤ suc K → proj₁ δ x y
      absorb-θ pψ (nil x≈y) _  = reflexive (proj₂ δ) x≈y
      absorb-θ pψ (cons (inj₁ s) C) le = δ-trans  (∨-upperˡ θ (φ ∧ ψ) s)
                                                  (absorb-θ (ψ-trans (ψ-sym (θ⊆ψ s)) pψ) C le)
      absorb-θ pψ (cons (inj₂ s) C) le = onφ pψ s C le

    -- the outer induction on the φ-count; at zero the chain collapses into θ
    chainModAt : (K : ℕ){a c : 𝕌[ 𝑩 ]} → proj₁ ψ a c
      → (C : Chain 𝑩 (θ ∪ᵣ φ) a c) → countφ C ≤ K → proj₁ δ a c
    chainModAt zero    pψ C le = ∨-upperˡ θ (φ ∧ ψ) (θ-collapse C le)
    chainModAt (suc K) pψ C le = chainModStep K (chainModAt K) pψ C le

    -- the chain-level modular law: ψ-tied chain endpoints are δ-related
    chainMod : {a c : 𝕌[ 𝑩 ]} → proj₁ ψ a c → Chain 𝑩 (θ ∪ᵣ φ) a c → proj₁ δ a c
    chainMod pψ C = chainModAt (countφ C) pψ C ≤-refl
```

Packaging the ladder as a forward statement: a variety with Day terms satisfies the
modular inclusion `(θ ∨ φ) ∧ ψ ⊆ θ ∨ (φ ∧ ψ)` (for `θ ⊆ ψ`) **along every θ/φ-chain**.
This is the finiteness-free content of Day's theorem; composing it with `Gen ⊆ Chain`
(the collapse of the generated join `Cg(θ ∪ φ)` to finite chains, valid for finitary
signatures) upgrades it to the literal `CongruenceModular`{.AgdaFunction} type.

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  {ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X}
  ( (n , dt) : Σ[ n ∈ ℕ ] HasDayTerms n {α} {ρ} ℰ )
  {𝑩 : Algebra {𝑆 = 𝑆} α ρ}
  (B⊨ : 𝑩 ⊨ₑ ℰ)
  where

  day⇒chainModular : (θ φ ψ : Con 𝑩 ℓ) → θ ⊆ ψ → {a b : 𝕌[ 𝑩 ]}
    → proj₁ ψ a b → Chain 𝑩 (θ ∪ᵣ φ) a b → proj₁ (θ ∨ (φ ∧ ψ)) a b
  day⇒chainModular = chainMod {ℰ = ℰ}{n = n} dt 𝑩 B⊨
```

To land the ladder in the *literal* `CongruenceModular`{.AgdaFunction} type (whose
join is the generated congruence `Cg(θ ∪ φ)`), the one extra ingredient is
`JoinIsChain` ([Setoid.Congruences.ChainJoin][]), applied once, to the hypothesis
join.  The other inclusion of the `≑` — `θ ∨ (φ ∧ ψ) ⊆ (θ ∨ φ) ∧ ψ` — is the trivial
lattice direction: both joinands sit below `θ ∨ φ` and, using `θ ⊆ ψ`, below `ψ`.

```agda
  -- Day terms ⟹ congruence modularity (the forward half of Day's theorem), modulo
  -- the hypothesis JoinIsChain.  The substantive inclusion is the chain ladder; the
  -- reverse inclusion holds in any lattice.
  day⇒CongruenceModular : JoinIsChain 𝑩 (α ⊔ ρ ⊔ ℓ) → CongruenceModular 𝑩 ℓ
  day⇒CongruenceModular jic θ φ ψ θ⊆ψ = fwd , bwd
    where
    fwd : θ ∨ (φ ∧ ψ) ⊆ (θ ∨ φ) ∧ ψ
    fwd = ∨-least θ (φ ∧ ψ) ((θ ∨ φ) ∧ ψ)
            (λ xθy → ∨-upperˡ θ φ xθy , θ⊆ψ xθy)
            (λ (xφy , xψy) → ∨-upperʳ θ φ xφy , xψy)

    bwd : (θ ∨ φ) ∧ ψ ⊆ θ ∨ (φ ∧ ψ)
    bwd (x∨y , xψy) = day⇒chainModular θ φ ψ θ⊆ψ xψy (jic θ φ x∨y)
```

#### The Maltsev condition as a property of a variety

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.
A *congruence-modular variety* is one in which all models are
congruence-modular (CM).  Day's characterization of CM varieties is the iff statement
`Day-Statement`{.AgdaFunction}.  The **forward** (term ⟹ CM) direction is proved just
below — `day⇒CongruenceModularVariety`{.AgdaFunction} and its unconditional finitary
form — and the **reverse** (CM ⟹ terms) direction is proved at the end of this module
(`CM⇒day`{.AgdaFunction}), so for finitary signatures the two halves assemble into the
complete iff `day-theorem`{.AgdaFunction}.

```agda
module _
  {α ρ : Level}
  {𝑆 : Signature 0ℓ 0ℓ}
  {X : Type χ}
  {Idx : Type ι}
  (ℓ : Level)
  (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X)
  where

  -- Every model is congruence-modular.
  CongruenceModularVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceModularVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceModular 𝑩 ℓ

  -- Day's theorem: CM ⇔ existence of Day terms.  Both halves are PROVED: the
  -- forward (term ⟹ CM) half is `day⇒CongruenceModularVariety` below (and,
  -- finiteness-free, `day⇒chainModular`); the reverse (CM ⟹ terms) half is
  -- `CM⇒day` at the end of this module.  `day-theorem` assembles the iff for
  -- finitary signatures.
  Day-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Day-Statement = CongruenceModularVariety ⇔ Σ[ n ∈ ℕ ] HasDayTerms n {α} {ρ}ℰ

  -- Forward Day at the variety level: with Day terms — and `JoinIsChain`, the
  -- finitary collapse of the generated join `Cg(θ ∪ φ)` to finite chains — every
  -- model is congruence-modular.  This is the proj₂ (term ⟹ CM) direction of
  -- `Day-Statement`, modulo `JoinIsChain`.
  day⇒CongruenceModularVariety :
    ( Σ[ n ∈ ℕ ] HasDayTerms n {α} {ρ} ℰ )
    → ( (𝑩 : Algebra α ρ) → JoinIsChain 𝑩 (α ⊔ ρ ⊔ ℓ) )
    → CongruenceModularVariety
  day⇒CongruenceModularVariety dh jic 𝑩 B⊨ =
    day⇒CongruenceModular {ℰ = ℰ} dh B⊨ {ℓ = ℓ} (jic 𝑩)

  -- ★ The finitary forward Day theorem.  For a finitary signature the JoinIsChain
  -- hypothesis is automatic (`finitary⇒JoinIsChain`), so a variety with Day terms is
  -- congruence-modular outright — the term ⟹ CM direction of `Day-Statement` with no
  -- residual side condition.  As everywhere in this development, the finiteness
  -- witness `fin` is `λ _ → _ , ↔-id _` for every `Fin`-arity signature (see
  -- `Examples.Setoid.FinitarySignatures`).
  day-finitary⇒CongruenceModularVariety :
    Finitary 𝑆 → ( Σ[ n ∈ ℕ ] HasDayTerms n ℰ ) → CongruenceModularVariety
  day-finitary⇒CongruenceModularVariety fin dh =
    day⇒CongruenceModularVariety dh (λ _ → finitary⇒JoinIsChain fin)
```

#### The converse of Day's theorem: CM ⟹ Day terms

The construction is the classical one (Day 1969; Burris–Sankappanavar, Thm. II.12.4, the
(1) ⟹ (2) direction[^bs]), run through the free-algebra congruence/derivability bridge
(`cg-pair→⊢`{.AgdaFunction} / `cg-pairs→⊢`{.AgdaFunction},
[Setoid.Varieties.FreeSubstitution][]) and the parity-chain machinery of the Jónsson
converse (`ParityChain`{.AgdaRecord}, [Setoid.Varieties.Maltsev.Distributivity][]),
which was designed to be reused here.

+  Work in `𝔽 = 𝔽[ Fin 4 ]`{.AgdaFunction}, the relatively free algebra on four
   generators `x , y , z , u`.  It is a model of the theory (`satisfies`{.AgdaFunction}),
   hence congruence-modular by hypothesis.

+  Take `θ = Cg ❴ y , z ❵`{.AgdaFunction}, `φ = Cg ❴ x , y ❵ ∨ Cg ❴ z , u ❵`{.AgdaFunction},
   and `ψ = Cg ❴ x , u ❵ ∨ Cg ❴ y , z ❵`{.AgdaFunction}.  Where the Jónsson converse takes
   three *principal* congruences, two of Day's are **joins of two principal congruences**
   — each must be collapsed by a substitution identifying *two* generator pairs at once,
   which is what the two-pair bridge `cg-pairs→⊢`{.AgdaFunction} is for — and `θ ⊆ ψ`,
   exactly the side condition of the modular law.  The pair `(x , u)` lies in `ψ` (a
   generator pair) and in `θ ∨ φ` (the walk `x φ y θ z φ u`), so the modular law
   `θ ∨ (φ ∧ ψ) ≑ (θ ∨ φ) ∧ ψ`, read right to left, moves it into `θ ∨ (φ ∧ ψ)`.

+  For a **finitary** signature that join membership is witnessed by a finite
   alternating chain (`finitary⇒JoinIsChain`{.AgdaFunction}), which the *off-phase*
   normalization `chain→parityᵒ`{.AgdaFunction} aligns: `(φ ∧ ψ)`-steps at even
   positions, `θ`-steps at odd ones.  (The join presents its `θ`-steps in the first
   tag, but the even forks of `Th-Day`{.AgdaFunction} are the `φ`-collapses, so the
   phase is swapped relative to the Jónsson converse — hence the `ᵒ` pass.)  Its
   `n + 1` elements are quaternary *terms* — the carrier of `𝔽` *is* `Term (Fin 4)` —
   and they are the Day terms `m₀ , … , mₙ`, packaged as the interpretation `I i = tᵢ`.
   The chain length is the `n` of the `Σ[ n ∈ ℕ ]` in `Day-Statement`{.AgdaFunction}.

+  Each Day identity is an endpoint fact about the chain, or a congruence membership
   pushed through a collapsing substitution (`cg-pair→⊢`{.AgdaFunction} for the
   principal `θ`, `cg-pairs→⊢`{.AgdaFunction} for the two-pair joins `φ` and `ψ`).  The endpoint
   identities are the chain's endpoints (`m₀` is *exactly* `x`; `mₙ` is derivably `u`).
   The middle family `mᵢ(x,y,y,x) ≈ x` collapses `z ↦ y , u ↦ x` — the two `ψ`-pairs —
   using that every chain element is `ψ`-tied to `x` (`head-linked`{.AgdaFunction}:
   both step relations lie below `ψ`, the meet by its second component and `θ` by
   `θ ⊆ ψ`, so the walk never leaves the `ψ`-class of `x`).  The fork at `i` collapses
   `y ↦ x , z ↦ u` (the two `φ`-pairs) when `i` is even and `z ↦ y` (the `θ`-pair)
   when `i` is odd — precisely the parity of the normalized chain's `i`-th step.

+  As in the Maltsev and Jónsson converses, the collapsing substitutions are chosen to
   be exactly the position maps `I ✦_`{.AgdaFunction} uses on a Day application, so each
   bridge output is *definitionally* the interpreted identity, modulo the one term-level
   shim `graft≐[]`{.AgdaFunction}; `⊧-interp`{.AgdaFunction} and `Soundness.sound`{.AgdaFunction}
   then discharge the satisfaction obligation in an arbitrary model.

Because the free algebra is built on the variable type `Fin 4 : Type 0ℓ`, and the free
construction shares one universe level between the equations' variables and the free
generators, the theory's variable type is taken at level `0ℓ` (`X : Type 0ℓ`), and the
converse inhabits the `proj₁` direction of `Day-Statement`{.AgdaFunction} at the levels
of `𝔽[ Fin 4 ] : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)` — the same instantiation as
`CD⇒jonsson`{.AgdaFunction} and `CP⇒maltsev`{.AgdaFunction}.

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}
  {X : Type 0ℓ}
  {Idx : Type ι}
  (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X)
  where
  -- the theory in the `I → Eq` shape that the free algebra consumes
  E : Idx → Eq
  E = toEq ℰ

  open FreeAlgebra E using ( 𝔽[_] ; satisfies )

  -- the relatively free algebra on four generators, and its generators
  𝔽 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)
  𝔽 = 𝔽[ Fin 4 ]

  private
    x y z u : 𝕌[ 𝔽 ]
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F ; u = ℊ 3F

  -- The converse half of Day's theorem: a congruence-modular variety
  -- over a finitary signature has a chain of Day terms.
  CM⇒day : Finitary 𝑆 → CongruenceModularVariety 0ℓ ℰ → Σ[ n ∈ ℕ ] HasDayTerms n ℰ
  CM⇒day fin cmv = n , I , red
    where

    -- 𝔽 is a model, hence congruence-modular by hypothesis
    𝔽cm : CongruenceModular 𝔽 0ℓ
    𝔽cm = cmv 𝔽 satisfies

    open principal 𝔽[ Fin 4 ]
    -- the three congruences of Day's construction; θ ⊆ ψ is the modular side condition
    θ φ ψ : Con 𝔽 (ι ⊔ lsuc 0ℓ)
    θ = Cg ❴ y , z ❵
    φ = Cg ❴ x , y ❵ ∨ Cg ❴ z , u ❵
    ψ = Cg ❴ x , u ❵ ∨ Cg ❴ y , z ❵

    θ⊆ψ : θ ⊆ ψ
    θ⊆ψ = ∨-upperʳ (Cg ❴ x , u ❵) (Cg ❴ y , z ❵)

    -- (x , u) lies in (θ ∨ φ) ∧ ψ: the ψ-pair is a generator, and θ ∨ φ walks
    -- x φ y θ z φ u (the two outer steps through φ's two principal components)
    xψu : ψ .proj₁ x u
    xψu = ∨-upperˡ (Cg ❴ x , u ❵) (Cg ❴ y , z ❵) (base pᵣ)

    xθ∨φu : (θ ∨ φ) .proj₁ x u
    xθ∨φu = transitive (∨-upperʳ θ φ (∨-upperˡ (Cg ❴ x , y ❵) (Cg ❴ z , u ❵) (base pᵣ)))
                       ( transitive (∨-upperˡ θ φ (base pᵣ))
                                    (∨-upperʳ θ φ (∨-upperʳ (Cg ❴ x , y ❵) (Cg ❴ z , u ❵) (base pᵣ))) )

    -- the modular law (right to left) moves the pair into θ ∨ (φ ∧ ψ)
    xδu : (θ ∨ (φ ∧ ψ)) .proj₁ x u
    xδu = (𝔽cm θ φ ψ θ⊆ψ) .proj₂ (xθ∨φu , xψu)

    -- the finite chain (the signature is finitary), parity-normalized *off-phase*:
    -- (φ∧ψ)-steps at even positions, θ-steps at odd positions.  The proof never
    -- computes this chain — it only reads its fields — so it is `abstract`, which
    -- keeps the extraction pipeline from being unfolded during type-checking
    abstract
      pc : ParityChain 𝔽 ((φ ∧ ψ) .proj₁) (θ .proj₁) x u
      pc = chain→parityᵒ θ (φ ∧ ψ) (finitary⇒JoinIsChain fin θ (φ ∧ ψ) xδu)

    open ParityChain pc renaming
      ( len to n ; elt to t ; elt-fst to t-fst ; elt-lst to t-lst ; step to t-step )

    -- the chain elements are terms — the carrier of 𝔽 is Term (Fin 4) — and they are
    -- the Day terms: the i-th element interprets the i-th Day symbol
    I : Interpretation Sig-Day 𝑆
    I i = t i

    -- the generators of the Day signature (the source side of I)
    xD yD zD uD : Term {𝑆 = Sig-Day} (Fin 4)
    xD = ℊ 0F ; yD = ℊ 1F ; zD = ℊ 2F ; uD = ℊ 3F

    -- the four Day application families appearing in Th-Day, as Sig-Day terms:
    -- mxyzu i is mᵢ(x,y,z,u), mxyyx i is mᵢ(x,y,y,x), and so on
    mxyzu mxyyx mxxuu mxyyu : Fin (suc n) → Term {𝑆 = Sig-Day} (Fin 4)
    mxyzu i = node i (quad xD yD zD uD)
    mxyyx i = node i (quad xD yD yD xD)
    mxxuu i = node i (quad xD xD uD uD)
    mxyyu i = node i (quad xD yD yD uD)

    -- the matching collapsing substitutions: exactly the position maps `I ✦_` uses on
    -- the corresponding application, so `graft (t i) σ` is definitionally `I ✦ m· i`
    σxyzu σxyyx σxxuu σxyyu : Sub {𝑆 = 𝑆} (Fin 4) (Fin 4)
    σxyzu j = I ✦ quad xD yD zD uD j    -- the identity positions (no collapse)
    σxyyx j = I ✦ quad xD yD yD xD j    -- z ↦ y , u ↦ x : collapses ψ's pairs (x,u), (y,z)
    σxxuu j = I ✦ quad xD xD uD uD j    -- y ↦ x , z ↦ u : collapses φ's pairs (x,y), (z,u)
    σxyyu j = I ✦ quad xD yD yD uD j    -- z ↦ y         : collapses the θ-pair (y,z)

    -- every chain element is ψ-tied to x: both step relations lie below ψ — the meet
    -- by its second component, θ by θ ⊆ ψ — so the walk never leaves the ψ-class of x
    xψt : (i : Fin (suc n)) → proj₁ ψ x (t i)
    xψt = head-linked pc ψ proj₂ θ⊆ψ

    -- the chain head, as a derivable equation: the setoid equality of 𝔽 *is*
    -- derivability, and the head is even a propositional equality (t-fst)
    t₀≈x : E ⊢ Fin 4 ▹ t fzero ≈ x
    t₀≈x = Setoid.reflexive 𝔻[ 𝔽 ] t-fst

    -- align the interpretation's node action (`graft`) with the bridge's substitution
    -- hom (`_[ σ ]`).  The shim `graft≐[]` is needed only on chain-element sides: on a
    -- *generator* v, `graft (ℊ v) σ` and `(ℊ v) [ σ ]` are both literally `σ v`.  So a
    -- generator right-hand side uses the one-sided form, and only the forks (chain
    -- elements on both sides) need the two-sided one
    graft-bridgeˡ : (w : 𝕌[ 𝔽 ]){v : 𝕌[ 𝔽 ]}(σ : Sub {𝑆 = 𝑆} (Fin 4) (Fin 4))
      → E ⊢ Fin 4 ▹ (w [ σ ]) ≈ v → E ⊢ Fin 4 ▹ graft w σ ≈ v
    graft-bridgeˡ w σ d = trans (≐→⊢ (graft≐[] w σ)) d

    graft-bridge : (w w′ : 𝕌[ 𝔽 ])(σ : Sub {𝑆 = 𝑆} (Fin 4) (Fin 4))
      → E ⊢ Fin 4 ▹ (w [ σ ]) ≈ (w′ [ σ ]) → E ⊢ Fin 4 ▹ graft w σ ≈ graft w′ σ
    graft-bridge w w′ σ d = trans (graft-bridgeˡ w σ d) (sym (≐→⊢ (graft≐[] w′ σ)))

    -- the five identity families of Th-Day, one derivation each: an endpoint fact or
    -- a collapsed (join of) principal-congruence membership(s), through the bridge
    deriv-fst : E ⊢ Fin 4 ▹ (I ✦ mxyzu fzero) ≈ (I ✦ xD)
    deriv-fst = graft-bridgeˡ (t fzero) σxyzu (sub t₀≈x σxyzu)

    deriv-lst : E ⊢ Fin 4 ▹ (I ✦ mxyzu (fromℕ n)) ≈ (I ✦ uD)
    deriv-lst = graft-bridgeˡ (t (fromℕ n)) σxyzu (sub t-lst σxyzu)

    deriv-mid : (i : Fin (suc n)) → E ⊢ Fin 4 ▹ (I ✦ mxyyx i) ≈ (I ✦ xD)
    deriv-mid i = graft-bridgeˡ (t i) σxyyx
                    (sym (cg-pairs→⊢ E σxyyx x u y z refl refl (xψt i)))

    deriv-fork-φ : (i : Fin n) → proj₁ φ (t (inject₁ i)) (t (fsuc i))
      → E ⊢ Fin 4 ▹ (I ✦ mxxuu (inject₁ i)) ≈ (I ✦ mxxuu (fsuc i))
    deriv-fork-φ i st = graft-bridge (t (inject₁ i)) (t (fsuc i)) σxxuu
                          (cg-pairs→⊢ E σxxuu x y z u refl refl st)

    deriv-fork-θ : (i : Fin n) → proj₁ θ (t (inject₁ i)) (t (fsuc i))
      → E ⊢ Fin 4 ▹ (I ✦ mxyyu (inject₁ i)) ≈ (I ✦ mxyyu (fsuc i))
    deriv-fork-θ i st = graft-bridge (t (inject₁ i)) (t (fsuc i)) σxyyu
                          (cg-pair→⊢ E σxyyu y z refl st)

    -- discharge one interpreted identity in an arbitrary model, by soundness and the
    -- satisfaction condition; the equation sides p, q are passed explicitly, since
    -- they are not recoverable from the interpreted terms I ✦ p, I ✦ q
    discharge : (𝑩 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)) → 𝑩 ⊨ₑ ℰ
      → (p q : Term {𝑆 = Sig-Day} (Fin 4))
      → E ⊢ Fin 4 ▹ (I ✦ p) ≈ (I ✦ q) → reductᴵ 𝑩 I ⊧ p ≈ q
    discharge 𝑩 B⊨ p q d = ⊧-interp 𝑩 I {s = p} {t = q} (Soundness.sound E 𝑩 B⊨ d)

    -- every model of ℰ satisfies the interpreted Day identities; the fork clause
    -- splits on the parity of i, matching the parity-normalized step of the chain
    red : (𝑩 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)) → 𝑩 ⊨ₑ ℰ → reductᴵ 𝑩 I ⊨ₑ Th-Day
    red 𝑩 B⊨ mxyzu≈x     = discharge 𝑩 B⊨ (mxyzu fzero) xD deriv-fst
    red 𝑩 B⊨ (mxyyx≈x i) = discharge 𝑩 B⊨ (mxyyx i) xD (deriv-mid i)
    red 𝑩 B⊨ mxyzu≈u     = discharge 𝑩 B⊨ (mxyzu (fromℕ n)) uD deriv-lst
    red 𝑩 B⊨ (m-fork i) with even? (toℕ i) | t-step i
    ... | true  | s = discharge 𝑩 B⊨ (mxxuu (inject₁ i)) (mxxuu (fsuc i)) (deriv-fork-φ i (proj₁ s))
    ... | false | s = discharge 𝑩 B⊨ (mxyyu (inject₁ i)) (mxyyu (fsuc i)) (deriv-fork-θ i s)
```

#### Day's theorem, the complete iff

With both halves in hand, `Day-Statement`{.AgdaFunction} itself is inhabited for every
finitary signature, at the levels of the free-algebra construction: a variety over a
finitary signature is congruence-modular **exactly when** it has a chain of Day terms.
This mirrors `jonsson-theorem`{.AgdaFunction} exactly, and closes the trio of classical
Maltsev-condition characterizations (Maltsev, Jónsson, Day) as complete iffs.

```agda
  -- ★ Day's theorem (Day 1969; Freese–McKenzie, Thm. 2.2), as a complete iff.
  day-theorem : Finitary 𝑆 → Day-Statement 0ℓ ℰ
  day-theorem fin = CM⇒day fin , day-finitary⇒CongruenceModularVariety 0ℓ ℰ fin
```

---

[^1]: [`docs/notes/m6-6-forward-jonsson-day.md`](https://github.com/ualib/agda-algebras/blob/master/docs/notes/m6-6-forward-jonsson-day.md)

[^day]: A. Day, *A characterization of modularity for congruence lattices of algebras*, Canad. Math. Bull. **12** (1969), 167–173.  [doi:10.4153/CMB-1969-016-6](https://doi.org/10.4153/CMB-1969-016-6).

[^fm]: R. Freese and R. McKenzie, *Commutator Theory for Congruence Modular Varieties*, London Math. Soc. Lecture Note Series **125**, Cambridge University Press (1987), Thm. 2.2 and Lemma 2.3.  [Free online edition](https://math.hawaii.edu/~ralph/Commutator/).

[^bs]: S. Burris and H. P. Sankappanavar, *A Course in Universal Algebra*, Graduate Texts in Mathematics 78, Springer (1981), Thm. II.12.4.  [Free online edition](https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html).
