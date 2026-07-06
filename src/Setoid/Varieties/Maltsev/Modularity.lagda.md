---
layout: default
file: "src/Setoid/Varieties/Maltsev/Modularity.lagda.md"
title: "Setoid.Varieties.Maltsev.Modularity module (The Agda Universal Algebra Library)"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Maltsev conditions: congruence modularity

This is the [Setoid.Varieties.Maltsev.Modularity][] module of the [Agda Universal Algebra Library][].

This module records the Maltsev term condition for *congruence modularity* — the Day
identities, as a theory interpretation `Th-Day n ≼ ℰ` — states Day's theorem, and
proves its **converse** direction: a congruence-modular variety has Day terms
(`CM⇒day`{.AgdaFunction}), mirroring the converse of Jónsson's theorem
([Setoid.Varieties.Maltsev.Distributivity][]).  The *forward* direction (Day terms ⟹ CM)
remains deferred for the substantive structural reason recorded below and in the
[design note](https://github.com/ualib/agda-algebras/blob/master/docs/notes/m6-6-forward-jonsson-day.md).

#### Modularity of the congruence lattice

**Congruence modularity** (CM) is a property of the congruence lattice of an algebra,
defined in [Setoid.Congruences.Properties][] as `CongruenceModular` (at the absorbing
relation level, so that meet and join are operations on a single type).  We use it
here to phrase the Day variety condition below.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev.Modularity where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Bool.Base                     using  ( true ; false ; if_then_else_ )
open import Data.Fin.Base                      using  ( Fin ; toℕ ; fromℕ ; inject₁ )
                                               renaming ( zero to fzero ; suc to fsuc )
open import Data.Fin.Patterns                  using  ( 0F ; 1F ; 2F ; 3F )
open import Data.Nat.Base                      using  ( ℕ ; suc )
open import Data.Product                       using  ( _×_ ; _,_ ; Σ-syntax
                                                      ; proj₁ ; proj₂ )
open import Level                              using  ( Level ; 0ℓ ; _⊔_ )
                                               renaming ( suc to lsuc )
open import Relation.Binary                    using  ( Setoid )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Basic                     using  ( _⇔_ )
open import Overture.Signatures                using  ( Signature )
open import Overture.Terms                     using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation      using  ( Interpretation ; graft ; _✦_ )
open import Setoid.Algebras.Basic              using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic           using  ( Con )
open import Setoid.Congruences.Generation      using  ( Cg ; base ; transitive ; _∨_
                                                      ; ∨-upperˡ ; ∨-upperʳ
                                                      ; module principal )
open import Setoid.Congruences.ChainJoin       using  ( Finitary ; finitary⇒JoinIsChain )
open import Setoid.Congruences.Lattice         using  ( _∧_ ; _⊆_ )
open import Setoid.Congruences.Properties      using  ( CongruenceModular )
open import Setoid.Terms.Basic                 using  ( Sub ; _[_] )
open import Setoid.Terms.Interpretation        using  ( graft≐[] )
open import Setoid.Varieties.EquationalLogic   using  ( _⊧_≈_ )
open import Setoid.Varieties.FreeSubstitution  using  ( ≐→⊢ ; cg-pair→⊢ ; cg-pairs→⊢ )
open import Setoid.Varieties.Interpretation    using  ( reductᴵ ; _⊨ₑ_ ; ⊧-interp
                                                      ; module Interpret )
open import Setoid.Varieties.Maltsev.Basic     using  ( even? )
open import Setoid.Varieties.Maltsev.Distributivity
                                               using  ( ParityChain ; chain→parityᵒ
                                                      ; head-linked )
open import Setoid.Varieties.SoundAndComplete  using  ( Eq ; toEq ; _⊢_▹_≈_
                                                      ; module FreeAlgebra
                                                      ; module Soundness )

open _⊢_▹_≈_ using ( sub ; refl ; sym ; trans )

private variable α ρ χ ι ℓ : Level
```
-->

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
quad : {ℓ : Level}{A : Type ℓ} → A → A → A → A → Fin 4 → A
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

The curried extraction for the Day chain is the verbatim quaternary analogue of the Jónsson
`d𝑩`{.AgdaFunction} / `eval-d`{.AgdaFunction} block (over `quad`{.AgdaFunction} in place of
`tri`{.AgdaFunction}).

The forward *staircase*, however, is *not* a mechanical mirror of Jónsson's, and is deferred.
The reason is structural: the `ψ`-pinning that makes Jónsson's argument go through —
every `dᵢ(a, ·, b)` is θ-tied to `a` via `dᵢ(x, y, x) ≈ x` — needs, for the Day term
`mᵢ(x, y, y, x) ≈ x`, the *two* middle arguments to be equal, so only elements
`mᵢ(a, c, c, b)` are `ψ`-pinnable.

The even-fork column `mᵢ(a, a, b, b)` (`a ≠ b`) is therefore *not* pinnable, and
connecting it to the pinnable columns demands a single-slot `a ↔ b` move that is not
a `θ ∨ (φ ∧ ψ)` step.

Jónsson's two-column staircase has no analogue here; Day's theorem needs the
genuinely different (2-dimensional / `A²`) construction of Day (1969), recorded
for a successor in the design note.[^1]

#### The Maltsev condition as a property of a variety

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.
A *congruence-modular variety* is one in which all models are
congruence-modular (CM).  Day's characterization of CM varieties is the iff statement
`Day-Statement`{.AgdaFunction}.  The **forward** (term ⟹ CM) direction is deferred for
the substantive reason recorded above and in the design note, not mere lack of effort;
the **reverse** (CM ⟹ terms) direction is proved at the end of this module
(`CM⇒day`{.AgdaFunction}), inhabiting the `proj₁` projection of
`Day-Statement`{.AgdaFunction}.

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

  -- Day's theorem: CM ⇔ existence of Day terms.  The reverse (CM ⟹ terms)
  -- half is `CM⇒day` at the end of this module.  The forward half is deferred:
  -- unlike Jónsson, the forward staircase is *not* a mechanical mirror — see
  -- the design note `docs/notes/m6-6-forward-jonsson-day.md`.
  Day-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Day-Statement = CongruenceModularVariety ⇔ Σ[ n ∈ ℕ ] HasDayTerms n {α} {ρ}ℰ
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
  {fin : Finitary 𝑆}
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
  CM⇒day : CongruenceModularVariety 0ℓ ℰ → Σ[ n ∈ ℕ ] HasDayTerms n ℰ
  CM⇒day cmv = n , I , red
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
    ... | true   | s = discharge 𝑩 B⊨ (mxxuu (inject₁ i)) (mxxuu (fsuc i))
                         (deriv-fork-φ i (proj₁ s))
    ... | false  | s = discharge 𝑩 B⊨ (mxyyu (inject₁ i)) (mxyyu (fsuc i))
                         (deriv-fork-θ i s)
```

With the converse in hand, `Day-Statement`{.AgdaFunction} awaits only its forward half:
once the genuinely two-dimensional staircase of Day 1969 is formalized (see the design
note `docs/notes/m6-6-forward-jonsson-day.md`), the two will assemble into the complete
iff exactly as `jonsson-theorem`{.AgdaFunction} does for distributivity.

---

[^1]: [`docs/notes/m6-6-forward-jonsson-day.md`](https://github.com/ualib/agda-algebras/blob/master/docs/notes/m6-6-forward-jonsson-day.md)

[^day]: A. Day, *A characterization of modularity for congruence lattices of algebras*, Canad. Math. Bull. **12** (1969), 167–173.  [doi:10.4153/CMB-1969-016-6](https://doi.org/10.4153/CMB-1969-016-6).

[^bs]: S. Burris and H. P. Sankappanavar, *A Course in Universal Algebra*, Graduate Texts in Mathematics 78, Springer (1981), Thm. II.12.4.  [Free online edition](https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html).
