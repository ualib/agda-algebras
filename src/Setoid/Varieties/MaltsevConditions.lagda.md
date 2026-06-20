---
layout: default
file: "src/Setoid/Varieties/MaltsevConditions.lagda.md"
title: "Setoid.Varieties.MaltsevConditions module"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Maltsev conditions: permutability, distributivity, modularity

This is the [Setoid.Varieties.MaltsevConditions][] module of the [Agda Universal Algebra Library][].

A **Maltsev condition** is a property of a variety equivalent to the existence of
terms satisfying prescribed identities.  The three most basic concern the shape of
the congruence lattices of the algebras in the variety:

+  **congruence permutability** (CP) — composition of congruences is commutative;
+  **congruence distributivity** (CD) — every congruence lattice is distributive;
+  **congruence modularity** (CM) — every congruence lattice is modular.

[Setoid.Varieties.Maltsev][] fixed the *term-existence* side of CP as a theory
interpretation: `HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ`.  This module connects that to
the *lattice* side built in [Setoid.Congruences.Permutability][], proving the
concrete (and required) direction of **Maltsev's theorem**:[^maltsev]

>  a variety with a Maltsev term is congruence-permutable.

It then records the encodings of CD and CM — the Jónsson and Day identities, again as
theory interpretations `Th-Jonsson n ≼ ℰ` and `Th-Day n ≼ ℰ` — and states Jónsson's
and Day's theorems, and the converse of Maltsev's theorem, as the goals that remain.[^1]

The design choice — encoding each condition as `Th-X ≼ ℰ` rather than as a record
bundling a term with its identities, or an inductive scheme of identities — is
discussed in that note; in short, the interpretation encoding *is* the "term plus its
identities", packaged so that the whole interpretability apparatus
([Setoid.Varieties.Interpretation][]) applies uniformly to every condition.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.MaltsevConditions where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Bool.Base                     using  ( Bool ; true ; not
                                                      ; if_then_else_ )
open import Data.Fin.Base                      using  ( Fin ; toℕ ; fromℕ ; inject₁ )
                                               renaming ( zero to fzero ; suc to fsuc )
open import Data.Fin.Patterns                  using  ( 0F ; 1F ; 2F ; 3F )
open import Data.Nat.Base                      using  ( ℕ ; zero ; suc )
open import Data.Product                       using  ( _×_ ; _,_ ; Σ-syntax
                                                      ; proj₁ ; proj₂ )
open import Level                              using  ( Level ; 0ℓ ; _⊔_ )
                                               renaming ( suc to lsuc )
open import Relation.Binary                    using  ( Setoid ; IsEquivalence )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures                using  ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Terms                     using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation      using  ( Interpretation ; _✦_ )
open import Setoid.Algebras.Basic              using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic           using  ( Con ; reflexive
                                                      ; is-equivalence ; is-compatible )
open import Setoid.Congruences.Generation      using  ( Cg ; base )
open import Setoid.Congruences.Permutability   using  ( CongruencePermutable )
open import Setoid.Congruences.Properties      using  ( CongruenceDistributive
                                                      ; CongruenceModular )
open import Setoid.Terms.Basic                 using  ( Sub ; _[_] ; module Environment )
open import Setoid.Terms.Interpretation        using  ( graft≐[] )
open import Setoid.Varieties.EquationalLogic
open import Setoid.Varieties.FreeBridge        using  ( ❴_,_❵ ; pᵣ ; cg-pair→⊢ ; toEq )
open import Setoid.Varieties.FreeSubstitution  using  ( ≐→⊢ )
open import Setoid.Varieties.Interpretation    using  ( reductᴵ ; _⊨ₑ_ ; ⊧-interp
                                                      ; module Interpret )
open import Setoid.Varieties.Maltsev           using  ( Sig-Maltsev ; m-Op ; m ; tri
                                                      ; mxxy≈y ; mxyy≈x ; Th-Maltsev
                                                      ; HasMaltsevTerm )
open import Setoid.Varieties.SoundAndComplete  using  ( Eq ; _⊢_▹_≈_ ; module FreeAlgebra
                                                      ; module Soundness )

-- the generators of the Maltsev signature (the source signature of the interpretation)
open import Overture.Terms.Basic {𝑆 = Sig-Maltsev} using () renaming ( ℊ to ℊᴹ )

open import Function using ( Func )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )
open _⊢_▹_≈_ using ( refl ; sym ; trans )

private variable α ρ χ ι ℓ : Level
```

#### Congruences are compatible with term operations

The Maltsev argument needs that the chosen Maltsev *term operation* respects every
congruence.  This is an instance of a fundamental fact, which we prove once in full
generality: Given an algebra `𝑩` and a term `t` in the signature of `𝑩`, every
congruence `ψ` of `𝑩` is compatible with the evaluation of `t` — if two environments
are pointwise `ψ`-related at the leaves, the values of `t` are `ψ`-related.  The
proof is the obvious structural induction.

```agda
module _
  {𝑆 : Signature 𝓞 𝓥}
  {𝑩 : Algebra {𝑆 = 𝑆} α ρ}
  where
  open Environment 𝑩 using ( ⟦_⟧ )

  term-compatible : {V : Type χ}(ψ : Con 𝑩 ℓ)(t : Term V){η η′ : V → 𝕌[ 𝑩 ]}
    → (∀ v → proj₁ ψ (η v) (η′ v)) → proj₁ ψ (⟦ t ⟧ ⟨$⟩ η) (⟦ t ⟧ ⟨$⟩ η′)
  term-compatible ψ (ℊ v) h = h v
  term-compatible ψ (node f ts) h =
    is-compatible (proj₂ ψ) f (λ i → term-compatible ψ (ts i) h)
```

#### Maltsev's theorem: a Maltsev term implies congruences permute

Fix a theory `ℰ` over a signature `𝑆` (at the level pair `(0ℓ , 0ℓ)`, as the Maltsev
condition is phrased; this is no restriction for finitary algebraic theories).  We
show: if `ℰ` has a Maltsev term then every model `𝑩` of `ℰ` is congruence-permutable
(CP).

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}
  {X : Type χ} {Idx : Type ι}
  (ℰ : Idx → Term X × Term X)
  where

  MaltsevTerm⇒CP : HasMaltsevTerm ℰ
    → (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → {ℓ : Level} → CongruencePermutable 𝑩 ℓ
  MaltsevTerm⇒CP mt 𝑩 B⊨ {ℓ} θ φ {x}{y} (z , xθz , zφy) =
    m𝑩 x z y , xφw , wθy
    where
    open Setoid 𝔻[ 𝑩 ] using ( _≈_ )
      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
    open Environment 𝑩 using ( ⟦_⟧ )
    open Environment (reductᴵ 𝑩 (proj₁ mt)) using () renaming ( ⟦_⟧ to ⟦_⟧ᴿ )

    -- the witnessing interpretation, and the reduct's satisfaction of Th-Maltsev
    I : Interpretation Sig-Maltsev 𝑆
    I = proj₁ mt

    satM : reductᴵ 𝑩 I ⊨ₑ Th-Maltsev
    satM = proj₂ mt 𝑩 B⊨

    -- the curried Maltsev term operation: evaluate the derived term I m-Op
    m𝑩 : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ]
    m𝑩 a b c = ⟦ I m-Op ⟧ ⟨$⟩ tri a b c

    -- m𝑩 is a term operation, hence compatible with every congruence
    m-compat : (ψ : Con 𝑩 ℓ)(a a′ b b′ c c′ : 𝕌[ 𝑩 ])
      → proj₁ ψ a a′ → proj₁ ψ b b′ → proj₁ ψ c c′ → proj₁ ψ (m𝑩 a b c) (m𝑩 a′ b′ c′)
    m-compat ψ a a′ b b′ c c′ pa pb pc =
      term-compatible ψ (I m-Op) {tri a b c}{tri a′ b′ c′} λ { 0F → pa ; 1F → pb ; 2F → pc }

    -- evaluating a Maltsev application in the reduct lands on the curried m𝑩
    eval-m : (i₀ i₁ i₂ : Fin 3)(η : Fin 3 → 𝕌[ 𝑩 ])
      → ⟦ m (ℊ i₀) (ℊ i₁) (ℊ i₂) ⟧ᴿ ⟨$⟩ η ≈ m𝑩 (η i₀) (η i₁) (η i₂)
    eval-m i₀ i₁ i₂ η = cong ⟦ I m-Op ⟧ (λ { 0F → ≈refl ; 1F → ≈refl ; 2F → ≈refl })

    -- the two Maltsev identities, curried, from the reduct's satisfaction of Th-Maltsev
    mxxy : (a b : 𝕌[ 𝑩 ]) → m𝑩 a a b ≈ b
    mxxy a b = ≈trans (≈sym (eval-m 0F 0F 1F (tri a b b))) (satM mxxy≈y (tri a b b))

    mxyy : (a b : 𝕌[ 𝑩 ]) → m𝑩 a b b ≈ a
    mxyy a b = ≈trans (≈sym (eval-m 0F 1F 1F (tri a b b))) (satM mxyy≈x (tri a b b))

    -- equivalence-relation structure of the two congruences
    open IsEquivalence (is-equivalence (proj₂ θ)) using ()
      renaming (refl to θ-refl; sym to θ-sym; trans to θ-trans)

    open IsEquivalence (is-equivalence (proj₂ φ)) using ()
      renaming (refl to φ-refl; trans to φ-trans)

    -- the witness w = m(x, z, y) lies φ-above x and θ-below y
    --   x φ m(x,z,z) = x  (identity mxyy) then m(x,z,z) φ m(x,z,y)  (since z φ y)
    xφw : proj₁ φ x (m𝑩 x z y)
    xφw = φ-trans  (reflexive (proj₂ φ) (≈sym (mxyy x z)))
                   (m-compat φ x x z z z y φ-refl φ-refl zφy)

    --   m(x,z,y) θ m(x,x,y)  (since z θ x) then m(x,x,y) = y  (identity mxxy)
    wθy : proj₁ θ (m𝑩 x z y) y
    wθy = θ-trans  (m-compat θ x x z x y y θ-refl (θ-sym xθz) θ-refl)
                   (reflexive (proj₂ θ) (mxxy x y))
```

The theorem above is the required acceptance criterion: CP's Maltsev-term
characterization, in its concrete "term ⟹ permutable" direction.

#### Congruence-permutable varieties

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.
A *congruence-permutable variety* is one in which all models are
congruence-permutable.

The forward Maltsev theorem, restated for the whole variety, asserts that every model
of a theory with a Maltsev term is congruence-permutable.

```agda
module _
  {α ρ ℓ : Level}
  {𝑆 : Signature 0ℓ 0ℓ}
  {X : Type χ} {Idx : Type ι}
  (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X)
  where

  -- "Every model is congruence-permutable."
  CongruencePermutableVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruencePermutableVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruencePermutable 𝑩 ℓ

  -- Maltsev's theorem, forward direction, as a statement about the variety (PROVED).
  maltsev⇒CP : HasMaltsevTerm ℰ → CongruencePermutableVariety
  maltsev⇒CP mt 𝑩 B⊨ = MaltsevTerm⇒CP ℰ mt 𝑩 B⊨
```

#### The converse of Maltsev's theorem

The converse can be stated formally (as a checked `Type`), as follows:

```agda
  -- A congruence-permutable variety has a Maltsev term.
  CP⇒maltsev-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CP⇒maltsev-Statement = CongruencePermutableVariety → HasMaltsevTerm {α = α}{ρ} ℰ
```

Our goal in this section is to show that the `CP⇒maltsev-Statement`{.AgdaFunction}
type is inhabited, thereby proving the statement and completing the characterization:
a congruence-permutable variety has a Maltsev term.[^maltsev2]

The construction is the classical one (Burris–Sankappanavar, Thm. II.12.2), run through
the free-algebra congruence/derivability bridge of [Setoid.Varieties.FreeBridge][].

+  Work in `𝔽[ Fin 3 ]`{.AgdaFunction}, the relatively free algebra on three generators
   `x , y , z`.  It is a model of the theory (`satisfies`{.AgdaFunction}), hence
   congruence-permutable by hypothesis.

+  Take the principal congruences `θ = Cg ❴ x , y ❵`{.AgdaFunction} and
   `φ = Cg ❴ y , z ❵`{.AgdaFunction}.  Then `x θ y` and `y φ z`, so `(θ ∘ φ) x z`;
   permutability gives `(φ ∘ θ) x z`, i.e. a witness term `w` with `x φ w` and
   `w θ z`.  Since the carrier of `𝔽` *is* `Term (Fin 3)`, this `w` is literally the
   Maltsev term `m x y z`.

+  Translate the two memberships through collapsing-substitution homomorphisms (the
   bridge `cg-pair→⊢`{.AgdaFunction}).  Collapsing `z ↦ y` turns `x φ w` into the
   derivable equation `m x y y ≈ x`; collapsing `y ↦ x` turns `w θ z` into
   `m x x y ≈ y` — the two Maltsev identities.

+  Package `m` as the interpretation `I : Th-Maltsev ≼ ℰ` and discharge the satisfaction
   obligation, for an arbitrary model `𝑩`, via `⊧-interp`{.AgdaFunction} and
   `sound`{.AgdaFunction}ness.

The collapsing substitutions are chosen to be exactly the position maps `_✦_` uses when
it interprets a Maltsev application, so the bridge's output equation is *definitionally*
`I ✦ (m x x y) ≈ I ✦ y` — only the term-level shim `graft≐[]`{.AgdaFunction} (identifying
the node action `graft` of `_✦_` with the substitution `_[_]` of the hom) stands between
the two, and it is one `≐→⊢`{.AgdaFunction} step.

Because the free algebra is built on the variable type `Fin 3 : Type 0ℓ`, and the free
construction shares one universe level between the equations' variables and the free
generators, the theory's variable type is taken at level `0ℓ` (`X : Type 0ℓ`); this is
no restriction for the finitary algebraic theories the Maltsev condition concerns.

##### The theorem

Fix a theory `ℰ` over a signature `𝑆 : Signature 0ℓ 0ℓ`, with variables `X : Type 0ℓ`.
We inhabit `CP⇒maltsev-Statement`{.AgdaFunction} at the levels of the free algebra
`𝔽[ Fin 3 ] : Algebra (ov 0ℓ) (ι ⊔ ov 0ℓ)` (here `ov 0ℓ = lsuc 0ℓ`, since
`𝓞 = 𝓥 = 0ℓ`), and at the congruence level `ι ⊔ ov 0ℓ` at which its principal
congruences live.

```agda
module _ {𝑆 : Signature 0ℓ 0ℓ}{X : Type 0ℓ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  CP⇒maltsev : CP⇒maltsev-Statement ℰ
  CP⇒maltsev cpv = I , red
    where
    -- the theory in the `I → Eq` shape that the free algebra consumes
    E : Idx → Eq
    E = toEq ℰ

    open FreeAlgebra E using ( 𝔽[_] ; satisfies )

    -- the relatively free algebra on three generators, and its three generators
    𝔽 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)
    𝔽 = 𝔽[ Fin 3 ]

    x y z : 𝕌[ 𝔽 ]
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F

    -- 𝔽 is a model, hence congruence-permutable by hypothesis
    𝔽cp : CongruencePermutable 𝔽 (ι ⊔ lsuc 0ℓ)
    𝔽cp = cpv 𝔽 satisfies

    -- the two principal congruences
    θ φ : Con 𝔽 (ι ⊔ lsuc 0ℓ)
    θ = Cg ❴ x , y ❵
    φ = Cg ❴ y , z ❵

    xθy : proj₁ θ x y
    xθy = base pᵣ

    yφz : proj₁ φ y z
    yφz = base pᵣ

    -- permutability: from (x , z) ∈ θ ∘ φ get (x , z) ∈ φ ∘ θ, with witness w
    perm : Σ[ v ∈ 𝕌[ 𝔽 ] ] (proj₁ φ x v × proj₁ θ v z)
    perm = 𝔽cp θ φ (y , xθy , yφz)

    w : 𝕌[ 𝔽 ]
    w = proj₁ perm

    xφw : proj₁ φ x w
    xφw = proj₁ (proj₂ perm)

    wθz : proj₁ θ w z
    wθz = proj₂ (proj₂ perm)

    -- the witness term packaged as the Maltsev interpretation
    I : Interpretation Sig-Maltsev 𝑆
    I m-Op = w

    -- the collapsing substitutions: exactly the position maps `I ✦` uses on a
    -- Maltsev application, so that `graft w σ` is definitionally `I ✦ (m _ _ _)`
    σxxy σxyy : Sub {𝑆 = 𝑆} (Fin 3) (Fin 3)
    σxxy i = I ✦ tri (ℊᴹ 0F) (ℊᴹ 0F) (ℊᴹ 1F) i
    σxyy i = I ✦ tri (ℊᴹ 0F) (ℊᴹ 1F) (ℊᴹ 1F) i

    -- the bridge: collapse turns each membership into a derivable equation
    bridge-xxy : E ⊢ Fin 3 ▹ w [ σxxy ] ≈ z [ σxxy ]
    bridge-xxy = cg-pair→⊢ E σxxy x y refl wθz

    bridge-xyy : E ⊢ Fin 3 ▹ x [ σxyy ] ≈ w [ σxyy ]
    bridge-xyy = cg-pair→⊢ E σxyy y z refl xφw

    -- the two Maltsev identities, as the interpreted equations
    deriv-xxy : E ⊢ Fin 3 ▹ I ✦ proj₁ (Th-Maltsev mxxy≈y) ≈ I ✦ proj₂ (Th-Maltsev mxxy≈y)
    deriv-xxy = trans (≐→⊢ (graft≐[] w σxxy)) bridge-xxy

    deriv-xyy : E ⊢ Fin 3 ▹ I ✦ proj₁ (Th-Maltsev mxyy≈x) ≈ I ✦ proj₂ (Th-Maltsev mxyy≈x)
    deriv-xyy = trans (≐→⊢ (graft≐[] w σxyy)) (sym bridge-xyy)

    -- every model satisfying ℰ satisfies the interpreted Maltsev identities
    red : (𝑩 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)) → 𝑩 ⊨ₑ ℰ → reductᴵ 𝑩 I ⊨ₑ Th-Maltsev
    red 𝑩 B⊨ mxxy≈y = Goal
      where
      Goal : reductᴵ 𝑩 I ⊧ m (ℊ 0F) (ℊ 0F) (ℊ 1F) ≈ (ℊ 1F)
      Goal = ⊧-interp 𝑩 I {s = proj₁ (Th-Maltsev mxxy≈y)} {t = proj₂ (Th-Maltsev mxxy≈y)}
               (Soundness.sound E 𝑩 B⊨ deriv-xxy)
    red 𝑩 B⊨ mxyy≈x = Goal
      where
      Goal : reductᴵ 𝑩 I ⊧ m (ℊ 0F) (ℊ 1F) (ℊ 1F) ≈ (ℊ 0F)
      Goal = ⊧-interp 𝑩 I {s = proj₁ (Th-Maltsev mxyy≈x)} {t = proj₂ (Th-Maltsev mxyy≈x)}
               (Soundness.sound E 𝑩 B⊨ deriv-xyy)
```


#### Distributivity and modularity of the congruence lattice

CD and CM are properties of the congruence *lattice*, defined in
[Setoid.Congruences.Properties][] as `CongruenceDistributive` and
`CongruenceModular` (at the absorbing relation level, so that meet and join are
operations on a single type).  We use them here to phrase the Jónsson and Day variety
conditions below.

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
-- parity of a natural number, to split the Jónsson/Day "fork" identities by index
even? : ℕ → Bool
even? zero = true
even? (suc m) = not (even? m)

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
  Th-Jonsson dxyz≈x      = d fzero x y z , x
  Th-Jonsson (dxyx≈x i)  = d i x y x , x
  Th-Jonsson dxyz≈z      = d (fromℕ n) x y z , z
  Th-Jonsson (d-fork i) = if even? (toℕ i)
    then ( d (inject₁ i) x x z , d (fsuc i) x x z )   -- i even: agree on (x,x,z)
    else ( d (inject₁ i) x y y , d (fsuc i) x y y )   -- i odd:  agree on (x,y,y)

HasJonssonTerms : (n : ℕ)
  {α ρ : Level} {𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
HasJonssonTerms n {α}{ρ} ℰ = Th-Jonsson n ≼ ℰ
  where open Interpret α ρ
```

#### Day terms (congruence modularity)

Congruence modularity is characterized by a chain of *quaternary* terms `m₀ , … , mₙ`,
the **Day terms**[^day] (Day 1969; Burris–Sankappanavar, Thm. 12.4), with identities

    m₀(x,y,z,u) ≈ x,   mₙ(x,y,z,u) ≈ u,   mᵢ(x,y,y,x) ≈ x   (all i),
    mᵢ(x,x,u,u) ≈ mᵢ₊₁(x,x,u,u)  (i even),  mᵢ(x,y,y,u) ≈ mᵢ₊₁(x,y,y,u)  (i odd).

```agda
-- the canonical 4-element tuple over the variable carrier Fin 4
quad : {ℓ : Level}{A : Type ℓ} → A → A → A → A → Fin 4 → A
quad a b c d 0F = a
quad a b c d 1F = b
quad a b c d 2F = c
quad a b c d 3F = d

module _ (n : ℕ) where

  -- n+1 quaternary operation symbols.
  Sig-Day : Signature 0ℓ 0ℓ
  Sig-Day = Fin (suc n) , (λ _ → Fin 4)

  private
    d : Fin (suc n) → (a b c d : Term (Fin 4)) → Term (Fin 4)
    d i a b c d = node i (quad a b c d)

    x y z u : Term {𝑆 = Sig-Day} (Fin 4)
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F ; u = ℊ 3F

  data Eq-Day : Type where
    mxyzu≈x  : Eq-Day                 -- m₀(x,y,z,u) ≈ x
    mxyyx≈x  : Fin (suc n) → Eq-Day   -- mᵢ(x,y,y,x) ≈ x
    mxyzu≈u  : Eq-Day                 -- mₙ(x,y,z,u) ≈ u
    m-fork   : Fin n → Eq-Day         -- consecutive mᵢ, mᵢ₊₁ agree (parity-dependent)

  Th-Day : Eq-Day → Term (Fin 4) × Term (Fin 4)
  Th-Day mxyzu≈x      = d fzero x y z u , x
  Th-Day mxyzu≈u      = d (fromℕ n) x y z u , u
  Th-Day (mxyyx≈x i)  = d i x y y x , x
  Th-Day (m-fork i)   = if even? (toℕ i)
    then ( d (inject₁ i) x x u u , d (fsuc i) x x u u )   -- i even: agree on (x,x,u,u)
    else ( d (inject₁ i) x y y u , d (fsuc i) x y y u )   -- i odd:  agree on (x,y,y,u)

HasDayTerms : (n : ℕ){α ρ : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
HasDayTerms n {α}{ρ} ℰ = Th-Day n ≼ ℰ  where open Interpret α ρ
```

#### Logical equivalence of types

Both remaining characterizations are *iff*s, so we package the two-way implication of
two types as `_⇔_`{.AgdaFunction}.  (The standard library's `_⇔_` is the bundled
`Function.Bundles.Equivalence` record, carrying congruence proofs; here the lighter
logical equivalence — a pair of functions — is what these `Type`-level statements want.)

```agda
_⇔_ : {a b : Level} → Type a → Type b → Type (a ⊔ b)
P ⇔ Q = (P → Q) × (Q → P)
infix 1 _⇔_
```

#### The conditions as properties of a variety, and the deferred theorems

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.
A *congruence-distributive variety* is one in which all models are
congruence-distributive, and similarly for CM.  The Jónsson and Day characterizations
of CD and CM varieties are stated here as the goals that remain (their constructions
are sketched in the design note); each is a `Type`.

```agda
module _ {α ρ ℓ : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  -- "Every model is congruence-distributive / -modular."
  CongruenceDistributiveVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceDistributiveVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceDistributive 𝑩 ℓ

  CongruenceModularVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceModularVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceModular 𝑩 ℓ

  -- Jónsson's theorem (DEFERRED): CD ⇔ existence of Jónsson terms.
  Jonsson-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Jonsson-Statement = CongruenceDistributiveVariety ⇔ (Σ[ n ∈ ℕ ] HasJonssonTerms n {α = α}{ρ = ρ} ℰ)

  -- Day's theorem (DEFERRED): CM ⇔ existence of Day terms.
  Day-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Day-Statement = CongruenceModularVariety ⇔ (Σ[ n ∈ ℕ ] HasDayTerms n {α = α}{ρ = ρ} ℰ)
```

---

[^1]: See the design note `docs/notes/m6-3-maltsev-conditions.md` for the construction plans.

[^day]: A. Day, *A characterization of modularity for congruence lattices of algebras*, Canad. Math. Bull. **12** (1969), 167–173.  [doi:10.4153/CMB-1969-016-6](https://doi.org/10.4153/CMB-1969-016-6).

[^jonsson]: B. Jónsson, *Algebras whose congruence lattices are distributive*, Math. Scand. **21** (1967), 110–121.  [doi:10.7146/math.scand.a-10850](https://doi.org/10.7146/math.scand.a-10850) (open access; mirror at [EUDML](https://eudml.org/doc/166010)).

[^maltsev]: A. I. Mal'cev, *On the general theory of algebraic systems* (Russian), Mat. Sb. (N.S.) **35(77)** (1954), 3–20; Engl. transl., *Amer. Math. Soc. Transl.* (2) **27** (1963), 125–142.  Original at [Math-Net.Ru](http://www.mathnet.ru/sm5264); translation in [*Eighteen Papers on Algebra* (AMS)](https://pubs.ams.org/ebooks/trans2/027/).

[^maltsev2]: A. I. Mal'cev, *On the general theory of algebraic systems* (Russian), Mat. Sb. (N.S.) **35(77)** (1954), 3–20; Burris and Sankappanavar, *A Course in Universal Algebra*, Thm. II.12.2.

{% include UALib.Links.md %}
