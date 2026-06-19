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
the congruence lattices of the variety's algebras:

+  **congruence permutability** (CP) — composition of congruences is commutative;
+  **congruence distributivity** (CD) — every congruence lattice is distributive;
+  **congruence modularity** (CM) — every congruence lattice is modular.

[Setoid.Varieties.Maltsev][] fixed the *term-existence* side of CP as a theory
interpretation: `HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ`.  This module connects that to
the *lattice* side built in [Setoid.Congruences.Permutability][], proving the
concrete (and required) direction of **Maltsev's theorem**:

>  a variety with a Maltsev term is congruence-permutable.

It then records the encodings of CD and CM — the Jónsson and Day identities, again as
theory interpretations `Th-Jonsson n ≼ ℰ` and `Th-Day n ≼ ℰ` — and states Jónsson's
and Day's theorems, and the converse of Maltsev's theorem, as the goals that remain
(see the design note `docs/notes/m6-3-maltsev-conditions.md` for the construction
plans).

The design choice — encoding each condition as `Th-X ≼ ℰ` rather than as a record
bundling a term with its identities, or an inductive scheme of identities — is
discussed in that note; in short, the interpretation encoding *is* the "term plus its
identities", packaged so that the whole interpretability apparatus
([Setoid.Varieties.Interpretation][]) applies uniformly to every condition.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.MaltsevConditions where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                    using  () renaming ( Set to Type )
open import Data.Bool.Base                    using  ( Bool ; true ; false ; not
                                                     ; if_then_else_ )
open import Data.Fin.Base                     using  ( Fin ; toℕ ; fromℕ ; inject₁ )
                                              renaming ( zero to fzero ; suc to fsuc )
open import Data.Fin.Patterns                 using  ( 0F ; 1F ; 2F ; 3F )
open import Data.Nat.Base                     using  ( ℕ ; zero ; suc )
open import Data.Product                      using  ( _×_ ; _,_ ; Σ-syntax
                                                     ; proj₁ ; proj₂ )
open import Level                             using  ( Level ; 0ℓ ; _⊔_ )
                                              renaming ( suc to lsuc )
open import Relation.Binary                   using  ( Setoid ; IsEquivalence )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures               using  ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Terms                    using  ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation     using  ( Interpretation )
open import Setoid.Algebras.Basic             using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms.Basic                using  ( module Environment )
open import Setoid.Congruences.Basic          using  ( Con ; reflexive
                                                     ; is-equivalence ; is-compatible )
open import Setoid.Congruences.Permutability  using  ( _⨾_ ; Permutes
                                                     ; CongruencePermutable )
open import Setoid.Congruences.Modularity     using  ( CongruenceDistributive
                                                     ; CongruenceModular ) public
open import Setoid.Varieties.Interpretation   using  ( reductᴵ ; _⊨ₑ_
                                                     ; module Interpret )
open import Setoid.Varieties.Maltsev          using  ( Sig-Maltsev ; m-Op ; m ; tri
                                                     ; mxxy≈y ; mxyy≈x ; Th-Maltsev
                                                     ; HasMaltsevTerm )

open import Function using ( Func )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α ρ χ ι ℓ : Level
```

#### Congruences are compatible with term operations

The Maltsev argument needs that the chosen Maltsev *term operation* respects every
congruence.  This is an instance of a fundamental fact, which we prove once in full
generality: a congruence `ψ` of an algebra `𝑩` is compatible with the evaluation of
*any* term `t` — if two environments are pointwise `ψ`-related at the leaves, the
values of `t` are `ψ`-related.  The proof is the obvious structural induction: a leaf
is the hypothesis; a node is closed under `ψ`'s `is-compatible` field.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}{𝑩 : Algebra {𝑆 = 𝑆} α ρ} where
  open Environment 𝑩 using ( ⟦_⟧ )

  term-compatible : {V : Type χ}(ψ : Con 𝑩 ℓ)(t : Term {𝑆 = 𝑆} V){η η′ : V → 𝕌[ 𝑩 ]}
    → (∀ v → proj₁ ψ (η v) (η′ v)) → proj₁ ψ (⟦ t ⟧ ⟨$⟩ η) (⟦ t ⟧ ⟨$⟩ η′)
  term-compatible ψ (ℊ v) h = h v
  term-compatible ψ (node f ts) h =
    is-compatible (proj₂ ψ) f (λ i → term-compatible ψ (ts i) h)
```

#### Maltsev's theorem: a Maltsev term gives permutability

Fix a theory `ℰ` over a signature `𝑆` (at the level pair `(0ℓ , 0ℓ)`, as the Maltsev
condition is phrased; this is no restriction for finitary algebraic theories).  We
show: if `ℰ` has a Maltsev term then every model `𝑩` of `ℰ` is
congruence-permutable.

```agda
module _
  {𝑆 : Signature 0ℓ 0ℓ}
  {X : Type χ} {Idx : Type ι}
  (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X)
  where

  hasMaltsevTerm⇒permutable : HasMaltsevTerm {α = α}{ρ = ρ} ℰ
    → (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ → {ℓ : Level} → CongruencePermutable 𝑩 ℓ
  hasMaltsevTerm⇒permutable mt 𝑩 B⊨ {ℓ} θ φ {x}{y} (z , xθz , zφy) =
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
characterization, in its concrete "term ⟹ permutable" direction.  Read for the whole
variety — every model of a theory with a Maltsev term is congruence-permutable — it is
`maltsev⇒CP` in the final section.

#### Distributivity and modularity of the congruence lattice

CD and CM are properties of the congruence *lattice*, defined in
[Setoid.Congruences.Modularity][] as `CongruenceDistributive` and
`CongruenceModular` (at the absorbing relation level, so that meet and join are
operations on a single type).  They are re-exported here (the `public` on the import
above) so the Maltsev conditions of this module — permutability, and the Jónsson/Day
conditions below — read from one place.

#### Jónsson terms (congruence distributivity)

Where a single ternary term characterizes CP, a *chain* of ternary terms
`d₀ , … , dₙ` — the **Jónsson terms** — characterizes CD.  They are encoded exactly
as the Maltsev term was: a signature `Sig-Jonsson n` of `n+1` ternary symbols, and a
theory `Th-Jonsson n` of the Jónsson identities (Burris–Sankappanavar, Def. 12.5),

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
    dⱼ : Fin (suc n) → (a b c : Term {𝑆 = Sig-Jonsson} (Fin 3)) → Term {𝑆 = Sig-Jonsson} (Fin 3)
    dⱼ i a b c = node {𝑆 = Sig-Jonsson} i (tri a b c)

    xⱼ yⱼ zⱼ : Term {𝑆 = Sig-Jonsson} (Fin 3)
    xⱼ = ℊ 0F ; yⱼ = ℊ 1F ; zⱼ = ℊ 2F

  -- the index of the Jónsson identities: endpoints, the "x,y,x" family, and the forks
  data Eq-Jonsson : Type where
    J-fst  : Eq-Jonsson                 -- d₀(x,y,z) ≈ x
    J-lst  : Eq-Jonsson                 -- dₙ(x,y,z) ≈ z
    J-mid  : Fin (suc n) → Eq-Jonsson   -- dᵢ(x,y,x) ≈ x
    J-fork : Fin n → Eq-Jonsson         -- consecutive dᵢ, dᵢ₊₁ agree (parity-dependent)

  Th-Jonsson : Eq-Jonsson → Term {𝑆 = Sig-Jonsson} (Fin 3) × Term {𝑆 = Sig-Jonsson} (Fin 3)
  Th-Jonsson J-fst      = dⱼ fzero xⱼ yⱼ zⱼ , xⱼ
  Th-Jonsson J-lst      = dⱼ (fromℕ n) xⱼ yⱼ zⱼ , zⱼ
  Th-Jonsson (J-mid i)  = dⱼ i xⱼ yⱼ xⱼ , xⱼ
  Th-Jonsson (J-fork i) = if even? (toℕ i)
    then ( dⱼ (inject₁ i) xⱼ xⱼ zⱼ , dⱼ (fsuc i) xⱼ xⱼ zⱼ )   -- i even: agree on (x,x,z)
    else ( dⱼ (inject₁ i) xⱼ yⱼ yⱼ , dⱼ (fsuc i) xⱼ yⱼ yⱼ )   -- i odd:  agree on (x,y,y)

HasJonssonTerms : (n : ℕ){α ρ χ ι : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type _
HasJonssonTerms n {α}{ρ} ℰ = Th-Jonsson n ≼ ℰ  where open Interpret α ρ
```

#### Day terms (congruence modularity)

Congruence modularity is characterized by a chain of *quaternary* terms `m₀ , … , mₙ`,
the **Day terms** (Day 1969; Burris–Sankappanavar, Thm. 12.4), with identities

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
    dᵈ : Fin (suc n) → (a b c d : Term {𝑆 = Sig-Day} (Fin 4)) → Term {𝑆 = Sig-Day} (Fin 4)
    dᵈ i a b c d = node {𝑆 = Sig-Day} i (quad a b c d)

    xᵈ yᵈ zᵈ uᵈ : Term {𝑆 = Sig-Day} (Fin 4)
    xᵈ = ℊ 0F ; yᵈ = ℊ 1F ; zᵈ = ℊ 2F ; uᵈ = ℊ 3F

  data Eq-Day : Type where
    D-fst  : Eq-Day                 -- m₀(x,y,z,u) ≈ x
    D-lst  : Eq-Day                 -- mₙ(x,y,z,u) ≈ u
    D-mid  : Fin (suc n) → Eq-Day   -- mᵢ(x,y,y,x) ≈ x
    D-fork : Fin n → Eq-Day         -- consecutive mᵢ, mᵢ₊₁ agree (parity-dependent)

  Th-Day : Eq-Day → Term {𝑆 = Sig-Day} (Fin 4) × Term {𝑆 = Sig-Day} (Fin 4)
  Th-Day D-fst      = dᵈ fzero xᵈ yᵈ zᵈ uᵈ , xᵈ
  Th-Day D-lst      = dᵈ (fromℕ n) xᵈ yᵈ zᵈ uᵈ , uᵈ
  Th-Day (D-mid i)  = dᵈ i xᵈ yᵈ yᵈ xᵈ , xᵈ
  Th-Day (D-fork i) = if even? (toℕ i)
    then ( dᵈ (inject₁ i) xᵈ xᵈ uᵈ uᵈ , dᵈ (fsuc i) xᵈ xᵈ uᵈ uᵈ )   -- i even: agree on (x,x,u,u)
    else ( dᵈ (inject₁ i) xᵈ yᵈ yᵈ uᵈ , dᵈ (fsuc i) xᵈ yᵈ yᵈ uᵈ )   -- i odd:  agree on (x,y,y,u)

HasDayTerms : (n : ℕ){α ρ χ ι : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type _
HasDayTerms n {α}{ρ} ℰ = Th-Day n ≼ ℰ  where open Interpret α ρ
```

#### The conditions as properties of a variety, and the deferred theorems

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.  A
*congruence-permutable variety* is one all of whose models are
congruence-permutable, and similarly for CD and CM.  The forward Maltsev theorem,
restated for the whole variety, is `maltsev⇒CP`.  The remaining theorems — the
converse of Maltsev, and the Jónsson and Day characterizations — are stated here as
the goals that remain (their constructions are sketched in the design note); each is a
`Type`, not yet inhabited.

```agda
module _ {χ ι : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X)(α ρ : Level) where

  -- "Every model is congruence-permutable / -distributive / -modular."
  CongruencePermutableVariety : (ℓ : Level) → Type _
  CongruencePermutableVariety ℓ =
    (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ → CongruencePermutable 𝑩 ℓ

  CongruenceDistributiveVariety : (ℓ₀ : Level) → Type _
  CongruenceDistributiveVariety ℓ₀ =
    (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceDistributive 𝑩 ℓ₀

  CongruenceModularVariety : (ℓ₀ : Level) → Type _
  CongruenceModularVariety ℓ₀ =
    (𝑩 : Algebra {𝑆 = 𝑆} α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceModular 𝑩 ℓ₀

  -- Maltsev's theorem, forward direction, as a statement about the variety (PROVED).
  maltsev⇒CP : HasMaltsevTerm {α = α}{ρ} ℰ → {ℓ : Level} → CongruencePermutableVariety ℓ
  maltsev⇒CP mt 𝑩 B⊨ = hasMaltsevTerm⇒permutable ℰ mt 𝑩 B⊨

  -- The converse (DEFERRED): a congruence-permutable variety has a Maltsev term.
  CP⇒maltsev-Statement : (ℓ : Level) → Type _
  CP⇒maltsev-Statement ℓ = CongruencePermutableVariety ℓ → HasMaltsevTerm {α = α}{ρ} ℰ

  -- Jónsson's theorem (DEFERRED): CD ⇔ existence of Jónsson terms.
  Jonsson-Statement : (ℓ₀ : Level) → Type _
  Jonsson-Statement ℓ₀ =
      (CongruenceDistributiveVariety ℓ₀ → Σ[ n ∈ ℕ ] HasJonssonTerms n {α = α}{ρ} ℰ)
    × (Σ[ n ∈ ℕ ] HasJonssonTerms n {α = α}{ρ} ℰ → CongruenceDistributiveVariety ℓ₀)

  -- Day's theorem (DEFERRED): CM ⇔ existence of Day terms.
  Day-Statement : (ℓ₀ : Level) → Type _
  Day-Statement ℓ₀ =
      (CongruenceModularVariety ℓ₀ → Σ[ n ∈ ℕ ] HasDayTerms n {α = α}{ρ} ℰ)
    × (Σ[ n ∈ ℕ ] HasDayTerms n {α = α}{ρ = ρ} ℰ → CongruenceModularVariety ℓ₀)
```

--------------------------------------

{% include UALib.Links.md %}
