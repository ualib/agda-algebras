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
open import Setoid.Congruences.Permutability  using  ( Permutes
                                                     ; CongruencePermutable )
open import Setoid.Congruences.Properties     using  ( CongruenceDistributive
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
characterization, in its concrete "term ⟹ permutable" direction.  Read for the whole
variety — every model of a theory with a Maltsev term is congruence-permutable — it is
`maltsev⇒CP` in the final section.

#### Distributivity and modularity of the congruence lattice

CD and CM are properties of the congruence *lattice*, defined in
[Setoid.Congruences.Properties][] as `CongruenceDistributive` and
`CongruenceModular` (at the absorbing relation level, so that meet and join are
operations on a single type).  They are re-exported here (the `public` on the import
above) so the Maltsev conditions of this module — permutability, and the Jónsson/Day
conditions below — read from one place.

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

HasDayTerms : (n : ℕ){α ρ χ ι : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
HasDayTerms n {α}{ρ} ℰ = Th-Day n ≼ ℰ  where open Interpret α ρ
```

#### The conditions as properties of a variety, and the deferred theorems

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.  A
*congruence-permutable variety* is one all of whose models are
congruence-permutable, and similarly for CD and CM.  The forward Maltsev theorem,
restated for the whole variety, is `maltsev⇒CP`.  The other theorems — the converse of
Maltsev, and the Jónsson and Day characterizations — are stated here as the goals that
remain (their constructions are sketched in the design note); each is a `Type`.  The
converse of Maltsev, `CP⇒maltsev-Statement`, is now *inhabited* by `CP⇒maltsev` in
[Setoid.Varieties.MaltsevConverse][] (M6-5, via the bridge of
[Setoid.Varieties.FreeBridge][], M6-4); the Jónsson and Day statements remain open.

```agda
module _ {χ ι : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X)(α ρ ℓ : Level) where

  -- "Every model is congruence-permutable / -distributive / -modular."
  CongruencePermutableVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruencePermutableVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruencePermutable 𝑩 ℓ

  CongruenceDistributiveVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceDistributiveVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceDistributive 𝑩 ℓ

  CongruenceModularVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceModularVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceModular 𝑩 ℓ

  -- Maltsev's theorem, forward direction, as a statement about the variety (PROVED).
  maltsev⇒CP : HasMaltsevTerm ℰ → CongruencePermutableVariety
  maltsev⇒CP mt 𝑩 B⊨ = MaltsevTerm⇒CP ℰ mt 𝑩 B⊨

  -- The converse: a congruence-permutable variety has a Maltsev term.  Inhabited by
  -- `CP⇒maltsev` in Setoid.Varieties.MaltsevConverse (M6-5).
  CP⇒maltsev-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CP⇒maltsev-Statement = CongruencePermutableVariety → HasMaltsevTerm {α = α}{ρ} ℰ

  -- Jónsson's theorem (DEFERRED): CD ⇔ existence of Jónsson terms.
  Jonsson-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Jonsson-Statement =
      (CongruenceDistributiveVariety → Σ[ n ∈ ℕ ] HasJonssonTerms n {α = α}{ρ} ℰ)
    × (Σ[ n ∈ ℕ ] HasJonssonTerms n {α = α}{ρ} ℰ → CongruenceDistributiveVariety)

  -- Day's theorem (DEFERRED): CM ⇔ existence of Day terms.
  Day-Statement : Type _
  Day-Statement =
      (CongruenceModularVariety → Σ[ n ∈ ℕ ] HasDayTerms n {α = α}{ρ} ℰ)
    × (Σ[ n ∈ ℕ ] HasDayTerms n {α = α}{ρ} ℰ → CongruenceModularVariety)
```

--------------------------------------

[^1]: See the design note `docs/notes/m6-3-maltsev-conditions.md` for the construction plans.

[^day]: A. Day, *A characterization of modularity for congruence lattices of algebras*, Canad. Math. Bull. **12** (1969), 167–173.  [doi:10.4153/CMB-1969-016-6](https://doi.org/10.4153/CMB-1969-016-6).

[^jonsson]: B. Jónsson, *Algebras whose congruence lattices are distributive*, Math. Scand. **21** (1967), 110–121.  [doi:10.7146/math.scand.a-10850](https://doi.org/10.7146/math.scand.a-10850) (open access; mirror at [EUDML](https://eudml.org/doc/166010)).

[^maltsev]: A. I. Mal'cev, *On the general theory of algebraic systems* (Russian), Mat. Sb. (N.S.) **35(77)** (1954), 3–20; Engl. transl., *Amer. Math. Soc. Transl.* (2) **27** (1963), 125–142.  Original at [Math-Net.Ru](http://www.mathnet.ru/sm5264); translation in [*Eighteen Papers on Algebra* (AMS)](https://pubs.ams.org/ebooks/trans2/027/).


{% include UALib.Links.md %}
