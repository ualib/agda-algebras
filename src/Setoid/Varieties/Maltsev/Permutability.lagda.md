---
layout: default
file: "src/Setoid/Varieties/Maltsev/Permutability.lagda.md"
title: "Setoid.Varieties.Maltsev.Permutability module (The Agda Universal Algebra Library)"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Maltsev conditions: permutability

This is the [Setoid.Varieties.Maltsev.Permutability][] module of the [Agda Universal Algebra Library][].

[Setoid.Varieties.Maltsev.Basic][] fixed the *term-existence* side of CP as a theory
interpretation: `HasMaltsevTerm ℰ = Th-Maltsev ≼ ℰ`.[^1]

The present module connects that to the *lattice* side (built in
[Setoid.Congruences.Permutability][]) and proves the concrete direction of
**Maltsev's theorem**:[^maltsev]

>  a variety with a Maltsev term is congruence-permutable.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev.Permutability where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Fin.Base      using  ( Fin )
open import Data.Fin.Patterns  using  ( 0F ; 1F ; 2F )
open import Data.Product       using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level              using  ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary    using  ( Setoid ; IsEquivalence )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures                using  ( Signature )
open import Overture.Terms                     using  ( Term ; ℊ )
open import Overture.Terms.Interpretation      using  ( Interpretation ; _✦_ )
open import Setoid.Algebras.Basic              using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic           using  ( Con ; reflexive ; is-equivalence )
open import Setoid.Congruences.Generation      using  ( Cg ; base ; module principal )
open import Setoid.Congruences.Permutability   using  ( CongruencePermutable )
open import Setoid.Terms.Basic                 using  ( Sub ; _[_] ; module Environment )
open import Setoid.Terms.Interpretation        using  ( graft≐[] )
open import Setoid.Varieties.EquationalLogic   using  ( _⊧_≈_ )
open import Setoid.Varieties.FreeSubstitution  using  ( ≐→⊢ ; cg-pair→⊢ )
open import Setoid.Varieties.Interpretation    using  ( reductᴵ ; _⊨ₑ_ ; ⊧-interp )
open import Setoid.Varieties.Maltsev.Basic     using  ( Sig-Maltsev ; m-Op ; m ; tri
                                                      ; mxxy≈y ; mxyy≈x ; Th-Maltsev
                                                      ; HasMaltsevTerm ; term-compatible )
open import Setoid.Varieties.SoundAndComplete  using  ( Eq ; toEq ; _⊢_▹_≈_
                                                      ; module FreeAlgebra
                                                      ; module Soundness )

-- the generators of the Maltsev signature (the source signature of the interpretation)
open import Overture.Terms.Basic {𝑆 = Sig-Maltsev} using () renaming ( ℊ to ℊᴹ )

open import Function using ( Func )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )
open _⊢_▹_≈_ using ( refl ; sym ; trans )

private variable α ρ χ ι ℓ : Level
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
the free-algebra congruence/derivability bridge `cg-pair→⊢`{.AgdaFunction}
([Setoid.Varieties.FreeSubstitution][]).

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

    open principal 𝔽[ Fin 3 ]
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

---

[^1]: The design choice — encoding each condition as `Th-X ≼ ℰ` rather than as a record bundling a term with its identities, or an inductive scheme of identities — is discussed in the design note `docs/notes/m6-3-maltsev-conditions.md`; in short, the interpretation encoding *is* the "term plus its identities", packaged so that the whole interpretability apparatus ([Setoid.Varieties.Interpretation][]) applies uniformly to every condition.

[^maltsev]: A. I. Mal'cev, *On the general theory of algebraic systems* (Russian), Mat. Sb. (N.S.) **35(77)** (1954), 3–20; Engl. transl., *Amer. Math. Soc. Transl.* (2) **27** (1963), 125–142.  Original at [Math-Net.Ru](http://www.mathnet.ru/sm5264); translation in [*Eighteen Papers on Algebra* (AMS)](https://pubs.ams.org/ebooks/trans2/027/).

[^maltsev2]: A. I. Mal'cev, *On the general theory of algebraic systems* (Russian), Mat. Sb. (N.S.) **35(77)** (1954), 3–20; Burris and Sankappanavar, *A Course in Universal Algebra*, Thm. II.12.2.
