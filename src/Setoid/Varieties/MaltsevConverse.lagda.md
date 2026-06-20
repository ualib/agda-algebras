---
layout: default
file: "src/Setoid/Varieties/MaltsevConverse.lagda.md"
title: "Setoid.Varieties.MaltsevConverse module"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### The converse of Maltsev's theorem

This is the [Setoid.Varieties.MaltsevConverse][] module of the [Agda Universal Algebra Library][].

[Setoid.Varieties.MaltsevConditions][] proved the *forward* direction of Maltsev's
theorem (`maltsev⇒CP`{.AgdaFunction}: a variety with a Maltsev term is
congruence-permutable) and stated the converse as a checked, uninhabited `Type`,
`CP⇒maltsev-Statement`{.AgdaFunction}.  This module *inhabits* that statement, completing
the characterization: a congruence-permutable variety has a Maltsev term.[^maltsev]

The construction is the classical one (Burris–Sankappanavar, Thm. II.12.2), run through
the free-algebra congruence/derivability bridge of [Setoid.Varieties.FreeBridge][].

+  Work in `𝔽[ Fin 3 ]`{.AgdaFunction}, the relatively free algebra on three generators
   `x , y , z`.  It is a model of the theory (`satisfies`{.AgdaFunction}), hence
   congruence-permutable by hypothesis.

+  Take the principal congruences `θ = Cg ❴ x , y ❵`{.AgdaFunction} and
   `φ = Cg ❴ y , z ❵`{.AgdaFunction}.  Then `x θ y` and `y φ z`, so `(x , z) ∈ θ ∘ φ`;
   permutability gives `(x , z) ∈ φ ∘ θ`, i.e. a witness term `w` with `x φ w` and
   `w θ z`.  Since the carrier of `𝔽` *is* `Term (Fin 3)`, this `w` is literally the
   Maltsev term `M(x , y , z)`.

+  Translate the two memberships through collapsing-substitution homomorphisms (the
   bridge `cg-pair→⊢`{.AgdaFunction}).  Collapsing `z ↦ y` turns `x φ w` into the
   derivable equation `M(x , y , y) ≈ x`; collapsing `y ↦ x` turns `w θ z` into
   `M(x , x , y) ≈ y` — the two Maltsev identities.

+  Package `M` as the interpretation `I : Th-Maltsev ≼ ℰ` and discharge the satisfaction
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

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.MaltsevConverse where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive     using () renaming ( Set to Type )
open import Data.Fin.Base      using ( Fin )
open import Data.Fin.Patterns  using ( 0F ; 1F ; 2F )
open import Data.Product       using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level              using ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using  ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Terms.Basic           using  ( Term ; ℊ )
open import Overture.Terms.Interpretation  using  ( Interpretation ; _✦_ )
open import Setoid.Algebras.Basic          using  ( Algebra ; 𝕌[_] )
open import Setoid.Terms.Basic             using  ( Sub ; _[_] )
open import Setoid.Congruences.Basic       using  ( Con )
open import Setoid.Congruences.Generation  using  ( Cg ; base )
open import Setoid.Congruences.Permutability using ( CongruencePermutable )
open import Setoid.Varieties.SoundAndComplete
  using  ( Eq ; _⊢_▹_≈_ ; module FreeAlgebra ; module Soundness )
open import Setoid.Varieties.FreeSubstitution using ( ≐→⊢ )
open import Setoid.Varieties.Interpretation   using ( reductᴵ ; ⊧-interp ; _⊨ₑ_ )
open import Setoid.Varieties.FreeBridge
  using  ( graft≐[] ; ❴_,_❵ ; pᵣ ; cg-pair→⊢ ; toEq ; ⊨ₑ⇒⊨ ; ⊨⇒⊨ₑ )
open import Setoid.Varieties.Maltsev
  using  ( Sig-Maltsev ; m-Op ; tri ; mxxy≈y ; mxyy≈x ; Th-Maltsev )
open import Setoid.Varieties.MaltsevConditions
  using  ( CP⇒maltsev-Statement ; CongruencePermutableVariety )

-- the generators of the Maltsev signature (the source signature of the interpretation)
open import Overture.Terms.Basic {𝑆 = Sig-Maltsev} using () renaming ( ℊ to ℊᴹ )

open _⊢_▹_≈_ using ( refl ; sym ; trans )
```

#### The theorem

Fix a theory `ℰ` over a signature `𝑆 : Signature 0ℓ 0ℓ`, with variables `X : Type 0ℓ`.
We inhabit `CP⇒maltsev-Statement`{.AgdaFunction} at the levels of the free algebra
`𝔽[ Fin 3 ] : Algebra (ov 0ℓ) (ι ⊔ ov 0ℓ)` (here `ov 0ℓ = lsuc 0ℓ`, since
`𝓞 = 𝓥 = 0ℓ`), and at the congruence level `ι ⊔ ov 0ℓ` at which its principal
congruences live.

```agda
module _ {ι : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type 0ℓ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  CP⇒maltsev : CP⇒maltsev-Statement ℰ (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)
  CP⇒maltsev cpv = I , red
    where
    -- the theory in the `I → Eq` shape that the free algebra consumes
    E : Idx → Eq {χ = 0ℓ}
    E = toEq ℰ

    open FreeAlgebra E using ( 𝔽[_] ; satisfies )

    -- the relatively free algebra on three generators, and its three generators
    𝔽 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)
    𝔽 = 𝔽[ Fin 3 ]

    x y z : 𝕌[ 𝔽 ]
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F

    -- 𝔽 is a model, hence congruence-permutable by hypothesis
    𝔽cp : CongruencePermutable 𝔽 (ι ⊔ lsuc 0ℓ)
    𝔽cp = cpv 𝔽 (⊨⇒⊨ₑ 𝔽 ℰ satisfies)

    -- the two principal congruences
    θ φ : Con 𝔽 (ι ⊔ lsuc 0ℓ)
    θ = Cg (❴_,_❵ {𝑨 = 𝔽} x y)
    φ = Cg (❴_,_❵ {𝑨 = 𝔽} y z)

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
    bridge-xxy : E ⊢ Fin 3 ▹ (w [ σxxy ]) ≈ (z [ σxxy ])
    bridge-xxy = cg-pair→⊢ E σxxy x y refl wθz

    bridge-xyy : E ⊢ Fin 3 ▹ (x [ σxyy ]) ≈ (w [ σxyy ])
    bridge-xyy = cg-pair→⊢ E σxyy y z refl xφw

    -- the two Maltsev identities, as the interpreted equations
    deriv-xxy : E ⊢ Fin 3 ▹ (I ✦ proj₁ (Th-Maltsev mxxy≈y)) ≈ (I ✦ proj₂ (Th-Maltsev mxxy≈y))
    deriv-xxy = trans (≐→⊢ (graft≐[] w σxxy)) bridge-xxy

    deriv-xyy : E ⊢ Fin 3 ▹ (I ✦ proj₁ (Th-Maltsev mxyy≈x)) ≈ (I ✦ proj₂ (Th-Maltsev mxyy≈x))
    deriv-xyy = trans (≐→⊢ (graft≐[] w σxyy)) (sym bridge-xyy)

    -- every model satisfying ℰ satisfies the interpreted Maltsev identities
    red : (𝑩 : Algebra (lsuc 0ℓ) (ι ⊔ lsuc 0ℓ)) → 𝑩 ⊨ₑ ℰ → reductᴵ 𝑩 I ⊨ₑ Th-Maltsev
    red 𝑩 B⊨ mxxy≈y = ⊧-interp 𝑩 I {s = proj₁ (Th-Maltsev mxxy≈y)} {t = proj₂ (Th-Maltsev mxxy≈y)}
                                 (Soundness.sound E 𝑩 (⊨ₑ⇒⊨ 𝑩 ℰ B⊨) deriv-xxy)
    red 𝑩 B⊨ mxyy≈x = ⊧-interp 𝑩 I {s = proj₁ (Th-Maltsev mxyy≈x)} {t = proj₂ (Th-Maltsev mxyy≈x)}
                                 (Soundness.sound E 𝑩 (⊨ₑ⇒⊨ 𝑩 ℰ B⊨) deriv-xyy)
```

--------------------------------------

[^maltsev]: A. I. Mal'cev, *On the general theory of algebraic systems* (Russian), Mat. Sb. (N.S.) **35(77)** (1954), 3–20; Burris and Sankappanavar, *A Course in Universal Algebra*, Thm. II.12.2.

{% include UALib.Links.md %}
