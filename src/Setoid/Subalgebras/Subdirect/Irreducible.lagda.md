---
layout: default
file: "src/Setoid/Subalgebras/Subdirect/Irreducible.lagda.md"
title: "Setoid.Subalgebras.Subdirect.Irreducible module (The Agda Universal Algebra Library)"
date: "2026-06-22"
author: "the agda-algebras development team"
---

### The structural characterization of subdirect irreducibility

This is the [Setoid.Subalgebras.Subdirect.Irreducible][] module of the
[Agda Universal Algebra Library][].

[Setoid.Congruences.Monolith][] *defines* subdirect irreducibility order-theoretically:
`IsSubdirectlyIrreducible 𝑨`{.AgdaFunction} is `Nontrivial 𝑨`{.AgdaFunction} together
with the existence of a **monolith** (a least nonzero congruence).  What makes the name
apt is the **structural** characterization: `𝑨` is subdirectly irreducible iff it
has no *nontrivial subdirect decomposition* — in every subdirect embedding
`𝑨 ↪ ⨅ 𝒜`, some coordinate projection `projᵢ ∘ h` is an isomorphism.[^1]

This module ties [Setoid.Congruences.Monolith][] to
[Setoid.Subalgebras.Subdirect.Basic][], proving the constructive direction in full
and recording the converse's cost.

The clean constructive route goes through the **kernels**.  A subdirect embedding
`h : 𝑨 ↪ ⨅ 𝒜` is the same data as a *separating family* of congruences `θ` (with
`θ i` the kernel of the `i`-th coordinate map and `⋂ θ ≑ 0ᴬ` ⟺ `h` injective); the
coordinate maps are already surjective, so "`projᵢ ∘ h` is an isomorphism" ⟺ "the
`i`-th coordinate map is injective" ⟺ "`θ i ≑ 0ᴬ`".  Each of these equivalences is in
fact a *definitional* identity here, so the embedding-level statement reduces to a
congruence-lattice statement about separating families, where the monolith argument
(`monolith⇒cmi`{.AgdaFunction} of [Setoid.Congruences.Monolith][]) applies.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Subdirect.Irreducible {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( ¬∀⟶∃¬ )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( _,_ ; ∃-syntax ; proj₁ ; proj₂ )
open import Function                               using ( id )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary                       using ( ¬_ ; Dec )
open import Relation.Nullary.Decidable             using ( ¬? ; decidable-stable )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Functions                       using  ( IsInjective ; IsSurjective )
open import Setoid.Algebras              {𝑆 = 𝑆}   using  ( Algebra ; ⨅ )
open import Setoid.Congruences           {𝑆 = 𝑆}   using  ( Con )
open import Setoid.Homomorphisms         {𝑆 = 𝑆}   using  ( hom ; kercon ; _≅_ ; Bijective→≅ )
open import Setoid.Congruences.Monolith  {𝑆 = 𝑆}   using  ( HasMonolith ; Nonzero ; BelowDiagonal
                                                          ; IsSubdirectlyIrreducible
                                                          ; mono-nonzero ; mono-least ; ⋂ )
open import Setoid.Subalgebras.Subdirect.Basic {𝑆 = 𝑆}
  using  ( coord ; SubdirectEmbedding ; Separates ; embed-inj ; proj-onto )

private variable α ρ αᵃ ι : Level
```
-->

#### The kernel family of a homomorphism into a product

Fix an algebra `𝑨`, a factor family `𝒜` whose relation level matches that of `𝑨` (so
the kernels are `Con 𝑨 ρ`), and a homomorphism `h : 𝑨 → ⨅ 𝒜`.  The `i`-th **kernel** of
`h` is the kernel congruence of the `i`-th coordinate map `coord 𝒜 h i = projᵢ ∘ h`.

```agda
module _ {I : Type ι}{𝑨 : Algebra α ρ}(𝒜 : I → Algebra αᵃ ρ)(h : hom 𝑨 (⨅ 𝒜)) where

  -- The kernel of the i-th coordinate map: the congruence on 𝑨 whose quotient is the
  -- image of 𝑨 under projᵢ ∘ h.
  kerfam : I → Con 𝑨 ρ
  kerfam i = kercon (coord 𝒜 h i)
```

The first two bridges are *definitional identities*, recorded as `id` (the
injectivity-is-separation pattern of [Setoid.Subalgebras.Subdirect.Basic][]).  A
coordinate map is injective exactly when its kernel is below the diagonal — both
unfold to `coordᵢ a ≈ coordᵢ b → a ≈ b`, since `BelowDiagonal (kercon g)` *is*
`IsInjective g`.

```agda
  coord-inj→below : {i : I} → IsInjective (proj₁ (coord 𝒜 h i)) → BelowDiagonal 𝑨 (kerfam i)
  coord-inj→below = id

  below→coord-inj : {i : I} → BelowDiagonal 𝑨 (kerfam i) → IsInjective (proj₁ (coord 𝒜 h i))
  below→coord-inj = id

  injective↔0kernel : {i : I} → IsInjective (proj₁ (coord 𝒜 h i)) ≡ BelowDiagonal 𝑨 (kerfam i)
  injective↔0kernel = refl

  injective⇔0kernel : (λ {i : I} → IsInjective (proj₁ (coord 𝒜 h i))) ≡ (λ {i : I} → BelowDiagonal 𝑨 (kerfam i))
  injective⇔0kernel = refl
```

Likewise, the injectivity of `h` itself is *definitionally* the assertion that the
kernel family separates points: equality in `⨅ 𝒜` is pointwise, so `h a ≈ h b` unfolds
to `∀ i, coordᵢ a ≈ coordᵢ b`, exactly the meet of the kernels.

```agda
  embed→separates : IsInjective (proj₁ h) → Separates kerfam
  embed→separates = id

  separates→embed : Separates kerfam → IsInjective (proj₁ h)
  separates→embed = id

  embed↔separates : IsInjective (proj₁ h) ≡ Separates kerfam
  embed↔separates = refl

```

The third bridge is the only one with content: a coordinate map that is surjective
and injective is an isomorphism `𝑨 ≅ 𝒜 i`, via the generic `Bijective→≅`{.AgdaFunction} of
[Setoid.Homomorphisms.Isomorphisms][].

```agda
  coord-iso : {i : I}
    → IsInjective (proj₁ (coord 𝒜 h i)) → IsSurjective (proj₁ (coord 𝒜 h i)) → 𝑨 ≅ 𝒜 i
  coord-iso = Bijective→≅ (coord 𝒜 h _)
```

#### The congruence-lattice forward direction

Now the monolith argument, stated at the family level.  If `𝑨` has a monolith `μ` and a
family `θ` of congruences **separates points**, then the members cannot *all* be
nonzero: `μ` would lie below every `θ i`, hence below their meet, hence (by separation)
below the diagonal — contradicting that `μ` is nonzero.  This is the constructively
honest, contrapositive reading of "`0ᴬ` is completely meet-irreducible".

```agda
module _ {𝑨 : Algebra α ρ} where

  monolith⇒¬all-nonzero :  HasMonolith 𝑨 → {I : Type ι}(θ : I → Con 𝑨 ρ)
                        →  Separates θ → ¬ (∀ i → Nonzero 𝑨 (θ i))
  monolith⇒¬all-nonzero (μ , mono) θ sep all-nz = mono-nonzero mono μ-below
    where
    -- μ lies below every θ i (the monolith is the least nonzero congruence), hence the
    -- separation hypothesis forces μ below the diagonal.
    μ-below : BelowDiagonal 𝑨 μ
    μ-below p = sep (λ i → mono-least mono (θ i) (all-nz i) p)
```

This is `monolith⇒cmi`{.AgdaFunction} (of [Setoid.Congruences.Monolith][]) read on the
separation predicate.  Indeed, for a `ρ`-small index, separation is *definitionally* the
assertion that the meet `⋂ θ` is below the diagonal — the exact hypothesis of complete
meet-irreducibility — so the two coincide.  The direct proof above additionally removes
the `ρ`-small-index restriction that `⋂`{.AgdaFunction} imposes (it is needed below for a
`Fin n`-indexed decomposition).

```agda
  separates≡below-meet : {I : Type ρ}(θ : I → Con 𝑨 ρ) → Separates θ ≡ BelowDiagonal 𝑨 (⋂ 𝑨 θ)
  separates≡below-meet θ = refl
```

#### No nontrivial subdirect decomposition

`𝑨` **is isomorphic to one of the factors** `𝒜` of a subdirect decomposition when some
coordinate map is an isomorphism.  "`𝑨` has no nontrivial subdirect decomposition" means
that *every* subdirect embedding of `𝑨` has such a coordinate.

```agda
IsoToFactor : {I : Type ι}(𝑨 : Algebra α ρ)(𝒜 : I → Algebra αᵃ ρ) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ αᵃ ⊔ ρ ⊔ ι)
IsoToFactor 𝑨 𝒜 = ∃[ i ] (𝑨 ≅ 𝒜 i)
```

Fix a subdirectly irreducible algebra `𝑨` and a subdirect embedding `𝑨 ↪ ⨅ 𝒜`.  Its
kernel family separates points (the embedding's injectivity *is* separation), so by the
forward direction the coordinates cannot all be proper quotients.

```agda
module _ {I : Type ι}{𝑨 : Algebra α ρ}{𝒜 : I → Algebra αᵃ ρ}
         (si : IsSubdirectlyIrreducible 𝑨)(sub : SubdirectEmbedding {𝑩 = 𝑨} 𝒜) where
  private
    h    = proj₁ sub
    emb  = proj₂ sub

  -- The kernel family of a subdirect embedding separates points.
  sub-separates : Separates (kerfam 𝒜 h)
  sub-separates = embed→separates 𝒜 h (embed-inj emb)

  -- Constructive structural irreducibility (contrapositive): in a subdirect embedding
  -- of a subdirectly irreducible algebra, the coordinates cannot all be proper
  -- quotients.
  si⇒¬all-proper : ¬ (∀ i → Nonzero 𝑨 (kerfam 𝒜 h i))
  si⇒¬all-proper = monolith⇒¬all-nonzero (proj₂ si) (kerfam 𝒜 h) sub-separates

  -- Equivalently, it is impossible that *no* coordinate is an isomorphism.  (The
  -- positive form "some coordinate is an isomorphism" needs to extract a witness from a
  -- negated statement, so it is available constructively only for a finite/decidable
  -- index — see `si⇒iso-coord` below.)
  si⇒¬no-iso-coord : ¬ (∀ i → ¬ (𝑨 ≅ 𝒜 i))
  si⇒¬no-iso-coord no-iso =
    si⇒¬all-proper (λ i 0ker → no-iso i (coord-iso 𝒜 h (below→coord-inj 𝒜 h 0ker) (proj-onto emb i)))
```

#### The finite witness: an explicit isomorphic coordinate

For a **finite** index `Fin n`, with a decision for each coordinate of "is this kernel
the diagonal?" (equivalently, "is this coordinate map injective?"), the contrapositive
yields an *explicit* isomorphic coordinate: `𝑨` is isomorphic to one of its subdirect
factors.  This is the witness-extracting form of the characterization, in the spirit of
the finite Birkhoff theorem of [Setoid.Subalgebras.Subdirect.Finite][] (#419); the
decision data is exactly what a `FiniteAlgebra`{.AgdaRecord} supplies (decidable `≈`
and a finite carrier make `BelowDiagonal`, a `Π` over carrier pairs, decidable).

```agda
module _ {n : ℕ}{𝑨 : Algebra α ρ}{𝒜 : Fin n → Algebra αᵃ ρ}
         (si : IsSubdirectlyIrreducible 𝑨)(sub : SubdirectEmbedding {𝑩 = 𝑨} 𝒜)
         (dec : (i : Fin n) → Dec (BelowDiagonal 𝑨 (kerfam 𝒜 (proj₁ sub) i))) where
  private
    h    = proj₁ sub
    emb  = proj₂ sub

  si⇒iso-coord : IsoToFactor 𝑨 𝒜
  si⇒iso-coord = i , coord-iso 𝒜 h (below→coord-inj 𝒜 h below) (proj-onto emb i)
    where
    -- the kernel family is not all-nonzero (the contrapositive forward direction)
    ¬all-nz : ¬ (∀ i → Nonzero 𝑨 (kerfam 𝒜 h i))
    ¬all-nz = monolith⇒¬all-nonzero (proj₂ si) (kerfam 𝒜 h) (embed→separates 𝒜 h (embed-inj emb))

    -- finite + decidable ⟹ some coordinate's kernel is (¬¬, hence) below the diagonal
    ex : ∃[ i ] (¬ Nonzero 𝑨 (kerfam 𝒜 h i))
    ex = ¬∀⟶∃¬ n (λ i → Nonzero 𝑨 (kerfam 𝒜 h i)) (λ i → ¬? (dec i)) ¬all-nz

    i : Fin n
    i = proj₁ ex

    below : BelowDiagonal 𝑨 (kerfam 𝒜 h i)
    below = decidable-stable (dec i) (proj₂ ex)
```

#### The converse bridge, and the converse's cost

The *converse* of the family-level forward direction needs no monolith and is
choice-free: if some coordinate map is injective — an isomorphism, given surjectivity —
then the kernel family is not all-nonzero.  So at the family level "some `θ i ≑ 0ᴬ`" and
"not all `θ i` nonzero" coincide; together with the forward direction, the subdirect
decompositions of an SI algebra are exactly those with an isomorphic coordinate.

```agda
module _ {I : Type ι}{𝑨 : Algebra α ρ}{𝒜 : I → Algebra αᵃ ρ}(h : hom 𝑨 (⨅ 𝒜)) where

  iso-coord⟹¬all-proper :  (∃[ i ] IsInjective (proj₁ (coord 𝒜 h i)))
                        →  ¬ (∀ i → Nonzero 𝑨 (kerfam 𝒜 h i))
  iso-coord⟹¬all-proper (i , inj) all-nz = all-nz i (coord-inj→below 𝒜 h inj)
```

The full converse **structural ⟹ monolith** is *not* added, for the same predicativity
reason recorded in the [M6-2 design note][].  The natural construction takes
`μ = ⋀ {θ : θ nonzero}`, the meet of *all* nonzero congruences: if `0ᴬ` is completely
meet-irreducible then this family (whose every member is nonzero, so it has no zero
member) cannot separate, so `μ` is nonzero; and `μ` is below every nonzero congruence,
hence a monolith.  But that family is indexed by `Σ[ θ ∈ Con 𝑨 ρ ] Nonzero θ`, which
lives one universe up, so the resulting meet is a `Con 𝑨 ℓ′` with `ℓ′ > ρ` — not a
monolith *at level `ρ`*, the level `IsMonolith`{.AgdaRecord} fixes.  Restricting to a
finite, complete list of congruences does not escape the wall either: the complete
congruence enumerations available constructively (the `cons`{.AgdaField} field of
`FiniteCongruences`{.AgdaRecord} in [Setoid.Congruences.Finite][], #419) live at the
absorbing level `clv α ρ ⊒ ρ`, so the
finite meet is again above `ρ`.  Stating the converse cleanly would need an impredicative
(or universe-resized) meet, or a level-generic `IsMonolith`; we record it here as a known
limitation, as the forward direction is the one consumed downstream.

--------------------------------------

[^1]: See e.g. Burris and Sankappanavar, *A Course in Universal Algebra*, Def. II.8.3 / Thm. II.8.4.

[M6-2 design note]: https://github.com/ualib/agda-algebras/blob/master/docs/notes/m6-2-subdirect.md
