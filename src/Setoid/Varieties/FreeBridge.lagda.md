---
layout: default
file: "src/Setoid/Varieties/FreeBridge.lagda.md"
title: "Setoid.Varieties.FreeBridge module"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### The free-algebra congruence/derivability bridge

This is the [Setoid.Varieties.FreeBridge][] module of the [Agda Universal Algebra Library][].

The *converse* directions of the basic Maltsev conditions (a lattice property of the
congruences of an algebra implies the existence of terms satisfying prescribed
identities) are all proved the same way: read an equational identity off a congruence
of the relatively free algebra `𝔽[ X ]`{.AgdaFunction}
([Setoid.Varieties.SoundAndComplete][]).  This module builds the **reusable bridge**
that those converses need — between the generated congruence `Cg`{.AgdaFunction}
([Setoid.Congruences.Generation][]) on `𝔽[ X ]` and derivability `_⊢_▹_≈_`{.AgdaFunction}
([Setoid.Varieties.SoundAndComplete][]) — so that each converse can consume it rather
than re-deriving it.[^1]

The bridge has four parts.

+  **The substitution-induced homomorphism** `subhom σ : 𝔽[ X ] → 𝔽[ Y ]`{.AgdaFunction}.
   A substitution `σ : X → Term Y` (a map of variables to terms, `Sub Y X`{.AgdaFunction})
   acts on the free algebra by `_[ σ ]`{.AgdaFunction}; this action *is* a homomorphism,
   and the proof is immediate — its action on a node `node f ts` is substitution, which
   commutes with `node` by the very definition of `_[_]`{.AgdaFunction}, so the
   compatibility square holds by `refl`{.AgdaInductiveConstructor}.  Its congruence (it
   respects derivable equality) is the `sub`{.AgdaInductiveConstructor} rule.

+  **The kernel of a homomorphism as a congruence**.  This is `kercon`{.AgdaFunction}
   ([Setoid.Homomorphisms.Kernels][]); we re-export it, since its three congruence
   fields (`reflexive`{.AgdaField}, the equivalence, and compatibility `HomKerComp`)
   are already assembled there.

+  **The bridge lemma** `Cg⊆ker`{.AgdaFunction}: for *any* hom `h` and *any* relation
   `R` contained in the kernel of `h`, the generated congruence `Cg R` is contained in
   the kernel of `h`.  This is immediate from `Cg-least`{.AgdaFunction} (the kernel is a
   congruence above `R`, so it is above the least one).  Specialized to a single
   identified pair and the substitution hom, it says: a principal-congruence membership
   yields a derivable equation — the lemma `cg-pair→⊢`{.AgdaFunction}.

+  **The impedance shim** `toEq`{.AgdaFunction}.  The interpretability relation
   `_≼_`{.AgdaFunction} ([Setoid.Varieties.Interpretation][]) records a theory as an
   `Idx → Term × Term`, while derivability `_⊢_▹_≈_`{.AgdaFunction} and `𝔽[_]`{.AgdaFunction}
   consume an `I → Eq`{.AgdaRecord}; `toEq`{.AgdaFunction} converts the former to the
   latter.  No conversion is needed for *satisfaction* — the two predicates
   `_⊨ₑ_`{.AgdaFunction} and `_⊨_`{.AgdaFunction} coincide definitionally.

A consumer that produces a witness term once via `_✦_`{.AgdaFunction} (whose node clause
is a `graft`{.AgdaFunction}) and once via `_[_]`{.AgdaFunction} lines the two up with
`graft≐[]`{.AgdaFunction}, which lives with the other laws of `graft` in
[Setoid.Terms.Interpretation][].

The first client of this bridge is the converse of Maltsev's theorem
([Setoid.Varieties.Maltsev.Permutability][]); the Jónsson and Day converses are designed to
reuse the same machinery.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.FreeBridge {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; _×_ ; proj₁ ; proj₂ )
open import Function         using ( Func )
open import Level            using ( Level )
open import Relation.Binary  using ()
                             renaming ( Rel to BinRel ; _⇒_ to _⊆_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Terms                {𝑆 = 𝑆}  using ( Term ; ℊ )
open import Setoid.Algebras.Basic         {𝑆 = 𝑆}  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Terms.Basic            {𝑆 = 𝑆}  using ( Sub ; _[_] )
open import Setoid.Congruences.Generation {𝑆 = 𝑆}  using ( Gen ; Cg-least ; base )
open import Setoid.Homomorphisms.Basic    {𝑆 = 𝑆}  using ( hom ; mkIsHom )
open import Setoid.Homomorphisms.Kernels  {𝑆 = 𝑆}  using ( kercon )
open import Setoid.Varieties.SoundAndComplete {𝑆 = 𝑆}
  using ( Eq ; _≈̇_ ; _⊢_▹_≈_ ; module FreeAlgebra )

open Func    using ( cong )
open _⊢_▹_≈_ using ( sub ; refl )

private variable
  α ρ β ρᵇ χ ι ℓ : Level
  X Y : Type χ
```

#### The principal (single-pair) relation

For two carrier elements `a`, `b` of an algebra, `❴ a , b ❵`{.AgdaFunction} is the
relation that relates exactly `a` to `b`.  Its generated congruence `Cg ❴ a , b ❵` is
the *principal* congruence collapsing the one pair.

```agda
module _ {𝑨 : Algebra α ρ} where

  data ❴_,_❵ (a b : 𝕌[ 𝑨 ]) : BinRel 𝕌[ 𝑨 ] α where
    pᵣ : ❴ a , b ❵ a b
```

#### The bridge lemma: a generated congruence sits inside any collapsing kernel

If a relation `R` is contained in the kernel of a homomorphism `h` (i.e. `h` collapses
every `R`-pair), then the congruence `Cg R` it generates is also contained in that
kernel.  This is exactly `Cg-least`{.AgdaFunction} applied to the kernel congruence
`kercon h`{.AgdaFunction}: the kernel is a congruence above `R`, hence above the least
such, `Cg R`.

```agda
module _ {𝑨 : Algebra α ρ}{𝑩 : Algebra β ρᵇ}(h : hom 𝑨 𝑩) where

  Cg⊆ker : {R : BinRel 𝕌[ 𝑨 ] ℓ} → R ⊆ proj₁ (kercon h) → Gen R ⊆ proj₁ (kercon h)
  Cg⊆ker R⊆k = Cg-least (kercon h) R⊆k
```

#### The impedance shim between the two theory shapes

`_≼_`{.AgdaFunction} records a theory as an `Idx → Term × Term`; `_⊢_▹_≈_`{.AgdaFunction}
and `𝔽[_]`{.AgdaFunction} consume an `I → Eq`{.AgdaRecord}.  `toEq`{.AgdaFunction}
bridges the two.  No companion is needed for *satisfaction*: the two predicates
`_⊨ₑ_`{.AgdaFunction} ([Setoid.Varieties.Interpretation][]) and
`_⊨_`{.AgdaFunction} of the converted theory coincide *definitionally* (both unfold to
pointwise equality of the two interpreted terms under all environments), so a proof of
one is directly a proof of the other.

```agda
toEq : {χ ι : Level}{Idx : Type ι}{X : Type χ}
  → (Idx → Term X × Term X) → (Idx → Eq {χ = χ})
toEq ℰ i = proj₁ (ℰ i) ≈̇ proj₂ (ℰ i)
```

#### The substitution-induced homomorphism, and the principal-pair bridge

Fix a theory `E : Idx → Eq`.  A substitution `σ : Sub Y X` (each `X`-variable to a
`Y`-term) induces the homomorphism `subhom σ : 𝔽[ X ] → 𝔽[ Y ]`{.AgdaFunction} whose
underlying map is `_[ σ ]`{.AgdaFunction}.  It respects derivable equality by the
`sub`{.AgdaInductiveConstructor} rule, and the homomorphism square holds by
`refl`{.AgdaInductiveConstructor} because `(node f ts) [ σ ]` is `node f (λ i → ts i [ σ ])`
on the nose.

```agda
module _ {χ ι : Level}{Idx : Type ι}(E : Idx → Eq {χ = χ}) where
  open FreeAlgebra E using ( 𝔽[_] )

  subhom : {X Y : Type χ}(σ : Sub Y X) → hom 𝔽[ X ] 𝔽[ Y ]
  subhom {X = X}{Y = Y} σ = subfunc , mkIsHom (λ {f}{a} → refl)
    where
    subfunc : Func 𝔻[ 𝔽[ X ] ] 𝔻[ 𝔽[ Y ] ]
    subfunc = record { to = _[ σ ] ; cong = λ {p}{q} pq → sub pq σ }
```

The special case of a plain variable renaming `ρ : X → Y` is `subhom (ℊ ∘ ρ)`.

```agda
  renhom : {X Y : Type χ}(r : X → Y) → hom 𝔽[ X ] 𝔽[ Y ]
  renhom r = subhom (λ x → ℊ (r x))
```

Now the principal-pair bridge: given a substitution `σ` that collapses the pair
`(a , b)` — i.e. `E ⊢ Y ▹ a [ σ ] ≈ b [ σ ]` is derivable — every pair `(s , t)` in the
principal congruence `Cg ❴ a , b ❵` becomes derivably equal after `σ`.

```agda
  cg-pair→⊢ : {X Y : Type χ}(σ : Sub Y X)(a b : Term X)
    → E ⊢ Y ▹ (a [ σ ]) ≈ (b [ σ ])
    → {s t : Term X} → Gen {𝑨 = 𝔽[ X ]} (❴_,_❵ {𝑨 = 𝔽[ X ]} a b) s t
    → E ⊢ Y ▹ (s [ σ ]) ≈ (t [ σ ])
  cg-pair→⊢ {X = X}{Y = Y} σ a b coll = Cg⊆ker (subhom {X = X}{Y = Y} σ) incl
    where
    incl : ❴ a , b ❵ ⊆ proj₁ (kercon (subhom σ))
    incl pᵣ = coll
```

#### Smoke test: recovering a derivable identity from a principal congruence

A small end-to-end consumer.  Fix two variables `u`, `v`, a substitution `σ` that
*merges* them (`σ u`, `σ v` are derivably equal), and the principal congruence
`Cg ❴ ℊ u , ℊ v ❵`.  Then every pair in that congruence is recovered as a derivable
equation after `σ`; in particular the generators themselves, and (by symmetry) the
swapped pair.

```agda
module _ {χ ι : Level}{Idx : Type ι}(E : Idx → Eq {χ = χ}){X : Type χ}
         (u v : X)(σ : Sub X X)(merge : E ⊢ X ▹ (σ u) ≈ (σ v)) where
  open FreeAlgebra E using ( 𝔽[_] )

  recover : {s t : Term X} → Gen {𝑨 = 𝔽[ X ]} (❴_,_❵ {𝑨 = 𝔽[ X ]} (ℊ u) (ℊ v)) s t
          → E ⊢ X ▹ (s [ σ ]) ≈ (t [ σ ])
  recover = cg-pair→⊢ E σ (ℊ u) (ℊ v) merge

  recover-gen : E ⊢ X ▹ (σ u) ≈ (σ v)
  recover-gen = recover (base pᵣ)

  recover-swap : E ⊢ X ▹ (σ v) ≈ (σ u)
  recover-swap = recover (Gen.symm (base pᵣ))
```

--------------------------------------

[^1]: See the design note `docs/notes/m6-4-free-bridge.md` and the M6-3 design note
`docs/notes/m6-3-maltsev-conditions.md`, § "The deferred theorems and their
construction plans".
