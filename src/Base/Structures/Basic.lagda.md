---
layout: default
title : "Base.Structures.Basic module (Agda Universal Algebra Library)"
date : "2021-05-20"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic Definitions</a>

This is the [Base.Structures.Basic][] module of the [Agda Universal Algebra Library][]. It is a submodule of the Structures module which presents general (relational-algebraic) structures as inhabitants of record types.  For a similar development using Sigma types see the Base.Structures.Sigma.Basic module.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Basic  where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Agda.Primitive        using () renaming ( Set to Type )
open import Function.Base         using ( flip ; _∘_ )
open import Level                 using ( _⊔_ ; suc ; Level )
open import Relation.Binary.Core  using () renaming ( Rel to BinRel )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Overture              using ( Op )
open import Base.Relations        using ( _|:_ ; _preserves_ ; Rel )

private variable 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level

-- Signature as a record type
record signature (𝓞 𝓥 : Level) : Type (suc (𝓞 ⊔ 𝓥)) where
 field
  symbol : Type 𝓞
  arity : symbol → Type 𝓥

siglˡ : {𝓞 𝓥 : Level} → signature 𝓞 𝓥 → Level
siglˡ {𝓞}{𝓥} _ = 𝓞

siglʳ : {𝓞 𝓥 : Level} → signature 𝓞 𝓥 → Level
siglʳ {𝓞}{𝓥} _ = 𝓥

sigl : {𝓞 𝓥 : Level} → signature 𝓞 𝓥 → Level
sigl {𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥

open signature public

record structure  (𝐹 : signature 𝓞₀ 𝓥₀)
                  (𝑅 : signature 𝓞₁ 𝓥₁)
                  {α ρ : Level} : Type (𝓞₀ ⊔ 𝓥₀ ⊔ 𝓞₁ ⊔ 𝓥₁ ⊔ (suc (α ⊔ ρ)))
 where
 field
  carrier : Type α
  op   : ∀(f : symbol 𝐹) → Op  carrier (arity 𝐹 f)      -- interpret. of operations
  rel  : ∀(r : symbol 𝑅) → Rel carrier (arity 𝑅 r) {ρ}  -- interpret. of relations

 -- Forgetful Functor
 𝕌 : Type α
 𝕌 = carrier

open structure public

module _ {𝐹 : signature 𝓞₀ 𝓥₀}{𝑅 : signature 𝓞₁ 𝓥₁} where
 -- Syntactic sugar for interpretation of operation
 _ʳ_ :  ∀{α ρ} → (r : symbol 𝑅)(𝒜 : structure 𝐹 𝑅 {α}{ρ})
  →     Rel (carrier 𝒜) ((arity 𝑅) r) {ρ}
 _ʳ_ = flip rel

 _ᵒ_ :  ∀{α ρ} → (f : symbol 𝐹)(𝒜 : structure 𝐹 𝑅 {α}{ρ})
  →     Op (carrier 𝒜)((arity 𝐹) f)
 _ᵒ_ = flip op

 compatible :  ∀{α ρ ℓ} → (𝑨 : structure 𝐹 𝑅 {α}{ρ})
  →            BinRel (carrier 𝑨) ℓ → Type _
 compatible 𝑨 r = ∀ (f : symbol 𝐹) → (f ᵒ 𝑨) |: r

 open Level

 -- lift an operation to act on type of higher universe level
 Lift-op :  ∀{ι α} → {I : Type ι}{A : Type α}
  →         Op A I → {ℓ : Level} → Op (Lift ℓ A) I

 Lift-op f = λ z → lift (f (lower ∘ z))

 -- lift a relation to a predicate on type of higher universe level
 -- (note ρ doesn't change; see Lift-Structʳ for that)
 Lift-rel :  ∀{ι α ρ} → {I : Type ι}{A : Type α}
  →          Rel A I {ρ} → {ℓ : Level} → Rel (Lift ℓ A) I{ρ}

 Lift-rel r x = r (lower ∘ x)

 -- lift the domain of a structure to live in a type at a higher universe level
 Lift-Strucˡ :  ∀{α ρ} → (ℓ : Level)
  →             structure 𝐹 𝑅 {α}{ρ} → structure 𝐹 𝑅  {α ⊔ ℓ}{ρ}

 Lift-Strucˡ ℓ 𝑨 = record  { carrier = Lift ℓ (carrier 𝑨)
                           ; op = λ f → Lift-op (f ᵒ 𝑨)
                           ; rel = λ R → Lift-rel (R ʳ 𝑨)
                           }

 -- lift the relations of a structure from level ρ to level ρ ⊔ ℓ
 Lift-Strucʳ :  ∀{α ρ} → (ℓ : Level)
  →             structure 𝐹 𝑅 {α}{ρ} → structure 𝐹 𝑅 {α}{ρ ⊔ ℓ}

 Lift-Strucʳ ℓ 𝑨 = record { carrier = carrier 𝑨 ; op = op 𝑨 ; rel = lrel }
  where
  lrel : (r : symbol 𝑅) → Rel (carrier 𝑨) ((arity 𝑅) r)
  lrel r = Lift ℓ ∘ r ʳ 𝑨

 -- lift both domain of structure and the level of its relations
 Lift-Struc :  ∀{α ρ} → (ℓˡ ℓʳ : Level)
  →            structure 𝐹 𝑅 {α}{ρ} → structure 𝐹 𝑅 {α ⊔ ℓˡ}{ρ ⊔ ℓʳ}

 Lift-Struc ℓˡ ℓʳ 𝑨 = Lift-Strucʳ ℓʳ (Lift-Strucˡ ℓˡ 𝑨)
```


--------------------------------

<span style="float:left;">[↑ Base.Structures](Base.Structures.html)</span>
<span style="float:right;">[Base.Structures.Graphs →](Base.Structures.Graphs.html)</span>

{% include UALib.Links.md %}
