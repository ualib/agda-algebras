---
layout: default
title : "Base.Algebras.Congruences module (The Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

### <a id="congruence-relations">Congruence Relations</a>

This is the [Base.Algebras.Congruences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( Σ-syntax ; _,_ )
open import Function.Base    using ( _∘_ )
open import Level            using ( Level ; _⊔_ ; suc )
open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from agda-algebras ---------------------------------------------------
open import Overture        using ( ∣_∣ ; ∥_∥ )
open import Base.Relations  using ( _|:_ ; 0[_] ; 0[_]Equivalence ; _/_ ; ⟪_⟫ ; IsBlock )
open import Base.Equality   using ( swelldef )

open import Base.Algebras.Basic     {𝑆 = 𝑆}  using ( Algebra ; compatible ; _̂_ )
open import Base.Algebras.Products  {𝑆 = 𝑆}  using ( ov )

private variable α β ρ : Level

\end{code}

A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation
that is compatible with the basic operations of `𝑨`.  This concept can be
represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of
being a congruence, and we define a Sigma type (`Con`) to represent the type of
congruences of a given algebra.

\begin{code}

record IsCongruence (𝑨 : Algebra α)(θ : BinRel ∣ 𝑨 ∣ ρ) : Type(ov ρ ⊔ α)  where
 constructor mkcon
 field
  is-equivalence : IsEquivalence θ
  is-compatible  : compatible 𝑨 θ

Con : (𝑨 : Algebra α) → Type(α ⊔ ov ρ)
Con {α}{ρ}𝑨 = Σ[ θ ∈ ( BinRel ∣ 𝑨 ∣ ρ ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are
equivalent in the sense that each implies the other. One implication is the
"uncurry" operation and the other is the second projection.

\begin{code}

IsCongruence→Con : {𝑨 : Algebra α}(θ : BinRel ∣ 𝑨 ∣ ρ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α} → ((θ , _) : Con{α}{ρ} 𝑨) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥
\end{code}


#### <a id="example">Example</a>

We now defined the *zero relation* `0[_]` and build the *trivial congruence*,
which has `0[_]` as its underlying relation. Observe that `0[_]` is equivalent to
the identity relation `≡` and is obviously an equivalence relation.

\begin{code}

open Level

-- Example. The zero congruence of a structure.
0[_]Compatible : {α : Level}(𝑨 : Algebra α){ρ : Level} → swelldef 𝓥 α → (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: (0[ ∣ 𝑨 ∣ ]{ρ})
0[ 𝑨 ]Compatible wd 𝑓 {i}{j} ptws0  = lift γ
  where
  γ : (𝑓 ̂ 𝑨) i ≡ (𝑓 ̂ 𝑨) j
  γ = wd (𝑓 ̂ 𝑨) i j (lower ∘ ptws0)

open IsCongruence
0Con[_] : {α : Level}(𝑨 : Algebra α){ρ : Level} → swelldef 𝓥 α → Con{α}{α ⊔ ρ} 𝑨
0Con[ 𝑨 ]{ρ} wd = let  0eq = 0[ ∣ 𝑨 ∣ ]Equivalence{ρ}  in
                       ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ]Compatible wd)
\end{code}

A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.


#### <a id="quotient-algebras">Quotient algebras</a>

In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with
respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient
is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients
using this standard notation.

\begin{code}

_╱_ : (𝑨 : Algebra α) → Con{α}{ρ} 𝑨 → Algebra (α ⊔ suc ρ)
𝑨 ╱ θ =  (∣ 𝑨 ∣ / ∣ θ ∣)  ,                              -- domain of quotient algebra
         λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.blk ∥ 𝑎 i ∥) ⟫  -- ops of quotient algebra

\end{code}

**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity)
  relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as
  follows.

\begin{code}

𝟘[_╱_] : (𝑨 : Algebra α)(θ : Con{α}{ρ} 𝑨) → BinRel (∣ 𝑨 ∣ / ∣ θ ∣)(α ⊔ suc ρ)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ`
function defined above.

\begin{code}

𝟎[_╱_] :  {α : Level}(𝑨 : Algebra α){ρ : Level}(θ : Con {α}{ρ}𝑨)
 →        swelldef 𝓥 (α ⊔ suc ρ)  → Con (𝑨 ╱ θ)

𝟎[_╱_] {α} 𝑨 {ρ} θ wd = let 0eq = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence  in
 ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ╱ θ ]Compatible {ρ} wd)

\end{code}

Finally, the following elimination rule is sometimes useful (but it 'cheats' a lot
by baking in a large amount of extensionality that is miraculously true).

\begin{code}

open IsCongruence

/-≡ :  {𝑨 : Algebra α}(θ : Con{α}{ρ} 𝑨){u v : ∣ 𝑨 ∣}
 →     ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v

/-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)
\end{code}

-------------------------------------------------

<span style="float:left;">[← Base.Algebras.Products](Base.Algebras.Products.html)</span>
<span style="float:right;">[Base.Homomorphisms →](Base.Homomorphisms.html)</span>

{% include UALib.Links.md %}
