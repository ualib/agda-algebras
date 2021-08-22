<h2>Algebras.Congruences module</h2>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic

module Algebras.Congruences {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product    using ( Σ-syntax ; _,_ )
open import Function.Base   using ( _∘_ )
open import Level           using ( Level )
open import Relation.Binary using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Binary.PropositionalEquality
                            using ( _≡_ ; refl )

-- Imports from agda-algebras ----------------------------------------------------------
open import Overture.Preliminaries    using ( ∣_∣  ; ∥_∥  )
open import Relations.Discrete        using ( _|:_ ; 0[_] )
open import Relations.Quotients       using ( 0[_]Equivalence ; _/_ ; ⟪_⟫ ; IsBlock )
open import Foundations.Welldefined   using ( swelldef )
open import Algebras.Products {𝑆 = 𝑆} using ( ov )

private variable α β ρ : Level
\end{code}

<h3>Congruence Relations</h3>

A <i>congruence relation</i> of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of being a congruence, and we define a Sigma type (`Con`) to represent the type of congruences of a given algebra.

\begin{code}

record IsCongruence (𝑨 : Algebra α 𝑆)(θ : BinRel ∣ 𝑨 ∣ ρ) : Type(ov ρ ⊔ α)  where
 constructor mkcon
 field       is-equivalence : IsEquivalence θ
             is-compatible  : compatible 𝑨 θ

Con : (𝑨 : Algebra α 𝑆) → Type(α ⊔ ov ρ)
Con {α}{ρ}𝑨 = Σ[ θ ∈ ( BinRel ∣ 𝑨 ∣ ρ ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

IsCongruence→Con : {𝑨 : Algebra α 𝑆}(θ : BinRel ∣ 𝑨 ∣ ρ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α 𝑆} → ((θ , _) : Con{α}{ρ} 𝑨) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

\end{code}

<h4 id="example">Example</h4>
We defined the <i>zero relation</i> `0[_]` in the [Relations.Discrete][] module.  We now build the <i>trivial congruence</i>, which has `0[_]` as its underlying relation. Observe that `0[_]` is equivalent to the identity relation `≡` and these are obviously both equivalence relations. In fact, we already proved this of `≡` in the [Overture.Equality][] module, so we simply apply the corresponding proofs.

\begin{code}
open Level

-- Example. The zero congruence of a structure.
0[_]Compatible : {α : Level}(𝑨 : Algebra α 𝑆){ρ : Level} → swelldef 𝓥 α → (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: (0[ ∣ 𝑨 ∣ ]{ρ})
0[ 𝑨 ]Compatible wd 𝑓 {i}{j} ptws0  = lift γ
  where
  γ : (𝑓 ̂ 𝑨) i ≡ (𝑓 ̂ 𝑨) j
  γ = wd (𝑓 ̂ 𝑨) i j (lower ∘ ptws0)

open IsCongruence
0Con[_] : {α : Level}(𝑨 : Algebra α 𝑆){ρ : Level} → swelldef 𝓥 α → Con{α}{α ⊔ ρ}  𝑨 
0Con[ 𝑨 ]{ρ} wd = let 0eq = 0[ ∣ 𝑨 ∣ ]Equivalence{ρ}  in
 ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ]Compatible wd)

\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

<h4 id="quotient-algebras">Quotient algebras</h4>
In many areas of abstract mathematics the <i>quotient</i> of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.<sup>[1](Algebras.Congruences.html#fn1)</sup>

\begin{code}

_╱_ : (𝑨 : Algebra α 𝑆) → Con{α}{ρ} 𝑨 → Algebra (α ⊔ lsuc ρ) 𝑆

𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)  ,                                  -- the domain of the quotient algebra
        λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.block-u ∥ 𝑎 i ∥) ⟫  -- the basic operations of the quotient algebra

\end{code}

<b>Example</b>. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}


𝟘[_╱_] : (𝑨 : Algebra α 𝑆)(θ : Con{α}{ρ} 𝑨) → BinRel (∣ 𝑨 ∣ / ∣ θ ∣)(α ⊔ lsuc ρ)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.

\begin{code}

𝟎[_╱_] : {α : Level}(𝑨 : Algebra α 𝑆){ρ : Level}(θ : Con {α}{ρ}𝑨) → swelldef 𝓥 (α ⊔ lsuc ρ)  → Con (𝑨 ╱ θ)
𝟎[_╱_] {α} 𝑨 {ρ} θ wd = let 0eq = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence  in
 ∣ 0eq ∣ , mkcon ∥ 0eq ∥ (0[ 𝑨 ╱ θ ]Compatible {ρ} wd)

\end{code}


Finally, the following elimination rule is sometimes useful (but it 'cheats' a lot by baking in
a large amount of extensionality that is miraculously true).

\begin{code}

open IsCongruence

/-≡ : {𝑨 : Algebra α 𝑆}(θ : Con{α}{ρ} 𝑨){u v : ∣ 𝑨 ∣} → ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
/-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}

{% include footnote.html %}
