module Graft where

open import Agda.Primitive        using () renaming ( Set to Type )
open import Level                 using ( Level )
open import Overture.Signatures   using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )
open import Overture.Terms.Basic  using ( Term ; ℊ ; node )

private variable
  χ ξ : Level
  X : Type χ
  Y : Type ξ
  𝑆 : Signature 𝓞 𝓥

-- Graft σ onto the leaves of t: replace each generator ℊ y by the term σ y.
graft : Term {𝑆 = 𝑆} Y → (Y → Term {𝑆 = 𝑆} X) → Term {𝑆 = 𝑆} X
graft (ℊ y) σ = σ y
graft (node f ts) σ = node f (λ i → graft (ts i) σ)
