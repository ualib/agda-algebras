module Interpret where

open import Agda.Primitive                 using () renaming ( Set to Type )
open import Level                          using ( Level )
open import Overture.Signatures            using ( 𝓞 ; 𝓥 ; Signature ; OperationSymbolsOf ; ArityOf )
open import Overture.Terms.Basic           using ( Term ; ℊ ; node )
open import Overture.Terms.Interpretation  using ( Interpretation ; graft )

private variable
  χ : Level
  X : Type χ
  𝑆₁ 𝑆₂ : Signature 𝓞 𝓥

-- An interpretation I sends each operation symbol of 𝑆₁ to an 𝑆₂-term.
-- I ✦ t rewrites the 𝑆₁-term t into an 𝑆₂-term over the same variables.
_✦_ : Interpretation 𝑆₁ 𝑆₂ → Term {𝑆 = 𝑆₁} X → Term {𝑆 = 𝑆₂} X
I ✦ ℊ x = ℊ x
I ✦ node f ts = graft (I f) (λ i → I ✦ ts i)
