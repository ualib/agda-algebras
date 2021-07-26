-- List of imports from Agda and the Agda Standard Library used in agda-algebras


\begin{code}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality                 using ( _≡_ ; refl )
open import Agda.Primitive                        using ( _⊔_ ; lsuc )                                           renaming ( Set to Type ; lzero to ℓ₀ ; Setω to Typeω )
open import Algebra.Definitions                   using ( IdempotentFun )
open import Axiom.Extensionality.Propositional    using ( )                                                      renaming (Extensionality to funext)
open import Data.Empty                            using ( ⊥ )
open import Data.Empty.Polymorphic                using ( ⊥ )
open import Data.Fin.Base                         using ( Fin )
open import Data.Nat                              using ( ℕ )
open import Data.Product                          using ( _,_ ; Σ ; Σ-syntax ; _×_ ; swap)                             renaming ( proj₁ to fst ; proj₂ to snd )
open import Data.Sum.Base                         using ( _⊎_ ; [_,_] )                                          renaming ( inj₁ to inl ; inj₂ to inr )
open import Data.Unit.Polymorphic                 using ( ⊤ ; tt )
open import Function.Base                         using ( _∘_ ; id )
open import Function.Bundles                      using ( _↣_ ; mk↣ )
open import Function.Construct.Identity           using ( id-↣ )
open import Function.Definitions                  using ( Injective )
open import Level                                 using ( Level ; Lift )
open import Relation.Binary                       using ( IsEquivalence )
open import Relation.Binary.Bundles               using ( Poset )
open import Relation.Binary.Core                  using ( _Preserves_⟶_ ) --; Extensive ; Idempotent₁ )
open import Relation.Binary.Core                  using ( _⇒_ ; _=[_]⇒_ )                                        renaming ( REL to BinREL ; Rel to BinRel )
open import Relation.Binary.PropositionalEquality using ( sym  ; trans ; cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary                        using ( ∅; _∈_; Pred ; _⊆_ ; ⋂ ; ｛_｝ ; _∪_ )



\end{code}
