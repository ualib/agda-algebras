-- Imports from Agda and the Agda Standard Library (organized by submodule)


\begin{code}
-- module Overture.Preliminaries where

open import Agda.Builtin.Equality                 using    ( _≡_      ;  refl   )
open import Function.Base                         using    ( _∘_      ;  id     )
open import Relation.Binary.PropositionalEquality using    ( sym      ;  trans  )
open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_   )
                                                  renaming ( proj₁    to  fst
                                                           ; proj₂    to  snd   )
open import Agda.Primitive                        using    ( _⊔_                )
                                                  renaming ( Set      to  Type  )
open import Level                                 using    ( Level    ;   Lift
                                                           ; lift     ;   lower )
                                                  renaming ( suc      to  lsuc  )


-- module Overture.Inverses where

open import Agda.Builtin.Equality       using    ( _≡_ ; refl   )
open import Agda.Primitive              using    ( _⊔_          )
                                        renaming ( Set  to Type )
open import Level                       renaming ( suc  to lsuc )
open import Data.Product                using    ( _,_ ; Σ
                                                 ; Σ-syntax     )
open import Function.Base               using    ( _∘_ ; id     )
import Function.Definitions as F  -- (for Injective)
open import Function.Bundles            using  ( _↣_ ; mk↣ )
open import Function.Construct.Identity using  ( id-↣      )


-- module Relations.Discrete where

open import Agda.Builtin.Equality using    ( _≡_ ; refl     )
open import Agda.Primitive        using    ( _⊔_            )
                                  renaming ( Set  to Type
                                           ; Setω to Typeω  )
open import Level                 using    ( Level          )
                                  renaming ( suc  to lsuc
                                           ; zero to ℓ₀     )
open import Relation.Binary.Core  using    ( _⇒_ ; _=[_]⇒_  )
                                  renaming ( REL  to BinREL ;
                                             Rel  to BinRel )
open import Relation.Unary        using    ( ∅; _∈_; Pred   )
open import Data.Product          using    ( _,_ ; _×_      )


-- module Relations.Continuous where

open import Agda.Primitive using (_⊔_) renaming ( Set   to  Type
                                                ; Setω  to  Typeω )
open import Level                      renaming ( suc   to  lsuc
                                                ; zero  to  ℓ₀ )
open import Relations.Discrete using (Op)



-- module Relations.Quotients where

open import Agda.Builtin.Equality                 using    (_≡_  ; refl      )
open import Data.Product                          using    ( _,_ ; Σ
                                                           ; Σ-syntax        )
                                                  renaming ( proj₁ to fst
                                                           ; proj₂ to snd    )
open import Agda.Primitive                        using    ( _⊔_             )
                                                  renaming ( Set   to Type
                                                           ; Setω  to Typeω  )
open import Level                                 renaming ( suc   to lsuc
                                                           ; zero  to ℓ₀     )
open import Relation.Binary                       using    ( IsEquivalence   )
                                                  renaming ( Rel   to BinRel )
open import Relation.Binary.PropositionalEquality using    ( sym  ; trans    )
open import Relation.Unary                        using    ( Pred ; _⊆_      )
open import Relations.Discrete                    using    ( ker             )





-- module Relations.Truncation where

open import Agda.Builtin.Equality                 using    ( _≡_      ;   refl     )
open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_      )
                                                  renaming ( proj₁    to  fst
                                                           ; proj₂    to  snd      )
open import Agda.Primitive                        using    ( _⊔_                   )
                                                  renaming ( Set      to  Type     )
open import Level                                 renaming ( suc      to  lsuc     )
open import Function.Base                         using    ( _∘_      ;   id       )
open import Relation.Binary                       using    ( IsEquivalence         )
                                                  renaming ( Rel      to  BinRel   )
open import Relation.Binary.PropositionalEquality using    ( sym      ;   trans    )
open import Relation.Unary                        using    ( Pred     ;   _⊆_      )
open import Relation.Binary.PropositionalEquality using    ( trans    ;   cong-app
                                                           ; module ≡-Reasoning    )


-- module Relations.Extensionality where

open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)

open import Agda.Builtin.Equality                 using    (_≡_    ;  refl    )
open import Agda.Primitive                        using    ( _⊔_              )
                                                  renaming ( Set   to Type    )
open import Data.Product                          using    ( _,_ ; Σ-syntax ; Σ )
                                                  renaming ( proj₁ to fst
                                                           ; proj₂ to snd     )
open import Function.Base                         using    ( _∘_   ;  id      )
open import Level                                 renaming ( suc   to lsuc    )
open import Relation.Binary                       using    ( IsEquivalence    )
                                                  renaming ( Rel   to BinRel  )
open import Relation.Binary.PropositionalEquality using    ( sym   ;  cong-app
                                                           ; trans            )
open import Relation.Unary                        using    ( Pred  ; _⊆_      )

open import Overture.Preliminaries using ( 𝑖𝑑 ; _⁻¹ ; _∙_ ; transport )
open import Overture.Inverses      using ( IsSurjective ; SurjInv
                                         ; InvIsInv ; Image_∋_ ; eq  )
open import Relations.Discrete     using ( Op                        )
open import Relations.Quotients    using ( [_] ; /-subset
                                         ; /-supset ; IsBlock ; ⟪_⟫  )
open import Relations.Truncation   using ( blk-uip ; to-Σ-≡          )



-- module Algebras.Basic where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality                 using    (_≡_    ;   refl     )
open import Agda.Primitive                        using    ( _⊔_                )
                                                  renaming ( Set   to  Type     )
open import Data.Empty                            using    ( ⊥                  )
open import Data.Product                          using    ( _,_ ; Σ-syntax ; Σ )
open import Level                                 renaming ( suc   to  lsuc
                                                           ; zero  to  lzero    )
open import Relation.Binary                       using    ( IsEquivalence      )
                                                  renaming ( Rel   to  BinRel   )


-- module Algebras.Products {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Primitive                        using    ( _⊔_              )
                                                  renaming ( Set   to Type    )
open import Data.Product                          using    ( _,_ ; Σ ; Σ-syntax )
open import Relation.Unary                        using    ( Pred  ; _⊆_ ; _∈_  )

open import Overture.Preliminaries using (_⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)



-- module Algebras.Congruences {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional    renaming (Extensionality to funext)
open import Agda.Builtin.Equality                 using    ( _≡_      ; refl    )
open import Agda.Primitive                        using    ( _⊔_                )
                                                  renaming ( Set      to  Type  )

open import Relation.Binary                       using    ( IsEquivalence      )
                                                  renaming ( Rel      to BinRel )

open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_   )
open import Relation.Binary.PropositionalEquality using    ( sym ; trans ; cong )




-- module Homomorphisms.Basic {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)

open import Agda.Builtin.Equality                 using    ( _≡_      ;   refl  )
open import Agda.Primitive                        using    ( _⊔_      ;   lsuc  )
                                                  renaming ( Set      to  Type  )
open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_   )
                                                  renaming ( proj₁    to  fst
                                                           ; proj₂    to  snd   )
open import Function.Base                         using    ( _∘_      ;   id    )
open import Relation.Binary.PropositionalEquality using    ( trans    ;   cong
                                                           ; cong-app
                                                           ; module ≡-Reasoning )


-- module Homomorphisms.Noether {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)
open import Agda.Primitive                        using    ( _⊔_      ;   lsuc  )
                                                  renaming ( Set      to  Type  )
open import Agda.Builtin.Equality                 using    ( _≡_      ;   refl  )
open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_   )
                                                  renaming ( proj₁    to  fst
                                                           ; proj₂    to  snd   )
open import Function.Base                         using    ( _∘_      ;   id    )
open import Relation.Binary                       using    ( IsEquivalence   )
open import Relation.Binary.PropositionalEquality using    ( trans    ;   cong
                                                           ; cong-app
                                                           ; module ≡-Reasoning )
open import Relation.Unary                        using    ( _⊆_ )



-- module Homomorphisms.Isomorphisms {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥)  where

open import Axiom.Extensionality.Propositional    renaming (Extensionality to funext )
open import Agda.Primitive                        using    ( _⊔_    ;   lsuc      )
                                                  renaming ( Set    to  Type      )
open import Agda.Builtin.Equality                 using    ( _≡_    ;   refl      )
open import Data.Product                          using    ( _,_    ;   Σ-syntax
                                                           ;  Σ     ;   _×_       )
                                                  renaming ( proj₁  to  fst
                                                           ; proj₂  to  snd       )
open import Function.Base                         using    ( _∘_                  )
open import Relation.Binary.PropositionalEquality using    ( cong   ;   cong-app  )



-- module Homomorphisms.HomomorphicImages {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Primitive        using    ( _⊔_ ; lsuc )
                                  renaming ( Set to Type )
open import Agda.Builtin.Equality using    ( _≡_ ; refl )
open import Data.Product          using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                  renaming ( proj₁ to fst
                                           ; proj₂ to snd )
open import Relation.Binary.PropositionalEquality.Core
                                  using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary        using    ( Pred ; _∈_ )


-- module Terms.Basic {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Relation.Binary.PropositionalEquality using ( cong ; module ≡-Reasoning )

open import Agda.Primitive          using    ( _⊔_ ;  lsuc )
                                    renaming ( Set to Type )
open import Agda.Builtin.Equality   using    ( _≡_ ;  refl )
open import Data.Product            using    ( _,_ ;  Σ
                                             ; Σ-syntax    )
open import Function.Base           using    ( _∘_         )


-- module Terms.Operations {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Relation.Binary.PropositionalEquality using ( cong ; module ≡-Reasoning )
open import Function.Base  using (_∘_)

open import Agda.Primitive          using    ( _⊔_ ;  lsuc )
                                    renaming ( Set to Type )
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ )


-- module Subalgebras.Subuniverses {𝓞 𝓥 : Level} {𝑆 : Signature 𝓞 𝓥} where

open import Relation.Binary.PropositionalEquality using ( cong ; module ≡-Reasoning )
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ ; lsuc )
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Function.Base           using    ( _∘_ )
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ⋂ )


-- module Subalgebras.Subalgebras {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Builtin.Equality      using    ( _≡_ ;  refl )
open import Agda.Primitive             using    ( _⊔_ ;  lsuc )
                                       renaming ( Set to Type )
open import Data.Product               using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                       renaming ( proj₁ to fst
                                                ; proj₂ to snd )
open import Function.Base              using    ( _∘_ )
open import Function.Bundles           using    ( Injection )
open import
 Relation.Binary.PropositionalEquality using    ( cong ; module ≡-Reasoning )
open import Relation.Unary             using    ( _∈_ ; Pred ; _⊆_ )


-- module Varieties.Basic {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Builtin.Equality   using    ( _≡_ ;  refl )
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ ;  lsuc )
open import Axiom.Extensionality.Propositional
                                    renaming ( Extensionality to funext )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Function.Base           using    ( _∘_ )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app
                                             ; module ≡-Reasoning)
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ⋂ )



-- module Varieties.EquationalLogic {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ )
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary          using    ( _∈_ ; Pred ; _⊆_ )


-- module Varieties.Preservation {α 𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Data.Sum.Base           using    ( _⊎_ )
open import Function.Base           using    ( _∘_ )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ｛_｝ ; _∪_ )


-- module Varieties.FreeAlgebras {α 𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Function.Base           using    ( _∘_ )
open import Relation.Binary         using    ( IsEquivalence )
                                    renaming ( Rel to BinRel )
open import Relation.Binary.PropositionalEquality
                                    using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ ; ｛_｝ ; _∪_ )


-- module Varieties.Closure.H {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Primitive                    using ( _⊔_ )
open import Data.Product                      using ( _,_ )
open import Relation.Unary                    using ( Pred ; _∈_ ; _⊆_ )



-- module Varieties.Closure.S {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Data.Product   using    ( _,_ )
                           renaming ( proj₁ to fst
                                    ; proj₂ to snd )
open import Relation.Unary using    ( Pred ; _∈_ ; _⊆_ )



-- module Varieties.Closure.P {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Primitive               using    ( _⊔_ ;  lsuc )
                                         renaming ( Set to Type )
open import Data.Product                 using    ( _,_ )
open import Relation.Unary               using    ( Pred ; _∈_ ; _⊆_ )


-- module Varieties.Closure.V {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional renaming ( Extensionality to funext )
open import Agda.Primitive   using    ( _⊔_ ;  lsuc )
                             renaming ( Set to Type )
open import Data.Product     using    ( _,_ ; Σ-syntax )
open import Relation.Unary   using    ( Pred ; _∈_ ; _⊆_)




\end{code}
