{-# OPTIONS --without-K --exact-split --safe #-}

module Demos.TYPES2021-imports where


-- Imports from Agda and Agda Std Lib -------------------------------------------------
open import Axiom.Extensionality.Propositional using    ()
                                  renaming (Extensionality to funext) public

open import Agda.Builtin.Equality using    ( _≡_   ; refl     ) public
open import Agda.Builtin.Bool     using    ( Bool             ) public
open import Agda.Primitive        using    ( _⊔_              )
                                  renaming ( Set   to Type
                                           ; Setω  to Typeω   ) public
open import Data.Empty            using    ( ⊥                ) public
open import Data.Product          using    ( _,_   ; Σ-syntax
                                           ; Σ     ;   _×_    )
                                  renaming ( proj₁ to  fst
                                           ; proj₂ to  snd    ) public
open import Data.Sum              using    (_⊎_               )
                                  renaming ( inj₁  to  inl
                                           ; inj₂  to  inr    ) public
open import Function.Base         using    ( _∘_   ;   id     ) public
open import Function.Bundles      using    ( Injection        ) public
open import Level                 renaming ( suc   to lsuc
                                           ; zero  to ℓ₀      ) public
open import Relation.Binary       using    ( IsEquivalence    ) public
open import Relation.Binary.Core  using    ( _⇒_   ;  _=[_]⇒_ )
                                  renaming ( REL   to BinREL
                                           ; Rel   to BinRel  ) public
open import Relation.Unary        using    ( ∅     ;  _∈_ ; ⋂
                                           ; Pred  ; _⊆_
                                           ; ｛_｝  ; _∪_      ) public
open import Relation.Binary.PropositionalEquality
                                  using    ( trans ; cong-app
                                           ; cong  ; module ≡-Reasoning ) public


-- Imports from agda-algebras ------------------------------------------------------------
open import Overture.Preliminaries     using ( Π ; 𝑖𝑑 ; Π-syntax ; ∣_∣ ; ∥_∥
                                             ; _⁻¹ ; _≈_ ; _∙_ ; lift∼lower
                                             ; lower∼lift                      ) public
open import Overture.Inverses          using ( IsInjective ; IsSurjective
                                             ; Image_∋_ ; SurjInv ; Inv
                                             ; InvIsInv ; eq ; id-is-injective
                                             ; ∘-injective                     ) public
open import Relations.Discrete         using ( arity[_] ; ker
                                             ; kernel ; Im_⊆_                  ) public
open import Relations.Quotients        using ( ker-IsEquivalence ; _/_ ; ⌞_⌟
                                             ; ⟪_⟫ ; IsBlock ; Quotient
                                             ; Equivalence ; 0[_]Equivalence
                                             ;  ⟪_∼_⟫-elim ; R-block           ) public
open import Foundations.Truncation     using ( is-set ; blk-uip
                                             ; is-embedding ; hfunext
                                             ; monic-is-embedding|Set          ) public
open import Foundations.Extensionality using ( DFunExt ; block-ext|uip ; pred-ext
                                             ; SurjInvIsRightInv ; epic-factor ) public
open import Foundations.Welldefined    using ( swelldef ; SwellDef ) public

open import Algebras.Basic             using ( Level-of-Carrier                ) public
open import Homomorphisms.Basic        using ( kercon ; ker[_⇒_]_↾_
                                             ; ⨅-hom-co ; πker ; ∘-is-hom
                                             ; epi ; epi-to-hom ; ker-in-con   ) public
open import Homomorphisms.Noether      using ( FirstHomTheorem|Set             ) public
