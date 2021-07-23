---
layout: default
title : Overture.Inverses module
date : 2021-06-09
author: [agda-algebras development team][]
---

All definitions/theorems in agda-algebras as of 22 June 2021.

\begin{code}


-- OVERTURE -----------------------------------------------------------------------------------------
open import Overture.Preliminaries          using    ( ℓ₁ ; ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; 𝑖𝑑 ; Π ; Π-syntax
                                                     ; lift∼lower ; lower∼lift ; _≈_ ; ≡-by-parts
                                                     ; transport )

open import Overture.Inverses               using    ( Image_∋_ ; eq ; Inv ; InvIsInv ; IsInjective
                                                     ; id-is-injective ; ∘-injective ; IsSurjective
                                                     ; Surjective ; SurjInv )



-- RELATIONS  -----------------------------------------------------------------------------------------

open import Relations.Discrete              using    (Im_⊆_ ; Arity ; ker ; kerlift ; ker' ; kernel ; 0[_]
                                                     ; _⊑_ ; ⊑-refl ; ⊑-trans ; Op ; π ; eval-rel
                                                     ; _preserves_ ; _|:_ ; compatibility-agreement
                                                     ; compatibility-agreement' ; arity[_] )

open import Relations.Continuous            using    ( ar ; Rel ; Rel-syntax ; ΠΡ ; ΠΡ-syntax ; eval-Rel
                                                     ; compatible-Rel ; eval-ΠΡ ; compatible-ΠΡ )

open import Relations.Quotients             using    ( Equivalence ; ker-IsEquivalence
                                                     ; kerlift-IsEquivalence ; [_] ; [_/_] ; Block
                                                     ; IsBlock ; Quotient ; _/_ ; ⟪_⟫ ; ⌞_⌟
                                                     ; []-⊆ ; []-⊇ ; ⊆-[] ; ⊇-[] ; 0[_]IsEquivalence
                                                     ; 0[_]Equivalence ; ⟪_∼_⟫-elim ; ≡→⊆ )

open import Relations.Truncation            using    ( is-center ; is-singleton ; is-prop ; is-prop-valued
                                                     ; singleton-is-prop ; fiber ; is-equiv ; hfunext
                                                     ; is-set ; to-Σ-≡ ; is-embedding ; singleton-type
                                                     ; invertible ; equiv-is-embedding ; monic-is-embedding|Set
                                                     ; blk-uip ; IsRelProp ; RelProp ; RelPropExt ; IsΠΡProp
                                                     ; ΠΡProp ; ΠΡPropExt )

open import Relations.Extensionality        using    ( DFunExt ; SurjInvIsRightInv ; epic-factor
                                                     ; epic-factor-intensional ; _≐_ ; pred-ext
                                                     ; block-ext ; block-ext|uip ; welldef
                                                     ; swelldef ; funext→swelldef ; SwellDef )


-- GALOIS CONNECTIONS -------------------------------------------------------------------------------

open import GaloisConnections.Basic         using    ( Galois ; _⃗_ ; _⃖_
                                                     ; ←→≥id ; →←≥id ; →←→⊆→ ; ←→←⊆←
                                                     ; ←→Closed ; →←Closed )

open import GaloisConnections.Properties    using    ( _≐_ ; ≐-iseqv ; PosetOfSubsets
                                                     ; 𝒫𝒜 ; 𝒫ℬ ; Rel→Gal )

-- CLOSURE SYSTEMS & OPERATORS -----------------------------------------------------------------------

open import ClosureSystems.Definitions      using    ( Extensive ) -- ; OrderPreserving ; Idempotent )

open import ClosureSystems.Basic            using    ( IntersectClosed ; ClosureSystem ; ClOp )

open import ClosureSystems.Properties       using    ( clop→law⇒ ; clop→law⇐ ; clop←law )


-- ALGEBRAS ------------------------------------------------------------------------------------------

open import Algebras.Basic                  using    ( Signature ; signature ; monoid-op ; monoid-sig
                                                     ; compatible ; Algebra ; lilAlgebra
                                                     ; Level-of-Alg ; Level-of-Carrier ; Level-of-lilAlg
                                                     ; Level-of-lilCarrier ; algebra ; lilalgebra
                                                     ; algebra→Algebra ; Algebra→algebra ; _̂_
                                                     ; Lift-alg-op ; Lift-Alg ; Lift-op-lilAlg
                                                     ; Lift-lilAlg ; Lift-algebra ;  compatible-lilAlg
                                                     ; compatible-Rel-alg ; compatible-ΠΡ-alg
                                                     ; compatible-Rel-lilAlg ; compatible-ΠΡ-lilAlg )

open import Algebras.Products               using    ( ⨅ ; ⨅' ; ov ; ℑ ; 𝔄 ; class-product )

open import Algebras.Congruences            using    ( IsCongruence ; Con ; IsCongruence→Con
                                                     ; Con→IsCongruence ; 0[_]Compatible ; 0Con[_]
                                                     ; _╱_ ; 𝟘[_╱_] ; 𝟎[_╱_] ; /-≡ )

open import Algebras.Setoid.Basic           using    ( ⟦_⟧s ; Algebroid ; SetoidAlgebra ; _̂_ ; _∙_ )

open import Algebras.Setoid.Products        using    ( ⨅ ; ⨅oid ; ℑ ; 𝔄 ; class-product )

open import Algebras.Setoid.Congruences     using    ( _∣≈_ ; _∣≋_ ; IsCongruence ; Con ; IsCongruence→Con
                                                     ; Con→IsCongruence ; _╱_ )


-- HOMOMORPHISMS ------------------------------------------------------------------------------------------

open import Homomorphisms.Basic             using    ( compatible-op-map ; is-homomorphism ; hom ; ∘-hom
                                                     ; ∘-is-hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-monomorphism
                                                     ; mon ; is-epimorphism ; epi ; mon-to-hom ; epi-to-hom
                                                     ; πhom ; homker-comp ; kercon ; kerquo ; ker[_⇒_]_↾_
                                                     ; πepi ; πker ; ker-in-con ; ⨅-hom-co ; ⨅-hom
                                                     ; Lift-hom ; ⨅-projection-hom )

open import Homomorphisms.Noether           using    ( FirstHomTheorem|Set ; FirstIsoTheorem|Set
                                                     ; NoetherHomUnique ; NoetherIsoUnique ; HomFactor
                                                     ; HomFactorEpi )

open import Homomorphisms.HomomorphicImages using    ( _IsHomImageOf_ ; HomImages ; IsHomImageOfClass
                                                     ; HomImageOfClass ; Lift-epi-is-epi
                                                     ; Lift-Alg-hom-image )

open import Homomorphisms.Isomorphisms      using    ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅
                                                     ; Lift-Alg-iso ; Lift-Alg-assoc
                                                     ; Lift-Alg-⨅≅ ; ⨅≅ )

open import Homomorphisms.Setoid.Basic      using    ( compatible-op-map ; is-homomorphism ; hom
                                                     ; ∘-hom ; ∘-is-hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇
                                                     ; module LiftSetoidHom ; is-monomorphism ; mon ; epi
                                                     ; is-epimorphism ; homker-comp ;  kercon ; kerquo
                                                     ; ker[_⇒_]_↾_ )

open import Homomorphisms.Setoid.Isomorphisms using    ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅
                                                     ; Lift-SetoidAlg-iso ; Lift-SetoidAlg-assoc )

-- TERMS ------------------------------------------------------------------------------------------

open import Terms.Basic                     using    (Term ; 𝑻 )

open import Terms.Properties                using    (free-lift ; lift-hom ; free-unique ; lift-of-epi-is-epi )

open import Terms.Operations                using    ( _⟦_⟧ ; free-lift-interp ; term-interp
                                                     ; term-gen ; term-gen-agreement ; term-agreement
                                                     ; interp-prod ; interp-prod2 ; comm-hom-term
                                                     ; _∣:_ ; _[_] ; Substerm ; _[_]t ; subst-lemma
                                                     ; subst-theorem )

open import Terms.Setoid.Basic              using    ( _≐_ ; ≐-isRefl ; ≐-isSym ; ≐-isTrans ; ≐-isEquiv
                                                     ; TermSetoid ; TermAlgebra ; Ops ; Sub ; _[_]
                                                     ; module Environment )

open Environment                            using    (_≃_ ; Env ; ⟦_⟧ ; Equal ; isEquiv ; ⟦_⟧s ; substitution)


-- SUBALGEBRAS ------------------------------------------------------------------------------------------

open import Subalgebras.Subuniverses        using    ( Subuniverses ; Subuniverse ; Sg ; sgIsSub
                                                     ; sgIsSmallest ; ⋂s ; sub-term-closed
                                                     ; TermImage ; TermImageIsSub ; Y-onlyif-TermImageY
                                                     ; SgY-onlyif-TermImageY ; hom-unique )

open import Subalgebras.Subalgebras         using    ( _≥_ ; _IsSupalgebraOf_ ; _≤_ ; _IsSubalgebraOf_
                                                     ; SubalgebraOf ; Subalgebra ; FirstHomCorollary|Set
                                                     ; free-quot-subalg ; _IsSubalgebraOfClass_
                                                     ; SubalgebraOfClass )


open import Subalgebras.Properties          using    ( ≤-refl ; ≥-refl ; ≤-reflexive ; ≤-trans ; ≥-trans
                                                     ; ≤-preorder ; ≥-preorder ; ≤-resp-≅ ; ≅-resp-≥
                                                     ; ≥-resp-≅ ; ≅-resp-≤ ; ≤-RESP-≅ ; ≥-RESP-≅ ; ≅-RESP-≤
                                                     ; ≅-RESP-≥ ; iso→injective ; ≤-mono ; Lift-is-sub
                                                     ; ≤-Lift ; ≥-Lift ; Lift-≤-Lift )


open import Subalgebras.Setoid.Subuniverses  using   ( Subuniverses ; Subuniverse ; Sg ; sgIsSub
                                                     ; sgIsSmallest ; ⋂s ; sub-term-closed
                                                     ; TermImage ; TermImageIsSub ; B-onlyif-TermImageB
                                                     ; SgB-onlyif-TermImageB ; hom-unique )

open import Subalgebras.Setoid.Subalgebras  using    ( _≥s_ ; _IsSupalgebraOf_ ; _≤s_ ; _IsSubalgebraOf_
                                                     ; SubalgebraOf ; Subalgebra
                                                     ; IsSubalgebraREL ; SubalgebraREL ; _≤c_
                                                     ; _IsSubalgebraOfClass_ ; SubalgebraOfClass
                                                     ; SubalgebraOfClass' ; SubalgebrasOfClass )

open import Subalgebras.Setoid.Properties   using    ( ≅→≤s ; ≅→≥s ; ≤s-refl ; ≥s-refl ; ≤s-reflexive
                                                     ; ≤s-trans ; ≥s-trans ; ≤s-preorder
                                                     ; A≥B×B≅C→A≥C ; A≤B×B≅C→A≤C ; A≅B×B≥C→A≥C ; A≅B×B≤C→A≤C
                                                     ; ≤s-TRANS-≅ ; ≤s-mono ; Lift-is-sub ; ≤s-Lift
                                                     ; ≥s-Lift ; Lift-≤s-Lift )



-- VARIETIES ------------------------------------------------------------------------------------------

open import Varieties.EquationalLogic       using    ( _⊧_≈_ ; _⊫_≈_ ; Th ; Mod )

open import Varieties.Closure               using    ( H ; S ; P ; V ; is-variety ; variety
                                                     ; S-mono ; subalgebra→S ; S→subalgebra
                                                     ; P-mono ; P-expa ; P-idemp ; Lift-Alg-subP
                                                     ; Lift-Alg-subP' ; module Vlift )

open import Varieties.Properties            using    ( ⊧-I-invar ; ⊧-Lift-invar ; ⊧-lower-invar
                                                     ; ⊧-S-invar ; ⊧-S-class-invar ; ⊧-P-invar
                                                     ; ⊧-P-class-invar ; ⊧-P-lift-invar ; ⊧-H-invar
                                                     ; ⊧-H-class-invar ; ⊧-H-class-coinvar )

open import Varieties.Preservation          using    (S⊆SP ; lemPS⊆SP ; PS⊆SP ; P⊆V ; SP⊆V ; SP⊆V'
                                                     ; module class-products-with-maps ; H-id1 ; H-id2
                                                     ; S-id1 ; S-id2 ; P-id1 ; P-id2 ; V-id1
                                                     ; module Vid' ; V-id1' ; ovu ; lovu ; 𝕍 ; 𝒱
                                                     ; class-ids-⇒ ; class-ids ; class-ids-⇐ ; V-id2 )

open import Varieties.FreeAlgebras          using    ( 𝓕 ; 𝓕⁺ ; ψ ; ψRel ; ψcompatible ; ψIsEquivalence
                                                     ; ψCon ; ℭ ; homℭ ; 𝔽 ; epi𝔽 ; hom𝔽 ; hom𝔽-is-epic
                                                     ; ψlemma0 ; ψlemma0-ap ; 𝔽-lift-hom ; X↪𝔽 ; 𝔑
                                                     ; hom𝔽-is-lift-hom ; ψlemma1 ; ψlemma2 ; ψlemma3
                                                     ; class-models-kernel ; 𝕍𝒦 ; kernel-in-theory
                                                     ; 𝔽-ModTh-epi ; 𝔽≤ℭ ; 𝔽∈SP ; 𝔽∈𝕍 ; Birkhoff
                                                     ; Birkhoff-converse ; _↠_ )


open import Varieties.Setoid.EquationalLogic using   ( Eq ; _⊨_ ; _⊧_ ; Mod ; _⊫_ ; _⊃_ ; _⊢_▹_≈_
                                                     ; module Soundness ; module TermModel
                                                     ; module Completeness )
open Soundness    using ( sound        )
open TermModel    using ( TermSetoid   )
open Completeness using ( completeness )




-- GENERAL STRUCTURES (allowing both operation and relation symbols) ---------------------------------

open import Structures.Basic                using    ( signature ; structure ; _ʳ_ ; _ᵒ_ ; compatible
                                                     ; Lift-op ; Lift-rel ; Lift-Strucˡ ; Lift-Strucʳ
                                                     ; Lift-Struc ; siglˡ ; siglʳ ; sigl )

open import Structures.Examples             using    ( Sig∅ ; Sig-0 ; Sig-1 ; Sig-2 ; Sig-0-1
                                                     ; Sig-0-1-2 ; SL ; NAE3SAT ; nae3sat )

open import Structures.Products             using    ( ⨅ ; ℓp ; ℑ ; 𝔄 ; class-product )

open import Structures.Congruences          using    ( con ; 0[_]compatible ; 0con[_] ; quotient
                                                     ; _╱_ ; /≡-elim ; 𝟎[_╱_] )

open import Structures.Homs                 using    ( preserves ; is-hom-rel ; comm-op ; is-hom-op
                                                     ; is-hom ; hom ; hom-alg ; ∘-is-hom-rel
                                                     ; ∘-is-hom-op ; ∘-is-hom ; ∘-hom ; 𝒾𝒹
                                                     ; is-mon ; mon ; mon→hom ; is-epi ; epi
                                                     ; epi→hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; homker-comp
                                                     ; kerlift-comp ; kercon ; kerquo ; ker[_⇒_]
                                                     ; πepi ; πhom ; πker ; ⨅-hom-co ; ⨅-hom
                                                     ; ⨅-projection-hom )

open import Structures.Terms.Basic          using    ( Term )

open import Structures.Terms.Operations     using    ( _⟦_⟧ )

open import Structures.EquationalLogic      using    ( _⊧_≈_ ; _⊧_≋_ ; Th ; Mod ; fMod )

open import Structures.Graphs               using    ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom )

open import Structures.Graphs0              using    ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom ; _⇛_⇚_ )



-- GENERAL STRUCTURES represented as Sigma types (instead of record types) -------------------------

open import Structures.Sigma.Basic          using    ( Signature ; Structure ; RStructure ; AStructure
                                                     ; Structure→RStructure ; Structure→AStructure
                                                     ; _⟦_⟧ᵣ ; _⟦_⟧ₒ ; _ʳ_ ; _ᵒ_ ; Compatible
                                                     ; Compatible' ; Lift-op ; Lift-rel
                                                     ; Lift-Strucˡ ; Lift-Strucʳ ; Lift-Struc )

open import Structures.Sigma.Products       using    ( ⨅ ; ℓp ; ℑ ; 𝔖 ; class-prod )

open import Structures.Sigma.Congruences    using    ( Con ; 0[_]Compatible ; 0Con[_] ; _╱_ ; /≡-elim
                                                     ; 𝟘[_╱_] ; 𝟎[_╱_] )

open import Structures.Sigma.Homs           using    ( preserves ; is-hom-rel ; comp-op ; is-hom-op
                                                     ; is-hom ; hom ; ∘-is-hom-rel ; ∘-is-hom-op
                                                     ; ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon ; mon ; is-epi
                                                     ; epi ; mon→hom ; epi→hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇
                                                     ; Lift-Hom ; Homker-comp )

open import Structures.Sigma.Isos           using    ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅
                                                     ; Lift-Struc-iso ; ⨅≅ )


-- COMPLEXITY ---------------------------------------------------------------------------------------

open import Complexity.CSP                   using   (Constraint ; CSPInstance )


\end{code}






--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
