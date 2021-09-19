---
layout: default
title : Overture.Inverses module
date : 2021-06-09
author: [agda-algebras development team][]
---

All definitions/theorems in agda-algebras as of 22 June 2021.

\begin{code}

-- OVERTURE -----------------------------------------------------------------------------------------
open import Overture.Preliminaries using ( ℓ₁ ; ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; 𝑖𝑑 ; Π ; Π-syntax ; ∃-syntax
                                         ; lift∼lower ; lower∼lift ; _≈_ ; ≡-by-parts ; transport )

open import Overture.Inverses      using ( Image_∋_ ; Range ; range ; Image⊆Range ; Range⊆Image
                                         ; Imagef∋f ; f∈range ; Inv ; [_]⁻¹ ; InvIsInverseʳ
                                         ; ⁻¹IsInverseʳ ;  InvIsInverseˡ ; ⁻¹IsInverseˡ )

open import Overture.FuncInverses  using ( Image_∋_ ; Range ; Image⊆Range ; Range⊆Image ; Imagef∋f
                                         ; range ; image ; preimage ; f∈range ; Inv ; Inv' ; [_]⁻¹
                                         ; InvIsInverseʳ ; ⁻¹IsInverseʳ ; InvIsInverseˡ ; ⁻¹IsInverseˡ )

open import Overture.Injective     using ( id-is-injective ; IsInjective ; ∘-injective )

open import Overture.Surjective    using ( IsSurjective ; Surjective ; SurjInv ; SurjInvIsInverseʳ
                                         ; epic-factor ; epic-factor-intensional )

open import Overture.Transformers  using ( Bijection ; ∣_∣=∣_∣ ; PointwiseBijection
                                         ; ∣_∣≈∣_∣ ; uncurry₀ ; Curry ; Uncurry ; A×A→B≅A→A→B
                                         ; A→A→Fin2A ; A→A→Fin2A' ; A→A→Fin2A-ptws-agree
                                         ; A×A→Fin2A ; Fin2A→A×A ; Fin2A~A×A ; A×A~Fin2A-ptws
                                         ; A→A~Fin2A-ptws ; Fin2A ; Fin2A≡ ; CurryFin2
                                         ; UncurryFin2 ; CurryFin2~UncurryFin2 ; CurryFin3
                                         ; UncurryFin3 ; Fin2A→B-to-A×A→B ; A×A→B-to-Fin2A→B
                                         ; Fin2A→B~A×A→B )

open import Overture.Func.Preliminaries using ( _⟶_ ; _∘_ ; 𝑙𝑖𝑓𝑡 ; lift∼lower ; lower∼lift
                                              ; liftFunc ; preserves≈ )

open import Overture.Func.Inverses      using ( image_∋_ ; Image_∋_ ; IsInRange ; Image⊆Range
                                              ; IsInRange→IsInImage ; Imagef∋f ; _range ; _image
                                              ; _preimage ; f∈range ; ⌜_⌝ ; Ran ; RRan
                                              ; _preimage≈image ; Dom ; inv ; Inv ; Inv' ; [_]⁻¹
                                              ; ⟦_⟧⁻¹ ; invIsInvʳ ; InvIsInverseʳ ; ⁻¹IsInverseʳ
                                              ; InvIsInverseˡ ; ⁻¹IsInverseˡ )

open import Overture.Func.Injective     using ( IsInjective ; LeftInvPreserves≈ ; module compose
                                              ; ∘-injection ; id-is-injective )
open compose using ( ∘-injective-func )

open import Overture.Func.Surjective    using ( IsSurjective ; SurjectionIsSurjective ; SurjInv
                                              ; SurjInvIsInverseʳ ; epic-factor )

open import Overture.Func.Bijective     using ( IsBijective ; BijInv )


open import Overture.Setoid.Preliminaries using ( preserves≈ )

open import Overture.Setoid.Inverses      using ( Image_∋_ ; Range ; Image⊆Range ; Range⊆Image
                                                ; Inv ; Inv' ; InvIsInv )

open import Overture.Setoid.Injective     using ( IsInjective ; LeftInvPreserves≈ ; ∘-injection )

open import Overture.Setoid.Surjective    using ( IsSurjective ; SurjectionIsSurjective ; RightInv
                                                ; RightInvIsRightInv ; epic-factor )

open import Overture.Setoid.Bijective     using ( IsBijective ; BijInv )


-- RELATIONS  -----------------------------------------------------------------------------------------
open import Relations.Discrete   using (Im_⊆_ ; ker ; kerlift ; ker' ; kernel ; 0[_]
                                       ; _⊑_ ; ⊑-refl ; ⊑-trans ; Op ; π ; eval-rel
                                       ; _preserves_ ; _|:_ ; compatibility-agreement
                                       ; compatibility-agreement' ; arity[_] )

open import Relations.Continuous using ( ar ; Rel ; Rel-syntax ; ΠΡ ; ΠΡ-syntax ; eval-Rel
                                       ; compatible-Rel ; eval-ΠΡ ; compatible-ΠΡ )

open import Relations.Quotients  using ( Equivalence ; ker-IsEquivalence ; kerlift-IsEquivalence
                                       ; [_] ; [_/_] ; Block ; IsBlock ; Quotient ; _/_ ; ⟪_⟫
                                       ; ⌞_⌟ ; []-⊆ ; []-⊇ ; ⊆-[] ; ⊇-[] ; 0[_]IsEquivalence
                                       ; 0[_]Equivalence ; ⟪_∼_⟫-elim ; ≡→⊆ )

-- EQUALITY -----------------------------------------------------------------------------------------
open import Equality.Welldefined    using ( welldef ; swelldef ; funext→swelldef ; SwellDef
                                          ; swelldef' ; funext' ; funext'→swelldef'
                                          ; swelldef'→funext' ; A×A-wd ; Fin2-wd
                                          ; Fin3-wd ; ListA→B ; CurryListA ; CurryListA' )


open import Equality.Truncation     using ( is-center ; is-singleton ; is-prop ; is-prop-valued ; fiber
                                          ; singleton-is-prop ; is-equiv ; hfunext ; is-set ; to-Σ-≡
                                          ; is-embedding ; singleton-type ; invertible ; blk-uip
                                          ; equiv-is-embedding ; monic-is-embedding|Set ; IsRelProp
                                          ; RelProp ; RelPropExt ; IsΠΡProp ; ΠΡProp ; ΠΡPropExt )

open import Equality.Extensionality using ( DFunExt ; _≐_ ; pred-ext ; block-ext ; block-ext|uip )


-- ADJUNCTION -------------------------------------------------------------------------------
open import Adjunction.Closure     using ( Extensive ; IntersectClosed ; ClosureSystem ; ClOp
                                         ; clop→law⇒ ; clop→law⇐ ; clop←law )

open import Adjunction.Galois      using ( Galois ; _⃗_ ; _⃖_ ; ←→≥id ; →←≥id ; →←→⊆→ ; ←→←⊆←
                                         ; ←→Closed ; →←Closed ;  _≐_ ; ≐-iseqv ; PosetOfSubsets
                                         ; 𝒫𝒜 ; 𝒫ℬ ; Rel→Gal )
open import Adjunction.Residuation using ( Residuation ; weak-inverse ; weak-inverse' )


-- ALGEBRAS ------------------------------------------------------------------------------------------
open import Algebras.Basic              using ( Signature ; compatible ; Algebra ; Level-of-Alg
                                              ; Level-of-Carrier ; algebra ; algebra→Algebra
                                              ; Algebra→algebra ; _̂_ ; Lift-alg-op ; Lift-algebra
                                              ; Lift-Alg ; compatible-Rel-alg ; compatible-ΠΡ-alg )

open import Algebras.Products           using ( ⨅ ; ⨅' ; ov ; ℑ ; 𝔄 ; class-product )

open import Algebras.Congruences        using ( IsCongruence ; Con ; IsCongruence→Con
                                              ; Con→IsCongruence ; 0[_]Compatible ; 0Con[_]
                                              ; _╱_ ; 𝟘[_╱_] ; 𝟎[_╱_] ; /-≡ )

open import Algebras.Setoid.Basic       using ( ⟦_⟧ ; Algebroid ; SetoidAlgebra ; _̂_ ; _∙_
                                              ; ov ; 𝕌[_] ; 𝔻[_] ; Level-of-Alg
                                              ; Level-of-Carrier ; Lift-Alg ; Lift-Alg' )

open import Algebras.Setoid.Products    using ( ⨅ ; ℑ ; 𝔄 ; class-product ; ⨅oid ; ℑ'
                                              ; 𝔄' ; class-product' )

open import Algebras.Setoid.Congruences using ( _∣≈_ ; _∣≋_ ; IsCongruence ; Con ; IsCongruence→Con
                                              ; Con→IsCongruence ; _╱_ )


-- HOMOMORPHISMS ------------------------------------------------------------------------------------------
open import Homomorphisms.Basic             using ( compatible-op-map ; is-homomorphism ; hom 
                                                  ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-monomorphism
                                                  ; mon ; is-epimorphism ; epi ; mon-to-hom ; epi-to-hom )

open import Homomorphisms.Properties        using ( ∘-hom ; ∘-is-hom ; Lift-hom )


open import Homomorphisms.Kernels           using ( homker-comp ; kercon ; kerquo ; ker[_⇒_]_↾_
                                                  ; πepi ; πhom ; πker ; ker-in-con )

open import Homomorphisms.Products          using (  ⨅-hom-co ; ⨅-hom ; ⨅-projection-hom )

open import Homomorphisms.Noether           using ( FirstHomTheorem|Set ; FirstIsoTheorem|Set
                                                  ; NoetherHomUnique ; NoetherIsoUnique ; HomFactor
                                                  ; HomFactorEpi )

open import Homomorphisms.Isomorphisms      using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅
                                                  ; Lift-Alg-iso ; Lift-Alg-assoc
                                                  ; Lift-Alg-⨅≅ ; ⨅≅ )

open import Homomorphisms.HomomorphicImages using ( _IsHomImageOf_ ; HomImages ; IsHomImageOfClass
                                                  ; HomImageOfClass ; Lift-epi-is-epi
                                                  ; Lift-Alg-hom-image )

open import Homomorphisms.Func.Basic        using ( ≈preserving ; compatible-map-op ; compatible-map
                                                  ; IsHom ; hom ; IsMon ; mon ; mon-to-hom
                                                  ; IsEpi ; epi ; epi-to-hom )

open import Homomorphisms.Func.Properties   using ( ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; 𝓁𝒾𝒻𝓉∼𝓁ℴ𝓌ℯ𝓇
                                                  ; 𝓁ℴ𝓌ℯ𝓇∼𝓁𝒾𝒻𝓉 ; Lift-hom ; lift-hom-lemma )

open import Homomorphisms.Func.Kernels      using ( HomKerComp ; kercon ; kerquo ; ker[_⇒_]_ ; πepi
                                                  ; πhom ; πker ; ker-in-con )

open import Homomorphisms.Func.Factor     using ( hom-factor )

open import Homomorphisms.Func.Isomorphisms using ( _≅_ ; mkiso ; ≅-refl ; ≅-sym ; ≅-trans
                                                  ; ≅toInjective ; ≅fromInjective ; Lift-≅
                                                  ; Lift-Alg-iso ; Lift-Alg-assoc ; ⨅≅ ; Lift-Alg-⨅≅ )

open import Homomorphisms.Func.HomomorphicImages using ( _IsHomImageOf_ ; HomImages ; HomImageOf[_]
                                                       ; IsHomImageOfClass ; HomImageOfClass
                                                       ; Lift-epi-is-epi ; Lift-Alg-hom-image )



-- TERMS ------------------------------------------------------------------------------------------
open import Terms.Basic               using (Term ; 𝑻 )

open import Terms.Properties          using (free-lift ; lift-hom ; free-unique ; lift-of-epi-is-epi )

open import Terms.Operations          using ( _⟦_⟧ ; free-lift-interp ; term-interp
                                            ; term-gen ; term-gen-agreement ; term-agreement
                                            ; interp-prod ; interp-prod2 ; comm-hom-term
                                            ; _∣:_ ; _[_] ; Substerm ; _[_]t ; subst-lemma
                                            ; subst-theorem )

open import Terms.Func.Basic          using ( _≐_ ; ≐-isRefl ; ≐-isSym ; ≐-isTrans ; ≐-isEquiv
                                            ; TermSetoid ; 𝑻 ; Sub ; _[_] ; module Environment )
open Environment using ( Env ; ⟦_⟧ ; Equal ; isEquiv ; ⟦_⟧s ; substitution )

open import Terms.Func.Properties     using ( free-lift ; free-lift-of-surj-isSurj ; free-lift-func
                                            ; lift-hom ; lift-of-epi-is-epi ; free-unique )


-- SUBALGEBRAS ------------------------------------------------------------------------------------------
open import Subalgebras.Subuniverses     using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub
                                               ; sgIsSmallest ; ⋂s ; sub-term-closed
                                               ; TermImage ; TermImageIsSub ; Y-onlyif-TermImageY
                                               ; SgY-onlyif-TermImageY ; hom-unique )

open import Subalgebras.Subalgebras      using ( _≥_ ; _IsSupalgebraOf_ ; _≤_ ; _IsSubalgebraOf_
                                               ; SubalgebraOf ; Subalgebra ; FirstHomCorollary|Set
                                               ; free-quot-subalg ; _IsSubalgebraOfClass_
                                               ; SubalgebraOfClass )


open import Subalgebras.Properties       using ( ≤-refl ; ≥-refl ; ≤-reflexive ; ≤-trans ; ≥-trans
                                               ; ≤-preorder ; ≥-preorder ; ≤-resp-≅ ; ≅-resp-≥
                                               ; ≥-resp-≅ ; ≅-resp-≤ ; ≤-RESP-≅ ; ≥-RESP-≅ ; ≅-RESP-≤
                                               ; ≅-RESP-≥ ; iso→injective ; ≤-mono ; Lift-is-sub
                                               ; ≤-Lift ; ≥-Lift ; Lift-≤-Lift )


open import Subalgebras.Setoid.Subuniverses using( Subuniverses ; Subuniverse ; Sg ; sgIsSub
                                                 ; sgIsSmallest ; ⋂s ; sub-term-closed
                                                 ; TermImage ; TermImageIsSub ; B-onlyif-TermImageB
                                                 ; SgB-onlyif-TermImageB ; hom-unique )

open import Subalgebras.Setoid.Subalgebras  using ( _≥_ ; _IsSupalgebraOf_ ; _≤_ ; _IsSubalgebraOf_
                                                  ; SubalgebraOf ; Subalgebra
                                                  ; IsSubalgebraREL ; SubalgebraREL ; _≤c_
                                                  ; _IsSubalgebraOfClass_ ; SubalgebraOfClass
                                                  ; SubalgebraOfClass' ; SubalgebrasOfClass )

open import Subalgebras.Setoid.Properties   using ( ≅→≤ ; ≅→≥ ; ≤-refl ; ≥-refl ; ≤-reflexive
                                                  ; ≤-trans ; ≤-TRANS-≅ ; ≥-trans ; ≤-preorder
                                                  ; A≥B×B≅C→A≥C ; A≤B×B≅C→A≤C ; A≅B×B≥C→A≥C
                                                  ; A≅B×B≤C→A≤C ; ≤-mono ; Lift-is-sub ; ≤-Lift
                                                  ; ≥-Lift ; Lift-≤-Lift )


-- VARIETIES ------------------------------------------------------------------------------------------
open import Varieties.EquationalLogic    using ( _⊧_≈_ ; _⊫_≈_ ; Th ; Mod )

open import Varieties.Closure            using ( H ; S ; P ; V ; is-variety ; variety
                                               ; S-mono ; subalgebra→S ; S→subalgebra
                                               ; P-mono ; P-expa ; P-idemp ; Lift-Alg-subP
                                               ; Lift-Alg-subP' ; module Vlift )

open import Varieties.Properties         using ( ⊧-I-invar ; ⊧-Lift-invar ; ⊧-lower-invar
                                               ; ⊧-S-invar ; ⊧-S-class-invar ; ⊧-P-invar
                                               ; ⊧-P-class-invar ; ⊧-P-lift-invar ; ⊧-H-invar
                                               ; ⊧-H-class-invar ; ⊧-H-class-coinvar )

open import Varieties.Preservation       using (S⊆SP ; lemPS⊆SP ; PS⊆SP ; P⊆V ; SP⊆V ; SP⊆V'
                                               ; module class-products-with-maps ; H-id1 ; H-id2
                                               ; S-id1 ; S-id2 ; P-id1 ; P-id2 ; V-id1
                                               ; module Vid' ; V-id1' ; ovu ; lovu ; 𝕍 ; 𝒱
                                               ; class-ids-⇒ ; class-ids ; class-ids-⇐ ; V-id2 )

open import Varieties.FreeAlgebras       using ( 𝓕 ; 𝓕⁺ ; ψ ; ψRel ; ψcompatible ; ψIsEquivalence
                                               ; ψCon ; ℭ ; homℭ ; 𝔽 ; epi𝔽 ; hom𝔽 ; hom𝔽-is-epic
                                               ; ψlemma0 ; ψlemma0-ap ; 𝔽-lift-hom ; X↪𝔽 ; 𝔑
                                               ; hom𝔽-is-lift-hom ; ψlemma1 ; ψlemma2 ; ψlemma3
                                               ; class-models-kernel ; 𝕍𝒦 ; kernel-in-theory
                                               ; 𝔽-ModTh-epi ; 𝔽≤ℭ ; 𝔽∈SP ; 𝔽∈𝕍 ; Birkhoff
                                               ; Birkhoff-converse ; _↠_ )


open import Varieties.Setoid.EquationalLogic using ( Eq ; _⊨_ ; _⊧_ ; Mod ; _⊫_ ; _⊃_ ; _⊢_▹_≈_
                                                   ; module Soundness ; module FreeAlgebra )
open Soundness   using ( sound )
open FreeAlgebra using ( FreeDomain ; FreeInterp ; 𝔽[_] ; σ₀ ; identity ; evaluation ; satisfies
                       ; completeness )

open import Varieties.Setoid.Closure         using ( H ; hbase ; hhimg ; S ; sbase ; ssub ; siso
                                                   ; P ; pbase ; pprod ; piso ; V ; vbase ; vhimg
                                                   ; vssub ; vpprod ; viso ; is-variety ; variety )

open import Varieties.Setoid.FreeAlgebras    using ( ℐ ; ℰ ; epi𝔽 ; hom𝔽 ; hom𝔽-is-epic )


-- GENERAL STRUCTURES ---------------------------------------------------------------------------------
open import Structures.Basic             using ( signature ; structure ; _ʳ_ ; _ᵒ_ ; compatible
                                               ; Lift-op ; Lift-rel ; Lift-Strucˡ ; Lift-Strucʳ
                                               ; Lift-Struc ; siglˡ ; siglʳ ; sigl )

open import Structures.Graphs            using ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom )

open import Structures.Graphs0           using ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom ; _⇛_⇚_ )

open import Structures.Products          using ( ⨅ ; ℓp ; ℑ ; 𝔄 ; class-product )

open import Structures.Congruences       using ( con ; 0[_]compatible ; 0con[_] ; quotient
                                               ; _╱_ ; /≡-elim ; 𝟎[_╱_] )

open import Structures.Homs              using ( preserves ; is-hom-rel ; comm-op ; is-hom-op
                                               ; is-hom ; hom ; hom-alg ; ∘-is-hom-rel
                                               ; ∘-is-hom-op ; ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon
                                               ; mon ; mon→hom ; is-epi ; epi ; epi→hom ; 𝓁𝒾𝒻𝓉
                                               ; 𝓁ℴ𝓌ℯ𝓇 ; 𝓁𝒾𝒻𝓉ˡ ; 𝓁𝒾𝒻𝓉ʳ ; 𝓁ℴ𝓌ℯ𝓇ˡ ; 𝓁ℴ𝓌ℯ𝓇ʳ
                                               ; homker-comp ; kerlift-comp ; kercon ; kerquo
                                               ; ker[_⇒_] ; πepi ; πhom ; πker ; ⨅-hom-co
                                               ; ⨅-hom ; ⨅-projection-hom )

open import Structures.Isos              using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅ˡ
                                               ; Lift-≅ʳ ; Lift-≅ ; Lift-Strucˡ-iso
                                               ; Lift-Struc-iso ; Lift-Struc-assocˡ
                                               ; Lift-Struc-assocʳ ; Lift-Struc-assoc ; ⨅≅
                                               ; Lift-Struc-⨅≅ )

open import Structures.Terms             using ( _⟦_⟧ )

open import Structures.EquationalLogic   using ( _⊧_≈_ ; _⊧_≋_ ; Th ; Mod ; fMod )

open import Structures.Substructures     using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub
                                               ; sgIsSmallest ; ⋂s ; sub-term-closed ; TermImage
                                               ; TermImageIsSub ; B-onlyif-TermImageB
                                               ; SgB-onlyif-TermImageB ; hom-unique ; _≥_
                                               ; _IsSupstructureOf_ ; _≤_ ; _IsSubstructureOf_
                                               ; SubstructureOf ; Substructure ; IsSubstructureREL
                                               ; _≤c_ ; _IsSubstructureOfClass_ ; SubstructureOfClass
                                               ; SubstructureOfClass' ; SubstructuresOfClass )


-- GENERAL STRUCTURES represented as Sigma types (instead of record types) -------------------------
open import Structures.Sigma.Basic       using ( Signature ; Structure ; RStructure ; AStructure
                                               ; Structure→RStructure ; Structure→AStructure
                                               ; _⟦_⟧ᵣ ; _⟦_⟧ₒ ; _ʳ_ ; _ᵒ_ ; Compatible
                                               ; Compatible' ; Lift-op ; Lift-rel
                                               ; Lift-Strucˡ ; Lift-Strucʳ ; Lift-Struc )

open import Structures.Sigma.Products    using ( ⨅ ; ℓp ; ℑ ; 𝔖 ; class-prod )

open import Structures.Sigma.Congruences using ( Con ; 0[_]Compatible ; 0Con[_] ; _╱_ ; /≡-elim
                                               ; 𝟘[_╱_] ; 𝟎[_╱_] )

open import Structures.Sigma.Homs        using ( preserves ; is-hom-rel ; comp-op ; is-hom-op
                                               ; is-hom ; hom ; ∘-is-hom-rel ; ∘-is-hom-op
                                               ; ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon ; mon ; is-epi
                                               ; epi ; mon→hom ; epi→hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇
                                               ; Lift-Hom ; Homker-comp )

open import Structures.Sigma.Isos        using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅
                                               ; Lift-Struc-iso ; ⨅≅ )


-- COMPLEXITY ---------------------------------------------------------------------------------------
open import Complexity.Basic                 using   ()
open import Complexity.CSP                   using   (Constraint ; CSPInstance )


-- EXAMPLES -----------------------------------------------------------------------------------------
open import Examples.Structures.Signatures   using  ( S∅ ; S1 ; S01 ; S001 ; S0001 ; S021 ; S101 ; S111 )
open import Examples.Structures.Basic        using  (SL ; NAE3SAT ; nae3sat )


-- EXERCISES -----------------------------------------------------------------------------------------
open import Exercises.Complexity.FiniteCSP   using  ( module solution-2-1 ; module solution-2-2 )

\end{code}

--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
