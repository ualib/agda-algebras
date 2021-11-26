---
layout: default
title : "Overture.Inverses module"
date : "2021-06-09"
author: "agda-algebras development team"
---

All definitions and theorems in agda-algebras as of 20 Sep 2021.

\begin{code}

-- OVERTURE -----------------------------------------------------------------------------------------
open import Overture.Preliminaries using ( ℓ₁ ; ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; 𝑖𝑑 ; Π ; Π-syntax ; ∃-syntax  )
                                   using ( lift∼lower ; lower∼lift ; _≈_ ; ≡-by-parts ; transport     )

open import Overture.Inverses      using ( Image_∋_ ; Range ; range ; Image⊆Range ; Range⊆Image  )
                                   using ( Imagef∋f ; f∈range ; Inv ; [_]⁻¹ ; InvIsInverseʳ      )
                                   using ( ⁻¹IsInverseʳ ;  InvIsInverseˡ ; ⁻¹IsInverseˡ          )

open import Overture.Injective     using ( id-is-injective ; IsInjective ; ∘-injective )

open import Overture.Surjective    using ( IsSurjective ; onto ; IsSurjective→Surjective          )
                                   using ( Surjective→IsSurjective ; SurjInv ; SurjInvIsInverseʳ  )
                                   using ( epic-factor ; epic-factor-intensional ; proj ; update  )
                                   using ( update-id ; proj-is-onto ; projIsOnto                  )

open import Overture.Transformers  using ( Bijection ; ∣_∣=∣_∣ ; PointwiseBijection ;  ∣_∣≈∣_∣      )
                                   using ( Curry ; Uncurry ; A×A→B≅A→A→B ; A→A→Fin2A ; A→A→Fin2A'   )
                                   using ( A→A→Fin2A-ptws-agree ; A×A→Fin2A ; Fin2A→A×A ; uncurry₀  )
                                   using ( Fin2A~A×A ; A×A~Fin2A-ptws ; A→A~Fin2A-ptws ; CurryFin2  )
                                   using ( UncurryFin2 ; Fin2A ; Fin2A≡ ; CurryFin2~UncurryFin2     )
                                   using ( CurryFin3 ; UncurryFin3 ; Fin2A→B-to-A×A→B               )
                                   using ( A×A→B-to-Fin2A→B ; Fin2A→B~A×A→B                         )

open import Overture.Setoid.Preliminaries using ( _∘_ ; 𝑙𝑖𝑓𝑡 ; lift∼lower ; lower∼lift ; liftFunc )

open import Overture.Setoid.Inverses      using ( Img_∋_ ; Image_∋_ ; IsInRange ; Image⊆Range       )
                                          using ( IsInRange→IsInImage ; Imagef∋f ; _range ; _image  )
                                          using ( _preimage ; f∈range ; ⌜_⌝ ; Ran ; RRan            )
                                          using ( _preimage≈image ; Dom ; inv ; Inv ; Inv' ; [_]⁻¹  )
                                          using ( ⟦_⟧⁻¹ ; invIsInvʳ ; InvIsInverseʳ ; ⁻¹IsInverseʳ  )
                                          using ( InvIsInverseˡ ; ⁻¹IsInverseˡ                      )

open import Overture.Setoid.Injective     using ( IsInjective ; LeftInvPreserves≈ ; module compose  )
                                          using ( ∘-injection ; id-is-injective                     )
open compose using ( ∘-injective-bare )

open import Overture.Setoid.Surjective    using ( IsSurjective ; SurjectionIsSurjective ; SurjInv  )
                                          using ( SurjInvIsInverseʳ ; ∘-IsSurjective ; ∘-epic      )
                                          using ( epic-factor                                      )

open import Overture.Setoid.Bijective     using ( IsBijective ; BijInv )


-- RELATIONS  -----------------------------------------------------------------------------------------
open import Relations.Discrete   using ( Im_⊆_ ; ker ; kerlift ; ker' ; kernel ; 0[_]  )
                                 using ( _⊑_ ; ⊑-refl ; ⊑-trans ; Op ; π ; eval-rel    )
                                 using ( _preserves_ ; _|:_ ; compatibility-agreement  )
                                 using ( compatibility-agreement' ; arity[_]           )

open import Relations.Continuous using ( ar ; Rel ; Rel-syntax ; ΠΡ ; ΠΡ-syntax ; eval-Rel  )
                                 using ( compatible-Rel ; eval-ΠΡ ; compatible-ΠΡ           )

open import Relations.Quotients  using ( Equivalence ; ker-IsEquivalence ; kerlift-IsEquivalence  )
                                 using ( [_] ; [_/_] ; Block ; IsBlock ; Quotient ; _/_ ; ⟪_⟫     )
                                 using ( ⌞_⌟ ; []-⊆ ; []-⊇ ; ⊆-[] ; ⊇-[] ; 0[_]IsEquivalence      )
                                 using ( 0[_]Equivalence ; ⟪_∼_⟫-elim ; ≡→⊆                       )

-- EQUALITY -----------------------------------------------------------------------------------------
open import Equality.Welldefined    using ( welldef ; swelldef ; funext→swelldef ; SwellDef  )
                                    using ( swelldef' ; funext' ; funext'→swelldef'          )
                                    using ( swelldef'→funext' ; A×A-wd ; Fin2-wd             )
                                    using ( Fin3-wd ; ListA→B ; CurryListA ; CurryListA'     )


open import Equality.Truncation     using ( is-center ; is-singleton ; is-prop ; is-prop-valued ; fiber  )
                                    using ( singleton-is-prop ; is-equiv ; hfunext ; is-set ; to-Σ-≡     )
                                    using ( is-embedding ; singleton-type ; invertible ; blk-uip         )
                                    using ( equiv-is-embedding ; monic-is-embedding|Set ; IsRelProp      )
                                    using ( RelProp ; RelPropExt ; IsΠΡProp ; ΠΡProp ; ΠΡPropExt         )

open import Equality.Extensionality using ( DFunExt ; _≐_ ; pred-ext ; block-ext ; block-ext|uip )


-- ADJUNCTION -------------------------------------------------------------------------------
open import Adjunction.Closure     using ( Extensive ; IntersectClosed ; ClosureSystem ; ClOp  )
                                   using ( clop→law⇒ ; clop→law⇐ ; clop←law                    )

open import Adjunction.Galois      using ( Galois ; _⃗_ ; _⃖_ ; ←→≥id ; →←≥id ; →←→⊆→ ; ←→←⊆←     )
                                   using ( ←→Closed ; →←Closed ;  _≐_ ; ≐-iseqv ; PosetOfSubsets  )
                                   using ( 𝒫𝒜 ; 𝒫ℬ ; Rel→Gal                                    )
open import Adjunction.Residuation using ( Residuation ; weak-inverse ; weak-inverse' )


-- ALGEBRAS ------------------------------------------------------------------------------------------
open import Algebras.Basic              using ( Signature ; compatible ; Algebra ; Level-of-Alg    )
                                        using ( Level-of-Carrier ; algebra ; algebra→Algebra       )
                                        using ( Algebra→algebra ; _̂_ ; Lift-alg-op ; Lift-algebra  )
                                        using ( Lift-Alg ; compatible-Rel-alg ; compatible-ΠΡ-alg  )

open import Algebras.Products           using ( ⨅ ; ⨅' ; ov ; ℑ ; 𝔄 ; class-product )

open import Algebras.Congruences        using ( IsCongruence ; Con ; IsCongruence→Con        )
                                        using ( Con→IsCongruence ; 0[_]Compatible ; 0Con[_]  )
                                        using ( _╱_ ; 𝟘[_╱_] ; 𝟎[_╱_] ; /-≡                  )

open import Algebras.Setoid.Basic       using ( ov ; EqArgs ; ⟦_⟧ ; Algebra ; 𝕌[_] ; 𝔻[_]       )
                                      using ( Level-of-Alg ; Level-of-Carrier ; _̂_ ; Lift-Algˡ  )
                                      using ( Lift-Algʳ ; Lift-Alg                              )

open import Algebras.Setoid.Products    using ( ⨅ ; ℑ ; 𝔄 ; class-product ; ProjAlgIsOnto )

open import Algebras.Setoid.Congruences using ( _∣≈_ ; IsCongruence ; Con ; IsCongruence→Con  )
                                      using ( Con→IsCongruence ; _╱_                          )


-- HOMOMORPHISMS ------------------------------------------------------------------------------------------
open import Homomorphisms.Basic             using ( compatible-op-map ; is-homomorphism ; hom ; 𝒾𝒹  )
                                            using ( 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-monomorphism ; mon          )
                                            using ( is-epimorphism ; epi ; mon→hom ; epi→hom        )

open import Homomorphisms.Properties        using ( ∘-hom ; ∘-is-hom ; Lift-hom )

open import Homomorphisms.Kernels           using ( homker-comp ; kercon ; kerquo ; ker[_⇒_]_↾_  )
                                            using ( πepi ; πhom ; πker ; ker-in-con              )

open import Homomorphisms.Products          using ( ⨅-hom-co ; ⨅-hom ; ⨅-projection-hom )

open import Homomorphisms.Noether           using ( FirstHomTheorem|Set ; FirstIsoTheorem|Set  )
                                            using ( FirstHomUnique ; FirstIsoUnique            )

open import Homomorphisms.Factor            using ( HomFactor ; HomFactorEpi )

open import Homomorphisms.Isomorphisms      using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅ ; ⨅≅  )
                                            using ( Lift-Alg-iso ; Lift-Alg-assoc ; Lift-Alg-⨅≅   )

open import Homomorphisms.HomomorphicImages using ( _IsHomImageOf_ ; HomImages ; IsHomImageOfClass  )
                                            using ( HomImageOfClass ; Lift-epi-is-epi               )
                                            using ( Lift-Alg-hom-image                              )

open import Homomorphisms.Setoid.Basic              using ( compatible-map-op ; compatible-map             )
                                                    using ( IsHom ; hom ; IsMon ; mon ; mon→hom ; epi→hom  )
                                                    using ( mon→intohom ; epi→ontohom ; IsEpi ; epi        )

open import Homomorphisms.Setoid.Properties         using ( ToLiftˡ ; FromLiftˡ ; ToFromLiftˡ ; FromToLiftˡ  )
                                                    using ( ToLiftʳ ; FromLiftʳ ; ToFromLiftʳ ; FromToLiftʳ  )
                                                    using ( ∘-is-hom ; ∘-hom ; Lift-homˡ ; Lift-homʳ         )
                                                    using ( lift-hom-lemma ; Lift-hom ; 𝒾𝒹                   )

open import Homomorphisms.Setoid.Kernels            using ( HomKerComp ; kercon ; kerquo ; ker[_⇒_]_  )
                                                    using ( πhom ; πker ; ker-in-con ; πepi           )

open import Homomorphisms.Setoid.Products           using ( ⨅-hom-co )

open import Homomorphisms.Setoid.Noether            using ( FirstHomTheorem ; FirstHomUnique )

open import Homomorphisms.Setoid.Factor             using ( HomFactor ; HomFactorEpi )

open import Homomorphisms.Setoid.Isomorphisms       using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; ≅toInjective  )
                                                    using ( ≅fromInjective ; Lift-≅ˡ ; Lift-≅ʳ ; Lift-≅    )
                                                    using ( Lift-Alg-isoˡ ; Lift-Alg-isoʳ ; Lift-Alg-iso   )
                                                    using ( Lift-assocˡ ; Lift-assocʳ ; Lift-assoc         )
                                                    using ( ⨅≅ ; Lift-Alg-⨅≅ˡ                             )

open import Homomorphisms.Setoid.HomomorphicImages  using ( _IsHomImageOf_ ; HomImages ; HomImageOf[_]  )
                                                    using ( IsHomImageOfClass ; HomImageOfClass         )
                                                    using ( Lift-epi-is-epiˡ ; Lift-Alg-hom-imageˡ      )



-- TERMS ------------------------------------------------------------------------------------------
open import Terms.Basic               using (Term ; 𝑻 )

open import Terms.Properties          using (free-lift ; lift-hom ; free-unique ; lift-of-epi-is-epi )

open import Terms.Operations          using ( _⟦_⟧ ; free-lift-interp ; term-interp  )
                                      using ( term-gen ; term-gen-agreement ; term-agreement  )
                                      using ( interp-prod ; interp-prod2 ; comm-hom-term  )
                                      using ( _∣:_ ; _[_] ; Substerm ; _[_]t ; subst-lemma  )
                                      using ( subst-theorem )

open import Terms.Setoid.Basic        using ( _≐_ ; ≐-isRefl ; ≐-isSym ; ≐-isTrans ; ≐-isEquiv  )
                                      using ( TermSetoid ; 𝑻 ; Sub ; _[_] ; module Environment )
open Environment                      using ( Env ; ⟦_⟧ ; Equal ; isEquiv ; ⟦_⟧s ; substitution )

open import Terms.Setoid.Properties   using ( free-lift ; free-lift-of-surj-isSurj ; free-lift-func  )
                                      using ( lift-hom ; lift-of-epi-is-epi ; free-unique )

open import Terms.Setoid.Operations   using ( free-lift-interp ; term-interp ; term-agreement        )
                                      using ( interp-prod ; comm-hom-term ; _[_] ; Substerm ; _[_]t  )

-- SUBALGEBRAS ------------------------------------------------------------------------------------------
open import Subalgebras.Subuniverses  using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub ; ⋂s  )
                                      using ( sgIsSmallest ; sub-term-closed ; TermImage      )
                                      using ( TermImageIsSub ; Y-onlyif-TermImageY            )
                                      using ( SgY-onlyif-TermImageY ; hom-unique              )

open import Subalgebras.Subalgebras   using ( _≥_ ; _IsSupalgebraOf_ ; _≤_ ; _IsSubalgebraOf_    )
                                      using ( SubalgebraOf ; Subalgebra ; FirstHomCorollary|Set  )
                                      using ( free-quot-subalg ; _IsSubalgebraOfClass_           )
                                      using ( SubalgebraOfClass                                  )

open import Subalgebras.Properties    using ( ≤-refl ; ≥-refl ; ≤-reflexive ; ≤-trans ; ≥-trans     )
                                      using ( ≤-preorder ; ≥-preorder ; ≤-resp-≅ ; ≅-resp-≥         )
                                      using ( ≥-resp-≅ ; ≅-resp-≤ ; ≤-RESP-≅ ; ≥-RESP-≅ ; ≅-RESP-≤  )
                                      using ( ≅-RESP-≥ ; iso→injective ; ≤-mono ; Lift-is-sub       )
                                      using ( ≤-Lift ; ≥-Lift ; Lift-≤-Lift                         )

open import Subalgebras.Setoid.Subuniverses using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub ; ⋂s     )
                                            using ( sgIsSmallest ; sub-term-closed ; TermImage         )
                                            using ( TermImageIsSub ; B-onlyif-TermImageB ; hom-unique  )
                                            using ( SgB-onlyif-TermImageB                              )

open import Subalgebras.Setoid.Subalgebras  using ( _≥_ ; _IsSupalgebraOf_ ; _≤_ ; _IsSubalgebraOf_  )
                                            using ( SubalgebraOf ; Subalgebra ; IsSubalgebraREL      )
                                            using ( SubalgebraREL ; _IsSubalgebraOfClass_ ; _≤c_     )
                                            using ( SubalgebraOfClass ; SubalgebraOfClass' ; mon→≤   )
                                            using ( SubalgebrasOfClass                               )

open import Subalgebras.Setoid.Properties   using ( ≅→≤ ; ≅→≥ ; ≤-refl ; ≥-refl ; ≤-reflexive ; ≥-Lift   )
                                            using ( ≤-trans ; ≤-trans-≅ ; ≥-trans ; ≤-preorder ; ≤-mono  )
                                            using ( A≥B×B≅C→A≥C ; A≤B×B≅C→A≤C ; A≅B×B≥C→A≥C              )
                                            using ( A≅B×B≤C→A≤C ; Lift-is-sub ; ≤-Lift ; Lift-≤-Lift     )


-- VARIETIES ------------------------------------------------------------------------------------------
open import Varieties.EquationalLogic    using ( _⊧_≈_ ; _⊫_≈_ ; Th ; Mod )

open import Varieties.Closure            using ( H ; S ; P ; V ; is-variety ; variety ; S-mono            )
                                         using ( subalgebra→S ; S→subalgebra ; P-mono ; P-expa            )
                                         using ( P-idemp ; Lift-Alg-subP ; Lift-Alg-subP' ; module Vlift  )

open import Varieties.Properties         using ( ⊧-I-invar ; ⊧-Lift-invar ; ⊧-lower-invar ; ⊧-S-invar         )
                                         using ( ⊧-S-class-invar ; ⊧-P-class-invar ; ⊧-P-lift-invar           )
                                         using ( ⊧-P-invar ; ⊧-H-invar ; ⊧-H-class-invar ; ⊧-H-class-coinvar  )

open import Varieties.Preservation       using ( S⊆SP ; lemPS⊆SP ; PS⊆SP ; P⊆V ; SP⊆V ; SP⊆V'  )
                                         using ( module class-products-with-maps ; H-id1 ; H-id2  )
                                         using ( S-id1 ; S-id2 ; P-id1 ; P-id2 ; V-id1  )
                                         using ( module Vid' ; V-id1' ; ovu ; lovu ; 𝕍 ; 𝒱  )
                                         using ( class-ids-⇒ ; class-ids ; class-ids-⇐ ; V-id2 )

open import Varieties.FreeAlgebras       using ( 𝓕 ; 𝓕⁺ ; ψ ; ψRel ; ψcompatible ; ψIsEquivalence  )
                                         using ( ψCon ; ℭ ; homℭ ; 𝔽 ; epi𝔽 ; hom𝔽 ; hom𝔽-is-epic  )
                                         using ( ψlemma0 ; ψlemma0-ap ; 𝔽-lift-hom ; X↪𝔽 ; 𝔑  )
                                         using ( hom𝔽-is-lift-hom ; ψlemma1 ; ψlemma2 ; ψlemma3  )
                                         using ( class-models-kernel ; 𝕍𝒦 ; kernel-in-theory  )
                                         using ( 𝔽-ModTh-epi ; 𝔽≤ℭ ; 𝔽∈SP ; 𝔽∈𝕍 ; Birkhoff  )
                                         using ( Birkhoff-converse ; _↠_ )


open import Varieties.Setoid.EquationalLogic  using ( _⊧_≈_ ; _⊫_≈_ ; Th ; Th' ; ℐ ; ℰ ; Mod ; Modᵗ )

open import Varieties.Setoid.SoundAndComplete using ( Eq ; _⊨_ ; _⊧_ ; Mod ; _⊫_ ; _⊃_ ; _⊢_▹_≈_  )
                                             using ( module Soundness ; module FreeAlgebra )
open Soundness    using ( sound )
open FreeAlgebra  using ( FreeDomain ; FreeInterp ; 𝔽[_] ; σ₀ ; identity ; evaluation ; satisfies  )
                  using ( completeness )

open import Varieties.Setoid.Closure        using ( Level-closure ; Lift-closed ; H ; S ; P ; SP   )
                                            using ( V ; is-variety ; variety ; S-mono ; S-idem     )
                                            using ( H-expa ; S-expa ; P-mono ; P-expa ; V-expa     )
                                            using ( S-≅ ; V-≅ ; V-≅-lc ; classP ; classSP          )
                                            using ( classHSP ; classS ; classK ; LevelClosure-S    )
                                            using ( S-LevelClosure ; S-Lift-lemma ; P-Lift-closed  )

open import Varieties.Setoid.Properties     using ( ⊧-I-invar ; ⊧-Lift-invar ; ⊧-lower-invar      )
                                            using ( ⊧-S-invar ; ⊧-S-class-invar ; ⊧-P-invar       )
                                            using ( ⊧-P-class-invar ; ⊧-P-lift-invar ; ⊧-H-invar  )

open import Varieties.Setoid.Preservation   using ( S⊆SP ; P⊆SP ; P⊆HSP ; P⊆V ; SP⊆V ; PS⊆SP       )
                                            using ( H-id1 ; H-id2 ; S-id1 ; S-id2 ; P-id1 ; P-id2  )
                                            using ( V-id1 ; V-id2 ; Lift-id1 ; classIds-⊆-VIds     )
                                            using ( VIds-⊆-classIds                                )

open import Varieties.Setoid.FreeAlgebras   using ( module FreeHom ; 𝔽-ModTh-epi ; 𝔽-ModTh-epi-lift )
open FreeHom                                using ( ℐ ; ℰ ; ℰ⊢[_]▹Th𝒦 ; epi𝔽[_] ; hom𝔽[_]           )
                                            using ( hom𝔽[_]-is-epic ; class-models-kernel           )
                                            using ( kernel-in-theory ; 𝒦⊫→ℰ⊢                        )

open import Varieties.Setoid.HSP            using ( ℑ⁺ ; 𝔄⁺ ; ℭ ; skEqual ; AllEqual⊆ker𝔽 ; homℭ  )
                                            using ( ker𝔽⊆kerℭ ; hom𝔽ℭ ; kerℭ⊆ker𝔽 ; mon𝔽ℭ ; 𝔽≤ℭ   )
                                            using ( SP𝔽 ; Birkhoff ; Birkhoff-converse            )

-- GENERAL STRUCTURES ---------------------------------------------------------------------------------
open import Structures.Basic                using ( signature ; structure ; _ʳ_ ; _ᵒ_ ; compatible  )
                                            using ( Lift-op ; Lift-rel ; Lift-Strucˡ ; Lift-Strucʳ  )
                                            using ( Lift-Struc ; siglˡ ; siglʳ ; sigl               )

open import Structures.Graphs               using ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom )

open import Structures.Graphs0              using ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom ; _⇛_⇚_ )

open import Structures.Products             using ( ⨅ ; ℓp ; ℑ ; 𝔄 ; class-product )

open import Structures.Congruences          using ( con ; 0[_]compatible ; 0con[_] ; quotient  )
                                            using ( _╱_ ; /≡-elim ; 𝟎[_╱_]                     )

open import Structures.Homs                 using ( preserves ; is-hom-rel ; comm-op ; is-hom-op   )
                                            using ( is-hom ; hom ; hom-alg ; ∘-is-hom-rel          )
                                            using ( ∘-is-hom-op ; ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon   )
                                            using ( mon ; mon→hom ; is-epi ; epi ; epi→hom ; 𝓁𝒾𝒻𝓉  )
                                            using ( 𝓁ℴ𝓌ℯ𝓇 ; 𝓁𝒾𝒻𝓉ˡ ; 𝓁𝒾𝒻𝓉ʳ ; 𝓁ℴ𝓌ℯ𝓇ˡ ; 𝓁ℴ𝓌ℯ𝓇ʳ        )
                                            using ( homker-comp ; kerlift-comp ; kercon ; kerquo   )
                                            using ( ker[_⇒_] ; πepi ; πhom ; πker ; ⨅-hom-co       )
                                            using ( ⨅-hom ; ⨅-projection-hom                       )

open import Structures.Isos                 using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅ˡ   )
                                            using ( Lift-≅ʳ ; Lift-≅ ; Lift-Strucˡ-iso         )
                                            using ( Lift-Struc-iso ; Lift-Struc-assocˡ         )
                                            using ( Lift-Struc-assocʳ ; Lift-Struc-assoc ; ⨅≅  )
                                            using ( Lift-Struc-⨅≅                              )

open import Structures.Terms                using ( _⟦_⟧ )

open import Structures.EquationalLogic      using ( _⊧_≈_ ; _⊧_≋_ ; Th ; Mod ; fMod )

open import Structures.Substructures        using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub             )
                                            using ( sgIsSmallest ; ⋂s ; sub-term-closed ; TermImage       )
                                            using ( TermImageIsSub ; B-onlyif-TermImageB                  )
                                            using ( SgB-onlyif-TermImageB ; hom-unique ; _≥_              )
                                            using ( _IsSupstructureOf_ ; _≤_ ; _IsSubstructureOf_         )
                                            using ( SubstructureOf ; Substructure ; IsSubstructureREL     )
                                            using ( _≤c_ ; _IsSubstructureOfClass_ ; SubstructureOfClass  )
                                            using ( SubstructureOfClass' ; SubstructuresOfClass           )


-- GENERAL STRUCTURES represented as Sigma types (instead of record types) -------------------------
open import Structures.Sigma.Basic          using ( Signature ; Structure ; RStructure ; AStructure         )
                                            using ( Structure→RStructure ; Structure→AStructure ; _⟦_⟧ᵣ     )
                                            using ( _⟦_⟧ₒ ; _ʳ_ ; _ᵒ_ ; Compatible ; Compatible' ; Lift-op  )
                                            using ( Lift-rel ; Lift-Strucˡ ; Lift-Strucʳ ; Lift-Struc       )

open import Structures.Sigma.Products       using ( ⨅ ; ℓp ; ℑ ; 𝔖 ; class-prod )

open import Structures.Sigma.Congruences    using ( Con ; 0[_]Compatible ; 0Con[_] ; _╱_ ; /≡-elim  )
                                            using ( 𝟘[_╱_] ; 𝟎[_╱_]                                 )

open import Structures.Sigma.Homs           using ( preserves ; is-hom-rel ; comp-op ; is-hom-op ; is-hom  )
                                            using ( hom ; ∘-is-hom-rel ; ∘-is-hom-op ; ∘-is-hom ; ∘-hom    )
                                            using ( 𝒾𝒹 ; is-mon ; mon ; is-epi ; epi ; mon→hom ; epi→hom   )
                                            using ( 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; Lift-Hom ; Homker-comp                  )

open import Structures.Sigma.Isos           using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅  )
                                            using ( Lift-Struc-iso ; ⨅≅                      )

-- CATS ---------------------------------------------------------------------------------------
open import Categories.Functors             using ( Functor₀ ; [_]₀ ; Functor ; [_]_ ; μ_ ; list  )
                                            using ( L ; List ; Option ; _[_] ; _⟦_⟧               )

-- COMPLEXITY ---------------------------------------------------------------------------------------
open import Complexity.Basic                using ()
open import Complexity.CSP                  using ( Constraint ; CSPInstance )


-- EXAMPLES -----------------------------------------------------------------------------------------
open import Examples.Structures.Signatures  using ( S∅ ; S1 ; S01 ; S001 ; S0001 ; S021 ; S101 ; S111  )

open import Examples.Structures.Basic       using (SL ; NAE3SAT ; nae3sat )

open import Examples.Categories.Functors    using ( L₀ ; l₀ ; L₁ ; l₁ ; L₃ ; l₃ ; L₀≡none ; l₀≡none        )
                                            using ( L₁[0]≡some3 ; L₁[n>0]≡none ; l₁⟦n>0⟧≡none ; ℓ₁         )
                                            using ( L₃[0]≡some1 ; l₃⟦0⟧≡some1 ; L₃[0]≢some2 ; l₃[0]≢some2  )


-- EXERCISES -----------------------------------------------------------------------------------------
open import Exercises.Complexity.FiniteCSP  using  ( module solution-2-1 ; module solution-2-2 )

\end{code}

--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
