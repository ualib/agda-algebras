---
layout: default
title : "Overture.Inverses module"
date : "2021-06-09"
author: "agda-algebras development team"
---

All definitions and theorems in agda-algebras as of 9 Oct 2022.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


-- ================================================================================================
-- ===============================  Version 1  ====================================================
-- Ver. 1 of the agda-algebras library was based on "bare" types
-- (as opposed to types with extra structure, e.g., setoids or HITs)
-- Version 1 included the submodules of the Base module.
-- ================================================================================================

-- OVERTURE -----------------------------------------------------------------------------------------
open import
 Overture.Basic               using ( ℓ₁ ; 𝟚 ; 𝟛 ; ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; 𝑖𝑑 ; ∃-syntax )
                              using ( Π ; Π-syntax ; lift∼lower ; lower∼lift ; _≈_ )
                              using ( ≈IsEquivalence ; ≡-by-parts ; transport )

open import
 Overture.Signatures          using ( 𝓞 ; 𝓥 ; Signature ; Level-of-Signature )

open import
 Overture.Operations          using ( Op ; π ; arity[_] )


open import
 Base.Functions.Inverses      using ( Image_∋_ ; Range ; range ; Image⊆Range ; Range⊆Image  )
                              using ( Imagef∋f ; f∈range ; Inv ; [_]⁻¹ ; InvIsInverseʳ      )
                              using ( ⁻¹IsInverseʳ ;  InvIsInverseˡ ; ⁻¹IsInverseˡ          )
open import
 Base.Functions.Injective     using ( id-is-injective ; IsInjective ; ∘-injective )
open import
 Base.Functions.Surjective    using ( IsSurjective ; onto ; IsSurjective→Surjective          )
                              using ( Surjective→IsSurjective ; SurjInv ; SurjInvIsInverseʳ  )
                              using ( epic-factor ; epic-factor-intensional ; proj ; update  )
                              using ( update-id ; proj-is-onto ; projIsOnto                  )
open import
 Base.Functions.Transformers  using ( Bijection ; ∣_∣=∣_∣ ; PointwiseBijection ; ∣_∣≈∣_∣     )
                              using ( Curry ; Uncurry ; A×A→B≅A→A→B ; A→A→Fin2A ; A→A→Fin2A' )
                              using ( A→A→Fin2A-ptws-agree ; A×A→Fin2A ; Fin2A→A×A           )
                              using ( Fin2A~A×A ; A×A~Fin2A-ptws ; A→A~Fin2A-ptws            )
                              using ( UncurryFin2 ; Fin2A ; Fin2A≡ ; CurryFin2~UncurryFin2   )
                              using ( CurryFin3 ; UncurryFin3 ; Fin2A→B-to-A×A→B ; uncurry₀  )
                              using ( A×A→B-to-Fin2A→B ; Fin2A→B~A×A→B ; CurryFin2           )

-- RELATIONS  -------------------------------------------------------------------------------------------
open import
 Base.Relations.Discrete    using ( Im_⊆_ ; ker ; kerlift ; ker' ; kernel ; 0[_] ; _⊑_  )
                            using ( ⊑-refl ; ⊑-trans ; eval-rel ; _preserves_ ; _|:_    )
                            using ( compatibility-agreement ; compatibility-agreement'  )
open import
 Base.Relations.Continuous  using ( ar ; Rel ; Rel-syntax ; REL ; REL-syntax ; eval-Rel  )
                            using ( compatible-Rel ; eval-REL ; compatible-REL           )
open import
 Base.Relations.Quotients   using ( Equivalence ; ker-IsEquivalence ; kerlift-IsEquivalence  )
                            using ( [_] ; [_/_] ; Block ; IsBlock ; Quotient ; _/_ ; ⟪_⟫     )
                            using ( ⌞_⌟ ; []-⊆ ; []-⊇ ; ⊆-[] ; ⊇-[] ; 0[_]IsEquivalence      )
                            using ( 0[_]Equivalence ; ⟪_∼_⟫-elim ; ≡→⊆                       )
-- EQUALITY ---------------------------------------------------------------------------------------------
open import
 Base.Equality.Welldefined     using ( welldef ; swelldef ; funext→swelldef ; SwellDef  )
                               using ( swelldef' ; funext' ; funext'→swelldef'          )
                               using ( swelldef'→funext' ; A×A-wd ; Fin2-wd             )
                               using ( Fin3-wd ; ListA→B ; CurryListA ; CurryListA'     )
open import
 Base.Equality.Truncation      using ( is-center ; is-singleton ; is-prop ; is-prop-valued  )
                               using ( fiber ; singleton-is-prop ; is-equiv ; hfunext       )
                               using ( is-set ; to-Σ-≡ ; is-embedding ; singleton-type      )
                               using ( invertible ; blk-uip ; equiv-is-embedding            )
                               using ( monic-is-embedding|Set ; IsRelProp ; RELPropExt      )
                               using ( RelProp ; RelPropExt ; IsRELProp ; RELProp           )
open import
 Base.Equality.Extensionality  using ( DFunExt ; _≐_ ; pred-ext ; block-ext ; block-ext|uip )

-- BASE.ADJUNCTION --------------------------------------------------------------------------------------
open import
 Base.Adjunction.Closure      using ( Extensive ; IntersectClosed ; ClosureSystem ; ClOp  )
                              using ( clop→law⇒ ; clop→law⇐ ; clop←law                    )
open import
 Base.Adjunction.Galois       using ( Galois ; _⃗_ ; _⃖_ ; ←→≥id ; →←≥id ; →←→⊆→ ; ←→←⊆←     )
                              using ( ←→Closed ; →←Closed ;  _≐_ ; ≐-iseqv ; PosetOfSubsets  )
                              using ( 𝒫𝒜 ; 𝒫ℬ ; Rel→Gal                                    )
open import
 Base.Adjunction.Residuation  using ( Residuation ; weak-inverse ; weak-inverse' )

-- BASE.ALGEBRAS ----------------------------------------------------------------------------------------
open import
 Base.Algebras.Basic        using ( compatible ; Algebra ; Level-of-Alg ; Level-of-Carrier  )
                            using ( algebra ; algebra→Algebra ; Algebra→algebra ; _̂_        )
                            using ( Lift-alg-op ; Lift-algebra ; Lift-Alg                   )
                            using ( compatible-Rel-alg ; compatible-REL-alg                 )
open import
 Base.Algebras.Products     using ( ⨅ ; ⨅' ; ov ; ℑ ; 𝔄 ; class-product )
open import
 Base.Algebras.Congruences  using ( IsCongruence ; Con ; IsCongruence→Con        )
                            using ( Con→IsCongruence ; 0[_]Compatible ; 0Con[_]  )
                            using ( _╱_ ; 𝟘[_╱_] ; 𝟎[_╱_] ; /-≡                  )

-- BASE.HOMOMORPHISMS -----------------------------------------------------------------------------------
open import
 Base.Homomorphisms.Basic              using ( compatible-op-map ; is-homomorphism ; hom  )
                                       using ( 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-monomorphism ; mon ; 𝒾𝒹  )
                                       using ( is-epimorphism ; epi ; mon→hom ; epi→hom   )
open import
 Base.Homomorphisms.Properties         using ( ∘-hom ; ∘-is-hom ; Lift-hom )
open import
 Base.Homomorphisms.Kernels            using ( homker-comp ; kercon ; kerquo ; ker[_⇒_]_↾_  )
                                       using ( πepi ; πhom ; πker ; ker-in-con              )
open import
 Base.Homomorphisms.Products           using ( ⨅-hom-co ; ⨅-hom ; ⨅-projection-hom )
open import
 Base.Homomorphisms.Noether            using ( FirstHomTheorem|Set ; FirstIsoTheorem|Set  )
                                       using ( FirstHomUnique ; FirstIsoUnique            )
open import
 Base.Homomorphisms.Factor             using ( HomFactor ; HomFactorEpi )
open import
 Base.Homomorphisms.Isomorphisms       using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅ ; ⨅≅  )
                                       using ( Lift-Alg-iso ; Lift-Alg-assoc ; Lift-Alg-⨅≅   )
open import
 Base.Homomorphisms.HomomorphicImages  using ( _IsHomImageOf_ ; HomImages              )
                                       using ( HomImageOfClass ; Lift-epi-is-epi       )
                                       using ( Lift-Alg-hom-image ; IsHomImageOfClass  )

-- BASE.TERMS -------------------------------------------------------------------------------------------
open import
 Base.Terms.Basic       using (Term ; 𝑻 )
open import
 Base.Terms.Properties  using (free-lift ; lift-hom ; free-unique ; lift-of-epi-is-epi )
open import
 Base.Terms.Operations  using ( _⟦_⟧ ; free-lift-interp ; term-interp ; term-gen ; _∣:_  )
                        using ( term-gen-agreement ; term-agreement  ; _[_]  ; _[_]t     )
                        using ( interp-prod ; interp-prod2 ; comm-hom-term               )
                        using ( Substerm ; subst-lemma ; subst-theorem                   )

-- BASE.SUBALGEBRAS ------------------------------------------------------------------------------------------
open import
 Base.Subalgebras.Subuniverses  using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub ; ⋂s  )
                                using ( sgIsSmallest ; sub-term-closed ; TermImage      )
                                using ( TermImageIsSub ; Y-onlyif-TermImageY            )
                                using ( SgY-onlyif-TermImageY ; hom-unique              )
open import
 Base.Subalgebras.Subalgebras   using ( _≥_ ; _IsSupalgebraOf_ ; _≤_ ; _IsSubalgebraOf_    )
                                using ( SubalgebraOf ; Subalgebra ; FirstHomCorollary|Set  )
                                using ( free-quot-subalg ; _IsSubalgebraOfClass_           )
                                using ( SubalgebraOfClass                                  )
open import
 Base.Subalgebras.Properties    using ( ≤-refl ; ≥-refl ; ≤-reflexive ; ≤-trans ; ≥-trans  )
                                using ( ≤-preorder ; ≥-preorder ; ≤-resp-≅ ; ≅-resp-≥      )
                                using ( ≥-resp-≅ ; ≅-resp-≤ ; ≤-RESP-≅ ; ≥-RESP-≅          )
                                using ( ≅-RESP-≥ ; iso→injective ; ≤-mono ; Lift-is-sub    )
                                using ( ≤-Lift ; ≥-Lift ; Lift-≤-Lift ;  ≅-RESP-≤          )

-- BASE.VARIETIES ------------------------------------------------------------------------------------------
open import
 Base.Varieties.EquationalLogic  using ( _⊧_≈_ ; _⊫_≈_ ; Th ; Mod )
open import
 Base.Varieties.Closure          using ( H ; S ; P ; V ; is-variety ; variety ; S-mono  )
                                 using ( subalgebra→S ; S→subalgebra ; P-mono ; P-expa  )
                                 using ( P-idemp ; Lift-Alg-subP ; Lift-Alg-subP'       )
                                 using ( module Vlift                                   )
open import
 Base.Varieties.Properties       using ( ⊧-I-invar ; ⊧-Lift-invar ; ⊧-lower-invar            )
                                 using ( ⊧-S-class-invar ; ⊧-P-class-invar ; ⊧-P-lift-invar  )
                                 using ( ⊧-P-invar ; ⊧-H-invar ; ⊧-H-class-invar             )
                                 using ( ⊧-H-class-coinvar ; ⊧-S-invar                       )
open import
 Base.Varieties.Preservation     using ( S⊆SP ; lemPS⊆SP ; PS⊆SP ; P⊆V ; SP⊆V ; SP⊆V'     )
                                 using ( module class-products-with-maps ; H-id1 ; H-id2  )
                                 using ( S-id1 ; S-id2 ; P-id1 ; P-id2 ; V-id1            )
                                 using ( module Vid' ; V-id1' ; ovu ; lovu ; 𝕍 ; 𝒱        )
                                 using ( class-ids-⇒ ; class-ids ; class-ids-⇐ ; V-id2    )
open import
 Base.Varieties.FreeAlgebras     using ( 𝓕 ; 𝓕⁺ ; ψ ; ψRel ; ψcompatible ; ψIsEquivalence  )
                                 using ( ψCon ; ℭ ; homℭ ; 𝔽 ; epi𝔽 ; hom𝔽 ; hom𝔽-is-epic  )
                                 using ( ψlemma0 ; ψlemma0-ap ; 𝔽-lift-hom ; X↪𝔽 ; 𝔑       )
                                 using ( hom𝔽-is-lift-hom ; ψlemma1 ; ψlemma2 ; ψlemma3    )
                                 using ( class-models-kernel ; 𝕍𝒦 ; kernel-in-theory       )
                                 using ( 𝔽-ModTh-epi ; 𝔽≤ℭ ; 𝔽∈SP ; 𝔽∈𝕍 ; Birkhoff         )
                                 using ( Birkhoff-converse ; _↠_                           )
open import
 Base.Varieties.Invariants       using ( AlgebraicInvariant )



-- BASE.STRUCTURES ---------------------------------------------------------------------------------
open import
 Base.Structures.Basic            using ( signature ; structure ; _ʳ_ ; _ᵒ_ ; compatible  )
                                  using ( Lift-op ; Lift-rel ; Lift-Strucˡ ; Lift-Strucʳ  )
                                  using ( Lift-Struc ; siglˡ ; siglʳ ; sigl               )
open import
 Base.Structures.Graphs           using ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom )
open import
 Base.Structures.Graphs0          using ( Gr-sig ; Gr ; hom→Grhom ; Grhom→hom ; _⇛_⇚_ )
open import
 Base.Structures.Products         using ( ⨅ ; ℓp ; ℑ ; 𝔄 ; class-product )
open import
 Base.Structures.Congruences      using ( con ; 0[_]compatible ; 0con[_] ; quotient  )
                                  using ( _╱_ ; /≡-elim ; 𝟎[_╱_]                     )
open import
 Base.Structures.Homs             using ( preserves ; is-hom-rel ; comm-op ; is-hom-op   )
                                  using ( is-hom ; hom ; hom-alg ; ∘-is-hom-rel          )
                                  using ( ∘-is-hom-op ; ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon   )
                                  using ( mon ; mon→hom ; is-epi ; epi ; epi→hom ; 𝓁𝒾𝒻𝓉  )
                                  using ( 𝓁ℴ𝓌ℯ𝓇 ; 𝓁𝒾𝒻𝓉ˡ ; 𝓁𝒾𝒻𝓉ʳ ; 𝓁ℴ𝓌ℯ𝓇ˡ ; 𝓁ℴ𝓌ℯ𝓇ʳ        )
                                  using ( homker-comp ; kerlift-comp ; kercon ; kerquo   )
                                  using ( ker[_⇒_] ; πepi ; πhom ; πker ; ⨅-hom-co       )
                                  using ( ⨅-hom ; ⨅-projection-hom                       )
open import
 Base.Structures.Isos             using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅ˡ ; ⨅≅  )
                                  using ( Lift-≅ ; Lift-Strucˡ-iso ; Lift-Struc-⨅≅       )
                                  using ( Lift-≅ʳ ; Lift-Struc-iso ; Lift-Struc-assocˡ   )
                                  using ( Lift-Struc-assocʳ ; Lift-Struc-assoc           )
open import
 Base.Structures.Terms            using ( _⟦_⟧ )
open import
 Base.Structures.EquationalLogic  using ( _⊧_≈_ ; _⊧_≋_ ; Th ; Mod ; fMod )
open import
 Base.Structures.Substructures    using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub          )
                                  using ( sgIsSmallest ; ⋂s ; sub-term-closed ; TermImage    )
                                  using ( TermImageIsSub ; B-onlyif-TermImageB ; _≥_ ; _≤_   )
                                  using ( SgB-onlyif-TermImageB ; hom-unique ; _≤c_          )
                                  using ( _IsSupstructureOf_ ; _IsSubstructureOf_            )
                                  using ( SubstructureOf ; Substructure ; IsSubstructureREL  )
                                  using ( _IsSubstructureOfClass_ ; SubstructureOfClass      )
                                  using ( SubstructureOfClass' ; SubstructuresOfClass        )


-- BASE.STRUCTURES.SIGMA (represented as Sigma types, instead of record types) -------------------------
open import
 Base.Structures.Sigma.Basic        using ( Signature ; Structure ; RStructure             )
                                    using ( AStructure ; Structure→RStructure ; _ᵒ_        )
                                    using ( Structure→AStructure ; _⟦_⟧ᵣ ; _⟦_⟧ₒ ; _ʳ_     )
                                    using ( Compatible ; Compatible' ; Lift-op ; Lift-rel  )
                                    using ( Lift-Strucˡ ; Lift-Strucʳ ; Lift-Struc         )
open import
 Base.Structures.Sigma.Products     using ( ⨅ ; ℓp ; ℑ ; 𝔖 ; class-prod )
open import
 Base.Structures.Sigma.Congruences  using ( Con ; 0[_]Compatible ; 0Con[_] ; _╱_ ; /≡-elim  )
                                    using ( 𝟘[_╱_] ; 𝟎[_╱_]                                 )
open import
 Base.Structures.Sigma.Homs         using ( preserves ; is-hom-rel ; comp-op ; is-hom-op   )
                                    using ( is-hom ; hom ; ∘-is-hom-rel ; ∘-is-hom-op      )
                                    using ( ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon ; mon ; is-epi  )
                                    using ( epi ; mon→hom ; epi→hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇         )
                                    using ( Lift-Hom ; Homker-comp                         )
open import
 Base.Structures.Sigma.Isos         using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅  )
                                    using ( Lift-Struc-iso ; ⨅≅                      )

-- BASE.CATEGORIES ------------------------------------------------------------------------------------
open import
 Base.Categories.Functors           using ( Functor₀ ; [_]₀ ; Functor ; [_]_ ; μ_ ; list  )
                                    using ( L ; List ; Option ; _[_] ; _⟦_⟧               )

-- BASE.COMPLEXITY ------------------------------------------------------------------------------------
open import
 Base.Complexity.Basic              using ()
open import
 Base.Complexity.CSP                using ( Constraint ; CSPInstance )





-- ==========================================================================================
-- ====================  Version 2 of the library  ==========================================
-- Ver. 2 of the agda-algebras library is based mainly on setoids and
-- includes the following new submodules of the Setoid module.
-- ==========================================================================================

-- SETOID.OVERTURE --------------------------------------------------------------------------

open import
 Setoid.Functions.Basic        using ( 𝑖𝑑 ; 𝑙𝑖𝑓𝑡 ; lift∼lower ; lower∼lift ; liftFunc ) -- _∘_ ;
open import
 Setoid.Functions.Inverses     using ( Img_∋_ ; Image_∋_ ; IsInRange ; Image⊆Range       )
                               using ( IsInRange→IsInImage ; Imagef∋f ; _range ; _image  )
                               using ( _preimage ; f∈range ; ⌜_⌝ ; Ran ; RRan            )
                               using ( _preimage≈image ; Dom ; inv ; Inv ; Inv' ; [_]⁻¹  )
                               using ( ⟦_⟧⁻¹ ; invIsInvʳ ; InvIsInverseʳ ; ⁻¹IsInverseʳ  )
                               using ( InvIsInverseˡ ; ⁻¹IsInverseˡ                      )
open import
 Setoid.Functions.Injective    using ( IsInjective ; LeftInvPreserves≈ ; module compose  )
                               using ( id-is-injective                     ) -- ∘-injection ;
open compose                   using ( ∘-injective-bare                                  )
open import
 Setoid.Functions.Surjective   using ( IsSurjective ; SurjectionIsSurjection ; SurjInv  )
                               using ( SurjInvIsInverseʳ ; ∘-epic      ) -- ∘-IsSurjective ;
                               using ( epic-factor                                      )
open import
 Setoid.Functions.Bijective    using ( IsBijective ; BijInv )




-- SETOID.RELATIONS --------------------------------------------------------------------------
open import
 Setoid.Relations.Discrete     using ( function-equality ; Im_⊆_ ; fker ; fkerPred  )
                               using ( fkerlift ; 0rel                              )

open import
 Setoid.Relations.Quotients    using ( ker-IsEquivalence ; IsBlock ; Quotient ; _/_ ; ⟪_⟫  )
                               using ( ⟪_∼_⟫-intro ; ⟪_∼_⟫-elim ; ≡→⊆                      )

-- SETOID.ALGEBRAS --------------------------------------------------------------------------
open import
 Setoid.Algebras.Basic       using ( ov ; EqArgs ; ⟨_⟩ ; Algebra ; 𝕌[_] ; 𝔻[_]         )
                             using ( Level-of-Alg ; Level-of-Carrier ; _̂_ ; Lift-Algˡ  )
                             using ( Lift-Algʳ ; Lift-Alg                              )
open import
 Setoid.Algebras.Products    using ( ⨅ ; ℑ ; 𝔄 ; class-product ; ProjAlgIsOnto )
open import
 Setoid.Algebras.Congruences using ( _∣≈_ ; IsCongruence ; Con ; IsCongruence→Con  )
                             using ( Con→IsCongruence ; _╱_                        )


-- SETOID.HOMOMORPHISMS ---------------------------------------------------------------------
open import
 Setoid.Homomorphisms.Basic              using ( compatible-map-op ; compatible-map ; IsEpi  )
                                         using ( IsHom ; hom ; IsMon ; mon ; mon→hom ; epi   )
                                         using ( epi→hom ; mon→intohom ; epi→ontohom         )
open import
 Setoid.Homomorphisms.Properties         using ( ToLiftˡ ; FromLiftˡ ; ToFromLiftˡ      )
                                         using ( FromToLiftˡ ; ToLiftʳ ; FromLiftʳ      )
                                         using ( ToFromLiftʳ ; FromToLiftʳ  ) -- ; ∘-is-hom  )
                                         using ( Lift-homˡ ; Lift-homʳ      ) -- ∘-hom ;     )
                                         using ( lift-hom-lemma ; Lift-hom ; 𝒾𝒹         )
open import
 Setoid.Homomorphisms.Kernels            using ( HomKerComp ; kercon ; kerquo ; ker[_⇒_]_  )
                                         using ( πhom ; πker ; ker-in-con ; πepi           )
open import
 Setoid.Homomorphisms.Products           using ( ⨅-hom-co )
open import
 Setoid.Homomorphisms.Noether            using ( FirstHomTheorem ; FirstHomUnique )
open import
 Setoid.Homomorphisms.Factor             using ( HomFactor ; HomFactorEpi )
open import
 Setoid.Homomorphisms.Isomorphisms       using ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans              )
                                         using ( ≅toInjective ; ≅fromInjective ; Lift-≅ˡ     )
                                         using ( Lift-≅ʳ ; Lift-≅ ; Lift-Alg-isoˡ            )
                                         using ( Lift-Alg-isoʳ ; Lift-Alg-iso ; Lift-assocˡ  )
                                         using ( Lift-assocʳ ; Lift-assoc ; ⨅≅               )
                                         using ( Lift-Alg-⨅≅ˡ                                )
open import
 Setoid.Homomorphisms.HomomorphicImages  using ( _IsHomImageOf_ ; HomImages ; HomImageOf[_]  )
                                         using ( IsHomImageOfClass ; HomImageOfClass         )
                                         using ( Lift-epi-is-epiˡ ; Lift-Alg-hom-imageˡ      )


-- SETOID.TERMS --------------------------------------------------------------------------
open import
 Setoid.Terms.Basic                      using ( _≐_ ; ≐-isRefl ; ≐-isSym ; ≐-isTrans        )
                                         using ( ≐-isEquiv ; TermSetoid ; 𝑻 ; Sub ; _[_]     )
                                         using ( module Environment )
open Environment                         using ( Env ; ⟦_⟧ ; Equal ; isEquiv ; ⟦_⟧s          )
                                         using ( substitution )
open import
 Setoid.Terms.Properties                 using ( free-lift ; free-lift-of-surj-isSurj        )
                                         using ( free-lift-func ; lift-hom ; free-unique     )
                                         using ( lift-of-epi-is-epi                          )
open import
 Setoid.Terms.Operations                 using ( free-lift-interp ; term-interp              )
                                         using ( term-agreement ; interp-prod ; _[_]s        )
                                         using ( comm-hom-term ; Substerm ; _[_]t            )

-- SETOID.SUBALGEBRAS --------------------------------------------------------------------------
open import
 Setoid.Subalgebras.Subuniverses         using ( Subuniverses ; Subuniverse ; Sg ; sgIsSub   )
                                         using ( ⋂s ; sgIsSmallest ; sub-term-closed         )
                                         using ( TermImage ; TermImageIsSub                  )
                                         using ( B-onlyif-TermImageB ; hom-unique            )
                                         using ( SgB-onlyif-TermImageB                       )
open import
 Setoid.Subalgebras.Subalgebras          using ( _≥_ ; _IsSupalgebraOf_ ; _≤_           )
                                         using ( _IsSubalgebraOf_ ; SubalgebraOf        )
                                         using ( Subalgebra ; IsSubalgebraREL           )
                                         using ( SubalgebraREL ; _IsSubalgebraOfClass_  )
                                         using ( _≤c_ ; SubalgebraOfClass               )
                                         using ( SubalgebraOfClass' ; mon→≤             )
                                         using ( SubalgebrasOfClass                     )
open import
 Setoid.Subalgebras.Properties           using ( ≅→≤ ; ≅→≥ ; ≤-refl ; ≥-refl ; ≤-reflexive  )
                                         using ( ≥-Lift ; ≤-trans ; ≤-trans-≅ ; ≥-trans     )
                                         using ( ≤-preorder ; ≤-mono ; A≥B×B≅C→A≥C          )
                                         using ( A≤B×B≅C→A≤C ; A≅B×B≥C→A≥C ; A≅B×B≤C→A≤C    )
                                         using ( Lift-is-sub ; ≤-Lift ; Lift-≤-Lift         )

-- SETOID.VARIETIES --------------------------------------------------------------------------
open import
 Setoid.Varieties.EquationalLogic   using ( _⊧_≈_ ; _⊫_≈_ ; Th' ; Th'' ; ℐ ; ℰ ; Mod' ; Modᵗ )
open import
 Setoid.Varieties.SoundAndComplete  using ( Eq ; _⊨_ ; _⊧_ ; Mod ; _⊫_ ; _⊃_ ; _⊢_▹_≈_      )
                                    using ( module Soundness ; module FreeAlgebra           )
open Soundness                      using ( sound                                           )
open FreeAlgebra                    using ( FreeDomain ; FreeInterp ; 𝔽[_] ; σ₀ ; identity  )
                                    using ( evaluation ; satisfies ; completeness           )
open import
 Setoid.Varieties.Closure           using ( Level-closure ; Lift-closed ; H ; S ; P ; SP   )
                                    using ( V ; is-variety ; variety ; S-mono ; S-idem     )
                                    using ( H-expa ; S-expa ; P-mono ; P-expa ; V-expa     )
                                    using ( S-≅ ; V-≅ ; V-≅-lc ; classP ; classSP          )
                                    using ( classHSP ; classS ; classK ; LevelClosure-S    )
                                    using ( S-LevelClosure ; S-Lift-lemma ; P-Lift-closed  )
open import
 Setoid.Varieties.Properties        using ( ⊧-I-invar ; ⊧-Lift-invar ; ⊧-lower-invar      )
                                    using ( ⊧-S-invar ; ⊧-S-class-invar ; ⊧-P-invar       )
                                    using ( ⊧-P-class-invar ; ⊧-P-lift-invar ; ⊧-H-invar  )
open import
 Setoid.Varieties.Preservation      using ( S⊆SP ; P⊆SP ; P⊆HSP ; P⊆V ; SP⊆V ; PS⊆SP       )
                                    using ( H-id1 ; H-id2 ; S-id1 ; S-id2 ; P-id1 ; P-id2  )
                                    using ( V-id1 ; V-id2 ; Lift-id1 ; classIds-⊆-VIds     )
                                    using ( VIds-⊆-classIds                                )
open import
 Setoid.Varieties.FreeAlgebras      using ( module FreeHom ; 𝔽-ModTh-epi ; 𝔽-ModTh-epi-lift  )
open FreeHom                        using ( ℐ ; ℰ ; ℰ⊢[_]▹Th𝒦 ; epi𝔽[_] ; hom𝔽[_]            )
                                    using ( hom𝔽[_]-is-epic ; class-models-kernel            )
                                    using ( kernel-in-theory ; 𝒦⊫→ℰ⊢                         )
open import
 Setoid.Varieties.HSP               using ( ℑ⁺ ; 𝔄⁺ ; ℭ ; skEqual ; AllEqual⊆ker𝔽 ; homℭ  )
                                    using ( ker𝔽⊆kerℭ ; hom𝔽ℭ ; kerℭ⊆ker𝔽 ; mon𝔽ℭ ; 𝔽≤ℭ   )
                                    using ( SP𝔽 ; Birkhoff ; Birkhoff-converse            )


-- EXAMPLES -----------------------------------------------------------------------------------------
open import
 Examples.Structures.Signatures     using ( S∅ ; S1 ; S01 ; S001 ; S0001 ; S021 ; S101 ; S111 )
open import
 Examples.Structures.Basic          using (SL ; NAE3SAT ; nae3sat )
open import
 Examples.Categories.Functors       using ( L₀ ; l₀ ; L₁ ; l₁ ; L₃ ; l₃ ; L₀≡none ; l₀≡none  )
                                    using ( L₁[0]≡some3 ; L₁[n>0]≡none ; l₁⟦n>0⟧≡none ; ℓ₁   )
                                    using ( L₃[0]≡some1 ; l₃⟦0⟧≡some1 ; L₃[0]≢some2          )
                                    using ( l₃[0]≢some2  )

-- EXERCISES -----------------------------------------------------------------------------------------
open import
 Exercises.Complexity.FiniteCSP     using  ( module solution-2-1 ; module solution-2-2 )

-- DEMOS ------------------------------------------------------------------------------------------------
open import
 Demos.HSP   using ( ∣_∣ ; ∥_∥ ; 𝑖𝑑 ; _⟨∘⟩_ ; Image_∋_ ; Inv ; InvIsInverseʳ ; IsInjective
                   ; IsSurjective ; SurjInv ; ∘-IsInjective ; ∘-IsSurjective ; Im ; toIm ; fromIm
                   ; fromIm-inj ; toIm-surj ; EqArgs ; ⟨_⟩ ; Algebra ; 𝔻[_] ; 𝕌[_] ; _̂_
                   ; Lift-Algˡ ; Lift-Algʳ ; Lift-Alg ; ⨅ ; compatible-map-op ; compatible-map
                   ; IsHom ; hom ; IsMon ; mon ; IsEpi ; epi ; mon→intohom ; epi→ontohom
                   ; ∘-is-hom ; ∘-is-epi ; ∘-hom ; ∘-epi ; 𝒾𝒹 ; ToLiftˡ ; FromLiftˡ ; ToFromLiftˡ
                   ; FromToLiftˡ ; ToLiftʳ ; FromLiftʳ ; ToFromLiftʳ ; FromToLiftʳ ; ToLift
                   ; FromLift ; ToFromLift ; ToLift-epi ; ⨅-hom-co ; _≅_ ; ≅-refl ; ≅-sym ; ≅-trans
                   ; ov ; _IsHomImageOf_ ; IdHomImage ; HomIm ; toHomIm ; fromHomIm ; Lift-≅ˡ
                   ; Lift-≅ʳ ; Lift-≅ ; _≤_ ; ≤-reflexive ; mon→≤ ; Term ; _≃_ ; ≃-isRefl ; ≃-isSym
                   ; ≃-isTrans ; ≃-isEquiv ; TermSetoid ; 𝑻 ; comm-hom-term ; interp-prod
                   ; _⊧_≈_ ; _⊫_≈_ ; _⊨_ ; ⊧-I-invar ; Th ; Mod ; H ; S ; P ; ⊧-H-invar ; ⊧-S-invar
                   ; ⊧-P-invar ; V ; H-id1 ; S-id1 ; S-id2 ; P-id1 ; V-id1 ; free-lift ; free-lift-func
                   ; lift-hom ; free-lift-interp ; module FreeAlgebra ; module FreeHom ; F-ModTh-epi
                   ; F-ModThV-epi ; F-ModTh-epi-lift ; V-expa ; EqCl⇒Var ; ModTh-closure ; homFC
                   ; monFC ; F≤C ; SPF ; Var⇒EqCl )

\end{code}

--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
