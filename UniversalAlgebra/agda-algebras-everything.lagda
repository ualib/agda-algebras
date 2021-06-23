---
layout: default
title : Overture.Inverses module
date : 2021-06-09
author: [the ualib/agda-algebras development team][]
---

All definitions/theorems in agda-algebras as of 22 June 2021.

\begin{code}


open import Overture.Preliminaries          using    ( ℓ₁ ; ∣_∣ ; ∥_∥ ; _⁻¹ ; _∙_ ; 𝑖𝑑 ; Π ; Π-syntax
                                                     ; lift∼lower ; lower∼lift ; _≈_ ; ≡-by-parts
                                                     ; transport )

open import Overture.Inverses               using    ( Image_∋_ ; eq ; Inv ; InvIsInv ; IsInjective
                                                     ; id-is-injective ; ∘-injective ; IsSurjective
                                                     ; Surjective ; SurjInv )


-- RELATIONS  ------------------------------------------------------------------------

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

open import Relations.Extensionality        using    ( SurjInvIsRightInv ; epic-factor ; pred-ext
                                                     ; block-ext ; block-ext|uip ; welldef ; swelldef )




-- ALGEBRAS ------------------------------------------------------------------------

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

open import Homomorphisms.Basic             using    ( compatible-op-map ; is-homomorphism ; hom ; ∘-hom
                                                     ; ∘-is-hom ; 𝒾𝒹 ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-monomorphism
                                                     ; mon ; is-epimorphism ; epi ; mon-to-hom ; epi-to-hom
                                                     ; πhom ; homker-comp ; kercon ; kerquo ; ker[_⇒_]_↾_
                                                     ; πepi ; πker ; ker-in-con ; ⨅-hom-co ; ⨅-hom
                                                     ; Lift-hom ; ⨅-projection-hom )

open import Homomorphisms.Noether           using    ( FirstHomTheorem|Set ; FirstIsoTheorem|Set
                                                     ; NoetherHomUnique ; fe-NoetherHomUnique
                                                     ; NoetherIsoUnique ; HomFactor ; HomFactorEpi )

open import Homomorphisms.Isomorphisms      using    ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans ; Lift-≅
                                                     ; Lift-Alg-iso ; Lift-Alg-assoc ; Lift-Alg-associative
                                                     ; Lift-Alg-⨅≅ ; ⨅≅ )

open import Homomorphisms.HomomorphicImages using    ( _IsHomImageOf_ ; HomImages ; IsHomImageOfClass
                                                     ; HomImageOfClass ; Lift-epi-is-epi
                                                     ; Lift-Alg-hom-image )

open import Terms.Basic                     using    (Term ; ℊ ; node ; 𝑻 ; free-lift ; lift-hom
                                                     ; free-unique ; lift-of-epi-is-epi )

open import Terms.Operations                using    ( _⟦_⟧ ; free-lift-interp ; term-interp
                                                     ; term-gen ; term-gen-agreement ; term-agreement
                                                     ; interp-prod ; interp-prod2 ; comm-hom-term
                                                     ; _∣:_ )

open import Subalgebras.Subuniverses        using    ( Subuniverses ; Subuniverse ; Sg ; sgIsSub
                                                     ; sgIsSmallest ; sub-intersection ; sub-term-closed
                                                     ; TermImage ; TermImageIsSub ; Y-onlyif-TermImageY
                                                     ; SgY-onlyif-TermImageY ; hom-unique )

open import Subalgebras.Subalgebras         using    ( _IsSubalgebraOf_ ; Subalgebra ; FirstHomCorollary|Set
                                                     ; free-quot-subalg ; _≤_ ; _IsSubalgebraOfClass_
                                                     ; SubalgebraOfClass ; ≤-reflexive ; ≤-refl ; ≤-Lift
                                                     ; ≤-transitivity ; ≤-trans ; iso→injective ; ≤-iso
                                                     ; ≤-trans-≅ ; ≤-TRANS-≅ ; ≤-mono ; Lift-is-sub
                                                     ; Lift-≤ ; Lift-≤-Lift )

open import Varieties.Basic                 using    ( _⊧_≈_ ; _⊧_≋_ ; _⊢_≈_ ; Th ; Mod ; ⊧-I-invar
                                                     ; ⊧-Lift-invar ; ⊧-lower-invar ; ⊧-S-invar
                                                     ; ⊧-S-class-invar ; ⊧-P-invar ; ⊧-P-class-invar
                                                     ; ⊧-P-lift-invar ; ⊧-H-invar ; ⊧-H-class-invar
                                                     ; ⊧-H-class-coinvar )

open import Varieties.EquationalLogic       using    ( S⊆SP ; lemPS⊆SP ; PS⊆SP ; P⊆V ; SP⊆V ; SP⊆V'
                                                     ; module class-products-with-maps )

open import Varieties.Closure.H             using    ( H )

open import Varieties.Closure.S             using    ( S ; S-mono ; subalgebra→S ; S→subalgebra )

open import Varieties.Closure.P             using    ( P ; P-mono ; P-expa ; P-idemp ; Lift-Alg-subP
                                                     ;  Lift-Alg-subP' )
open import Varieties.Closure.V             using    ( V ; is-variety ; variety ; module Vlift )

open import Varieties.Preservation          using    (𝓕 ; 𝓕⁺ ; H-id1 ; H-id2 ; S-id1 ; S-id2
                                                     ; P-id1 ; P-id2 ; V-id1 ; module Vid' ; V-id1'
                                                     ; ovu ; lovu ; 𝕍 ; 𝒱 ; class-ids-⇒ ; class-ids
                                                     ; class-ids-⇐ ; V-id2 )

open import Varieties.FreeAlgebras          using    ( ψ ; ψRel ; ψcompatible ; ψIsEquivalence ; ψCon
                                                     ; ℭ ; homℭ ; 𝔽 ; epi𝔽 ; hom𝔽 ; hom𝔽-is-epic
                                                     ; ψlemma0 ; ψlemma0-ap ; 𝔽-lift-hom ; X↪𝔽 ; 𝔑
                                                     ; hom𝔽-is-lift-hom ; ψlemma1 ; ψlemma2 ; ψlemma3
                                                     ; class-models-kernel ; 𝕍𝒦 ; kernel-in-theory
                                                     ; 𝔽-ModTh-epi ; 𝔽≤ℭ ; 𝔽∈SP ; 𝔽∈𝕍 ; Birkhoff
                                                     ; Birkhoff-converse ; _↠_ )



-- STRUCTURES ------------------------------------------------------------------------


open import Structures.AsRecordsBasic       using    ( ar ; signature ; structure ; compatible
                                                     ; Lift-op ; Lift-rel ; Lift-struc
                                                     ; Sig∅ ; Sig-0 ; Sig-1 ; Sig-2 ; Sig-0-1
                                                     ; Sig-0-1-2 )

open import Structures.AsRecordsCongruences using    ( con ; 0[_]compatible ; 0con[_] ; quotient
                                                     ; _╱_ ; /≡-elim ; 𝟎[_╱_] )

open import Structures.AsRecordsHoms        using    ( preserves ; is-hom-rel ; comm-op ; is-hom-op
                                                     ; is-hom ; hom ; hom-alg ; ∘-is-hom-rel
                                                     ; ∘-is-hom-op ; ∘-is-hom ; ∘-hom ; 𝒾𝒹
                                                     ; is-mon ; mon ; mon→hom ; is-epi ; epi
                                                     ; epi→hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; homker-comp
                                                     ; kerlift-comp ; kercon ; kerquo ; ker[_⇒_]
                                                     ; πepi ; πhom ; πker ; ⨅-hom-co ; ⨅-hom
                                                     ; ⨅-projection-hom )

open import Structures.AsRecordsProducts    using    (  ⨅ ; ℓp ; ℑ ; 𝔄 ; class-product )

open import Structures.Basic                using    ( Signature ; Structure ; RStructure ; AStructure
                                                     ; Structure→RStructure ; Structure→AStructure
                                                     ; _⟦_⟧ᵣ ; _⟦_⟧ₒ ; _ʳ_ ; _ᵒ_ ; Compatible
                                                     ; Compatible' ; Lift-op ; Lift-rel
                                                     ; Lift-Strucˡ ; Lift-Strucʳ ; Lift-Struc )

open import Structures.Congruences          using    ( Con ; 0[_]Compatible ; 0Con[_] ; _╱_ ; /≡-elim
                                                     ; 𝟘[_╱_] ; 𝟎[_╱_] )

open import Structures.Homs                 using    ( preserves ; is-hom-rel ; comp-op ; is-hom-op
                                                     ; is-hom ; hom ; ∘-is-hom-rel ; ∘-is-hom-op
                                                     ; ∘-is-hom ; ∘-hom ; 𝒾𝒹 ; is-mon ; mon ; is-epi
                                                     ; epi ; mon→hom ; epi→hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇
                                                     ; Lift-Hom ; Homker-comp )




\end{code}















---------- The rest is not yet integrated ------------------------------------------------









(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.


 kercon : swelldef 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Con{𝓤}{𝓦} 𝑨
 kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.


 kerquo : swelldef 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
 kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)


ker[_⇒_]_↾_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → hom 𝑨 𝑩 → swelldef 𝓥 𝓦 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.


module _ {𝓤 𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} where
 πepi : (θ : Con{𝓤}{𝓦} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
  cπ-is-epic (C , (a , refl)) =  Image_∋_.im a

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.


 πhom : (θ : Con{𝓤}{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)


 πker : (wd : swelldef 𝓥 𝓦){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef 𝓥 (𝓤 ⊔ lsuc 𝓦)}(θ : Con 𝑨)
  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra 𝓦 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.


module _ {𝓘 𝓦 : Level}{I : Type 𝓘}(ℬ : I → Algebra 𝓦 𝑆) where

 ⨅-hom-co : funext 𝓘 𝓦 → {𝓤 : Level}(𝑨 : Algebra 𝓤 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra 𝓤 𝑆 and ℬ : I → Algebra 𝓦 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.


 ⨅-hom : funext 𝓘 𝓦 → {𝓤 : Level}(𝒜 : I → Algebra 𝓤 𝑆) → Π[ i ꞉ I ] hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.


 ⨅-projection-hom : Π[ i ꞉ I ] hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl
)

open import Structures.Products             using    (  ⨅ ; ℓp ; ℑ ; 𝔖 ; class-prod )

open import Structures.Iso                  using    ( _≅_ ; ≅-refl ; ≅-sym ; ≅-trans
                                                     ; Lift-≅ ; Lift-Struc-iso )

\end{code}


--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
