---
layout: default
title : "Base.Varieties.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-03-01"
author: "the agda-algebras development team"
---

### <a id="free-algebras-and-birkhoffs-theorem">Free Algebras and Birkhoff's Theorem</a>

This is the [Base.Varieties.FreeAlgebras][] module of the [Agda Universal Algebra Library][].

First we will define the relatively free algebra in a variety, which is the "freest" algebra among (universal for) those algebras that model all identities holding in the variety. Then we give a formal proof of Birkhoff's theorem which says that a variety is an equational class. In other terms, a class `𝒦` of algebras is closed under the operators `H`, `S`, and `P` if and only if `𝒦` is the class of algebras that satisfy some set of identities.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Level            using ( Level )
open import Overture  using ( 𝓞 ; 𝓥 ; Signature )
module Legacy.Base.Varieties.FreeAlgebras {α : Level} {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------
open  import Agda.Primitive   using ( _⊔_ )renaming  ( Set to Type )
open  import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
                              renaming  ( proj₁ to fst ; proj₂ to snd )
open  import Function         using ( _∘_ )
open  import Level            using ( suc )
open  import Relation.Binary  using ( IsEquivalence ) renaming  ( Rel to BinRel )
open  import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ ; ｛_｝ ; _∪_ )

open  import Axiom.Extensionality.Propositional
      using () renaming  (Extensionality to funext)
open  import Relation.Binary.PropositionalEquality as ≡
      using ( _≡_ ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open  import Overture        using ( ∣_∣ ; ∥_∥ ; _∙_ ; _⁻¹ )
open  import Legacy.Base.Functions  using ( IsSurjective )
open  import Legacy.Base.Relations  using ( kernel ; ⟪_⟫ )
open  import Legacy.Base.Equality
      using ( SwellDef ; swelldef ; is-set ; blk-uip ; hfunext ; DFunExt; pred-ext )

open  import Legacy.Base.Algebras {𝑆 = 𝑆}
      using ( Algebra ; Lift-Alg ; compatible;  _̂_ ; ov ; ⨅ ; Con; mkcon ; IsCongruence )
open  import Legacy.Base.Homomorphisms {𝑆 = 𝑆}
      using ( hom ; epi ; epi→hom ; kercon ; ker-in-con ; πker ; ker[_⇒_]_↾_ ; ∘-hom )
      using ( ⨅-hom-co ; HomFactor ; HomFactorEpi ; _≅_ ; ≅-refl ; ≅-sym ; Lift-≅ )
open  import Legacy.Base.Terms {𝑆 = 𝑆}
      using ( Term ; 𝑻 ; free-lift ; lift-hom ; free-unique ; _⟦_⟧ )
      using ( lift-of-epi-is-epi ; comm-hom-term; free-lift-interp )
open  import Legacy.Base.Subalgebras {𝑆 = 𝑆}
      using ( _≤_ ; FirstHomCorollary|Set )

open  import Legacy.Base.Varieties.EquationalLogic {𝑆 = 𝑆}
      using ( _⊫_≈_; _⊧_≈_; Th; Mod )
open  import Legacy.Base.Varieties.Closure {𝑆 = 𝑆}
      using ( S ; P ; V )
open  import Legacy.Base.Varieties.Preservation {𝑆 = 𝑆}
      using ( module class-products-with-maps ; class-ids-⇒ ; class-ids ; SP⊆V')

open Term ; open S ; open V

𝓕 𝓕⁺ : Level
𝓕 = ov α
𝓕⁺ = suc (ov α)    -- (this will be the level of the free algebra)
```



#### <a id="the-free-algebra-in-theory">The free algebra in theory</a>

Recall, we proved in the [Base.Terms.Basic][] module that the term algebra `𝑻 X` is absolutely free in the class of all `𝑆`-structures.
In this section, we formalize, for a given class `𝒦` of `𝑆`-algebras, the (relatively) free algebra in `S(P 𝒦)` over `X`.

We use the next definition to take a free algebra *for* a class `𝒦` and produce the free algebra *in* `𝒦`.
Let `Θ(𝒦, 𝑨) := {θ ∈ Con 𝑨 : 𝑨 / θ ∈ (S 𝒦)}`, and let `ψ(𝒦, 𝑨) := ⋂ Θ(𝒦, 𝑨)`.
(Notice that `Θ(𝒦, 𝑨)` may be empty, in which case `ψ(𝒦, 𝑨) = 1` and then `𝑨 / ψ(𝒦, 𝑨)` is trivial.)
The free algebra is constructed by applying the definitions of `θ` and `ψ` to the special case in which `𝑨` is the algebra `𝑻 X` of `𝑆`-terms over `X`.

Since `𝑻 X` is free for (and in) the class of all `𝑆`-algebras, it follows that `𝑻 X` is free for every class `𝒦` of `𝑆`-algebras. Of course, `𝑻 X` is not necessarily a member of `𝒦`, but if we form the quotient of `𝑻 X` modulo the congruence `ψ(𝒦, 𝑻 X)`, which we denote by `𝔽[ X ] := (𝑻 X) / ψ(𝒦, 𝑻 X)`, then it's not hard to see that `𝔽[ X ]` is a subdirect product of the algebras in `{(𝑻 𝑋) / θ}`, where `θ` ranges over `Θ(𝒦, 𝑻 X)`, so `𝔽[ X ]` belongs to `SP(𝒦)`, and must therefore satisfy all identities modeled by all members of `𝒦`.  Indeed, for each pair `p q : 𝑻 X`, if `𝒦 ⊧ p ≈ q`, then `p` and `q` belong to the same `ψ(𝒦, 𝑻 X)`-class, so `p` and `q` are identified in the quotient `𝔽[ X ]`.

The `𝔽[ X ]` that we have just defined is called the *free algebra over* `𝒦` *generated by* `X` and (because of what we just observed) we may say that `𝔽[ X ]` is free *in* `SP(𝒦)`.

**Remarks**. Since `X` is not a subset of `𝔽[ X ]`, technically it doesn't make sense to say "`X` generates `𝔽[ X ]`." But as long as `𝒦` contains a nontrivial algebra, we will have `ψ(𝒦, 𝑻 𝑋) ∩ X² ≠ ∅`, and we can identify `X` with `X / ψ(𝒦, 𝑻 X)` which *is* a subset of `𝔽[ X ]`.



#### <a id="the-free-algebra-in-agda">The free algebra in Agda</a>

Before we attempt to represent the free algebra in Agda we construct the congruence `ψ(𝒦, 𝑻 𝑋)` described above.
First, we represent the congruence relation `ψCon`, modulo which `𝑻 X` yields the relatively free algebra, `𝔽[ X ] := 𝑻 X ╱ ψCon`.  We let `ψ` be the collection of identities `(p, q)` satisfied by all subalgebras of algebras in `𝒦`.


```agda


module _ {X : Type α}(𝒦 : Pred (Algebra α) 𝓕) where

 ψ : Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) 𝓕
 ψ (p , q) = ∀(𝑨 : Algebra α)(sA : 𝑨 ∈ S{α}{α} 𝒦)(h : X → ∣ 𝑨 ∣ )
                 →  (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
```


We convert the predicate `ψ` into a relation by [currying](https://en.wikipedia.org/wiki/Currying).


```agda


 ψRel : BinRel ∣ 𝑻 X ∣ 𝓕
 ψRel p q = ψ (p , q)
```


To express `ψRel` as a congruence of the term algebra `𝑻 X`, we must prove that

1. `ψRel` is compatible with the operations of `𝑻 X` (which are jsut the terms themselves) and
2. `ψRel` it is an equivalence relation.


```agda


 open ≡-Reasoning

 ψcompatible : swelldef 𝓥 α → compatible (𝑻 X) ψRel
 ψcompatible wd 𝑓 {p} {q} ψpq 𝑨 sA h = γ
  where
  φ : hom (𝑻 X) 𝑨
  φ = lift-hom 𝑨 h

  γ : ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p) ≡ ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)

  γ = ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p)  ≡⟨ ∥ φ ∥ 𝑓 p ⟩
      (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ p)  ≡⟨ wd (𝑓 ̂ 𝑨)(∣ φ ∣ ∘ p)(∣ φ ∣ ∘ q)(λ x → ψpq x 𝑨 sA h) ⟩
      (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ q)  ≡⟨ (∥ φ ∥ 𝑓 q)⁻¹ ⟩
      ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)  ∎

 ψIsEquivalence : IsEquivalence ψRel
 ψIsEquivalence = record  { refl = λ 𝑨 sA h → ≡.refl
                          ; sym = λ x 𝑨 sA h → (x 𝑨 sA h)⁻¹
                          ; trans = λ pψq qψr 𝑨 sA h → (pψq 𝑨 sA h) ∙ (qψr 𝑨 sA h) }
```


We have collected all the pieces necessary to express the collection of identities satisfied by all subalgebras of algebras in the class as a congruence relation of the term algebra. We call this congruence `ψCon` and define it using the Congruence constructor `mkcon`.


```agda


 ψCon : swelldef 𝓥 α → Con (𝑻 X)
 ψCon wd = ψRel , mkcon ψIsEquivalence (ψcompatible wd)
```



#### <a id="hsp-theorem">HSP Theorem</a>

To complete the proof of the HSP theorem, it remains to show that `Mod X (Th (V 𝒦))` is contained in `V 𝒦`; that is, every algebra that models the equations in `Th (V 𝒦)` belongs to `V 𝒦`.  This will prove that `V 𝒦` is an equational class.  (The converse, that every equational class is a variety was already proved; see the remarks at the end of this module.)

We accomplish this goal by constructing an algebra `𝔽` with the following properties:

1. `𝔽 ∈ V 𝒦` and

2. Every `𝑨 ∈ Mod X (Th (V 𝒦))` is a homomorphic image of `𝔽`.

We denote by `ℭ` the product of all subalgebras of algebras in `𝒦`, and by `homℭ` the homomorphism from `𝑻 X` to `ℭ` defined as follows: `homℭ := ⨅-hom-co (𝑻 X) 𝔄 hom𝔄`. Here, `⨅-hom-co` (defined in the [Base.Homomorphisms.Properties][] module) takes the term algebra `𝑻 X`, a family `{𝔄 : I → Algebra α}` of `𝑆`-algebras, and a family `hom𝔄 : ∀ i → hom (𝑻 X) (𝔄 i)` of homomorphisms and constructs the natural homomorphism `homℭ` from `𝑻 X` to the product `ℭ := ⨅ 𝔄`.  The homomorphism `homℭ : hom (𝑻 X) (⨅ ℭ)` is "natural" in the sense that the `i`-th component of the image of `t : Term X` under `homℭ` is the image `∣ hom𝔄 i ∣ t` of `t` under the i-th homomorphism `hom𝔄 i`.


#### <a id="F-in-classproduct">𝔽 ≤  ⨅ S(𝒦)</a>
Now we come to a step in our approach to formalizing the HSP theorem that turned out to be more technically challenging than we anticipated.  We must prove that the free algebra embeds in the product `ℭ` of all subalgebras of algebras in the class `𝒦`.  This is really the only stage in the proof of Birkhoff's theorem that requires the truncation assumption that `ℭ` be a *set* (that is, `ℭ` has the [UIP][] property).  We will also need to assume several local function extensionality postulates and, as a result, the next submodule will take as given the parameter `fe : (∀ a b → funext a b)`.  This allows us to postulate local function extensionality when and where we need it in the proof. For example, if we want to assume function extensionality at universe levels `𝓥` and `α`, we simply apply `fe` to those universes: `fe 𝓥 α`. (Earlier versions of the library used just a single *global* function extensionality postulate at the start of most modules, but we have since decided to exchange that elegant but crude option for greater precision and transparency.)


```agda


module _ {fe : DFunExt}{wd : SwellDef}{X : Type α} {𝒦 : Pred (Algebra α) 𝓕} where

 open class-products-with-maps {X = X}{fe 𝓕 α}{fe 𝓕⁺ 𝓕⁺}{fe 𝓕 𝓕} 𝒦
```


We begin by constructing `ℭ`, using the techniques described in the section on <a href="https://ualib.gitlab.io/Base.Varieties.Base.Varieties.html#products-of-classes">products of classes</a>.


```agda


 -- ℭ is the product of all subalgebras of algebras in 𝒦.
 ℭ : Algebra 𝓕
 ℭ = ⨅ 𝔄'
```


Observe that the inhabitants of `ℭ` are maps from `ℑ` to `{𝔄 i : i ∈ ℑ}`.  A homomorphism from `𝑻 X` to `ℭ` is obtained as follows.


```agda


 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄' (fe 𝓕 α){𝓕}(𝑻 X) λ i → lift-hom (𝔄' i)(snd ∥ i ∥)
```



#### <a id="the-free-algebra">The free algebra</a>

 As mentioned, the initial version of the [agda-algebras](https://github.com/ualib/agda-algebras) library used the free algebra `𝔉` developed above.  However, our new, more direct proof uses the algebra `𝔽`, which we now define, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.

 We now define the algebra `𝔽`, which plays the role of the free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.


```agda


 𝔽 : Algebra 𝓕⁺
 𝔽 = ker[ 𝑻 X ⇒ ℭ ] homℭ ↾ (wd 𝓥 (ov α))

 epi𝔽 : epi (𝑻 X) 𝔽
 epi𝔽 = πker (wd 𝓥 (ov α)) {ℭ} homℭ

 hom𝔽 : hom (𝑻 X) 𝔽
 hom𝔽 = epi→hom 𝔽 epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = snd ∥ epi𝔽 ∥
```


We will need the following facts relating `homℭ`, `hom𝔽`, `and ψ`.


```agda


 ψlemma0 : ∀ p q →  ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q  → (p , q) ∈ ψ 𝒦
 ψlemma0 p q phomℭq 𝑨 sA h = ≡.cong-app phomℭq (𝑨 , sA , h)

 ψlemma0-ap : {𝑨 : Algebra α}{h : X → ∣ 𝑨 ∣} → 𝑨 ∈ S{α}{α} 𝒦
  →           kernel ∣ hom𝔽 ∣ ⊆ kernel (free-lift 𝑨 h)

 ψlemma0-ap {𝑨}{h} skA {p , q} x = γ where

  ν : ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q
  ν = ker-in-con {α = (ov α)}{ov α}{𝑻 X}{wd 𝓥 (suc (ov α))}(kercon (wd 𝓥 (ov α)) {ℭ} homℭ) {p}{q} x

  γ : (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
  γ = ((ψlemma0 p q) ν) 𝑨 skA h
```


We now use `ψlemma0-ap` to prove that every map `h : X → ∣ 𝑨 ∣`, from `X` to a subalgebra `𝑨 ∈ S 𝒦` of `𝒦`, lifts to a homomorphism from `𝔽` to `𝑨`.


```agda


 𝔽-lift-hom : (𝑨 : Algebra α) → 𝑨 ∈ S{α}{α} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
 𝔽-lift-hom 𝑨 skA h = fst(HomFactor (wd 𝓥 (suc (ov α)))  𝑨 (lift-hom 𝑨 h) hom𝔽 (ψlemma0-ap skA) hom𝔽-is-epic)
```



#### <a id="k-models-psi">𝒦 models ψ</a>

The goal of this subsection is to prove that `𝒦` models `ψ 𝒦`. In other terms, for all pairs `(p , q) ∈ Term X × Term X` of terms, if `(p , q) ∈ ψ 𝒦`, then `𝒦 ⊫ p ≈ q`.

Next we define the lift of the natural embedding from `X` into `𝔽`. We denote this homomorphism by `𝔑 : hom (𝑻 X) 𝔽` and define it as follows.


```agda


 open IsCongruence

 X↪𝔽 : X → ∣ 𝔽 ∣
 X↪𝔽 x = ⟪ ℊ x ⟫ -- (the implicit relation here is  ⟨ kercon (fe 𝓥 𝓕) ℭ homℭ ⟩ )

 𝔑 : hom (𝑻 X) 𝔽
 𝔑 = lift-hom 𝔽 X↪𝔽
```


It turns out that the homomorphism so defined is equivalent to `hom𝔽`.


```agda

 open ≡-Reasoning

 hom𝔽-is-lift-hom : ∀ p → ∣ 𝔑 ∣ p ≡ ∣ hom𝔽 ∣ p
 hom𝔽-is-lift-hom (ℊ x) = ≡.refl
 hom𝔽-is-lift-hom (node 𝑓 𝒕) =
  ∣ 𝔑 ∣ (node 𝑓 𝒕)              ≡⟨ ∥ 𝔑 ∥ 𝑓 𝒕 ⟩
  (𝑓 ̂ 𝔽)(λ i → ∣ 𝔑 ∣(𝒕 i))     ≡⟨ wd-proof ⟩
  (𝑓 ̂ 𝔽)(λ i → ∣ hom𝔽 ∣ (𝒕 i)) ≡⟨ (∥ hom𝔽 ∥ 𝑓 𝒕)⁻¹ ⟩
  ∣ hom𝔽 ∣ (node 𝑓 𝒕)           ∎
   where wd-proof = wd 𝓥 (suc (ov α))
                    (𝑓 ̂ 𝔽) (λ i → ∣ 𝔑 ∣(𝒕 i)) (λ i → ∣ hom𝔽 ∣ (𝒕 i))
                    (λ x → hom𝔽-is-lift-hom(𝒕 x))
```


We need a three more lemmas before we are ready to tackle our main goal.


```agda


 ψlemma1 : kernel ∣ 𝔑 ∣ ⊆ ψ 𝒦
 ψlemma1 {p , q} 𝔑pq 𝑨 sA h = γ
  where
   f : hom 𝔽 𝑨
   f = 𝔽-lift-hom 𝑨 sA h

   h' φ : hom (𝑻 X) 𝑨
   h' = ∘-hom (𝑻 X) 𝑨 𝔑 f
   φ = lift-hom 𝑨 h

   h≡φ : ∀ t → (∣ f ∣ ∘ ∣ 𝔑 ∣) t ≡ ∣ φ ∣ t
   h≡φ t = free-unique (wd 𝓥 α) 𝑨 h' φ (λ x → ≡.refl) t

   γ : ∣ φ ∣ p ≡ ∣ φ ∣ q
   γ = ∣ φ ∣ p             ≡⟨ (h≡φ p)⁻¹ ⟩
       ∣ f ∣ ( ∣ 𝔑 ∣ p )   ≡⟨ ≡.cong ∣ f ∣ 𝔑pq ⟩
       ∣ f ∣ ( ∣ 𝔑 ∣ q )   ≡⟨ h≡φ q ⟩
       ∣ φ ∣ q             ∎


 ψlemma2 : kernel ∣ hom𝔽 ∣ ⊆ ψ 𝒦
 ψlemma2 {p , q} x = ψlemma1 {p , q} γ
   where
    γ : (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q
    γ = (hom𝔽-is-lift-hom p) ∙ x ∙ (hom𝔽-is-lift-hom q)⁻¹


 ψlemma3 : ∀ p q → (p , q) ∈ ψ{X = X} 𝒦 → 𝒦 ⊫ p ≈ q
 ψlemma3 p q pψq {𝑨} kA h = goal
   where
   goal : (𝑨 ⟦ p ⟧) h ≡ (𝑨 ⟦ q ⟧) h
   goal = (𝑨 ⟦ p ⟧) h       ≡⟨ free-lift-interp (wd 𝓥 α) 𝑨 h p ⟩
          (free-lift 𝑨 h) p ≡⟨ pψq 𝑨 (siso (sbase kA) (≅-sym Lift-≅)) h ⟩
          (free-lift 𝑨 h) q ≡⟨ (free-lift-interp (wd 𝓥 α) 𝑨 h q)⁻¹  ⟩
          (𝑨 ⟦ q ⟧) h       ∎
```


With these results in hand, it is now trivial to prove the main theorem of this subsection.


```agda


 class-models-kernel : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝒦 ⊫ p ≈ q
 class-models-kernel p q x = ψlemma3 p q (ψlemma2 x)

 𝕍𝒦 : Pred (Algebra 𝓕⁺) (suc 𝓕⁺)
 𝕍𝒦 = V{α = α}{β = 𝓕⁺} 𝒦

 kernel-in-theory' : kernel ∣ hom𝔽 ∣ ⊆ Th (V 𝒦)
 kernel-in-theory' {p , q} pKq = (class-ids-⇒ fe wd p q (class-models-kernel p q pKq))

 kernel-in-theory : kernel ∣ hom𝔽 ∣ ⊆ Th 𝕍𝒦
 kernel-in-theory {p , q} pKq vkA x = class-ids fe wd p q (class-models-kernel p q pKq) vkA x

 _↠_ : Type α → Algebra 𝓕⁺ → Type 𝓕⁺
 X ↠ 𝑨 = Σ[ h ∈ (X → ∣ 𝑨 ∣) ] IsSurjective h

 𝔽-ModTh-epi : (𝑨 : Algebra 𝓕⁺) → (X ↠ 𝑨) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 𝔽-ModTh-epi 𝑨 (η , ηE) AinMTV = goal
  where
  φ : hom (𝑻 X) 𝑨
  φ = lift-hom 𝑨 η

  φE : IsSurjective ∣ φ ∣
  φE = lift-of-epi-is-epi 𝑨 ηE

  pqlem2 : ∀ p q → (p , q) ∈ kernel ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
  pqlem2 p q z = λ x → AinMTV p q (kernel-in-theory z) x

  kerincl : kernel ∣ hom𝔽 ∣ ⊆ kernel ∣ φ ∣
  kerincl {p , q} x = ∣ φ ∣ p      ≡⟨ (free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η p)⁻¹ ⟩
                      (𝑨 ⟦ p ⟧) η  ≡⟨ pqlem2 p q x η ⟩
                      (𝑨 ⟦ q ⟧) η  ≡⟨ free-lift-interp (wd 𝓥 𝓕⁺) 𝑨 η q ⟩
                      ∣ φ ∣ q      ∎

  goal : epi 𝔽 𝑨
  goal = fst (HomFactorEpi (wd 𝓥 (suc (ov α))) 𝑨 φ hom𝔽 kerincl hom𝔽-is-epic φE)
```



#### <a id="the-homomorphic-images-of-F">The homomorphic images of 𝔽</a>

Finally we come to one of the main theorems of this module; it asserts that every algebra in `Mod X (Th 𝕍𝒦)` is a homomorphic image of `𝔽`.  We prove this below as the function (or proof object) `𝔽-ModTh-epi`.  Before that, we prove two auxiliary lemmas.


```agda


 module _ (pe : pred-ext (ov α)(ov α))(wd : SwellDef) -- extensionality assumptions
          (Cset : is-set ∣ ℭ ∣)                       -- truncation assumptions
          (kuip : blk-uip(Term X)∣ kercon (wd 𝓥 (ov α)){ℭ}homℭ ∣)
  where

  𝔽≤ℭ : (ker[ 𝑻 X ⇒ ℭ ] homℭ ↾ (wd 𝓥 (ov α))) ≤ ℭ
  𝔽≤ℭ = FirstHomCorollary|Set (𝑻 X) ℭ homℭ pe (wd 𝓥 (ov α)) Cset kuip
```


The last piece we need to prove that every model of `Th 𝕍𝒦` is a homomorphic image of `𝔽` is a crucial assumption that is taken for granted throughout informal universal algebra---namely, that our collection `X` of variable symbols is arbitrarily large and that we have an *environment* which interprets the variable symbols in every algebra under consideration. In other terms, an environment provides, for every algebra `𝑨`, a surjective mapping `η : X → ∣ 𝑨 ∣` from `X` onto the domain of `𝑨`.

We do *not* assert that for an arbitrary type `X` such surjective maps exist.  Indeed, our `X` must is quite special to have this property.  Later, we will construct such an `X`, but for now we simply postulate its existence. Note that this assumption that an environment exists is only required in the proof of the theorem `𝔽-ModTh-epi`.


#### <a id="F-in-VK">𝔽 ∈ V(𝒦)</a>

With this result in hand, along with what we proved earlier---namely, `PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ V 𝒦`---it is not hard to show that `𝔽` belongs to `V 𝒦`.


```agda


  𝔽∈SP : hfunext (ov α)(ov α) → 𝔽 ∈ (S{𝓕}{𝓕⁺} (P{α}{𝓕} 𝒦))
  𝔽∈SP hfe = ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

  𝔽∈𝕍 : hfunext (ov α)(ov α) → 𝔽 ∈ V 𝒦
  𝔽∈𝕍 hfe = SP⊆V' {α}{fe 𝓕 α}{fe 𝓕⁺ 𝓕⁺}{fe 𝓕 𝓕}{𝒦} (𝔽∈SP hfe)
```



#### The HSP Theorem

Now that we have all of the necessary ingredients, it is all but trivial to
combine them to prove Birkhoff's HSP theorem. (Note that since the proof enlists
the help of the `𝔽-ModTh-epi` theorem, we must assume an environment exists,
which is manifested in the premise `∀ 𝑨 → X ↠ 𝑨`.


```agda


  Birkhoff : hfunext (ov α)(ov α) → (∀ 𝑨 → X ↠ 𝑨) → Mod (Th (V 𝒦)) ⊆ V 𝒦
  Birkhoff hfe 𝕏 {𝑨} α = vhimg{𝑩 = 𝑨} (𝔽∈𝕍 hfe) (𝑨 , epi→hom 𝑨 φE , snd ∥ φE ∥)
   where
   φE : epi 𝔽 𝑨
   φE = 𝔽-ModTh-epi 𝑨 (𝕏 𝑨) α
```


The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the
fact that `Mod Th` is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.


```agda


  Birkhoff-converse : V{α}{𝓕} 𝒦 ⊆ Mod{X = X} (Th (V 𝒦))
  Birkhoff-converse α p q pThq = pThq α
```


We have thus proved that every variety is an equational class.  Readers familiar
with the classical formulation of the Birkhoff HSP theorem, as an "if and only
if" result, might worry that we haven't completed the proof.  But recall that
in the [Base.Varieties.Preservation][] module we proved the following identity
preservation lemmas:

* `𝒦 ⊫ p ≈ q → H 𝒦 ⊫ p ≈ q`
* `𝒦 ⊫ p ≈ q → S 𝒦 ⊫ p ≈ q`
* `𝒦 ⊫ p ≈ q → P 𝒦 ⊫ p ≈ q`

From these it follows that every equational class is a variety. Thus, our formal
proof of Birkhoff's theorem is complete.

--------------------------------

<span style="float:left;">[← Base.Varieties.Preservation](Base.Varieties.Preservation.html)</span>
<span style="float:right;">[Base.Structures →](Base.Structures.html)</span>

{% include UALib.Links.md %}
