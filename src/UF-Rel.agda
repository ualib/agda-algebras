--FILE: UF-Rel.agda
--BLAME: William DeMeo
--DATE: 23 Apr 2020
--UPDATE: 23 May 2020
--REF: Much of this file simply transcribes some of the Agda std lib 1.1 file Binary/Core.agda, slightly modified to comport with UF notation.
--       The person(s) named above makes no claims as to the novelty, usefulness, or correctness of the contents of this file.

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (Universe; 𝓤; 𝓥; 𝓦; 𝓡; 𝓢; 𝓣; _⁺; _̇;_⊔_; _×_; _,_; _≡_; _≡⟨_⟩_; _∎; ¬; _+_; Σ; -Σ )
open import Relation.Unary using (Pred)

module UF-Rel where

--Heterogeneous binary relations.
REL : 𝓤 ̇ → 𝓥 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓝 ⁺) ̇
REL A B 𝓝 = A → B → 𝓝 ̇

--Homogeneous binary relations.
Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
Rel A 𝓝 = REL A A 𝓝

--Kernel of a function.
KER : {A : 𝓤 ̇} {B : 𝓦 ̇} → (f : A → B) → 𝓤 ⊔ 𝓦 ̇
KER {𝓤}{𝓦}{A} f = Σ x ꞉ A , Σ y ꞉ A , f x ≡ f y

ker : {A B : 𝓤 ̇} → (f : A → B) → 𝓤 ̇
ker {𝓤} = KER{𝓤}{𝓤}

-- ...as a relation.
KER-rel : {A : 𝓤 ̇} {B : 𝓦 ̇} → (f : A → B) → Rel A 𝓦
KER-rel f x y = f x ≡ f y

-- ...as a relation in the special case 𝓦 ≡ 𝓤.
ker-rel : {A B : 𝓤 ̇} → (f : A → B) → Rel A 𝓤
ker-rel {𝓤} = KER-rel {𝓤} {𝓤}

-- ...as a binary predicate.
KER-pred :  {A : 𝓤 ̇} {B : 𝓦 ̇} → (f : A → B) → Pred (A × A) 𝓦
KER-pred f (x , y) = f x ≡ f y
-- ...as a binary predicate in the special case 𝓦 ≡ 𝓤.
ker-pred :  {A : 𝓤 ̇} {B : 𝓤 ̇} → (f : A → B) → Pred (A × A) 𝓤
ker-pred {𝓤} = KER-pred {𝓤} {𝓤}


--Implication/containment (could also be written _⊆_.).
_⇒_ : {A : 𝓤 ̇}  {B : 𝓥 ̇}  → REL A B 𝓡 → REL A B 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
P ⇒ Q = ∀ {i j} → P i j → Q i j
infixr 4 _⇒_

_on_ : {A : 𝓤 ̇}  {B : 𝓥 ̇}  {C : 𝓦 ̇} → (B → B → C) → (A → B) → (A → A → C)
_*_ on f = λ x y → f x * f y

--Generalised implication: if P ≡ Q it can be read as "f preserves P".
_=[_]⇒_ : {A : 𝓤 ̇}  {B : 𝓥 ̇} → Rel A 𝓡 → (A → B) → Rel B 𝓢 →  𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
P =[ f ]⇒ Q = P ⇒ (Q on f)
infixr 4 _=[_]⇒_

--A synonym for _=[_]⇒_.
_Preserves_⟶_ : {A : 𝓤 ̇}  {B : 𝓥 ̇} → (A → B) → Rel A 𝓡 → Rel B 𝓢 →  𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
f Preserves P ⟶ Q = P =[ f ]⇒ Q

--A binary variant of _Preserves_⟶_.
_Preserves₂_⟶_⟶_ : {A : 𝓤 ̇}  {B : 𝓥 ̇}  {C : 𝓦 ̇}
 →                            (A → B → C) → Rel A 𝓡 → Rel B 𝓢 → Rel C 𝓣
 →                            𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
_+_ Preserves₂ P ⟶ Q ⟶ R =  ∀ {x y u v} → P x y → Q u v → R (x + u) (y + v)

--Reflexivity defined without an underlying equality.
Reflexive : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
Reflexive _∼_ = ∀ {x} → x ∼ x

flip : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : A → B → 𝓦 ̇} → ( (x : A) (y : B) → C x y ) → ( (y : B) (x : A) → C x y )
flip f = λ y x → f x y

--Generalised symmetry.
Sym : {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → REL B A 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
Sym P Q = P ⇒ flip Q

--Symmetry.
Symmetric : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
Symmetric _∼_ = Sym _∼_ _∼_

--Generalised transitivity.
Trans : {A : 𝓤 ̇}  {B : 𝓥 ̇}  {C : 𝓦 ̇} → REL A B 𝓡 → REL B C 𝓢 → REL A C 𝓣 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

--A flipped variant of generalised transitivity.
TransFlip : {A : 𝓤 ̇}  {B : 𝓥 ̇}  {C : 𝓦 ̇} → REL A B 𝓡 → REL B C 𝓢 → REL A C 𝓣 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

--Transitivity.
Transitive : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
Transitive _∼_ = Trans _∼_ _∼_ _∼_

--Generalised antisymmetry.
Antisym : {A : 𝓤 ̇}  {B : 𝓥 ̇} → REL A B 𝓡 → REL B A 𝓢 → REL A B 𝓣 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
Antisym R S E = ∀ {i j} → R i j → S j i → E i j

--Antisymmetry.
Antisymmetric : {A : 𝓤 ̇} → Rel A 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
Antisymmetric _≈_ _≤_ = Antisym _≤_ _≤_ _≈_

--Irreflexivity: this is defined terms of the underlying equality.
Irreflexive : {A : 𝓤 ̇}  {B : 𝓥 ̇} → REL A B 𝓡 → REL A B 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)

--Asymmetry.
Asymmetric : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

--Generalised connex: exactly one of the two relations holds.
Connex : {A : 𝓤 ̇}  {B : 𝓥 ̇} → REL A B 𝓡 → REL B A 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
Connex P Q = ∀ x y → P x y + Q y x

--Totality.
Total : {A : 𝓤 ̇} → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
Total _∼_ = Connex _∼_ _∼_

--Generalised trichotomy: exactly one of three types has a witness.
data Tri (A : 𝓤 ̇) (B : 𝓥 ̇) (C : 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

--Trichotomy.
Trichotomous : {A : 𝓤 ̇} → Rel A 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇
Trichotomous _≈_ _<_ = ∀ x y → Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip _<_

--Generalised maximum element.
Max : {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → B → 𝓤 ⊔ 𝓡 ̇
Max _≤_ T = ∀ x → x ≤ T

--Maximum element.
Maximum : {A : 𝓤 ̇} → Rel A 𝓡 → A → 𝓤 ⊔ 𝓡 ̇
Maximum = Max

--Generalised minimum element.
Min : {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → A → 𝓥 ⊔ 𝓡 ̇
Min R = Max (flip R)

--Minimum element.
Minimum : {A : 𝓤 ̇} → Rel A 𝓡 → A → 𝓤 ⊔ 𝓡 ̇
Minimum = Min

--Unary relations respecting a binary relation.
_⟶_Respects_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → 𝓡 ̇) → (B → 𝓢 ̇) → REL A B 𝓣 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ⊔ 𝓣 ̇
P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y

--Unary relation respects a binary relation.
_Respects_ :  {A : 𝓤 ̇} → (A → 𝓥 ̇) → Rel A 𝓡 → Set _
P Respects _∼_ = P ⟶ P Respects _∼_

--Right respecting: relatedness is preserved on the right by equality.
_Respectsʳ_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → Rel B 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
_∼_ Respectsʳ _≈_ = ∀ {x} → (x ∼_) Respects _≈_

--Left respecting: relatedness is preserved on the left by equality.
_Respectsˡ_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ⊔ 𝓢 ̇
P Respectsˡ _∼_ = ∀ {y} → (flip P y) Respects _∼_

--Respecting: relatedness is preserved on both sides by equality
_Respects₂_ :  {A : 𝓤 ̇} {B : 𝓥 ̇} → Rel A 𝓡 → Rel A 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇ 
P Respects₂ _∼_ = (P Respectsʳ _∼_) × (P Respectsˡ _∼_)

--Substitutivity: any two related elements satisfy exactly the same set of unary relations.
Substitutive :  {A : 𝓤 ̇} {B : 𝓥 ̇} → Rel A 𝓡 → (𝓢 : Universe) → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ⁺ ̇
Substitutive {A = A} _∼_ 𝓢 = (P : A → 𝓢 ̇) → P Respects _∼_
--(Note that only the various derivatives of propositional equality can satisfy this property.)

----------------------------------------------------------------------------------------------
--Decidable relations.
data Dec {𝓤} (P : 𝓤 ̇) : 𝓤 ̇ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

--Decidability: it is possible to determine whether a given pair of elements are related.
Decidable :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

--Weak decidability: it is sometimes possible to determine if a given pair of elements are related.
data Maybe (A : 𝓤 ̇) : 𝓤 ̇ where
  just    : (x : A) → Maybe A
  nothing : Maybe A

WeaklyDecidable :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
WeaklyDecidable _∼_ = ∀ x y → Maybe (x ∼ y)

--Irrelevancy: all proofs that a given pair of elements are related are indistinguishable (analogous to subsingleton, or prop, or set).
Irrelevant : {A : 𝓤 ̇} {B : 𝓥 ̇} →  REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
Irrelevant _∼_ = ∀ {x y} (a b : x ∼ y) → a ≡ b

--Recomputability: we can rebuild a relevant proof given an irrelevant one.
Recomputable :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
Recomputable _∼_ = ∀ {x y} → .(x ∼ y) → x ∼ y

--Universal: all pairs of elements are related
Universal :  {A : 𝓤 ̇} {B : 𝓥 ̇} → REL A B 𝓡 → 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇
Universal _∼_ = ∀ x y → x ∼ y

--Non-emptiness: at least one pair of elements are related.
record NonEmpty  {A : 𝓤 ̇} {B : 𝓥 ̇} (T : REL A B 𝓡) : 𝓤 ⊔ 𝓥 ⊔ 𝓡 ̇ where
  constructor nonEmpty
  field
    {x}   : A
    {y}   : B
    proof : T x y

------------------------------------------------------------------------
--Equivalence relations.
--The preorders of the standard library are defined in terms of an underlying equivalence relation, and hence
-- equivalence relations are not defined in terms of preorders. 
record IsEquivalence {A : 𝓤 ̇} (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
  field
    rfl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  -- reflexive : _≡_ ⇒ _≈_
  -- reflexive ≡-refl = rfl
