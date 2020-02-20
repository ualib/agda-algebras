open import Preliminaries using (Level; suc; _⊔_; _,_; ∣_∣; ⟦_⟧; Pred; _∈_; _∈∈_; _⊆_)

open import Basic
open import Hom

IsSubuniverse : {i j k l : Level} {S : Signature i j} {A : Algebra k S} →
  Pred (Pred ∣ A ∣ l) (i ⊔ j ⊔ k ⊔ l)
IsSubuniverse {S = F , ρ} {A = a , A} B =
  (o : F) (x : ρ o → a) → x ∈∈ B → A o x ∈ B

module _ {i j k : Level} {S : Signature i j} {A : Algebra k S} where
  data Sg (X : Pred ∣ A ∣ k) : Pred ∣ A ∣ (i ⊔ j ⊔ k) where
    var : ∀ {v} → v ∈ X → v ∈ Sg X
    app : (o : ∣ S ∣) {x : ⟦ S ⟧ o → ∣ A ∣} → x ∈∈ Sg X → ⟦ A ⟧ o x ∈ Sg X

module _ {i j k : Level} {S : Signature i j} {A : Algebra k S} (X : Pred ∣ A ∣ k) where
  sgIsSub : IsSubuniverse {A = A} (Sg {A = A} X)
  sgIsSub o x α = app o α

  sgIsSmallest : {Y : Pred ∣ A ∣ k} → IsSubuniverse {A = A} Y → X ⊆ Y → Sg {A = A} X ⊆ Y
  -- By induction on x ∈ Sg X, show x ∈ Y
  sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X
  sgIsSmallest {Y} YIsSub X⊆Y (app o {x} x∈∈SgX) = app∈Y where
    -- First, show the args are in Y
    x∈∈Y : x ∈∈ Y
    x∈∈Y i = sgIsSmallest YIsSub X⊆Y (x∈∈SgX i)

    -- Since Y is a subuniverse of A, it contains the application of o to said args
    app∈Y : ⟦ A ⟧ o x ∈ Y
    app∈Y = YIsSub o x x∈∈Y
