open import Preliminaries using (Level; suc; _⊔_; _,_; ∣_∣; ⟦_⟧; Pred; _∈_; _∈∈_;im_⊆_; _⊆_)

open import Basic
open import Hom

IsSubuniverse : {i j k l : Level} {S : Signature i j} {𝑨 : Algebra k S}
              -----------------------------------------------------------
  ->            Pred (Pred ∣ 𝑨 ∣ l) (i ⊔ j ⊔ k ⊔ l)
IsSubuniverse {S = (𝐹 , ρ)} {𝑨 = (A , 𝐹ᴬ)} B =          -- type \MiF\^A for 𝐹ᴬ
  (𝓸 : 𝐹) (𝒂 : ρ 𝓸 → A) → im 𝒂 ⊆ B → 𝐹ᴬ 𝓸 𝒂 ∈ B

-- IsSubuniverse {S = F , ρ} {𝑨 = a , 𝑨} B =
--   (o : F) (x : ρ o → a) → x ∈∈ B → 𝑨 o x ∈ B

module _ {i j k : Level} {S : Signature i j} {𝑨 : Algebra k S} where

  data Sg (X : Pred ∣ 𝑨 ∣ k) : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k) where
    var : ∀ {v} → v ∈ X → v ∈ Sg X
    app :  (𝓸 : ∣ S ∣) {𝒂 : ⟦ S ⟧ 𝓸 → ∣ 𝑨 ∣}
      ->     im 𝒂 ⊆ Sg X
           --------------------------------
      ->    ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Sg X  

module _ {i j k : Level} {S : Signature i j} {𝑨 : Algebra k S} (X : Pred ∣ 𝑨 ∣ k) where
  sgIsSub : IsSubuniverse {𝑨 = 𝑨} (Sg {𝑨 = 𝑨} X)
  sgIsSub 𝓸 x α = app 𝓸 α

  sgIsSmallest : {Y : Pred ∣ 𝑨 ∣ k}
    ->           IsSubuniverse {𝑨 = 𝑨} Y
    ->           X ⊆ Y
                -----------------------------
    ->           Sg {𝑨 = 𝑨} X ⊆ Y
  -- By induction on x ∈ Sg X, show x ∈ Y
  sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X
  sgIsSmallest {Y} YIsSub X⊆Y (app 𝓸 {𝒂} im𝒂⊆SgX) = app∈Y where
    -- First, show the args are in Y
    im𝒂⊆Y : im 𝒂 ⊆ Y
    im𝒂⊆Y i = sgIsSmallest YIsSub X⊆Y (im𝒂⊆SgX i)

    -- Since Y is a subuniverse of 𝑨, it contains the application of 𝓸 to said args
    app∈Y : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Y
    app∈Y = YIsSub 𝓸 𝒂 im𝒂⊆Y
