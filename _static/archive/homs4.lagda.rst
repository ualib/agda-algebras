
.. code-block:: agda

  -- The following are from UF-Rel.agda.

  -- Kernel of a function (as a binary predicate)
  KER-pred : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B) → Pred (A × A) 𝓦
  KER-pred f (x , y) = f x ≡ f y

  -- Kernel of a function (in the special case 𝓦 ≡ 𝓤)
  ker-pred : {A : 𝓤 ̇}{B : 𝓤 ̇}(f : A → B) → Pred (A × A) 𝓤
  ker-pred {𝓤} = KER-pred {𝓤} {𝓤}


  -- The following are from UF-Prelude.agda.

  -- Epic (surjective) function from 𝓤 ̇ to 𝓦 ̇
  Epic : {A : 𝓤 ̇}{B : 𝓦 ̇}(g : A → B) →  𝓤 ⊔ 𝓦 ̇
  Epic g = ∀ y → Image g ∋ y


  -- The (pseudo-)inverse of an epic function
  EpicInv : {A : 𝓤 ̇}{B : 𝓦 ̇}(f : A → B) → Epic f → B → A
  EpicInv f fEpic b = Inv f b (fEpic b)


  -- The (psudo-)inverse of an epic is the right inverse.
  EInvIsRInv : funext 𝓦 𝓦 → {A : 𝓤 ̇} {B : 𝓦 ̇}
               (f : A → B)  (fEpic : Epic f)
               --------------------------------
   →            f ∘ (EpicInv f fEpic) ≡ 𝑖𝑑 B

  EInvIsRInv fe f fEpic = fe (λ x → InvIsInv f x (fEpic x))
