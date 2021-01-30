
.. code-block:: agda

  -- Homs are determined by their values on a generating set.
  -- (See UF-Birkhoff.agda)

  HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
            (X : Pred ∣ 𝑨 ∣ 𝓤)  (f g : hom 𝑨 𝑩)
   →        (∀ ( x : ∣ 𝑨 ∣ )  →  x ∈ X  →  ∣ f ∣ x ≡ ∣ g ∣ x)
           -------------------------------------------------
   →        (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg {𝑨 = 𝑨} X → ∣ f ∣ a ≡ ∣ g ∣ a)

  HomUnique _ _ _ _ fx≡gx a (var x) = (fx≡gx) a x
  HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
   (f , fhom) (g , ghom) fx≡gx a (app 𝓸 {𝒂} im𝒂⊆SgX) =
    f ( Fᴬ 𝓸 𝒂)        ≡⟨ fhom 𝓸 𝒂 ⟩
    Fᴮ 𝓸 ( f ∘ 𝒂 )     ≡⟨ ap (Fᴮ 𝓸) (fe induction-hypothesis) ⟩
    Fᴮ 𝓸 ( g ∘ 𝒂)      ≡⟨ ( ghom 𝓸 𝒂 )⁻¹ ⟩
    g ( Fᴬ 𝓸 𝒂 )       ∎
    where
     induction-hypothesis =
      λ x → HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X
       (f , fhom) (g , ghom) fx≡gx (𝒂 x)(im𝒂⊆SgX x)
