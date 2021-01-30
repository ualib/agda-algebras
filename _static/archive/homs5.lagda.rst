
.. code-block:: agda

  -- Factorization of homs.
  homFactor : funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 S}
              (f : hom 𝑨 𝑩) (g : hom 𝑨 𝑪)
   →          ker-pred ∣ g ∣ ⊆ ker-pred ∣ f ∣  →   Epic ∣ g ∣
              -------------------------------------------
   →          Σ h ꞉ ( hom 𝑪 𝑩 ) ,  ∣ f ∣ ≡ ∣ h ∣ ∘ ∣ g ∣

  homFactor fe {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
            (f , fhom) (g , ghom) Kg⊆Kf gEpic =
   (h , hIsHomCB) ,  f≡h∘g
    where
     gInv : C → A
     gInv = λ c → (EpicInv g gEpic) c

     h : C → B
     h = λ c → f ( gInv c )

     ξ : (x : A) → ker-pred g (x , gInv (g x))
     ξ x =  ( cong-app (EInvIsRInv fe g gEpic) ( g x ) )⁻¹

     f≡h∘g : f ≡ h ∘ g
     f≡h∘g = fe  λ x → Kg⊆Kf (ξ x)

     ζ : (𝓸 : ∣ S ∣)(𝒄 : ∥ S ∥ 𝓸 → C)(x : ∥ S ∥ 𝓸)
      →  𝒄 x ≡ (g ∘ gInv) (𝒄 x)
     ζ 𝓸 𝒄 x = (cong-app (EInvIsRInv fe g gEpic) (𝒄 x))⁻¹

     ι : (𝓸 : ∣ S ∣ )  ( 𝒄 : ∥ S ∥ 𝓸 → C )
      →  (λ x → 𝒄 x) ≡ (λ x → g (gInv (𝒄 x)))
     ι 𝓸 𝒄 = ap (λ - → - ∘ 𝒄)
                 (EInvIsRInv fe g gEpic)⁻¹

     useker : (𝓸 : ∣ S ∣)  (𝒄 : ∥ S ∥ 𝓸 → C)
      → f(gInv(g(FA 𝓸(λ x → gInv (𝒄 x)))))
        ≡ f(FA 𝓸(λ x → gInv(𝒄 x)))
     useker = λ 𝓸 𝒄 → Kg⊆Kf
                       (cong-app
                        ( EInvIsRInv fe g gEpic )
                        ( g(FA 𝓸(gInv ∘ 𝒄)) )
                       )

     hIsHomCB : (𝓸 : ∣ S ∣) (𝒂 : ∥ S ∥ 𝓸 → C)
      →         h (FC 𝓸 𝒂)  ≡  FB 𝓸 (λ x → h (𝒂 x))
     hIsHomCB 𝓸 𝒄 =
      f (gInv (FC 𝓸 𝒄))               ≡⟨ i ⟩
      f (gInv (FC 𝓸 (g ∘ (gInv ∘ 𝒄)))) ≡⟨ ii ⟩
      f (gInv (g (FA 𝓸 (gInv ∘ 𝒄))))  ≡⟨ iii ⟩
      f (FA 𝓸 (gInv ∘ 𝒄))             ≡⟨ iv ⟩
      FB 𝓸 (λ x → f (gInv (𝒄 x)))     ∎
      where
       i  = ap (f ∘ gInv) (ap (FC 𝓸) (ι 𝓸 𝒄))
       ii = ap (λ - → f (gInv -)) (ghom 𝓸 (gInv ∘ 𝒄))⁻¹
       iii = useker 𝓸 𝒄
       iv = fhom 𝓸 (gInv ∘ 𝒄)
