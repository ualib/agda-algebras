
.. code-block:: agda

  -- Composition of homomorphisms (see UF-Hom.agda)

  HCompClosed : {𝑨 : Algebra 𝓤 S}
                {𝑩 : Algebra 𝓦 S}
                {𝑪 : Algebra 𝓣 S}
    →           hom 𝑨 𝑩   →    hom 𝑩 𝑪
               --------------------------
    →                hom 𝑨 𝑪

  HCompClosed {𝑨 = A , FA} {𝑩 = B , FB} {𝑪 = C , FC}
   (f , fhom) (g , ghom) = g ∘ f , γ
    where
     γ : ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸  →  A )
      →  ( g ∘ f ) ( FA 𝓸 𝒂 ) ≡ FC 𝓸 ( g ∘ f ∘ 𝒂 )

     γ 𝓸 𝒂 = (g ∘ f) (FA 𝓸 𝒂)    ≡⟨ ap g ( fhom 𝓸 𝒂 ) ⟩
             g (FB 𝓸 (f ∘ 𝒂))    ≡⟨ ghom 𝓸 ( f ∘ 𝒂 ) ⟩
             FC 𝓸 (g ∘ f ∘ 𝒂)    ∎
