.. code-block:: agda

   --Equalizers (see UF-Birkhoff.agda)

   --...of functions
   𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (f g : A → B) → Pred A 𝓦
   𝑬 f g x = f x ≡ g x

   --..of homs  (see also definition 𝓔 in UF-Hom)
   𝑬𝑯 : {A B : Algebra 𝓤 S} (f g : hom A B) → Pred ∣ A ∣ 𝓤
   𝑬𝑯 f g x = ∣ f ∣ x ≡ ∣ g ∣ x

   𝑬𝑯-is-closed : funext 𝓥 𝓤 → {𝓸 : ∣ S ∣ } {𝑨 𝑩 : Algebra 𝓤 S}
            (f g : hom 𝑨 𝑩)     (𝒂 : ( ∥ S ∥ 𝓸 )  → ∣ 𝑨 ∣ )
    →   (( x : ∥ S ∥ 𝓸 ) → ( 𝒂 x ) ∈ ( 𝑬𝑯 {A = 𝑨} {B = 𝑩} f g ))
         ------------------------------------------------------
    →       ∣ f ∣ ( ∥ 𝑨 ∥ 𝓸 𝒂 ) ≡ ∣ g ∣ ( ∥ 𝑨 ∥ 𝓸 𝒂 )

   𝑬𝑯-is-closed fe {𝓸 = 𝓸}{𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ}
    (f , fhom) (g , ghom) 𝒂 p =
     f ( Fᴬ 𝓸 𝒂)                     ≡⟨ fhom 𝓸 𝒂 ⟩
     Fᴮ 𝓸 ( λ i  →  f ( 𝒂 i ) )    ≡⟨ ap ( Fᴮ _ ) ( fe p ) ⟩
     Fᴮ 𝓸 ( λ i →  g  ( 𝒂 i ) )    ≡⟨ (ghom 𝓸 𝒂)⁻¹ ⟩
     g ( Fᴬ 𝓸 𝒂)                     ∎

   -- Equalizer `𝑬𝑯 f g`  of `f g : Hom 𝑨 𝑩` is a subuniverse of 𝑨.
   𝑬𝑯-is-subuniverse :  funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
                 (f g : hom 𝑨 𝑩)  → Subuniverse {𝑨 = 𝑨}

   𝑬𝑯-is-subuniverse fe {𝑨 = 𝑨} {𝑩 = 𝑩} f g =
     mksub ( 𝑬𝑯 {A = 𝑨}{B = 𝑩} f g )
       λ 𝓸 𝒂 x → 𝑬𝑯-is-closed fe {𝑨 = 𝑨} {𝑩 = 𝑩}  f g 𝒂 x
