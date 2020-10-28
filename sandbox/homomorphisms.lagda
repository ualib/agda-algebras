\begin{code}
-- File: homomorphisms.agda
-- Author: William DeMeo and Siva Somayyajula
-- Date: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import congruences
open import prelude using (global-dfunext)

module homomorphisms {𝑆 : Signature 𝓞 𝓥} where

open import prelude using (_∘_; _⊆_; EpicInv; cong-app; EInvIsRInv; Image_∋_; embedding-elim; _≃_;
 Nat; NatΠ; NatΠ-is-embedding; embedding-criterion; _∼_; is-embedding; fst; snd; invertible; 𝑖𝑑;
 equivs-are-embeddings; id; invertibles-are-equivs; dintensionality; is-subsingleton; fiber; monic;
 intensionality; hfunext) public

compatible-op-map : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)
                    (𝑓 : ∣ 𝑆 ∣)(g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇

compatible-op-map 𝑨 𝑩 𝑓 g = ∀ 𝒂 → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)
--(infered type  𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)

op_interpreted-in_and_commutes-with : {𝓠 𝓤 : Universe}
   (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓠 𝑆) (𝑩 : Algebra 𝓤 𝑆)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g = compatible-op-map 𝑨 𝑩 𝑓 g

is-homomorphism : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
is-homomorphism 𝑨 𝑩 g = ∀ (𝑓 : ∣ 𝑆 ∣) → compatible-op-map 𝑨 𝑩 𝑓 g

hom : {𝓠 𝓤 : Universe} → Algebra 𝓠 𝑆 → Algebra 𝓤 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

epi : {𝓠 𝓤 : Universe} → Algebra 𝓠 𝑆 → Algebra 𝓤 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
epi 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g × Epic g

𝒾𝒹 : {𝓤 : Universe} (A : Algebra 𝓤 𝑆) → hom A A
𝒾𝒹 _ = (λ x → x) , λ _ _ → 𝓇ℯ𝒻𝓁

id-is-hom : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → is-homomorphism 𝑨 𝑨 (𝑖𝑑 ∣ 𝑨 ∣)
id-is-hom = λ _ _ → refl _

-- composition of homomorphisms 1
HCompClosed : {𝓠 𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑪 : Algebra 𝓦 𝑆)
 →            hom 𝑨 𝑩  →  hom 𝑩 𝑪
              --------------------
 →                 hom 𝑨 𝑪

HCompClosed (A , FA) (B , FB) (C , FC) (g , ghom) (h , hhom) = h ∘ g , γ
  where
   γ : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f  →  A) → (h ∘ g)(FA f a) ≡ FC f (h ∘ g ∘ a)

   γ f a = (h ∘ g) (FA f a) ≡⟨ ap h ( ghom f a ) ⟩
          h (FB f (g ∘ a)) ≡⟨ hhom f ( g ∘ a ) ⟩
          FC f (h ∘ g ∘ a) ∎

-- composition of homomorphisms 2
∘-hom : {𝓠 𝓤 𝓦 : Universe}
        (𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑪 : Algebra 𝓦 𝑆)
        {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣} {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}
 →      is-homomorphism{𝓤}{𝓦} 𝑩 𝑪 g →  is-homomorphism{𝓠}{𝓤} 𝑨 𝑩 f
       --------------------------------------------------------------------
 →          is-homomorphism{𝓠}{𝓦} 𝑨 𝑪 (g ∘ f)

∘-hom 𝑨 𝑩 𝑪 {f} {g} fhom ghom = ∥ HCompClosed 𝑨 𝑩 𝑪 (g , ghom) (f , fhom) ∥


homFactor : {𝓤 : Universe} → funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
           ---------------------------------------------
 →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
 (g , ghom) (h , hhom) Kh⊆Kg hEpic = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpic) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → ker-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EInvIsRInv fe h hEpic) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EInvIsRInv fe h hEpic) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EInvIsRInv fe h hEpic)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EInvIsRInv fe h hEpic)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C)
    →         ϕ (FC f a)  ≡  FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))                ≡⟨ i   ⟩
    g (hInv (FC f (h ∘ (hInv ∘ c)))) ≡⟨ ii  ⟩
    g (hInv (h (FA f (hInv ∘ c))))   ≡⟨ iii ⟩
    g (FA f (hInv ∘ c))              ≡⟨ iv  ⟩
    FB f (λ x → g (hInv (c x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC f) (ι f c))
     ii  = ap (λ - → g (hInv -)) (hhom f (hInv ∘ c))⁻¹
     iii = useker f c
     iv  = ghom f (hInv ∘ c)

HomFactor : {𝓠 𝓤 𝓦 : Universe} → global-dfunext
 →          {𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}{𝑪 : Algebra 𝓦 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          (KER-pred ∣ h ∣) ⊆ (KER-pred ∣ g ∣)  →  Epic ∣ h ∣
           ------------------------------------------------
 →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

HomFactor gfe {A , FA}{B , FB}{C , FC}(g , ghom)(h , hhom) Kh⊆Kg hEpic = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpic) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → KER-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EInvIsRInv gfe h hEpic) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = gfe  λ x → Kh⊆Kg (ξ x)

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EInvIsRInv gfe h hEpic) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EInvIsRInv gfe h hEpic)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EInvIsRInv gfe h hEpic)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C) → ϕ (FC f a) ≡ FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))               ≡⟨ i   ⟩
    g (hInv (FC f (h ∘ (hInv ∘ c)))) ≡⟨ ii  ⟩
    g (hInv (h (FA f (hInv ∘ c))))   ≡⟨ iii ⟩
    g (FA f (hInv ∘ c))              ≡⟨ iv  ⟩
    FB f (λ x → g (hInv (c x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC f) (ι f c))
     ii  = ap (λ - → g (hInv -)) (hhom f (hInv ∘ c))⁻¹
     iii = useker f c
     iv  = ghom f (hInv ∘ c)


--(extensional versions)
--Isomorphism
_≅_ : {𝓤 𝓦 : Universe} (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑨 ≅ 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , ((∣ f ∣ ∘ ∣ g ∣) ∼ ∣ 𝒾𝒹 𝑩 ∣) × ((∣ g ∣ ∘ ∣ f ∣) ∼ ∣ 𝒾𝒹 𝑨 ∣)
--Recall, f ~ g means f and g are extensionally equal; i.e., ∀ x, f x ≡ g x

-- An algebra is (extensionally) isomorphic to itself
refl-≅ id≅ : {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ≅ 𝑨
id≅ 𝑨 = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , (λ a → 𝓇ℯ𝒻𝓁) , (λ a → 𝓇ℯ𝒻𝓁)
refl-≅ = id≅

sym-≅ : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}
 →      𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑨
sym-≅ h = fst ∥ h ∥ , fst h , ∥ snd ∥ h ∥ ∥ , ∣ snd ∥ h ∥ ∣

trans-≅ : {𝓠 𝓤 𝓦 : Universe}
          (𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑪 : Algebra 𝓦 𝑆)
 →         𝑨 ≅ 𝑩 → 𝑩 ≅ 𝑪
          ----------------
 →            𝑨 ≅ 𝑪

trans-≅ 𝑨 𝑩 𝑪 ab bc = f , g , α , β
 where
  f1 : hom 𝑨 𝑩
  f1 = ∣ ab ∣
  f2 : hom 𝑩 𝑪
  f2 = ∣ bc ∣
  f : hom 𝑨 𝑪
  f = HCompClosed 𝑨 𝑩 𝑪 f1 f2

  g1 : hom 𝑪 𝑩
  g1 = fst ∥ bc ∥
  g2 : hom 𝑩 𝑨
  g2 = fst ∥ ab ∥
  g : hom 𝑪 𝑨
  g = HCompClosed 𝑪 𝑩 𝑨 g1 g2

  f1∼g2 : ∣ f1 ∣ ∘ ∣ g2 ∣ ∼ ∣ 𝒾𝒹 𝑩 ∣
  f1∼g2 = ∣ snd ∥ ab ∥ ∣

  g2∼f1 : ∣ g2 ∣ ∘ ∣ f1 ∣ ∼ ∣ 𝒾𝒹 𝑨 ∣
  g2∼f1 = ∥ snd ∥ ab ∥ ∥

  f2∼g1 : ∣ f2 ∣ ∘ ∣ g1 ∣ ∼ ∣ 𝒾𝒹 𝑪 ∣
  f2∼g1 =  ∣ snd ∥ bc ∥ ∣

  g1∼f2 : ∣ g1 ∣ ∘ ∣ f2 ∣ ∼ ∣ 𝒾𝒹 𝑩 ∣
  g1∼f2 = ∥ snd ∥ bc ∥ ∥

  α : ∣ f ∣ ∘ ∣ g ∣ ∼ ∣ 𝒾𝒹 𝑪 ∣
  α x = (∣ f ∣ ∘ ∣ g ∣) x                   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        ∣ f2 ∣ ( (∣ f1 ∣ ∘ ∣ g2 ∣) (∣ g1 ∣ x)) ≡⟨ ap ∣ f2 ∣ (f1∼g2 (∣ g1 ∣ x)) ⟩
        ∣ f2 ∣ ( ∣ 𝒾𝒹 𝑩 ∣ (∣ g1 ∣ x))        ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
        (∣ f2 ∣ ∘ ∣ g1 ∣) x                  ≡⟨ f2∼g1 x ⟩
        ∣ 𝒾𝒹 𝑪 ∣ x                         ∎
  β : ∣ g ∣ ∘ ∣ f ∣ ∼ ∣ 𝒾𝒹 𝑨 ∣
  β x = (ap ∣ g2 ∣ (g1∼f2 (∣ f1 ∣ x))) ∙ g2∼f1 x


⨅≅ : global-dfunext → {𝓠 𝓤 𝓘 : Universe}
     {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
 →   ((i : I) → (𝒜 i) ≅ (ℬ i))
     ---------------------------
 →       ⨅ 𝒜 ≅ ⨅ ℬ

⨅≅ gfe {𝓠}{𝓤}{𝓘}{I}{𝒜}{ℬ} AB = γ
 where
  F : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣
  F i = ∣ fst (AB i) ∣
  Fhom : ∀ i → is-homomorphism (𝒜 i) (ℬ i) (F i)
  Fhom i = ∥ fst (AB i) ∥

  G : ∀ i → ∣ ℬ i ∣ → ∣ 𝒜 i ∣
  G i = fst ∣ snd (AB i) ∣
  Ghom : ∀ i → is-homomorphism (ℬ i) (𝒜 i) (G i)
  Ghom i = snd ∣ snd (AB i) ∣

  F∼G : ∀ i → (F i) ∘ (G i) ∼ (∣ 𝒾𝒹 (ℬ i) ∣)
  F∼G i = fst ∥ snd (AB i) ∥

  G∼F : ∀ i → (G i) ∘ (F i) ∼ (∣ 𝒾𝒹 (𝒜 i) ∣)
  G∼F i = snd ∥ snd (AB i) ∥

  ϕ : ∣ ⨅ 𝒜 ∣ → ∣ ⨅ ℬ ∣
  ϕ a i = F i (a i)

  ϕhom : is-homomorphism (⨅ 𝒜) (⨅ ℬ) ϕ
  ϕhom 𝑓 𝒂 = gfe (λ i → (Fhom i) 𝑓 (λ x → 𝒂 x i))

  ψ : ∣ ⨅ ℬ ∣ → ∣ ⨅ 𝒜 ∣
  ψ b i = ∣ fst ∥ AB i ∥ ∣ (b i)

  ψhom : is-homomorphism (⨅ ℬ) (⨅ 𝒜) ψ
  ψhom 𝑓 𝒃 = gfe (λ i → (Ghom i) 𝑓 (λ x → 𝒃 x i))

  ϕ~ψ : ϕ ∘ ψ ∼ ∣ 𝒾𝒹 (⨅ ℬ) ∣
  ϕ~ψ 𝒃 = gfe λ i → F∼G i (𝒃 i)

  ψ~ϕ : ψ ∘ ϕ ∼ ∣ 𝒾𝒹 (⨅ 𝒜) ∣
  ψ~ϕ 𝒂 = gfe λ i → G∼F i (𝒂 i)

  γ : ⨅ 𝒜 ≅ ⨅ ℬ
  γ = (ϕ , ϕhom) , ((ψ , ψhom) , ϕ~ψ , ψ~ϕ)


embedding-lift-nat : {𝓠 𝓤 𝓘 : Universe} → hfunext 𝓘 𝓠 → hfunext 𝓘 𝓤
 →                   {I : 𝓘 ̇}{A : I → 𝓠 ̇}{B : I → 𝓤 ̇}
                     (h : Nat A B)
 →                   ((i : I) → is-embedding (h i))
                     -------------------------------
 →                   is-embedding(NatΠ h)

embedding-lift-nat hfiq hfiu h hem = NatΠ-is-embedding hfiq hfiu h hem

embedding-lift-nat' : {𝓠 𝓤 𝓘 : Universe} → hfunext 𝓘 𝓠 → hfunext 𝓘 𝓤
 →                    {I : 𝓘 ̇}{𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
                      (h : Nat (fst ∘ 𝒜) (fst ∘ ℬ))
 →                   ((i : I) → is-embedding (h i))
                     -------------------------------
 →                   is-embedding(NatΠ h)

embedding-lift-nat' hfiq hfiu h hem = NatΠ-is-embedding hfiq hfiu h hem

embedding-lift : {𝓠 𝓤 𝓘 : Universe} → hfunext 𝓘 𝓠 → hfunext 𝓘 𝓤
 →               {I : 𝓘 ̇} -- global-dfunext → {𝓠 𝓤 𝓘 : Universe}{I : 𝓘 ̇}
                 {𝒜 : I → Algebra 𝓠 𝑆}{ℬ : I → Algebra 𝓤 𝑆}
 →               (h : ∀ i → ∣ 𝒜 i ∣ → ∣ ℬ i ∣)
 →               ((i : I) → is-embedding (h i))
                 ----------------------------------------------------
 →               is-embedding(λ (x : ∣ ⨅ 𝒜 ∣) (i : I) → (h i) (x i))
embedding-lift {𝓠} {𝓤} {𝓘} hfiq hfiu {I} {𝒜} {ℬ} h hem =
 embedding-lift-nat' {𝓠} {𝓤} {𝓘} hfiq hfiu {I} {𝒜} {ℬ} h hem


--INTENSIONAL versions
--Isomorphism
_≅'_ : {𝓤 𝓦 : Universe} (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑨 ≅' 𝑩 =  Σ f ꞉ (hom 𝑨 𝑩) , Σ g ꞉ (hom 𝑩 𝑨) , ((∣ f ∣ ∘ ∣ g ∣) ≡ ∣ 𝒾𝒹 𝑩 ∣) × ((∣ g ∣ ∘ ∣ f ∣) ≡ ∣ 𝒾𝒹 𝑨 ∣)
-- An algebra is (intensionally) isomorphic to itself
id≅' : {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ≅' 𝑨
id≅' 𝑨 = 𝒾𝒹 𝑨 , 𝒾𝒹 𝑨 , 𝓇ℯ𝒻𝓁 , 𝓇ℯ𝒻𝓁

iso→embedding : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
 →              (ϕ : 𝑨 ≅ 𝑩) → is-embedding (fst ∣ ϕ ∣)
iso→embedding {𝓤}{𝓦}{𝑨}{𝑩} ϕ = γ
 where
  f : hom 𝑨 𝑩
  f = ∣ ϕ ∣
  g : hom 𝑩 𝑨
  g = ∣ snd ϕ ∣

  finv : invertible ∣ f ∣
  finv = ∣ g ∣ , (snd ∥ snd ϕ ∥ , fst ∥ snd ϕ ∥)

  γ : is-embedding ∣ f ∣
  γ = equivs-are-embeddings ∣ f ∣ (invertibles-are-equivs ∣ f ∣ finv)



-- is-algebra-iso : {𝑨 𝑩 : Algebra 𝓤 𝑆} (f : hom 𝑨 𝑩) → 𝓤 ⁺ ̇
-- is-algebra-iso {𝑨} f = ker ∣ f ∣ ≡ 𝟎 {A = ∣ 𝑨 ∣}

-- AlgebraIsos : (𝑨 𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
-- AlgebraIsos 𝑨 𝑩 = Σ f ꞉ (hom 𝑨 𝑩) , is-algebra-iso {𝑨}{𝑩} f

-- _≈_ : Rel (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
-- 𝑨 ≈ 𝑩 = is-singleton (AlgebraIsos 𝑨 𝑩)


-- The following seems to be the most useful definition (for our
-- purposes) of the class of homomomrphic images of an algebra.
HomImage : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}(𝑩 : Algebra 𝓤 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓠 ⊔ 𝓤 ̇
HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b

HomImagesOf : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ (𝓦 ⁺) ̇
HomImagesOf {𝓤}{𝓦} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

_is-hom-image-of_ : {𝓤 𝓦 : Universe} (𝑩 : Algebra 𝓦 𝑆)
  →                (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇

_is-hom-image-of_ {𝓤}{𝓦} 𝑩 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf{𝓤}{𝓦} 𝑨) , 𝑩 ≅ ∣ 𝑪ϕ ∣

_is-hom-image-of-class_ : {𝓤 : Universe}
  →                       Algebra 𝓤 𝑆
  →                       Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)
  →                       𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

_is-hom-image-of-class_ {𝓤} 𝑩 𝓚 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
                             (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ 𝑆) ,
                     (𝑩 is-hom-image-of-class 𝓚)

H : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
H 𝓚 = HomImagesOfClass 𝓚

-- Here 𝓛𝓚 represents a (universe-indexed) collection of classes.
H-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
 →         (𝓤 : Universe) → Algebra 𝓤 𝑆
 →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

H-closed 𝓛𝓚 = λ 𝓤 𝑩 → _is-hom-image-of-class_ {𝓤 = 𝓤} 𝑩 (𝓛𝓚 𝓤) → 𝑩 ∈ (𝓛𝓚 𝓤)

all-ops-in_and_commute-with : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
all-ops-in 𝑨 and 𝑩 commute-with g = is-homomorphism 𝑨 𝑩 g

\end{code}
