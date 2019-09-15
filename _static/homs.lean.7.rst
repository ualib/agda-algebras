.. highlight:: lean

::

  import data.set
  universes u v w
  namespace ualib
    definition op (γ: Type w) (α: Type u) := (γ → α) → α
    structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type u)
    section algebra
      parameter σ: signature
      def algebra_on (α: Type u) := Π f, op (σ.ρ f) α
      def algebra := sigma algebra_on
      instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
      instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
    end algebra
  end ualib
  namespace ualib
    section basic_facts
      parameter {σ: signature}
      def hom {𝔸 𝔹: algebra σ} (g: 𝔸 → 𝔹): Prop := ∀ f a, g (𝔸 f a) = 𝔹 f (g ∘ a)
      def epic {α β: Type u} (g: α → β ): Prop := ∀ y, ∃ x, g x = y
      def monic {α β: Type u} (g: α → β): Prop := ∀ ⦃x₁ x₂⦄, g x₁ = g x₂ → x₁ = x₂
      def bijective {α β: Type u} (g: α → β): Prop := epic g ∧ monic g
  
      open classical function
      local attribute [instance] prop_decidable
  
      noncomputable def inverse {α β: Type u} (f: α → β) (default: α): β → α := λ b, if h: ∃ a, f a = b then some h else default
      noncomputable def right_inv {α β: Type u} (f : α → β) (h₁: epic f): β → α := λ b, some (h₁ b)

      lemma r_inv_is_r_inv {α β: Type u} (f: α → β) (h₁: epic f): ∀ b, b = f ((right_inv f h₁) b) := 
      assume b, have h₂: (right_inv f h₁) b = some (h₁ b), from rfl,
      have h₃: f (some (h₁ b)) = b, from some_spec (h₁ b), eq.subst (eq.symm h₂) (eq.symm h₃)
  
      -- BEGIN
      /-Lemma. If g: 𝔸 → 𝔹 and h: 𝔸 → ℂ are homs, g epic,
        and ker g ⊆ ker h, then there is a hom k: 𝔹 → C such
        that h = g ∘ k.
  
               g
           𝔸 ----> 𝔹
           |      /
           |     /
         h |    / k
           |   /
           |  /
           v v         
            ℂ 
      -/
      lemma hom_factor_down {𝔸 𝔹 ℂ: algebra σ}

      -- assumptions:
      (g: 𝔸 → 𝔹) (h: 𝔸 → ℂ) (hg: hom g) (hh: hom h) (hs: epic g)
      (kk: ∀ x y, g x = g y → h x = h y):

      -- conclusion:
      ∃ k: 𝔹 → ℂ, (h = k ∘ g) ∧ (hom k) := 

      -- proof:
      let g_inv:= (right_inv g hs) in 
      let k:= λ (b: 𝔹), h (g_inv b) in 
  
      -- prove the left conjunct
      have hl: h = k ∘ g, from 
        have h₁: ∀ a, h a = k (g a), from
          assume a,
          have h₃: g a = g (g_inv (g a)), from 
            r_inv_is_r_inv g hs (g a),
          (kk a (g_inv (g a))) h₃,
        funext h₁,
  
      -- prove the right conjunct
      have hr: hom k, from
        assume f b,
        have h₁: ∃ a, g ∘ a = b, from 
          let a' := g_inv ∘ b in 
          exists.intro a'
            (have h₂: ∀ i, g (a' i) = b i, from
              assume i,
              calc g (a' i) = g (g_inv (b i)): rfl
              ... = b i: eq.symm ((r_inv_is_r_inv g hs) (b i)),
            funext h₂), 
        show k (𝔹 f b) = ℂ f (k ∘ b), from 
          have h₇: ∀ a, k (𝔹 f (g ∘ a)) = ℂ f (k ∘ (g ∘ a)),
          from assume a,
            calc 
              k (𝔹 f (g ∘ a)) = k (g (𝔸 f a)): by rw hg
                          ... = h (𝔸 f a): by rw hl
                          ... = ℂ f (h ∘ a): by rw hh
                          ... = ℂ f (k ∘ g ∘ a): by rw hl,
          have h₅: g ∘ (some h₁) = b, from some_spec h₁,
          calc 
            k (𝔹 f b) = k (𝔹 f (g ∘ (some h₁))): by rw h₅
            ... = ℂ f (k ∘ g ∘ (some h₁)): by rw (h₇ (some h₁))
            ... = ℂ f (k ∘ b): by rw (some_spec h₁),
        
      exists.intro k (and.intro hl hr)
      -- END  
    end basic_facts
  end ualib

