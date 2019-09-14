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
  
      -- BEGIN
      open classical function
      local attribute [instance] prop_decidable
  
      noncomputable def inverse {α β: Type u}
      (f: α → β) (default: α): β → α :=
      λ b, if h: ∃ a, f a = b then some h else default
  
      -- The right inverse of a surjective function.
      noncomputable def right_inv {α β: Type u} (f : α → β)
      (h₁: epic f): β → α := λ b, some (h₁ b)

      -- A surjective function has a right inverse.
      lemma r_inv_is_r_inv {α β: Type u}
      (f: α → β) (h₁: epic f): ∀ b, b = f ((right_inv f h₁) b) := 
      assume b,
      have h₂: (right_inv f h₁) b = some (h₁ b), from rfl,
      have h₃: f (some (h₁ b)) = b, from some_spec (h₁ b),
      eq.subst (eq.symm h₂) (eq.symm h₃)
      -- END
    end basic_facts
  end ualib
