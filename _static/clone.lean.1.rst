.. code-block:: lean

    import data.set  -- the set.lean file from mathlib
    definition op (β α) := (β → α) → α
    definition π {β α} (i) : op β α := λ a, a i
    structure signature := mk :: (F : Type*) (ρ : F → Type*)
    definition algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α
    definition algebra (σ : signature) := sigma (algebra_on σ)
    instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
    instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩


    namespace clone

      section clo

        -- BEGIN
        parameters (α : Type*) (F : Type*) (X : set (op F α))

        structure is_clone (C : set (op F α)) :=
        ( proj_closed : ∀ k, (λ (x : F → α), x k) ∈ C )
        (
          comp_closed : ∀ f (g : F → op F α),
          f ∈ C → (∀ i, g i ∈ C) → (λ x, f (λ i, g i x)) ∈ C
        )
        -- END

      end clo

    end clone
