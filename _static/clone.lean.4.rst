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

      parameters (α : Type*) (F : Type*) (X : set (op F α))

      structure is_clone (C : set (op F α)) :=
      (proj_closed : ∀ k, (λ (x : F → α), x k) ∈ C)
      (
        comp_closed : ∀ f (g : F → op F α),
        f ∈ C → (∀ i, g i ∈ C) → (λ x, f (λ i, g i x)) ∈ C
      )
      -- The smallest clone containing X
      inductive clo : set (op F α)
      | proj (k) : clo (π k)
      | comp {f} {g : F → op F α} :
          f ∈ X → (∀ i, clo (g i)) → clo (λ x, f (λ i, g i x))
      theorem clo_contains : X ⊆ clo :=
      begin
        intros _ h,
        apply clo.comp h,
        apply clo.proj
      end
        theorem clo_is_clone : is_clone clo :=
      {
        proj_closed := clo.proj,

        comp_closed :=
        begin
          intros _ _ fc gc,
          induction fc with _ f _ _ _ ih,
          { apply gc },
          { apply @clo.comp f,
            assumption,
            apply ih }
        end
      }

      theorem clo_is_smallest (Y : set (op F α)) :
      is_clone Y → X ⊆ Y → clo ⊆ Y :=
      begin
        intros hY hX f hf,
        induction hf,
        { apply hY.proj_closed },
        {
          apply hY.comp_closed,
          apply hX,
          repeat { assumption }
        }
      end
    end clo

end clone


      -- BEGIN

section term_algebra
  parameters {σ : signature} (𝔸 : algebra σ)

  -- TODO: relate clone of term operations to term algebra

end term_algebra
      -- END


end clone

