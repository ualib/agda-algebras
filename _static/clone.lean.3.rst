::

  import data.set
  universes u v w 𝕩
    namespace ualib
      definition op (γ: Type w) (α: Type u) := (γ → α) → α
      definition π {β α} (i): op β α := λ x, x i
      structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type u)
      section algebra
        parameters (α: Type u) (γ: Type w) (σ: signature)
        def algebra_on (α: Type u) := Π f, op (σ.ρ f) α 
        def algebra := sigma algebra_on
        instance alg_carrier : has_coe_to_sort algebra :=
        ⟨_, sigma.fst⟩
        instance alg_operations : has_coe_to_fun algebra :=
        ⟨_, sigma.snd⟩
        def pr (i: γ): op γ α := λ (t: γ → α), t i
      end algebra
    end ualib
  
  namespace ualib
    section clone
      parameter ℱ: Type v    -- operation symbol type
      parameter {σ: signature}
      variable {τ: signature}
      def comp {α: Type u} {γ γ': Type w}
      (f: op γ α) (gs: γ → op γ' α): op γ' α :=
      λ x, f (λ i, gs i x)
      infix `◾`:50 := comp
      lemma comp_proj_id {α: Type u} {γ: Type w}
      (ar:γ) (gs: γ → op γ α): comp (π ar) gs = gs ar := rfl
      structure clone {α: Type u} {γ: Type w}
      (C: set (op γ α)) :=
      ( proj_closed: ∀ (ar: γ), (λ (x: γ → α), x ar) ∈ C )
      ( comp_closed: ∀ (f: op γ α)  (gs: γ → op γ α), 
            f ∈ C → (∀ i, gs i ∈ C) → (f ◾ gs) ∈ C )
      inductive clo {α: Type u} {γ: Type w}
      {𝒪 : set (op γ α)} : set (op γ α)
      | pr (ar): clo (π ar)
      | comp {f} {gs: γ → op γ α}:
        f ∈ 𝒪  → (∀ i, clo (gs i)) → clo (f ◾ gs)
      theorem clo_contains_gens {α: Type u} {γ: Type w}
      (𝒪 : set (op γ α)) : 𝒪 ⊆ (@clo α γ 𝒪) :=
      assume f (h: f ∈ 𝒪), show f ∈ (@clo α γ 𝒪),
      from clo.comp h clo.pr
      -- BEGIN 
      theorem clo_is_clone {α: Type u} {γ: Type w}
      (𝒪 : set (op γ α)): clone (@clo α γ 𝒪):=
      { 
        proj_closed := clo.pr,
        comp_closed :=
        assume (f: op γ α) (gs: γ → op γ α),
        assume (hf: f ∈ clo) (hgs: ∀ (i:γ), (gs i) ∈ clo),
        show (f ◾ gs) ∈ clo, from 
        begin
        induction hf with ar' f' gs' hf' ghs' ih,
          { -- show comp (π ar') gs ∈ clo
            apply hgs
          },
          { -- show: comp (comp f' gs') gs ∈ clo
            apply clo.comp hf', 
            assumption
          }
        end
      }
  
      theorem clone_is_minimal
      {α: Type u} {γ: Type w}
      (𝒪 : set (op γ α)) (ops: set (op γ α)):
      clone ops → 𝒪 ⊆ ops → (@clo α γ 𝒪) ⊆ ops :=
      assume (hco: clone ops) (hso: 𝒪 ⊆ ops),
      assume f (hf: f ∈ @clo α γ 𝒪), 
      show f ∈ ops, from 
      begin
        induction hf with 
        ar' -- γ 
        g'  -- op γ α
        gs' -- γ → op γ α
        hg' -- g' ∈ 𝒪 
        ghs'-- ∀ (i: γ), clo (gs' i)
        ih, -- ∀ (i: γ),(λ(f: op γ α)(hf: f ∈ clo), f ∈ ops)(gs' i)
  
        { -- base step: show π ar' ∈ Ops
          apply hco.proj_closed 
        },
  
        { -- induction step: show comp f' gs' ∈ Ops
          apply hco.comp_closed, apply hso,
          repeat { assumption } 
        }
      end
      -- END
    end clone
  
  end ualib
  
  
  