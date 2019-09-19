::

  import data.set

  universe u -- where carrier types live
  universe v -- where operation symbol types live
  universe w -- where arity types live
  universe 𝕩 -- where variable types live

  namespace ualib

    def op (γ: Type w) (α: Type u) := (γ → α) → α
    def π {β α} (i): op β α := λ x, x i

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
