:: 

  universes u v w 𝕩 
  namespace ualib
    def op (γ: Type w) (α: Type u) := (γ → α) → α
    def π {γ α} (i): op γ α := λ (x: γ → α), x i
    structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type w)
    -- BEGIN
    section algebra
      parameter σ: signature
  
      -- algebra_on
      -- Given a signature σ, each symbol f: σ.ℱ is given an 
      -- interpretation as an operation, on a carrier type α, 
      -- and of arity σ.ρ f.
  
      def algebra_on (α: Type u) := Π (f: σ.ℱ), op (σ.ρ f) α 
  
      -- algebra
      -- This is the type of algebras; an algebra consists of a 
      -- pair, (α, 𝔸), where α is a carrier type and 𝔸 has type
      -- algebra_on α.
  
      def algebra := sigma algebra_on
    
        -- N.B. The Lean syntax ``sigma algebra_on σ`` denotes the 
        -- dependent pair type (or "dependent product"),
        --
        --       ∑ (α: Type u) (algebra_on α).
        -- or
        --
        --       ∑ (α: Type u) (Π (f: σ.ℱ), op (σ.ρ f) α)
  
      instance alg_carrier:
      has_coe_to_sort algebra := ⟨_, sigma.fst⟩
      
      instance alg_operations:
      has_coe_to_fun algebra := ⟨_, sigma.snd⟩
  
    end algebra
    -- END
  end ualib  
