::

  universe u -- where carrier types live (usually α)
  universe v -- where op symbol types live (usually β)
  universe w -- where arity types live (usually γ)
  universe 𝕩 -- where variable types live (usually X)
             -- (type ``\Bbbx`` to produce 𝕩)
  
  namespace ualib
  
    -- op: the type of operation symbols.
    def op (γ: Type w) (α: Type u) := (γ → α) → α
      -- N.B. NEW CONVETION
      --   1. carrier type is *first* arg.
      --   2. arity type is *second* arg.
      -- (i.e., arguments swapped wrt old convention)
  
    -- π: the i-th β-ary projection is a (β-ary) operation on α
    -- that returns the i-th element of the β-tuple x.
    def π {β α} (i): op β α := λ (x: β → α), x i
  
  end ualib  
  
  namespace ualib
    -- signature: the type of operation symbols together
    -- with their arities (given by the function ρ).
    structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type w)
  
    section algebra
      parameter σ: signature
  
      -- algebra_on: given a signature σ, each symbol f: σ.ℱ
      -- is given an interpretation as an operation, on a
      -- carrier type α, and of arity σ.ρ f.
      def algebra_on (α: Type u) := Π (f: σ.ℱ), op (σ.ρ f) α 
  
      -- algebra: the type of algebras; consists of a pair, (α, 𝔸),
      -- where α is a carrier type and 𝔸 has type ``algebra_on α``.
      def algebra := sigma algebra_on
    
        -- N.B. The Lean syntax ``sigma algebra_on σ`` denotes the 
        -- dependent pair type (or "dependent product"),
        --
        --       ∑ (α: Type u) (algebra_on α).
        -- or
        --
        --       ∑ (α: Type u) (Π (f: σ.ℱ), op (σ.ρ f) α)
  
      instance alg_carrier : has_coe_to_sort algebra :=
      ⟨_, sigma.fst⟩
      
      instance alg_operations : has_coe_to_fun algebra := 
      ⟨_, sigma.snd⟩
  
    end algebra
  end ualib  
  
  namespace ualib
    section examples
  
      -- operations --------
      parameter α: Type u      -- α is a carrier type
      parameter γ: Type w      -- γ is an arity type
  
      variable aa: γ → α      -- aa is a γ-tuple of elements of type α 
      variable i: γ           -- i is an index
  
      #check (π i aa: α)
  
      -- BEGIN
      -- Example: the tuple (1, 2, 3, ...).
      definition add_one: ℕ → ℕ := λ n, n+1
  
      -- What's the 3rd projection of add_one?
      #eval π 3 add_one           -- answer: 4
  
      -- Example: the constant tuple (7, 7, 7, ...)
      definition sevens : ℕ → ℕ := λ n, 7
  
      -- What's the 3rd projection of sevens?
      #eval π 3 sevens           -- answer: 7
  
      -- END
  
    end examples
  end ualib

