::

  universes u v w 𝕩 
  namespace ualib
    def op (γ: Type w) (α: Type u) := (γ → α) → α
    def π {γ α} (i): op γ α := λ (x: γ → α), x i
    structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type w)
    section algebra
      parameter σ: signature
      def algebra_on (α: Type u) := Π (f: σ.ℱ), op (σ.ρ f) α 
      def algebra := sigma algebra_on
      instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
      instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
    end algebra
  end ualib  

  -- BEGIN
  namespace ualib
    section examples
      parameter α: Type u      -- α is a carrier type
      parameter γ: Type w      -- γ is an arity type
  
      -- pr.
      -- The i-th projection (alternative definition)
      def pr (i: γ): op γ α:= λ (t: γ → α), t i

      variable aa: γ → α  -- aa is a γ-tuple of elements of type α 
      variable i: γ       -- i is an index
  
      -- It may seem we are making something out of nothing here.
      -- Indeed...
      lemma pi_is_projection: π i aa = aa i := rfl
      lemma pr_is_projection: pr i aa = aa i := rfl
  
      -- Denote the type of op symbols by ℱ (enter ``\mscrF``).
      parameter ℱ: Type v      -- an operation symbol type
      parameter ρ: ℱ → Type w  -- an arity function
      variable foo: ℱ          -- an operation symbol
  
      #check ρ foo              -- Type w
  
      -- signatures ---------
  
      #check signature       -- Type (max (u_1+1) (u_2+1))
  
      variable σ: signature -- a signature
      variable f: σ.ℱ        -- an operation symbol
  
      #check σ.ℱ             -- Type u_2
      #check σ.ρ             -- σ.ℱ → Type u_1
      #check σ.ρ f           -- Type u_1
  
      ----------------------------------------------
  
      -- An inhabitant of algebra_on assigns to each op symbol 
      -- f : F of arity β = σ.ρ f, an interpretation of f, 
      -- that is, a function of type (β → ?) → ?.
  
      variable 𝔸: algebra_on σ α    -- ``\BbbA``
  
      #check algebra_on σ α -- Type (max u_2 u_1 u)
  
      #check 𝔸              -- algebra_on σ α  
      #check f              -- σ.ℱ 
      #check 𝔸 f            -- op (σ.ρ f) α  
                           
      ----------------------------------------------
  
      #check psigma (algebra_on σ)
      -- Type (max (u_3+1) u_2 u_1 u_3)
  
      #check algebra σ
      -- Type (max (u_3+1) u_2 u_1 u_3)
  
      variable 𝔹 : algebra σ    -- ``\BbbB``
      #check 𝔹 f                -- ⇑𝔹 f : op (σ.ρ f) (𝔹.fst)
  
    end examples
  end ualib
  -- END
  