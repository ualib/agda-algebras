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

-- BEGIN
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

-- END

namespace ualib
  section examples

    -- operations --------
    parameter α: Type u      -- α is a carrier type
    parameter γ: Type w      -- γ is an arity type

    variable aa: γ → α      -- aa is a γ-tuple of elements of type α 
    variable i: γ           -- i is an index

    #check (π i aa: α)

    -- Example: the tuple (1, 2, 3, ...).
    definition add_one: ℕ → ℕ := λ n, n+1

    -- What's the 3rd projection of add_one?
    #eval π 3 add_one           -- answer: 4

    -- Example: the constant tuple (7, 7, 7, ...)
    definition sevens : ℕ → ℕ := λ n, 7

    -- What's the 3rd projection of sevens?
    #eval π 3 sevens           -- answer: 7

    -- pr: alt def of the i-th projection. This is the (γ-ary)
    -- operation on α that returns the i-th element of a given γ-tuple.
    def pr (i: γ): op γ α:= λ (t: γ → α), t i


    #check aa i           -- α
    #check pr i aa        -- α
 
    -- It may seem we are making something out of
    -- nothing here, since... 
    lemma projection_is_projection: π i aa = aa i := rfl
    lemma projection_is_projection': pr i aa = aa i := rfl

    -- We denote the op symbol type by ℱ (``\mscrF``).
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

-- Misc. Notes
-- -----------
-- An algebra pairs a carrier with an interpretation of the op symbols.
-- def algebra := sigma algebra_on
-- 
-- sigma is the dependent product (i.e., dependent pair) type.
--
-- sigma := Π α, ⟨α, β (α)⟩ 
--
-- This is appropriate here since an algebra consists of a universe (of type α),
-- along with operations on that universe, and the type of each operation is
-- dependent on the type, α, of the universe.
--
-- We use coersions so that, if A is an algebra, Lean will correctly interpret 
-- the symbol A to mean either the algebra itself or the carrier of the algebra.