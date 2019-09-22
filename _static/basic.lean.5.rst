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
  -- BEGIN
    -- signature: the type of operation symbols together
    -- with their arities (given by the function ρ).
    structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type w)
  -- END
  end ualib
