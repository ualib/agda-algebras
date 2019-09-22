::

  -- BEGIN
  universe u -- where carrier types live (usually α)
  universe v -- where op symbol types live (usually β)
  universe w -- where arity types live (usually γ)
  universe 𝕩 -- where variable types live (usually X)
             -- (type ``\Bbbx`` to produce 𝕩)
  -- END
  namespace ualib
  
    -- op: the type of operation symbols.
    def op (γ: Type w) (α: Type u) := (γ → α) → α
  
    -- π: the i-th β-ary projection is a (β-ary) operation on α
    -- that returns the i-th element of the β-tuple x.
    def π {β α} (i): op β α := λ (x: β → α), x i
    
  end ualib
