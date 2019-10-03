::

  -- BEGIN
  universe u -- where carrier types live (often denoted α)
  universe v -- where op symbol types live (often β)
  universe w -- where arity types live (often γ)
  universe 𝕩 -- where variable types live (often X)
             -- (type ``\Bbbx`` to produce the symbol 𝕩)
  -- END
  namespace ualib
  
    -- op: the type of operation symbols.
    def op (γ: Type w) (α: Type u) := (γ → α) → α
  
    -- π: the i-th γ-ary projection is a (γ-ary) operation on α
    -- that returns the i-th element of the γ-tuple x.
    def π {γ α} (i): op γ α := λ (x: γ → α), x i
    
  end ualib
