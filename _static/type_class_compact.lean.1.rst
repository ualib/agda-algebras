-- File: type_class.lean
-- Authors: William DeMeo
-- Date: 26 Oct 2018
-- Updated: 26 Oct 2018


-- Reference: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html

import basic

namespace ualib

  --There are three steps involved in using type classes.

  --#.First, we declare a family of inductive types to be a type class.
  --#.Second, we declare instances of the type class.
  --#.Finally, we mark implicit args with [] brackets, so elaborator will use type class inference.

  --Step 1.Declare a family of inductive types.
    class inhabited (α: Type _) := (default: α)

    --...is shorthand for:
    --@[class] structure inhabited (α: Type _) := (default: α)

    --An element of ``inhabited α`` is an expression of the form ``inhabited.mk a``, for some ``a : α``. 
    --The projection ``inhabited.default`` "extracts" an elem of ``α`` from an element of ``inhabited α``.

  --Step 2.Populate the class with some instances.

    instance Prop_inhabited: inhabited Prop := inhabited.mk true
    instance bool_inhabited: inhabited bool := inhabited.mk tt
    instance nat_inhabited: inhabited nat := inhabited.mk 0
    instance unit_inhabited: inhabited unit := inhabited.mk ()

    --Alternatively, we could use the anonymous constructor, like so
    instance Prop_inhabited': inhabited Prop := ⟨true⟩ -- ...etc...

    --These declarations record the defs ``Prop_inhabited``, ``bool_inhabited``, ``nat_inhabited``, and ``unit_inhabited`` in a *list of instances* so that when the elaborator looks for a val to assign to an argument ``?M`` of type ``inhabited α``, it checks the list for a suitable instance.
    
    --For example, when looking for an instance of ``inhabited Prop``, it finds ``Prop_inhabited``.

  --Step 3.Define a function that infers an element ``s: inhabited α`` and puts it to use. 
  
  --default
  --Extract the corresponding element ``a: α`` of the given type ``α``.
    def default (α: Type _) [s: inhabited α]: α := @inhabited.default α s

    #check default Prop  -- Prop ...etc...

  --In general, when we write ``default α`` the elaborator tries to synthesize an element of type ``α``.

  --We can "see" the value that is synthesized with ``#reduce``.
    #reduce default Prop -- true  ...etc...

  --Sometimes we want to think of the default element of a type as being an *arbitrary* element, whose value should not play a role in proofs. For that purpose, we write ``arbitrary α`` instead of ``default α``. The definition of ``arbitrary`` is the same as that of default, but is marked ``irreducible`` to discourage the elaborator from unfolding it. This does not preclude proofs from making use of the value, however, so ``arbitrary`` is used to merely signal intent.

  --Chaining Instances
  --------------------

  --If that were the extent of type class inference, it would not be very impressive; it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table. What makes type class inference powerful is that we can *chain* instances. That is, an instance declaration can in turn depend on an implicit instance of a type class. This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

  --For example, if two types ``α`` and ``β`` are inhabited, then so is their product.
    instance prod_inhabited {α β: Type _} [inhabited α] [inhabited β]:
      inhabited (prod α β) :=
    ⟨(default α, default β)⟩

  --So now using type class inference, we can infer a default element of ``nat × bool``:
    #check  default (nat × bool) -- ℕ × bool
    #reduce default (nat × bool) -- (0, tt)
    example: default (nat × bool) = (0, tt) := rfl

  --Similarly, we can inhabit function spaces with suitable constant functions.
    instance fun_inhabited (α: Type _) {β: Type _} [inhabited β]:
      inhabited (α → β) :=
    inhabited.mk (λ (a: α), default β)

    #check  default (nat → bool) -- ℕ → bool
    #reduce default (nat → bool) -- λ (a: ℕ), tt
    example: default (nat → bool) = λ (a: ℕ), tt := rfl
    
    #check  default (nat → Prop × unit) -- ℕ → Prop × unit
    #reduce default (nat → Prop × unit) -- λ (a: ℕ), (true, punit.star)
    example: default (nat → Prop × unit) = λ (a: ℕ), (true, ()) := rfl

  -----------------------------------------------------------
  --EXERCISE: try defining default instances for other types,
  --such as sum types and the list type.

    instance list_inhabited (α: Type _) [inhabited α]:
      inhabited (list α) :=
    inhabited.mk (list.cons (default α) list.nil)

    instance sum_inl_inhabited (α: Type _) (β: Type _)
      [inhabited α]: inhabited (sum α β) :=
    inhabited.mk (sum.inl (default α))

    instance sum_inr_inhabited (α: Type _) (β: Type _)
      [inhabited β]: inhabited (sum α β) :=
    inhabited.mk (sum.inr (default β))

    -- Here are some types that are not assumed to be inhabited.
    variables (α : Type) (β : Type)

    #check  default (sum nat bool) -- ℕ ⊕ bool
    #check  default (sum α bool)   -- α ⊕ bool
    #check  default (sum Prop β)   -- Prop ⊕ β

    -- #check  default (sum α β)  -- results in error:
    -- failed to synthesize type class instance 
    -- for α β : type ⊢ inhabited (α ⊕ β)

    example: default (sum nat bool) = sum.inr tt := rfl
    example: default (sum   α bool) = sum.inr tt := rfl
    example: default (sum nat    β) = sum.inl 0 := rfl
    example: default (sum nat unit) = sum.inr () := rfl
      
  --Inferring Notation
  --------------------

  --We now motivate the use of type classes in functional programming languages---namely,
  --
  --      to overload notation in a principled way.
  --
  --A symbol like ``+`` can be have unrelated meanings; sometimes called "ad-hoc" overloading. Typically, the ``+`` symbol denotes a binary operation, of type ``α → α → α`` for some ``α``. Type classes let us infer an appropriate addition function for a given type.  *This is especially useful for developing algebraic hierarchies of structures in a formal setting*.

  --The standard library declares a type class ``has_add α`` as follows:
  universes u v
  class has_add (α: Type u) := (add: α → α → α)
  def add {α: Type u} [has_add α]: α → α → α := has_add.add
  local notation a `+` b := add a b

  instance nat_has_add: has_add nat:= has_add.mk nat.add
  instance bool_had_add: has_add bool:= has_add.mk bor

  #reduce 2 + 2   -- 4
  #reduce tt + ff -- tt

  --prod_has_add: ptwise addition of pairs
  instance prod_has_add {α: Type u} {β: Type v}
    [has_add α] [has_add β]: has_add (α × β) :=
  has_add.mk (λ (p q: α × β), (p.fst + q.fst, p.snd + q.snd))

  #check (1, tt) + (2, ff) -- ℕ × bool
  example: (1, tt) + (2, ff) = (3, tt) := rfl

  --fun_has_add: ptwise addition of functions
  instance fun_has_add {α: Type u} {β: Type v}
    [has_add β]: has_add (α → β) :=
  has_add.mk (λ (f g: α → β), (λ (a:α), (f a) + (g a)))
  
  #reduce (λ (n:nat), n+1) + (λ (n:nat), n-1)
  #reduce (λ (n:nat), 1) + (λ (n:nat), 3) -- λ (a: ℕ), 4


  -----------------------------------------------------------
  --EXERCISE: try defining instances of ``has_add`` for lists, 
  --and show that they work as expected.

  --add_lists: ptwise addition of lists
  def add_lists {α: Type u} [has_add α]: (list α) → (list α) → (list α)
  | l1 list.nil := l1
  | list.nil l2 := l2
  | (h1::t1) (h2::t2) := list.cons (h1 + h2) (add_lists t1 t2)

  --list_has_add
  instance list_has_add {α: Type u} [has_add α]: has_add (list α) :=
  has_add.mk (λ (l1 l2: list α), add_lists l1 l2)

  #reduce add_lists [0,10] [1,2,3] -- [1, 12, 3]

  --Decidable Propositions
  ------------------------

  --Another example from the lstl is the type class of ``decidable`` propositions. An element of ``Prop`` is "decidable" if we can decide whether it is true or false. The distinction is only useful in constructive mathematics; classically, every proposition is decidable. But if we use the classical principle, say, to define a function by cases, that function will not be computable. Algorithmically speaking, the ``decidable`` type class can be used to infer a procedure that effectively determines whether or not the proposition is true. As a result, the type class supports such computational definitions when they are possible while at the same time allowing a smooth transition to the use of classical definitions and classical reasoning.
  
  -- .. todo:: revisit this section.

  --Managing Type Class Inference
  -------------------------------

  --Show the classes and instances that are currently in scope using
    #print classes
    #print instances inhabited
    -- ...produces:
    --  ualib.sum_inr_inhabited : Π (α : Type u_1) (β : Type u_2) [_inst_1 : inhabited β], inhabited (α ⊕ β)
    --  ualib.sum_inl_inhabited : Π (α : Type u_1) (β : Type u_2) [_inst_1 : inhabited α], inhabited (α ⊕ β)
    --  ualib.list_inhabited : Π (α : Type u_1) [_inst_1 : inhabited α], inhabited (list α)
    --  ualib.fun_inhabited : Π (α : Type u_1) {β : Type u_2} [_inst_1 : inhabited β], inhabited (α → β)
    -- ...etc...

  -- If we need an expression that Lean can infer by type class inference, we ask Lean to infer it using the tactic ``apply_instance`` or the expression ``infer_instance``.

    def foo: has_add nat := by apply_instance
    #print foo -- ualib.nat_has_add (or, outside ualib namespace, nat.has_add)
    #reduce foo -- add := λ (a a_1: ℕ), ... proof object ...

    def bar: has_add nat := infer_instance
    #print bar -- infer_instance
    #reduce bar -- add := λ (a a_1: ℕ), ... proof object ...

    def baz: inhabited (nat → nat) := by apply_instance
    #print baz -- uafun.fun_inhabited ℕ (or, outside ualib, pi.inhabited ℕ)
    #reduce baz -- {default := λ (a: ℕ), 0}

    def bla: inhabited (nat → nat) := infer_instance
    #print bla -- infer_instance
    #reduce bla -- {default := λ (a: ℕ), 0}

    lemma ex1 : inhabited (nat → nat) := by apply_instance
    #print ex1 -- ualib.fun_inhabited ℕ
    #reduce ex1 -- {default := λ (a: ℕ), 0}

    lemma ex2 : inhabited (nat → nat) := ualib.fun_inhabited ℕ
    #print ex2 -- ualib.fun_inhabited ℕ
    #reduce ex2 -- {default := λ (a: ℕ), 0}
  
    lemma ex3 : inhabited (nat → nat) := infer_instance
    #print ex3 -- infer_instance
    #reduce ex3 -- {default := λ (a: ℕ), 0}

    --The following fails:
    -- lemma ex4 {α: Type*} : inhabited (set α) := by apply_instance
    -- Lean can't find an instance of ``inhabited (set α)`` because the class is buried under a definition.

    lemma ex4 {α: Type*} : inhabited (set α) := ⟨∅⟩
    #print ex4 -- λ {α: Type u_1}, {default := ∅}
    #reduce @ex4 nat -- {default := λ (a: ℕ), false}

    -- or we could unfold the definition of set
    lemma ex5 {α: Type*} : inhabited (set α) := by unfold set; apply_instance
    #print ex5 -- λ {α: Type u_1}, eq.mpr _ (ualib.fun_inhabited α)
    #reduce @ex5 -- λ {α: Type u_1}, {default := λ (a: α), true}

    --(section ends with notes on debugging and inference priority of namespaces)

  --Coercions using Type Classes
  ------------------------------

  --The most basic type of coercion maps elements of one type to another. For example, a coercion from ``nat`` to ``int`` allows us to view ``n : nat`` as having type ``int``. Some coercions depend on parameters; e.g., given ``α``,  view ``l: list α`` as of type ``set α``---the set of elements in l. The corresponding coercion is defined on the "family" of types ``list α``, parameterized by ``α``.

  --Three kinds of coercions in Lean:
  --1. from a family of types to another family of types
  --2. from a family of types to the class of sorts
  --3. from a family of types to the class of function types
  --We consider each kind in turn.

  --1. allows us to view an inhabitant of a member of the source family as inhabiting a corresponding member of the target family.

  --Define a coercion from ``α`` to ``β`` by declaring an instance of ``has_coe α β``; e.g.,
    instance bool_to_Prop: has_coe bool Prop := has_coe.mk (λ b, b=tt)
    #reduce if tt then 3 else 5
    #reduce if ff then 3 else 5

  --coercion from list to set requires a helper function.
    def list.to_set {α: Type u}: list α → set α
    | [] := ∅
    | (h::tl) := {h} ∪ (list.to_set tl)

  --coercion from ``list α`` to ``set α``.
    instance list_to_set_coe (α: Type u): has_coe (list α) (set α) :=
    has_coe.mk list.to_set

    def s: set nat := {1, 2}
    def l: list nat := [3, 4]
    #check s ∪ l -- s ∪ ↑l: set ℕ

  -- #check s ∪ [3,4] -- fails since [3,4] is of type ``list ?m``
    #check s ∪ ↑[3,4]   -- set ℕ (okay)

  --The standard library defines a coercion from subtype ``{x : α // p x}`` to ``α`` as follows:
    instance coe_subtype {α: Type u} {p: α → Prop}: has_coe {x // p x} α := has_coe.mk (λ s, subtype.val s)

  --2. from a family of types to the class of sorts. View an inhabitant of a member of source family as a type.
  --By the *class of sorts*, we mean the collection of universes ``Type u``.
  
  --A coercion of the second kind is of the form
  --c: Π x1: A1, ..., xn: An, F x1 ... xn → Type u
  --where ``F`` is a family of types. We can write ``s: t`` whenever ``t`` is of type ``F a1 ... an``.
  --i.e., the coercion allows us to view the elements of ``F a1 ... an`` as types.
  --This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a ``Type``. For example, we can define a semigroup as follows:

    structure Semigroup: Type (u+1) :=
    (carrier: Type u) (mul: carrier → carrier → carrier)
    (mul_assoc: ∀ a b c: carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S: Semigroup): has_mul (S.carrier) :=
    has_mul.mk S.mul

    #check signature
    #check algebra -- signature → Type (max (u_3+1) u_1 u_2 u_3)

end ualib

    universes u v w

    class sig :=  mk :: (ℱ: Type u) (ρ: ℱ → nat)
    
    structure ssig (α: Type u) := mk :: (mul: α → α → α)
    structure msig (α: Type u) extends ssig α := mk :: (one: α)
    structure gsig (α: Type u) extends msig α := mk :: (inv: α → α)

    class opsymbol := mk :: (name: string) (arity: nat)

    -- def one : op := {name:= "one", arity:= 0}
    -- def mul : op := {name:= "mul", arity:= 2}
    -- def inv : op := {name:= "inv", arity:= 1}

    structure signat := mk :: (ops: list opsymbol)

    -- def gsignat : signat := {ops:=[one, inv, mul]}
    structure signature :=
    mk :: (ℱ: Type v) (ρ: ℱ → Type w)

    structure oper (ℱ: Type v) (ρ: ℱ → Type w) :=
    mk :: (f: ℱ) (ar: ρ f)


    open fin
    def f:= fin 7
    #check f
    #check list (Type u)
    instance binary : opsymbol := {name:= "b", arity:= 2}

    def operation (s: opsymbol) (carrier: Type u) := ((fin s.arity) → carrier) → carrier

    --signature.mk []
    variable α: Type u
    #check gsig α
    variable f: gsig α 
    #check f.one
    
    inductive group_sig : Type
    | eye : group_sig
    | inv : group_sig
    | mul : group_sig

    open group_sig

    def ar (f: group_sig): nat := match f with
    | eye := 0
    | inv := 1
    | mul := 2
    end


    structure algebraic (σ: sig) :=
    (carrier: Type u) (ops: Π(f:σ.ℱ), (nat → carrier) → carrier)

    structure Semigroup: Type (u+1) :=
    (carrier: Type u) (mul: carrier → carrier → carrier)
    (mul_assoc: ∀ a b c: carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S: Semigroup): has_mul (S.carrier) :=
    has_mul.mk S.mul



  -- - 3. from a family of types to the class of function types
  --3: view an inhabitant of the source family as a function.



