.. highlight:: lean

::

  import data.set
  universes u v w
  namespace ualib
    definition op (γ: Type w) (α: Type u) := (γ → α) → α
    structure signature := mk :: (ℱ: Type v) (ρ: ℱ  → Type u)
  
    section algebra
      parameter σ: signature
      def algebra_on (α: Type u) := Π f, op (σ.ρ f) α
      def algebra := sigma algebra_on
      instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
      instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
    end algebra

    section subuniverse
      parameters {α: Type u} {γ: Type w} {σ: signature}
      definition F := σ.ℱ 
      definition ρ := σ.ρ 
      def Sub {𝔸: algebra σ}(B₀: set 𝔸): Prop:= ∀ (f: F) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸.snd f a) ∈ B₀
      def is_subalgebra {𝔸: algebra σ}(B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= ∀ f b, ↑(𝔹 f b) = 𝔸.snd f ↑b
      def Sg {𝔸: algebra σ}(X: set 𝔸): set 𝔸:= ⋂₀ {U | Sub U ∧ X ⊆ U}

      theorem Inter.intro {𝔸: algebra σ} {x: 𝔸} {s: γ → set 𝔸}: (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) := assume h, iff.elim_right set.mem_Inter h

      theorem Inter.elim {𝔸: algebra σ} {x: 𝔸} {C: γ → set 𝔸}: (x ∈ ⋂ i, C i) →  (∀ i, x ∈ C i):= assume h, iff.elim_left set.mem_Inter h

      lemma sub_of_sub_inter_sub {𝔸: algebra σ} (C: γ → set 𝔸): (∀ i, Sub (C i)) → Sub (⋂i, C i):= assume h: (∀ i, Sub (C i)), show Sub (⋂i, C i), from
        assume (f: σ.ℱ) (a: σ.ρ f → 𝔸) (h₁: ∀ x, a x ∈ ⋂i, C i),
        Inter.intro (λ j, (h j) f a (λ x, Inter.elim (h₁ x) j))

      lemma subset_X_of_SgX {𝔸: algebra σ} (X : set 𝔸): X ⊆ Sg X:= assume x (h: x ∈ X), 
      assume W (h₁: W ∈ {U | Sub U ∧ X ⊆ U}), have h₂: Sub W ∧ X ⊆ W, from h₁, h₂.right h

      lemma sInter_mem {𝔸: algebra σ} {X: set 𝔸}: ∀ R, Sub R → X ⊆ R → (Sg X ⊆ R) := 
      assume R (h₁: Sub R) (h₂: X ⊆ R), assume x (h: x ∈ Sg X), h R (and.intro h₁ h₂)

      lemma sInter_mem' {𝔸: algebra σ} {X: set 𝔸}: ∀ R, Sub R ∧ X ⊆ R → (Sg X ⊆ R):= 
      assume R (hc : Sub R ∧ X ⊆ R), have h₁: Sub R, from hc.left,
      have h₂: X ⊆ R, from hc.right, assume x (h: x ∈ Sg X), h R (and.intro h₁ h₂)

      lemma sInter_mem'' {𝔸: algebra σ} {X: set 𝔸}: ∀ x, x ∈ Sg X → ∀ R, Sub R → X ⊆ R → x ∈ R:= assume x (h₁: x ∈ Sg X), assume (R: set 𝔸) (h₂: Sub R) (h₃: X ⊆ R), h₁ R (and.intro h₂ h₃)

      lemma SgX_is_Sub {𝔸: algebra σ} (X: set 𝔸): Sub (Sg X):= assume f (a: σ.ρ f → 𝔸) (h₀: ∀ i, a i ∈ Sg X), assume W (h: Sub W ∧ X ⊆ W), have h₁: Sg X ⊆ W, from sInter_mem' W h,
      have h': ∀ i, a i ∈ W, from assume i, h₁ (h₀ i), (h.left f a h')

      inductive Y {𝔸: algebra σ} (X: set 𝔸): set 𝔸
      | var (x : 𝔸) : x ∈ X → Y x
      | app (f : σ.ℱ) (a : σ.ρ f → 𝔸) : (∀ i, Y (a i)) → Y (𝔸.snd f a)

      lemma Y_is_Sub {𝔸: algebra σ}(X: set 𝔸): Sub (Y X):= assume f a (h: ∀ i, Y X (a i)),Y.app f a h 

      theorem sg_inductive {𝔸: algebra σ} (X: set 𝔸): Sg X = Y X :=
      have h₀: X ⊆ Y X, from assume x (h: x ∈ X), Y.var x h,
      have h₁: Sub (Y X), from assume f a (h : ∀ x, Y X (a x)), Y.app f a h,
      have inc_l: Sg X ⊆ Y X, from sInter_mem (Y X) h₁ h₀, 
      have inc_r: Y X ⊆ Sg X, from
        assume a (h: a ∈ Y X), have h₂: a ∈ Y X → a ∈ Sg X, from
        Y.rec
          (assume x (hr₁: x ∈ X), show x ∈ Sg X, from subset_X_of_SgX X hr₁)
          (assume f b (hr₂: ∀ i, b i ∈ Y X) (hr₃: ∀ i, b i ∈ Sg X), show 𝔸.snd f b ∈ Sg X, from SgX_is_Sub X f b hr₃ ),
          h₂ h,
        set.subset.antisymm inc_l inc_r

      lemma Y_is_min_Sub {𝔸: algebra σ} (U X: set 𝔸): Sub U → X ⊆ U → Y X ⊆ U:= assume (h₁: Sub U) (h₂ : X ⊆ U), assume (y: 𝔸)  (p: Y X y), have q: Y X y → Y X y → U y, from 
        Y.rec
          ( assume y (h: X y) (h': Y X y), h₂ h )
          ( assume f a (h₃: ∀ i, Y X (a i)) (h₄: ∀ i, Y X (a i) → U (a i)) (h₅: Y X (𝔸.snd f a)), have h₆: ∀ i, a i ∈ U, from
            assume i, h₄ i (h₃ i), h₁ f a h₆ ), q p p
    end subuniverse

    section homomorphism
      parameters {α: Type u} {γ: Type v}
      def homomorphic {σ: signature} {𝔸 𝔹: algebra σ} (h: 𝔸 → 𝔹) := ∀ f a, h (𝔸.snd f a) = 𝔹.snd f (h ∘ a)
      def homomorphic_verbose {σ: signature} {𝔸 𝔹: algebra σ} (h: 𝔸.fst → 𝔹.fst) := ∀ (f: σ.ℱ) (a : σ.ρ f → 𝔸.fst), h (𝔸.snd f a) = 𝔹.snd f (h ∘ a)
    end homomorphism

    def ker {α β: Type u} (f: α → β): α → α → Prop := λ a b, f a = f b

    section basic_facts
      parameter {σ: signature}
      def E {α β: Type u} (f g: α → β): set α := λ (x: α), f x = g x 
      def hom {𝔸 𝔹: algebra σ} (g: 𝔸 → 𝔹): Prop := ∀ f a, g (𝔸 f a) = 𝔹 f (g ∘ a)
      def E_homs {𝔸 𝔹: algebra σ} (g h: 𝔸 → 𝔹) (hg: hom g) (hh: hom h): set 𝔸 :=  λ (a: 𝔸), g a = h a 

    -- BEGIN
    -- Composition of homomorphisms is a homomorphism.
    lemma hom_comp_of_hom {𝔸 𝔹 ℂ: algebra σ}
    (g: 𝔸 → 𝔹) (h: 𝔹 → ℂ) (hg: hom g) (hh: hom h): hom (h ∘ g) :=
    assume f a, 
    show (h ∘ g)(𝔸 f a) = ℂ f (h ∘ g ∘ a), from 
      have h₃: (h ∘ g)(𝔸 f a) = h (g (𝔸 f a)), from  rfl,
      calc
        (h ∘ g)(𝔸 f a) = h ((𝔹 f) (g ∘ a)) : (h₁ f a) ▸ h₃ 
                   ... = (ℂ f) (h ∘ g ∘ a)  : h₂ f (g ∘ a)
    -- END
    end basic_facts
  end ualib
