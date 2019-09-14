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
  
      lemma sub_of_sub_inter_sub {𝔸: algebra σ} (C: γ → set 𝔸): (∀ i, Sub (C i)) → Sub (⋂i, C i):= assume h: (∀ i, Sub (C i)), assume (f: σ.ℱ) (a: σ.ρ f → 𝔸) (h₁: ∀ x, a x ∈ ⋂i, C i), Inter.intro (λ j, (h j) f a (λ x, Inter.elim (h₁ x) j))

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

  -- BEGIN
  inductive Y {𝔸: algebra σ} (X: set 𝔸): set 𝔸
  | var (x: 𝔸): x ∈ X → Y x
  | app (f: σ.ℱ) (a: σ.ρ f → 𝔸): (∀ i, Y (a i)) → Y (𝔸.snd f a)
  -- END
  end subuniverse
