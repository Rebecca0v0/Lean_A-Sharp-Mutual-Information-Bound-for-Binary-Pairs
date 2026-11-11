module

public import BinaryPairBound.FiniteContraction

/-! # Equivalence with the usual finite-distribution KL supremum

`relativeEntropy r p` is the ordinary finite KL sum when `Supported r p`.
Every use as KL below supplies this condition. In particular, no alternative
input law putting mass outside the reference support is silently accepted.
-/

noncomputable section
@[expose] public section
open scoped BigOperators
namespace BinaryPairBound.FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

def Supported (r p : Law α) : Prop := ∀ a, p.mass a = 0 → r.mass a = 0

def relativeEntropy (r p : Law α) : ℝ :=
  ∑ a, r.mass a * Real.log (r.mass a / p.mass a)

def density (r p : Law α) (a : α) : ℝ := r.mass a / p.mass a

theorem density_nonneg (r p : Law α) (a : α) : 0 ≤ density r p a :=
  div_nonneg (r.nonneg a) (p.nonneg a)

theorem mass_mul_density {r p : Law α} (h : Supported r p) (a : α) :
    p.mass a * density r p a = r.mass a := by
  by_cases hp : p.mass a = 0
  · simp [hp, h a hp]
  · exact mul_div_cancel₀ _ hp

theorem sum_mass_mul_density {r p : Law α} (h : Supported r p) :
    ∑ a, p.mass a * density r p a = 1 := by
  simp_rw [mass_mul_density h]
  exact r.total

theorem relativeEntropy_eq_entropy {r p : Law α} (h : Supported r p) :
    relativeEntropy r p = entropy p.mass (density r p) := by
  unfold entropy
  rw [sum_mass_mul_density h, Real.log_one, mul_zero, sub_zero]
  simp only [mass_mul_density h]
  rfl

@[simp] theorem relativeEntropy_self (p : Law α) : relativeEntropy p p = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases hp : p.mass a = 0
  · simp [hp]
  · simp [hp]

theorem supported_out {r p : Law α} (h : Supported r p) (K : Channel α β) :
    Supported (out r K) (out p K) := by
  intro b hb
  apply Finset.sum_eq_zero
  intro a _
  have hz := joint_zero_of_out_zero p K hb a
  rcases mul_eq_zero.mp hz with hp | hK
  · simp [h a hp]
  · simp [hK]

theorem density_out {r p : Law α} (h : Supported r p) (K : Channel α β) :
    density (out r K) (out p K) = transfer p K (density r p) := by
  funext b
  unfold density transfer
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have hd := mass_mul_density h a
  dsimp [density] at hd
  change r.mass a * K.prob a b = p.mass a * K.prob a b * (r.mass a / p.mass a)
  rw [mul_right_comm _ (K.prob a b), hd]

theorem relativeEntropy_out_eq_entropy {r p : Law α} (h : Supported r p)
    (K : Channel α β) :
    relativeEntropy (out r K) (out p K) =
      entropy (out p K).mass (transfer p K (density r p)) := by
  rw [relativeEntropy_eq_entropy (supported_out h K), density_out h K]

theorem relativeEntropy_nonneg {r p : Law α} (h : Supported r p) :
    0 ≤ relativeEntropy r p := by
  rw [relativeEntropy_eq_entropy h]
  exact entropy_nonneg p (density_nonneg r p)

theorem relativeEntropy_dataProcessing {r p : Law α} (h : Supported r p)
    (K : Channel α β) : relativeEntropy (out r K) (out p K) ≤ relativeEntropy r p := by
  rw [relativeEntropy_out_eq_entropy h, relativeEntropy_eq_entropy h]
  exact entropy_transfer_le p K (density_nonneg r p)

/-- Tilting a reference law by a normalized nonnegative likelihood ratio. -/
def tilt (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hm : ∑ a, p.mass a * f a = 1) : Law α where
  mass a := p.mass a * f a
  nonneg a := mul_nonneg (p.nonneg a) (hf a)
  total := hm

theorem supported_tilt (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hm : ∑ a, p.mass a * f a = 1) : Supported (tilt p f hf hm) p := by
  intro a ha
  simp [tilt, ha]

theorem entropy_congr_support (p : Law α) {f g : α → ℝ}
    (h : ∀ a, p.mass a ≠ 0 → f a = g a) : entropy p.mass f = entropy p.mass g := by
  have hterm : ∀ a, p.mass a * f a = p.mass a * g a := by
    intro a
    by_cases hp : p.mass a = 0
    · simp [hp]
    · rw [h a hp]
  unfold entropy
  simp_rw [hterm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p.mass a = 0
  · simp [hp]
  · rw [h a hp]

theorem transfer_congr_support (p : Law α) (K : Channel α β) {f g : α → ℝ}
    (h : ∀ a, p.mass a ≠ 0 → f a = g a) : transfer p K f = transfer p K g := by
  funext b
  unfold transfer
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p.mass a = 0
  · simp [hp]
  · rw [h a hp]

theorem transfer_smul (p : Law α) (K : Channel α β) (f : α → ℝ) (t : ℝ) :
    transfer p K (fun a => t * f a) = fun b => t * transfer p K f b := by
  funext b
  simp only [transfer, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem relativeEntropy_tilt (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hm : ∑ a, p.mass a * f a = 1) :
    relativeEntropy (tilt p f hf hm) p = entropy p.mass f := by
  rw [relativeEntropy_eq_entropy (supported_tilt p f hf hm)]
  apply entropy_congr_support p
  intro a hp
  simp [density, tilt, mul_div_cancel_left₀ _ hp]

theorem relativeEntropy_out_tilt (p : Law α) (K : Channel α β) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hm : ∑ a, p.mass a * f a = 1) :
    relativeEntropy (out (tilt p f hf hm) K) (out p K) =
      entropy (out p K).mass (transfer p K f) := by
  rw [relativeEntropy_out_eq_entropy (supported_tilt p f hf hm)]
  congr 1
  apply transfer_congr_support p K
  intro a hp
  simp [density, tilt, mul_div_cancel_left₀ _ hp]

/-- The conventional alternative-input KL ratios; the unchanged input adds zero. -/
def probabilityRatios (p : Law α) (K : Channel α β) : Set ℝ :=
  {v | ∃ r : Law α, Supported r p ∧
    v = relativeEntropy (out r K) (out p K) / relativeEntropy r p}

theorem ratios_eq_probabilityRatios (p : Law α) (K : Channel α β) :
    ratios p K = probabilityRatios p K := by
  ext v
  constructor
  · rintro ⟨f, hf, rfl⟩
    let m := ∑ a, p.mass a * f a
    have hm0 : 0 ≤ m := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (hf a)
    by_cases hm : m = 0
    · have he := entropy_zero_of_mean_zero p hf hm
      refine ⟨p, (fun _ h => h), ?_⟩
      simp [he]
    · let g := fun a => m⁻¹ * f a
      have hg : ∀ a, 0 ≤ g a := fun a => mul_nonneg (inv_nonneg.mpr hm0) (hf a)
      have hgmean : ∑ a, p.mass a * g a = 1 := by
        simp only [g, mul_left_comm _ m⁻¹, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hm
      refine ⟨tilt p g hg hgmean, supported_tilt p g hg hgmean, ?_⟩
      rw [relativeEntropy_out_tilt, relativeEntropy_tilt]
      dsimp [g]
      rw [transfer_smul, entropy_smul, entropy_smul]
      exact (mul_div_mul_left _ _ (inv_ne_zero hm)).symm
  · rintro ⟨r, hr, rfl⟩
    refine ⟨density r p, density_nonneg r p, ?_⟩
    rw [relativeEntropy_out_eq_entropy hr, relativeEntropy_eq_entropy hr]

/-- The finite-alphabet coefficient is precisely the supremum of KL ratios over
all alternative input probability distributions absolutely continuous with the reference. -/
theorem coefficient_eq_sup_KL (p : Law α) (K : Channel α β) :
    coefficient p K = sSup (probabilityRatios p K) := by
  rw [coefficient, ratios_eq_probabilityRatios]

end BinaryPairBound.FiniteInfo
