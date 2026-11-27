module

public import BinaryPairBound.BinaryInformation
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Finite laws and the standard KL contraction coefficient

从有限概率分布、信道和密度熵出发，完整证明内部系数与通常KL比值定义的对应，包括零概率与满支持特例。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Finite probability laws, channels, and density entropy

定义有限字母表上的概率分布、信道和密度熵，并证明经过信道后密度熵不增加。
-/

@[expose] public noncomputable section FiniteEntropy

open scoped BigOperators

namespace FiniteInfo

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

structure Channel (α β : Type*) [Fintype β] where
  prob : α → β → ℝ
  nonneg : ∀ a b, 0 ≤ prob a b
  total : ∀ a, ∑ b, prob a b = 1

def entropy {α : Type*} [Fintype α] (p f : α → ℝ) : ℝ :=
  (∑ a, p a * f a * Real.log (f a)) -
    (∑ a, p a * f a) * Real.log (∑ a, p a * f a)

def out {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) : Law β where
  mass b := ∑ a, p.mass a * K.prob a b
  nonneg b := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (K.nonneg a b)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, K.total, mul_one]
    exact p.total

def transfer {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (f : α → ℝ) (b : β) : ℝ :=
  (∑ a, p.mass a * K.prob a b * f a) / (out p K).mass b

def Contracts {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (lam : ℝ) : Prop :=
  ∀ f : α → ℝ, (∀ a, 0 ≤ f a) →
    entropy (out p K).mass (transfer p K f) ≤ lam * entropy p.mass f

theorem entropy_nonneg {α : Type*} [Fintype α] (p : Law α)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ entropy p.mass f := by
  have h := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := p.mass) (p := f) (fun a _ => p.nonneg a) p.total (fun a _ => hf a)
  simp only [smul_eq_mul] at h
  unfold entropy
  simpa only [mul_assoc] using sub_nonneg.mpr h

theorem transfer_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (b : β) :
    0 ≤ transfer p K f b :=
  div_nonneg (Finset.sum_nonneg fun a _ =>
    mul_nonneg (mul_nonneg (p.nonneg a) (K.nonneg a b)) (hf a)) ((out p K).nonneg b)

theorem joint_zero_of_out_zero {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) {b : β} (hb : (out p K).mass b = 0) (a : α) :
    p.mass a * K.prob a b = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    mul_nonneg (p.nonneg a) (K.nonneg a b))).mp hb a (Finset.mem_univ a)

theorem out_mul_transfer {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (f : α → ℝ) (b : β) :
    (out p K).mass b * transfer p K f b = ∑ a, p.mass a * K.prob a b * f a := by
  by_cases hb : (out p K).mass b = 0
  · simp [hb, joint_zero_of_out_zero p K hb]
  · exact mul_div_cancel₀ _ hb

theorem sum_out_mul_transfer {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (f : α → ℝ) :
    ∑ b, (out p K).mass b * transfer p K f b = ∑ a, p.mass a * f a := by
  simp_rw [out_mul_transfer]
  rw [Finset.sum_comm]
  congr 1
  funext a
  simp_rw [mul_right_comm (p.mass a), ← Finset.mul_sum, K.total, mul_one]

theorem entropy_transfer_le {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    entropy (out p K).mass (transfer p K f) ≤ entropy p.mass f := by
  have hpoint (b : β) :
      (out p K).mass b * transfer p K f b * Real.log (transfer p K f b) ≤
        ∑ a, p.mass a * K.prob a b * f a * Real.log (f a) := by
    by_cases hb : (out p K).mass b = 0
    · simp [hb, joint_zero_of_out_zero p K hb]
    have hbpos : 0 < (out p K).mass b := lt_of_le_of_ne ((out p K).nonneg b) (Ne.symm hb)
    have hw : ∑ a, p.mass a * K.prob a b / (out p K).mass b = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      change (out p K).mass b * ((out p K).mass b)⁻¹ = 1
      exact mul_inv_cancel₀ hb
    have h := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
      (w := fun a => p.mass a * K.prob a b / (out p K).mass b) (p := f)
      (fun a _ => div_nonneg (mul_nonneg (p.nonneg a) (K.nonneg a b)) hbpos.le)
      hw (fun a _ => hf a)
    simp only [smul_eq_mul] at h
    have he : (∑ a, p.mass a * K.prob a b / (out p K).mass b * f a) =
        transfer p K f b := by
      simp only [transfer, div_eq_mul_inv, mul_right_comm _ _ (f _), Finset.sum_mul]
    rw [he] at h
    have hm := mul_le_mul_of_nonneg_left h hbpos.le
    convert hm using 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      field_simp
  unfold entropy
  rw [sum_out_mul_transfer]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ b, ∑ a, p.mass a * K.prob a b * f a * Real.log (f a) :=
      Finset.sum_le_sum fun b _ => hpoint b
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [show ∀ b, p.mass a * K.prob a b * f a * Real.log (f a) =
        (p.mass a * f a * Real.log (f a)) * K.prob a b by intro b; ring]
      rw [← Finset.mul_sum, K.total, mul_one]

end FiniteInfo

end FiniteEntropy

/-! ## The internal entropy contraction coefficient

用密度熵比值定义内部系数，证明它在 0 与 1 之间且给出有效的收缩上界。
-/

@[expose] public noncomputable section FiniteContraction

open scoped BigOperators

namespace FiniteInfo

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def ratios (p : Law α) (K : Channel α β) : Set ℝ :=
  {r | ∃ f : α → ℝ, (∀ a, 0 ≤ f a) ∧
    r = entropy (out p K).mass (transfer p K f) / entropy p.mass f}

/-- KL contraction expressed using nonnegative likelihood-ratio densities.
The zero-entropy test contributes zero, including deterministic inputs. -/
def coefficient (p : Law α) (K : Channel α β) : ℝ := sSup (ratios p K)

theorem ratios_nonempty (p : Law α) (K : Channel α β) : (ratios p K).Nonempty := by
  exact ⟨_, (fun _ => 0), (fun _ => le_rfl), rfl⟩

theorem ratios_bddAbove (p : Law α) (K : Channel α β) : BddAbove (ratios p K) := by
  refine ⟨1, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  by_cases he : entropy p.mass f = 0
  · simp [he]
  · exact (div_le_one (lt_of_le_of_ne (entropy_nonneg p hf) (Ne.symm he))).mpr
      (entropy_transfer_le p K hf)

theorem coefficient_nonneg (p : Law α) (K : Channel α β) : 0 ≤ coefficient p K := by
  apply Real.sSup_nonneg
  rintro r ⟨f, hf, rfl⟩
  exact div_nonneg (entropy_nonneg (out p K) (transfer_nonneg p K hf)) (entropy_nonneg p hf)

theorem coefficient_le_one (p : Law α) (K : Channel α β) : coefficient p K ≤ 1 := by
  apply csSup_le (ratios_nonempty p K)
  rintro r ⟨f, hf, rfl⟩
  by_cases he : entropy p.mass f = 0
  · simp [he]
  · exact (div_le_one (lt_of_le_of_ne (entropy_nonneg p hf) (Ne.symm he))).mpr
      (entropy_transfer_le p K hf)

theorem coefficient_mem (p : Law α) (K : Channel α β) :
    coefficient p K ∈ Set.Icc (0 : ℝ) 1 := ⟨coefficient_nonneg p K, coefficient_le_one p K⟩

theorem contracts_coefficient (p : Law α) (K : Channel α β) :
    Contracts p K (coefficient p K) := by
  intro f hf
  by_cases he : entropy p.mass f = 0
  · have h := entropy_transfer_le p K hf
    simpa only [he, mul_zero] using h
  · apply (div_le_iff₀ (lt_of_le_of_ne (entropy_nonneg p hf) (Ne.symm he))).mp
    exact le_csSup (ratios_bddAbove p K) ⟨f, hf, rfl⟩

theorem coefficient_le_iff {p : Law α} {K : Channel α β} {lam : ℝ} (hlam : 0 ≤ lam) :
    coefficient p K ≤ lam ↔ Contracts p K lam := by
  constructor
  · intro h f hf
    exact (contracts_coefficient p K f hf).trans
      (mul_le_mul_of_nonneg_right h (entropy_nonneg p hf))
  · intro h
    apply csSup_le (ratios_nonempty p K)
    rintro r ⟨f, hf, rfl⟩
    by_cases he : entropy p.mass f = 0
    · simpa [he] using hlam
    · exact (div_le_iff₀ (lt_of_le_of_ne (entropy_nonneg p hf) (Ne.symm he))).mpr (h f hf)

theorem mul_log_mul (a b : ℝ) :
    a * b * Real.log (a * b) = a * (b * Real.log b) + b * (a * Real.log a) := by
  have h := Real.negMulLog_mul a b
  simp only [Real.negMulLog_def] at h
  nlinarith [h]

/-- Homogeneity permits restriction to likelihood-ratio densities of mean one. -/
theorem entropy_smul (p f : α → ℝ) (t : ℝ) :
    entropy p (fun a => t * f a) = t * entropy p f := by
  have hmean : (∑ a, p a * (t * f a)) = t * ∑ a, p a * f a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold entropy
  rw [hmean, mul_log_mul]
  have hsum : (∑ a, p a * (t * f a) * Real.log (t * f a)) =
      t * ∑ a, p a * f a * Real.log (f a) + (∑ a, p a * f a) * (t * Real.log t) := by
    simp_rw [mul_assoc (p _) (t * f _), mul_log_mul, mul_add]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
  rw [hsum]
  ring

theorem entropy_zero_of_mean_zero (p : Law α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a)
    (hm : ∑ a, p.mass a * f a = 0) : entropy p.mass f = 0 := by
  have hz : ∀ a, p.mass a * f a = 0 := fun a =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => mul_nonneg (p.nonneg a) (hf a))).mp hm
      a (Finset.mem_univ a)
  simp [entropy, hz]

def Channel.comp (K : Channel α β) (L : Channel β γ) : Channel α γ where
  prob a c := ∑ b, K.prob a b * L.prob b c
  nonneg a c := Finset.sum_nonneg fun b _ => mul_nonneg (K.nonneg a b) (L.nonneg b c)
  total a := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, L.total, mul_one]
    exact K.total a

theorem out_comp_mass (p : Law α) (K : Channel α β) (L : Channel β γ) (c : γ) :
    (out p (K.comp L)).mass c = (out (out p K) L).mass c := by
  simp only [out, Channel.comp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem transfer_comp (p : Law α) (K : Channel α β) (L : Channel β γ) (f : α → ℝ) :
    transfer p (K.comp L) f = transfer (out p K) L (transfer p K f) := by
  funext c
  simp only [transfer, out_comp_mass]
  congr 1
  calc
    _ = ∑ b, (∑ a, p.mass a * K.prob a b * f a) * L.prob b c := by
      simp only [Channel.comp, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      change (∑ a, p.mass a * K.prob a b * f a) * L.prob b c =
        (out p K).mass b * L.prob b c * transfer p K f b
      rw [mul_right_comm _ (L.prob b c), out_mul_transfer]

theorem Contracts.postprocess {p : Law α} {K : Channel α β} {lam : ℝ}
    (h : Contracts p K lam) (L : Channel β γ) : Contracts p (K.comp L) lam := by
  intro f hf
  have hout : (out p (K.comp L)).mass = (out (out p K) L).mass := funext (out_comp_mass p K L)
  rw [hout, transfer_comp]
  exact (entropy_transfer_le (out p K) L (transfer_nonneg p K hf)).trans (h f hf)

theorem coefficient_postprocess (p : Law α) (K : Channel α β) (L : Channel β γ) :
    coefficient p (K.comp L) ≤ coefficient p K :=
  (coefficient_le_iff (coefficient_nonneg p K)).mpr ((contracts_coefficient p K).postprocess L)

end FiniteInfo

end FiniteContraction

/-! ## Identifying density ratios with finite KL ratios

证明密度熵比值等于支持范围内的 KL 比值，从而把内部系数接到概率分布的 KL 表达式。
-/

@[expose] public noncomputable section FiniteKL

open scoped BigOperators

namespace FiniteInfo

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

end FiniteInfo

end FiniteKL

/-! ## The standard coefficient, excluding the unchanged input

从 KL 候选分布中排除 Q=P，并证明这个标准系数与内部系数相等；无候选分布时取零。
-/

@[expose] public noncomputable section FiniteKLStandard

open scoped BigOperators

namespace FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Gibbs' equality case on finite laws, including zero-probability atoms. -/
theorem relativeEntropy_eq_zero_iff {r p : Law α} (h : Supported r p) :
    relativeEntropy r p = 0 ↔ r = p := by
  constructor
  · intro he
    have hm := sum_mass_mul_density h
    have hj := Real.strictConvexOn_mul_log.map_sum_eq_iff'
      (t := Finset.univ) (w := p.mass) (p := density r p)
      (fun a _ => p.nonneg a) p.total (fun a _ => density_nonneg r p a)
    simp only [smul_eq_mul] at hj
    have hsum : (∑ a, p.mass a * (density r p a * Real.log (density r p a))) = 0 := by
      rw [relativeEntropy_eq_entropy h] at he
      simpa only [entropy, hm, Real.log_one, mul_zero, sub_zero, mul_assoc] using he
    have hd : ∀ a, p.mass a ≠ 0 → density r p a = 1 := by
      have heq : (∑ a, p.mass a * density r p a) *
          Real.log (∑ a, p.mass a * density r p a) =
          ∑ a, p.mass a * (density r p a * Real.log (density r p a)) := by
        rw [hm, hsum, Real.log_one, mul_zero]
      intro a ha
      simpa only [hm] using hj.mp heq a (Finset.mem_univ a) ha
    have hmass : r.mass = p.mass := by
      funext a
      by_cases hp : p.mass a = 0
      · rw [hp, h a hp]
      · have he := mass_mul_density h a
        rw [hd a hp, mul_one] at he
        exact he.symm
    cases r
    cases p
    cases hmass
    rfl
  · rintro rfl
    simp

/-- The denominator in every supported, nontrivial KL test is strictly positive. -/
theorem relativeEntropy_pos_iff {r p : Law α} (h : Supported r p) :
    0 < relativeEntropy r p ↔ r ≠ p := by
  rw [lt_iff_le_and_ne]
  simp only [relativeEntropy_nonneg h, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    relativeEntropy_eq_zero_iff h]

/-- The standard supported KL ratios, excluding the unchanged input law. -/
def standardKLRatios (p : Law α) (K : Channel α β) : Set ℝ :=
  {v | ∃ r : Law α, Supported r p ∧ r ≠ p ∧
    v = relativeEntropy (out r K) (out p K) / relativeEntropy r p}

/-- The standard KL contraction coefficient, with an explicit zero convention
when no supported alternative input law exists. -/
def standardKLCoefficient (p : Law α) (K : Channel α β) : ℝ := by
  classical
  exact if (standardKLRatios p K).Nonempty then sSup (standardKLRatios p K) else 0

/-- The finite-KL domain is expressed by `Supported`; within that domain the
usual positive-denominator condition is exactly the exclusion of `Q = P`. -/
theorem standardKLRatios_eq_positive (p : Law α) (K : Channel α β) :
    standardKLRatios p K =
      {v | ∃ r : Law α, Supported r p ∧ 0 < relativeEntropy r p ∧
        v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  ext v
  constructor
  · rintro ⟨r, hr, hne, hv⟩
    exact ⟨r, hr, (relativeEntropy_pos_iff hr).mpr hne, hv⟩
  · rintro ⟨r, hr, hpos, hv⟩
    exact ⟨r, hr, (relativeEntropy_pos_iff hr).mp hpos, hv⟩

theorem standardKLRatios_subset (p : Law α) (K : Channel α β) :
    standardKLRatios p K ⊆ probabilityRatios p K := by
  rintro v ⟨r, hr, _, hv⟩
  exact ⟨r, hr, hv⟩

theorem standardKLRatios_bddAbove (p : Law α) (K : Channel α β) :
    BddAbove (standardKLRatios p K) := by
  have h : BddAbove (probabilityRatios p K) := by
    rw [← ratios_eq_probabilityRatios]
    exact ratios_bddAbove p K
  exact h.mono (standardKLRatios_subset p K)

theorem standardKLRatios_nonneg {p : Law α} {K : Channel α β} {v : ℝ}
    (hv : v ∈ standardKLRatios p K) : 0 ≤ v := by
  rcases hv with ⟨r, hr, _, rfl⟩
  exact div_nonneg (relativeEntropy_nonneg (supported_out hr K))
    (relativeEntropy_nonneg hr)

/-- Keeping the unchanged input adds exactly the single value zero. -/
theorem probabilityRatios_eq_insert_standard (p : Law α) (K : Channel α β) :
    probabilityRatios p K = insert 0 (standardKLRatios p K) := by
  classical
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases he : r = p
    · subst r
      simp
    · exact Set.mem_insert_of_mem 0 ⟨r, hr, he, rfl⟩
  · intro hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact ⟨p, (fun _ h => h), by simp⟩
    · exact standardKLRatios_subset p K hv

/-- The existing coefficient is exactly the standard one excluding `Q = P`,
including the explicit empty-test convention. -/
theorem coefficient_eq_standardKLCoefficient (p : Law α) (K : Channel α β) :
    coefficient p K = standardKLCoefficient p K := by
  classical
  rw [coefficient_eq_sup_KL, probabilityRatios_eq_insert_standard]
  unfold standardKLCoefficient
  split_ifs with h
  · rw [csSup_insert (standardKLRatios_bddAbove p K) h]
    exact sup_eq_right.mpr (Real.sSup_nonneg (fun _ hv => standardKLRatios_nonneg hv))
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    simp

/-- When an alternative exists, no empty-set convention is needed. -/
theorem coefficient_eq_sup_KL_ne (p : Law α) (K : Channel α β)
    (h : ∃ r : Law α, Supported r p ∧ r ≠ p) :
    coefficient p K = sSup (standardKLRatios p K) := by
  rw [coefficient_eq_standardKLCoefficient]
  have hn : (standardKLRatios p K).Nonempty := by
    rcases h with ⟨r, hr, hne⟩
    exact ⟨_, r, hr, hne, rfl⟩
  simp [standardKLCoefficient, hn]

/-- The standard positive-KL formula for any reference with an alternative.
`Supported` is essential because `relativeEntropy` is real-valued, not an
extended-real divergence on unsupported laws. -/
theorem coefficient_eq_sup_positive_KL (p : Law α) (K : Channel α β)
    (h : ∃ r : Law α, Supported r p ∧ r ≠ p) :
    coefficient p K = sSup {v | ∃ r : Law α, Supported r p ∧
      0 < relativeEntropy r p ∧
      v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  rw [coefficient_eq_sup_KL_ne p K h, standardKLRatios_eq_positive]

/-- If the reference law is the only supported law, the coefficient is zero. -/
theorem coefficient_eq_zero_of_no_alternative (p : Law α) (K : Channel α β)
    (h : ∀ r : Law α, Supported r p → r = p) : coefficient p K = 0 := by
  rw [coefficient_eq_standardKLCoefficient]
  have hn : ¬(standardKLRatios p K).Nonempty := by
    rintro ⟨_, r, hr, hne, _⟩
    exact hne (h r hr)
  simp [standardKLCoefficient, hn]

/-- A supported law cannot differ from a point-mass reference. -/
theorem supported_eq_of_pointMass {r p : Law α} (h : Supported r p)
    {a : α} (hp : p.mass a = 1) : r = p := by
  classical
  have hpzero (b : α) (hb : b ≠ a) : p.mass b = 0 := by
    have he : ∑ i ∈ Finset.univ.erase a, p.mass i = 0 := by
      have hs := Finset.sum_erase_add Finset.univ p.mass (Finset.mem_univ a)
      rw [p.total, hp] at hs
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => p.nonneg i)).mp he b (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
  have hrzero (b : α) (hb : b ≠ a) : r.mass b = 0 := h b (hpzero b hb)
  have hra : r.mass a = 1 := by
    calc
      r.mass a = ∑ b, r.mass b :=
        (Finset.sum_eq_single a (fun b _ hb => hrzero b hb) (by simp)).symm
      _ = 1 := r.total
  have hmass : r.mass = p.mass := by
    funext b
    by_cases hb : b = a
    · subst b
      rw [hra, hp]
    · rw [hrzero b hb, hpzero b hb]
  cases r
  cases p
  cases hmass
  rfl

/-- Deterministic inputs have zero coefficient, without any condition on the channel. -/
theorem coefficient_eq_zero_of_pointMass (p : Law α) (K : Channel α β)
    {a : α} (hp : p.mass a = 1) : coefficient p K = 0 :=
  coefficient_eq_zero_of_no_alternative p K (fun _ h => supported_eq_of_pointMass h hp)

/-- With full-support reference input, support restrictions remove no law. -/
theorem standardKLRatios_of_fullSupport (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) :
    standardKLRatios p K =
      {v | ∃ r : Law α, r ≠ p ∧
        v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  ext v
  constructor
  · rintro ⟨r, _, hne, hv⟩
    exact ⟨r, hne, hv⟩
  · rintro ⟨r, hne, hv⟩
    exact ⟨r, (fun a ha => False.elim ((ne_of_gt (hp a)) ha)), hne, hv⟩

/-- The familiar full-support formula, whose only test restriction is `Q ≠ P`.
The existence hypothesis separates the one-point alphabet convention. -/
theorem coefficient_eq_sup_KL_ne_of_fullSupport (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (h : ∃ r : Law α, r ≠ p) :
    coefficient p K = sSup {v | ∃ r : Law α, r ≠ p ∧
      v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  have hs : ∃ r : Law α, Supported r p ∧ r ≠ p := by
    rcases h with ⟨r, hne⟩
    exact ⟨r, (fun a ha => False.elim ((ne_of_gt (hp a)) ha)), hne⟩
  rw [coefficient_eq_sup_KL_ne p K hs, standardKLRatios_of_fullSupport p K hp]

end FiniteInfo

end FiniteKLStandard

/-! ## The full-support AGKN special case -/

@[expose] public noncomputable section AGKNGeneral

namespace FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- AGKN KL ratios: a full-support reference and only distinct alternative laws.
An alternative law itself may have zero-probability symbols. -/
def agknRatios (p : Law α) (K : Channel α β)
    (_hp : ∀ a, 0 < p.mass a) : Set ℝ :=
  {v | ∃ r : Law α, r ≠ p ∧
    v = relativeEntropy (out r K) (out p K) / relativeEntropy r p}

/-- The AGKN full-support coefficient, directly excluding the unchanged input.
The explicit zero branch covers an input alphabet with no alternative law. -/
def agknCoefficient (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) : ℝ := by
  classical
  exact if (agknRatios p K hp).Nonempty then sSup (agknRatios p K hp) else 0

/-- Full support makes every distinct test law have a positive KL denominator. -/
theorem agkn_denominator_pos (p r : Law α) (hp : ∀ a, 0 < p.mass a)
    (hne : r ≠ p) : 0 < relativeEntropy r p := by
  have hs : Supported r p := fun a ha => False.elim ((ne_of_gt (hp a)) ha)
  exact (relativeEntropy_pos_iff hs).mpr hne

/-- On a full-support reference, the supported and AGKN test sets coincide. -/
theorem agknRatios_eq_standardKLRatios (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) :
    agknRatios p K hp = standardKLRatios p K := by
  exact (standardKLRatios_of_fullSupport p K hp).symm

/-- The direct AGKN definition equals the previously verified general extension. -/
theorem agknCoefficient_eq_coefficient (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) : agknCoefficient p K hp = coefficient p K := by
  rw [coefficient_eq_standardKLCoefficient]
  unfold agknCoefficient standardKLCoefficient
  have he := agknRatios_eq_standardKLRatios p K hp
  split_ifs with ha hs hs
  · exact congrArg sSup he
  · exact False.elim (hs (he ▸ ha))
  · exact False.elim (ha (he.symm ▸ hs))
  · rfl

/-- If an alternative input law exists, AGKN is the displayed supremum over `r ≠ p`. -/
theorem agknCoefficient_eq_sup (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (h : ∃ r : Law α, r ≠ p) :
    agknCoefficient p K hp = sSup {v | ∃ r : Law α, r ≠ p ∧
      v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_eq_sup_KL_ne_of_fullSupport p K hp h

/-- The direct definition is zero when no distinct input law exists. -/
theorem agknCoefficient_eq_zero_of_no_alternative (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (h : ∀ r : Law α, r = p) :
    agknCoefficient p K hp = 0 := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_eq_zero_of_no_alternative p K (fun r _ => h r)

/-- A deterministic output has zero AGKN coefficient, for every full-support input. -/
theorem agknCoefficient_eq_zero_of_output_pointMass (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) {b : β} (hb : (out p K).mass b = 1) :
    agknCoefficient p K hp = 0 := by
  rw [agknCoefficient_eq_coefficient, coefficient_eq_sup_KL]
  have hz : probabilityRatios p K = {0} := by
    ext v
    constructor
    · rintro ⟨r, hr, rfl⟩
      have ho := supported_eq_of_pointMass (supported_out hr K) hb
      simp [ho]
    · intro hv
      have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨p, (fun _ h => h), by simp⟩
  rw [hz]
  simp

/-- The AGKN coefficient lies in the usual interval. -/
theorem agknCoefficient_mem (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) : agknCoefficient p K hp ∈ Set.Icc (0 : ℝ) 1 := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_mem p K

end FiniteInfo

end AGKNGeneral

/-! ## Recovering a joint law from its marginal and conditional channel

把有限联合分布拆成输入边缘分布与条件信道，证明零概率条件行的任意选择不改变系数。
-/

@[expose] public noncomputable section FiniteJoint

open scoped BigOperators

namespace FiniteInfo

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

def joint (p : Law α) (K : Channel α β) : Law (α × β) where
  mass z := p.mass z.1 * K.prob z.1 z.2
  nonneg z := mul_nonneg (p.nonneg _) (K.nonneg _ _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, K.total, mul_one]
    exact p.total

def first (P : Law (α × β)) : Law α where
  mass a := ∑ b, P.mass (a,b)
  nonneg a := Finset.sum_nonneg fun b _ => P.nonneg (a,b)
  total := by simpa only [Fintype.sum_prod_type] using P.total

def second (P : Law (α × β)) : Law β where
  mass b := ∑ a, P.mass (a,b)
  nonneg b := Finset.sum_nonneg fun a _ => P.nonneg (a,b)
  total := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using P.total

theorem atom_zero_of_first_zero (P : Law (α × β)) {a : α}
    (ha : (first P).mass a = 0) (b : β) : P.mass (a,b) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => P.nonneg (a,b))).mp ha b (Finset.mem_univ b)

/-- The conditional distribution is arbitrary only on null input atoms. -/
def conditional (P : Law (α × β)) (default : β) : Channel α β where
  prob a b := if (first P).mass a = 0 then (if b = default then 1 else 0)
    else P.mass (a,b) / (first P).mass a
  nonneg a b := by
    split_ifs <;> first | positivity | exact div_nonneg (P.nonneg _) ((first P).nonneg _)
  total a := by
    classical
    by_cases ha : (first P).mass a = 0
    · simp [ha]
    · simp only [ha, ↓reduceIte, div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ ha

/-- Reconstructing a conditional channel recovers every atom of the original law. -/
theorem first_mul_conditional (P : Law (α × β)) (default : β) (a : α) (b : β) :
    (first P).mass a * (conditional P default).prob a b = P.mass (a,b) := by
  by_cases ha : (first P).mass a = 0
  · simp [ha, atom_zero_of_first_zero P ha b]
  · simp only [conditional, ha, ↓reduceIte]
    exact mul_div_cancel₀ _ ha

theorem joint_conditional_mass (P : Law (α × β)) (default : β) (z : α × β) :
    (joint (first P) (conditional P default)).mass z = P.mass z :=
  first_mul_conditional P default z.1 z.2

theorem out_conditional_mass (P : Law (α × β)) (default : β) (b : β) :
    (out (first P) (conditional P default)).mass b = (second P).mass b := by
  simp only [out, first_mul_conditional, second]

theorem transfer_conditional (P : Law (α × β)) (default : β) (f : α → ℝ) (b : β) :
    transfer (first P) (conditional P default) f b =
      (∑ a, P.mass (a,b) * f a) / (second P).mass b := by
  simp only [transfer, first_mul_conditional, out_conditional_mass]

/-- The exact KL contraction coefficient of an arbitrary finite-alphabet pair. -/
def jointCoefficient (P : Law (α × β)) (default : β) : ℝ :=
  coefficient (first P) (conditional P default)

/-- Choices of a conditional channel on null atoms have no effect on the coefficient. -/
theorem jointCoefficient_default_irrel (P : Law (α × β)) (b₀ b₁ : β) :
    jointCoefficient P b₀ = jointCoefficient P b₁ := by
  unfold jointCoefficient coefficient
  apply congrArg sSup
  ext v
  simp only [ratios, Set.mem_ofPred_eq]
  have he (f : α → ℝ) :
      entropy (out (first P) (conditional P b₀)).mass
        (transfer (first P) (conditional P b₀) f) =
      entropy (out (first P) (conditional P b₁)).mass
        (transfer (first P) (conditional P b₁) f) := by
    have ho₀ : (out (first P) (conditional P b₀)).mass = (second P).mass :=
      funext (out_conditional_mass P b₀)
    have ho₁ : (out (first P) (conditional P b₁)).mass = (second P).mass :=
      funext (out_conditional_mass P b₁)
    rw [ho₀, ho₁]
    congr 1
    funext b
    rw [transfer_conditional, transfer_conditional]
  simp_rw [he]

end FiniteInfo

end FiniteJoint

end BinaryPairBound
