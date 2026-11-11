module

public import BinaryPairBound.FiniteEntropy

/-! # The distribution-dependent finite-alphabet KL contraction coefficient -/

noncomputable section
@[expose] public section
open scoped BigOperators

namespace BinaryPairBound.FiniteInfo

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

end BinaryPairBound.FiniteInfo
