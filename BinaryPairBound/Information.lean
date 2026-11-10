module

public import BinaryPairBound.TangentGap
public import Mathlib.Analysis.Convex.Function

/-! # Basic bounds and equality cases for binary mutual information -/

public section

namespace BinaryPairBound

@[simp] theorem J_zero_input (c d : ℝ) : J 0 c d = 0 := by
  simp [J, q, k]

@[simp] theorem J_one_input (c d : ℝ) : J 1 c d = 0 := by
  have hq : q c d 1 = 1 - d := by unfold q k; ring
  simp [J, hq, H]

theorem J_nonneg {s c d : ℝ} (hv : Valid s c d) : 0 ≤ J s c d := by
  rcases hv with ⟨hs, hc, hd⟩
  have h1d : 1 - d ∈ Set.Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hd.2, by linarith [hd.1]⟩
  have h := Real.strictConcave_binEntropy.concaveOn.2 hc h1d
    (sub_nonneg.mpr hs.2) hs.1 (show (1 - s) + s = 1 by ring)
  have hq : (1 - s) * c + s * (1 - d) = q c d s := by unfold q k; ring
  simp only [smul_eq_mul, Real.binEntropy_one_sub, hq] at h
  unfold J
  linarith

theorem J_le_log_two {s c d : ℝ} (hv : Valid s c d) : J s c d ≤ Real.log 2 := by
  have hc := mul_nonneg (sub_nonneg.mpr hv.1.2) (Real.binEntropy_nonneg hv.2.1.1 hv.2.1.2)
  have hd := mul_nonneg hv.1.1 (Real.binEntropy_nonneg hv.2.2.1 hv.2.2.2)
  have hq := Real.binEntropy_le_log_two (p := q c d s)
  unfold J
  linarith

/-- A deterministic input or constant-output channel has zero information. -/
theorem J_eq_zero_of_independent {s c d : ℝ} (hi : Independent s c d) : J s c d = 0 := by
  rcases hi with hs | hs | hcd
  · subst s; exact J_zero_input c d
  · subst s; exact J_one_input c d
  · have hk : k c d = 0 := by unfold k; linarith
    have hd : d = 1 - c := by linarith
    unfold J
    simp only [q, hk, zero_mul, add_zero]
    simp only [hd, H, Real.binEntropy_one_sub]
    ring

theorem J_pos_of_not_independent {s c d : ℝ} (hv : Valid s c d)
    (hi : ¬Independent s c d) : 0 < J s c d := by
  have hs0 : s ≠ 0 := fun h => hi (Or.inl h)
  have hs1 : s ≠ 1 := fun h => hi (Or.inr (Or.inl h))
  have hspos : 0 < s := lt_of_le_of_ne hv.1.1 (Ne.symm hs0)
  have hslt : s < 1 := lt_of_le_of_ne hv.1.2 hs1
  have h1d : 1 - d ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr hv.2.2.2, by linarith [hv.2.2.1]⟩
  have hcd : c ≠ 1 - d := by
    intro h
    exact hi (Or.inr (Or.inr (by linarith)))
  have h := Real.strictConcave_binEntropy.2 hv.2.1 h1d hcd
    (sub_pos.mpr hslt) hspos (show (1 - s) + s = 1 by ring)
  have hq : (1 - s) * c + s * (1 - d) = q c d s := by unfold q k; ring
  simp only [smul_eq_mul, Real.binEntropy_one_sub, hq] at h
  unfold J
  linarith

theorem J_eq_zero_iff_independent {s c d : ℝ} (hv : Valid s c d) :
    J s c d = 0 ↔ Independent s c d := by
  constructor
  · intro h
    by_contra hi
    exact (ne_of_gt (J_pos_of_not_independent hv hi)) h
  · exact J_eq_zero_of_independent

/-- A dependent binary pair cannot have a deterministic marginal. -/
theorem nondegenerate_of_not_independent {s c d : ℝ} (hv : Valid s c d)
    (hi : ¬Independent s c d) : Nondegenerate s c d := by
  have hs0 : s ≠ 0 := fun h => hi (Or.inl h)
  have hs1 : s ≠ 1 := fun h => hi (Or.inr (Or.inl h))
  have hspos : 0 < s := lt_of_le_of_ne hv.1.1 (Ne.symm hs0)
  have hslt : s < 1 := lt_of_le_of_ne hv.1.2 hs1
  have hq := q_mem_Icc c d s hv.2.1 hv.2.2 hv.1
  have hA := mul_nonneg (sub_nonneg.mpr hv.1.2) hv.2.1.1
  have hB := mul_nonneg hv.1.1 (sub_nonneg.mpr hv.2.2.2)
  have hC := mul_nonneg (sub_nonneg.mpr hv.1.2) (sub_nonneg.mpr hv.2.1.2)
  have hE := mul_nonneg hv.1.1 hv.2.2.1
  have hq0 : q c d s ≠ 0 := by
    intro hz
    have hsum : (1 - s) * c + s * (1 - d) = 0 := by
      unfold q k at hz
      nlinarith
    have hc : c = 0 := by nlinarith
    have hd : d = 1 := by nlinarith
    exact hi (Or.inr (Or.inr (by linarith)))
  have hq1 : q c d s ≠ 1 := by
    intro hz
    have hsum : (1 - s) * (1 - c) + s * d = 0 := by
      unfold q k at hz
      nlinarith
    have hc : c = 1 := by nlinarith
    have hd : d = 0 := by nlinarith
    exact hi (Or.inr (Or.inr (by linarith)))
  exact ⟨⟨hspos, hslt⟩,
    ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), lt_of_le_of_ne hq.2 hq1⟩⟩

/-- Maximum binary information is attained exactly by a uniform, noiseless or
complementing channel. This is the equality condition used at cap 1 in Section 8. -/
theorem J_eq_log_two_iff {s c d : ℝ} (hv : Valid s c d) :
    J s c d = Real.log 2 ↔ s = 1 / 2 ∧ c = d ∧ (c = 0 ∨ c = 1) := by
  constructor
  · intro hJ
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hs0 : s ≠ 0 := by
      intro h; subst s; rw [J_zero_input] at hJ; linarith
    have hs1 : s ≠ 1 := by
      intro h; subst s; rw [J_one_input] at hJ; linarith
    have hspos : 0 < s := lt_of_le_of_ne hv.1.1 (Ne.symm hs0)
    have hslt : s < 1 := lt_of_le_of_ne hv.1.2 hs1
    have hc0 := Real.binEntropy_nonneg hv.2.1.1 hv.2.1.2
    have hd0 := Real.binEntropy_nonneg hv.2.2.1 hv.2.2.2
    have hc := mul_nonneg (sub_nonneg.mpr hv.1.2) hc0
    have hd := mul_nonneg hv.1.1 hd0
    have hq := Real.binEntropy_le_log_two (p := q c d s)
    have heq : H (q c d s) = Real.log 2 := by unfold J at hJ; linarith
    have hcz : H c = 0 := by unfold J at hJ; nlinarith
    have hdz : H d = 0 := by unfold J at hJ; nlinarith
    have hqhalf : q c d s = (2 : ℝ)⁻¹ := Real.binEntropy_eq_log_two.mp heq
    rcases Real.binEntropy_eq_zero.mp hcz with hcz | hcz <;>
      rcases Real.binEntropy_eq_zero.mp hdz with hdz | hdz
    all_goals simp only [hcz, hdz, q, k] at hqhalf ⊢
    all_goals norm_num at hqhalf
    all_goals norm_num
    all_goals linarith
  · rintro ⟨rfl, hcd, hc | hc⟩
    all_goals subst c; subst d; norm_num [J, q, k, H]
    all_goals exact Real.binEntropy_eq_log_two.mpr (by norm_num)

end BinaryPairBound
