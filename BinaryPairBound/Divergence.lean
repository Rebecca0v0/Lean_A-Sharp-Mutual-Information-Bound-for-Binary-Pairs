module

public import BinaryPairBound.TangentGap
public import Mathlib.Analysis.Convex.Deriv

/-! # Positivity and data processing for scalar Bernoulli divergence -/

public section

namespace BinaryPairBound

@[simp] theorem D_self (x : ℝ) : D x x = 0 := by
  rw [D, H_eq]
  ring

theorem D_pos {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hxy : x ≠ y) : 0 < D x y := by
  have hdy := Real.hasDerivAt_binEntropy (ne_of_gt hy.1) (ne_of_lt hy.2)
  have hyc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  have hid := entropy_tangent_gap x y
  rcases lt_or_gt_of_ne hxy with h | h
  · have hs := Real.strictConcave_binEntropy.lt_slope_of_hasDerivAt hx hyc h hdy
    rw [slope_def_field] at hs
    have ht := (lt_div_iff₀ (sub_pos.mpr h)).mp hs
    dsimp [H] at hid
    nlinarith
  · have hs := Real.strictConcave_binEntropy.slope_lt_of_hasDerivAt hyc hx h hdy
    rw [slope_def_field] at hs
    have ht := (div_lt_iff₀ (sub_pos.mpr h)).mp hs
    dsimp [H] at hid
    linarith

theorem D_nonneg {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : 0 ≤ D x y := by
  by_cases hxy : x = y
  · subst x
    simp
  · exact (D_pos hx hy hxy).le

theorem D_eq_zero_iff {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : D x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    exact (ne_of_gt (D_pos hx hy hxy)) h
  · rintro rfl
    simp

private lemma mul_log_mix_le {a b u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (a * u + b * v) * Real.log (a * u + b * v) ≤
      a * (u * Real.log u) + b * (v * Real.log v) := by
  simpa only [smul_eq_mul] using Real.convexOn_mul_log.2 hu hv ha hb hab

/-- Binary data processing, including zero transition probabilities and endpoint test inputs. -/
theorem D_dataProcessing {s c d x : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    D (q c d x) (q c d s) ≤ D x s := by
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have hs1 : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs.2)
  have hq0 : q c d s ≠ 0 := ne_of_gt hqs.1
  have hq1 : 1 - q c d s ≠ 0 := ne_of_gt (sub_pos.mpr hqs.2)
  have hu : 0 ≤ (1 - x) / (1 - s) := div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hs.2).le
  have hv : 0 ≤ x / s := div_nonneg hx.1 hs.1.le
  have hsum1 : (1 - s) * c / q c d s + s * (1 - d) / q c d s = 1 := by
    field_simp
    dsimp [q, k]
    ring
  have havg1 : (1 - s) * c / q c d s * ((1 - x) / (1 - s)) +
      s * (1 - d) / q c d s * (x / s) = q c d x / q c d s := by
    field_simp
    dsimp [q, k]
    ring
  have hsum0 : (1 - s) * (1 - c) / (1 - q c d s) + s * d / (1 - q c d s) = 1 := by
    field_simp
    dsimp [q, k]
    ring
  have havg0 : (1 - s) * (1 - c) / (1 - q c d s) * ((1 - x) / (1 - s)) +
      s * d / (1 - q c d s) * (x / s) = (1 - q c d x) / (1 - q c d s) := by
    field_simp
    dsimp [q, k]
    ring
  have j1 := mul_log_mix_le
    (div_nonneg (mul_nonneg (sub_pos.mpr hs.2).le hc.1) hqs.1.le)
    (div_nonneg (mul_nonneg hs.1.le (sub_nonneg.mpr hd.2)) hqs.1.le) hsum1 hu hv
  rw [havg1] at j1
  have j0 := mul_log_mix_le
    (div_nonneg (mul_nonneg (sub_pos.mpr hs.2).le (sub_nonneg.mpr hc.2))
      (sub_pos.mpr hqs.2).le)
    (div_nonneg (mul_nonneg hs.1.le hd.1) (sub_pos.mpr hqs.2).le) hsum0 hu hv
  rw [havg0] at j0
  have h1 := mul_le_mul_of_nonneg_left j1 hqs.1.le
  have h0 := mul_le_mul_of_nonneg_left j0 (sub_pos.mpr hqs.2).le
  have e1 : q c d s *
      ((1 - s) * c / q c d s * ((1 - x) / (1 - s) * Real.log ((1 - x) / (1 - s))) +
       s * (1 - d) / q c d s * (x / s * Real.log (x / s))) =
      c * (1 - x) * Real.log ((1 - x) / (1 - s)) + (1 - d) * x * Real.log (x / s) := by
    field_simp
  have e0 : (1 - q c d s) *
      ((1 - s) * (1 - c) / (1 - q c d s) *
        ((1 - x) / (1 - s) * Real.log ((1 - x) / (1 - s))) +
       s * d / (1 - q c d s) * (x / s * Real.log (x / s))) =
      (1 - c) * (1 - x) * Real.log ((1 - x) / (1 - s)) + d * x * Real.log (x / s) := by
    field_simp
  rw [e1] at h1
  rw [e0] at h0
  have eq1 : q c d s * (q c d x / q c d s * Real.log (q c d x / q c d s)) =
      q c d x * Real.log (q c d x / q c d s) := by field_simp
  have eq0 : (1 - q c d s) * ((1 - q c d x) / (1 - q c d s) *
      Real.log ((1 - q c d x) / (1 - q c d s))) =
      (1 - q c d x) * Real.log ((1 - q c d x) / (1 - q c d s)) := by field_simp
  rw [eq1] at h1
  rw [eq0] at h0
  rw [D_eq_log_ratio (q_mem_Icc c d x hc hd hx) hqs, D_eq_log_ratio hx hs]
  nlinarith

end BinaryPairBound
