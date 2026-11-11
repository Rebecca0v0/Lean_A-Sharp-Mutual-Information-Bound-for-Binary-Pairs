module

public import BinaryPairBound.Curvature
public import BinaryPairBound.DivergenceCalculus

/-!
# Exact contact reflection identities

Reflection about the distinguished input in log-odds coordinates has a
rational expression. These identities prove the symmetry of the local
coefficient and of the normalized output log odds used in Appendix C.4.
The placement of the two supporting contacts is proved in `ContactPlacement.lean`.
-/

noncomputable section
@[expose] public section

namespace BinaryPairBound

/-- Reflection of the log odds about half the log ratio of two weights. -/
def weightedReflection (a b x : ℝ) : ℝ := a * (1 - x) / (a * (1 - x) + b * x)

lemma weightedReflection_mem_Ioo {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : weightedReflection a b x ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 := mul_pos ha (sub_pos.mpr hx.2)
  have h2 := mul_pos hb hx.1
  exact ⟨div_pos h1 (add_pos h1 h2), (div_lt_one (add_pos h1 h2)).mpr (by linarith)⟩

theorem logOdds_weightedReflection {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    logOdds (weightedReflection a b x) + logOdds x = Real.log a - Real.log b := by
  have hden : 0 < a * (1 - x) + b * x :=
    add_pos (mul_pos ha (sub_pos.mpr hx.2)) (mul_pos hb hx.1)
  have hsub : 1 - weightedReflection a b x = b * x / (a * (1 - x) + b * x) := by
    unfold weightedReflection
    field_simp (disch := nlinarith [hden])
    ring
  unfold logOdds
  rw [hsub, weightedReflection,
    Real.log_div (ne_of_gt (mul_pos ha (sub_pos.mpr hx.2))) (ne_of_gt hden),
    Real.log_div (ne_of_gt (mul_pos hb hx.1)) (ne_of_gt hden),
    Real.log_mul (ne_of_gt ha) (ne_of_gt (sub_pos.mpr hx.2)),
    Real.log_mul (ne_of_gt hb) (ne_of_gt hx.1)]
  ring

theorem weightedReflection_involution {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    weightedReflection a b (weightedReflection a b x) = x := by
  have hr := weightedReflection_mem_Ioo ha hb hx
  have hrr := weightedReflection_mem_Ioo ha hb hr
  apply logOdds_strictMonoOn.injOn hrr hx
  linarith [logOdds_weightedReflection ha hb hx, logOdds_weightedReflection ha hb hr]

theorem weightedReflection_strictAntiOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictAntiOn (weightedReflection a b) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxR := weightedReflection_mem_Ioo ha hb hx
  have hyR := weightedReflection_mem_Ioo ha hb hy
  have hlog := logOdds_strictMonoOn hx hy hxy
  have hr : logOdds (weightedReflection a b y) < logOdds (weightedReflection a b x) := by
    linarith [logOdds_weightedReflection ha hb hx, logOdds_weightedReflection ha hb hy]
  exact (logOdds_strictMonoOn.lt_iff_lt hyR hxR).mp hr

/-- The input reflection about the distinguished input in log-odds coordinates. -/
def contactReflection (c d x : ℝ) : ℝ :=
  weightedReflection (c * (1 - c)) (d * (1 - d)) x

theorem contactReflection_mem_Ioo {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : contactReflection c d x ∈ Set.Ioo (0 : ℝ) 1 :=
  weightedReflection_mem_Ioo (mul_pos hc.1 (sub_pos.mpr hc.2))
    (mul_pos hd.1 (sub_pos.mpr hd.2)) hx

theorem contactReflection_involution {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    contactReflection c d (contactReflection c d x) = x :=
  weightedReflection_involution (mul_pos hc.1 (sub_pos.mpr hc.2))
    (mul_pos hd.1 (sub_pos.mpr hd.2)) hx

theorem q_contactReflection {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    q c d (contactReflection c d x) =
      weightedReflection (c * (1 - d)) ((1 - c) * d) (q c d x) := by
  have hq := q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩
  have hden : 0 < c * (1 - c) * (1 - x) + d * (1 - d) * x :=
    add_pos (mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (sub_pos.mpr hx.2))
      (mul_pos (mul_pos hd.1 (sub_pos.mpr hd.2)) hx.1)
  have hdenq : 0 < c * (1 - d) * (1 - q c d x) + (1 - c) * d * q c d x :=
    add_pos (mul_pos (mul_pos hc.1 (sub_pos.mpr hd.2)) (sub_pos.mpr hq.2))
      (mul_pos (mul_pos (sub_pos.mpr hc.2) hd.1) hq.1)
  unfold contactReflection weightedReflection q k at *
  field_simp (disch := nlinarith [hden, hdenq])
  ring

/-- The exact output log-odds symmetry used to compare the two contacts. -/
theorem output_logOdds_contactReflection {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    logOdds (q c d (contactReflection c d x)) + logOdds (q c d x) =
      logOdds c + logOdds (1 - d) := by
  rw [q_contactReflection hc hd hx,
    logOdds_weightedReflection (mul_pos hc.1 (sub_pos.mpr hd.2))
      (mul_pos (sub_pos.mpr hc.2) hd.1) (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩),
    Real.log_mul (ne_of_gt hc.1) (ne_of_gt (sub_pos.mpr hd.2)),
    Real.log_mul (ne_of_gt (sub_pos.mpr hc.2)) (ne_of_gt hd.1)]
  unfold logOdds
  rw [show 1 - (1 - d) = d by ring]
  ring

lemma logOdds_div_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logOdds (a / (a + b)) = Real.log a - Real.log b := by
  have hden := add_pos ha hb
  have hsub : 1 - a / (a + b) = b / (a + b) := by
    field_simp (disch := nlinarith [hden])
    ring
  rw [logOdds, hsub, Real.log_div (ne_of_gt ha) (ne_of_gt hden),
    Real.log_div (ne_of_gt hb) (ne_of_gt hden)]
  ring

/-- The distinguished input has log odds `τ₀` from Appendix C.4. -/
theorem logOdds_distinguishedInput {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    logOdds (distinguishedInput c d) =
      (Real.log (c * (1 - c)) - Real.log (d * (1 - d))) / 2 := by
  have hA := mul_pos hc.1 (sub_pos.mpr hc.2)
  have hB := mul_pos hd.1 (sub_pos.mpr hd.2)
  rw [distinguishedInput, logOdds_div_add (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hB),
    Real.log_sqrt hA.le, Real.log_sqrt hB.le]
  ring

/-- Reflection is exactly `τ ↦ 2τ₀ - τ` in input log-odds coordinates. -/
theorem logOdds_contactReflection {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    logOdds (contactReflection c d x) =
      2 * logOdds (distinguishedInput c d) - logOdds x := by
  have h := logOdds_weightedReflection (mul_pos hc.1 (sub_pos.mpr hc.2))
    (mul_pos hd.1 (sub_pos.mpr hd.2)) hx
  rw [logOdds_distinguishedInput hc hd]
  change logOdds (contactReflection c d x) + logOdds x = _ at h
  linarith

theorem contactReflection_distinguishedInput {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    contactReflection c d (distinguishedInput c d) = distinguishedInput c d := by
  have hs := distinguishedInput_mem_Ioo hc hd
  apply logOdds_strictMonoOn.injOn (contactReflection_mem_Ioo hc hd hs) hs
  rw [logOdds_contactReflection hc hd hs]
  ring

/-- The local coefficient is even around the distinguished input in log odds. -/
theorem rhoSquared_contactReflection {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    rhoSquared c d (contactReflection c d x) = rhoSquared c d x := by
  have hr := contactReflection_mem_Ioo hc hd hx
  have hq := q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩
  have hqR := q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hden : 0 < c * (1 - c) * (1 - x) + d * (1 - d) * x :=
    add_pos (mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (sub_pos.mpr hx.2))
      (mul_pos (mul_pos hd.1 (sub_pos.mpr hd.2)) hx.1)
  unfold rhoSquared
  apply (div_eq_div_iff (mul_ne_zero (ne_of_gt hqR.1) (ne_of_gt (sub_pos.mpr hqR.2)))
    (mul_ne_zero (ne_of_gt hq.1) (ne_of_gt (sub_pos.mpr hq.2)))).mpr
  unfold contactReflection weightedReflection q k
  field_simp (disch := nlinarith [hden])
  ring

/-- The function `Z` from Appendix C.3, evaluated at the input probability. -/
def normalizedOutputLogOdds (c d x : ℝ) : ℝ :=
  (logOdds (q c d x) - logOdds c) / (logOdds (1 - d) - logOdds c)

lemma channel_logOdds_gap_pos {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) : 0 < logOdds (1 - d) - logOdds c :=
  sub_pos.mpr (logOdds_strictMonoOn hc ⟨by linarith [hd.2], by linarith [hd.1]⟩
    (by linarith))

/-- The identity `Z(τ₀+u)+Z(τ₀-u)=1`, written without an inverse-logistic
parameterization. -/
theorem normalizedOutputLogOdds_contactReflection {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    normalizedOutputLogOdds c d (contactReflection c d x) +
      normalizedOutputLogOdds c d x = 1 := by
  have hM := channel_logOdds_gap_pos hc hd hcd
  have hsum := output_logOdds_contactReflection hc hd hx
  unfold normalizedOutputLogOdds
  rw [← add_div, div_eq_one_iff_eq (ne_of_gt hM)]
  linarith

theorem normalizedOutputLogOdds_distinguishedInput {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) :
    normalizedOutputLogOdds c d (distinguishedInput c d) = 1 / 2 := by
  have h := normalizedOutputLogOdds_contactReflection hc hd hcd
    (distinguishedInput_mem_Ioo hc hd)
  rw [contactReflection_distinguishedInput hc hd] at h
  linarith

theorem normalizedOutputLogOdds_strictMonoOn {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) :
    StrictMonoOn (normalizedOutputLogOdds c d) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hk : 0 < k c d := by unfold k; linarith
  have hqxy : q c d x < q c d y := by unfold q; nlinarith
  have hlog := logOdds_strictMonoOn
    (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)
    (q_mem_Ioo_of_channel hc hd ⟨hy.1.le, hy.2.le⟩) hqxy
  exact (div_lt_div_iff_of_pos_right (channel_logOdds_gap_pos hc hd hcd)).mpr
    (sub_lt_sub_right hlog _)

/-- The contact-placement inequality in C.4 is exactly an order comparison
with the reflected input. The comparison for actual supporting contacts is established in
`ContactPlacement.lean`. -/
theorem normalizedOutputLogOdds_sum_ge_one_iff {c d x y : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    1 ≤ normalizedOutputLogOdds c d x + normalizedOutputLogOdds c d y ↔
      contactReflection c d x ≤ y := by
  have hsum := normalizedOutputLogOdds_contactReflection hc hd hcd hx
  have heq := (normalizedOutputLogOdds_strictMonoOn hc hd hcd).le_iff_le
    (contactReflection_mem_Ioo hc hd hx) hy
  constructor
  · intro h
    apply heq.mp
    linarith
  · intro h
    have hle := heq.mpr h
    linarith

/-- Reflection lies to the right exactly below the distinguished input. -/
theorem lt_contactReflection_iff {c d x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    x < contactReflection c d x ↔ x < distinguishedInput c d := by
  have href := logOdds_contactReflection hc hd hx
  have h1 := logOdds_strictMonoOn.lt_iff_lt hx (contactReflection_mem_Ioo hc hd hx)
  have h2 := logOdds_strictMonoOn.lt_iff_lt hx (distinguishedInput_mem_Ioo hc hd)
  constructor
  · intro h
    apply h2.mp
    have hlt := h1.mpr h
    linarith
  · intro h
    apply h1.mp
    have hlt := h2.mpr h
    linarith

/-- Under the positive-slope normalization, `c ≥ d` places `τ₀` to the right
of zero, as required in the final reflection argument of Appendix C.4. -/
theorem logOdds_distinguishedInput_nonneg {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) :
    0 ≤ logOdds (distinguishedInput c d) := by
  have hA := mul_pos hc.1 (sub_pos.mpr hc.2)
  have hB := mul_pos hd.1 (sub_pos.mpr hd.2)
  have hBA : d * (1 - d) ≤ c * (1 - c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdc) (show 0 ≤ 1 - c - d by linarith)]
  have hlog := Real.log_le_log hB hBA
  rw [logOdds_distinguishedInput hc hd]
  positivity

end BinaryPairBound
