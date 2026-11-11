module

public import BinaryPairBound.ContactMonotonicity
public import BinaryPairBound.ContactSymmetry

/-! # The scalar sign at the reflected contact (Appendix C.4) -/

noncomputable section
@[expose] public section

namespace BinaryPairBound

/-- The value of the scalar sign test in exponential log-odds coordinates. -/
def reflectedOddsSign (m n : ℝ) : ℝ :=
  1 / 2 - Real.log n / (2 * Real.log m) +
    (m - n) ^ 2 / ((m ^ 2 - 1) * (n ^ 2 - 1)) -
    (m - n) * (m * n - 1) / (2 * n * (m ^ 2 - 1) * Real.log n)

theorem reflectedOddsSign_pos {m n : ℝ} (hn : 1 < n) (hnm : n < m) :
    0 < reflectedOddsSign m n := by
  have hm : 1 < m := hn.trans hnm
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hw := Real.log_pos hn
  have hv := Real.log_lt_log hn0 hnm
  have hsign := contactHyperbolicExpression_pos hw hv
  have hm2 : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hn2 : n ^ 2 - 1 ≠ 0 := by nlinarith
  have heq : (1 / (2 * Real.sinh (Real.log m))) *
      ((Real.cosh (Real.log n) / Real.sinh (Real.log n) - 1 / Real.log n) *
        (Real.cosh (Real.log m) - Real.cosh (Real.log n)) +
        Real.sinh (Real.log n) - Real.log n * Real.sinh (Real.log m) / Real.log m) =
      reflectedOddsSign m n := by
    simp only [Real.sinh_eq, Real.cosh_eq, Real.exp_neg, Real.exp_log hm0, Real.exp_log hn0]
    unfold reflectedOddsSign
    field_simp [ne_of_gt hn0, ne_of_gt hm0, ne_of_gt hw,
      ne_of_gt (Real.log_pos hm), hm2, hn2]
    ring
  rwa [heq] at hsign

/-- Probability corresponding to a positive odds value. -/
def oddsProbability (a : ℝ) : ℝ := a / (1 + a)

theorem oddsProbability_mem_Ioo {a : ℝ} (ha : 0 < a) :
    oddsProbability a ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold oddsProbability
  exact ⟨div_pos ha (by linarith), (div_lt_one (by linarith : 0 < 1 + a)).mpr (by linarith)⟩

theorem oddsProbability_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    oddsProbability b - oddsProbability a = (b - a) / ((1 + a) * (1 + b)) := by
  unfold oddsProbability
  field_simp
  ring

theorem logOdds_oddsProbability {a : ℝ} (ha : 0 < a) :
    logOdds (oddsProbability a) = Real.log a := by
  have heq : oddsProbability a = a / (a + 1) := by unfold oddsProbability; congr 1; ring
  rw [heq, logOdds_div_add ha zero_lt_one, Real.log_one, sub_zero]

theorem oddsProbability_exp_logOdds {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    oddsProbability (Real.exp (logOdds a)) = a := by
  apply logOdds_strictMonoOn.injOn (oddsProbability_mem_Ioo (Real.exp_pos _)) ha
  rw [logOdds_oddsProbability (Real.exp_pos _), Real.log_exp]

theorem oddsProbability_variance {a : ℝ} (ha : 0 < a) :
    oddsProbability a * (1 - oddsProbability a) = a / (1 + a) ^ 2 := by
  unfold oddsProbability
  field_simp
  ring

def reducedContactQ (a b y z : ℝ) : ℝ :=
  (logOdds y - logOdds a) / (logOdds b - logOdds a) +
    (y - a) * (b - z) / ((b - a) * (z - y)) -
    (y - a) * (b - y) / ((b - a) * y * (1 - y) * (logOdds z - logOdds y))

theorem contactQ_eq_reduced {a b y z : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a < b) (hyz : y < z) :
    contactQ ((logOdds y - logOdds a) / (logOdds b - logOdds a))
      ((y - a) / (b - a)) y (b - a) ((z - a) / (b - a)) = reducedContactQ a b y z := by
  have harg : y + (b - a) * ((z - a) / (b - a) - (y - a) / (b - a)) = z := by
    field_simp
    ring
  have hdiff : (z - a) / (b - a) - (y - a) / (b - a) = (z - y) / (b - a) := by ring
  unfold contactQ reducedContactQ
  rw [harg, hdiff]
  have hL := sub_pos.mpr (logOdds_strictMonoOn hy hz hyz)
  field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr hyz),
    ne_of_gt hy.1, ne_of_gt (sub_pos.mpr hy.2), ne_of_gt hL]
  ring

theorem reducedContactQ_odds {a m n : ℝ} (ha : 0 < a) (hn : 1 < n) (hnm : n < m) :
    reducedContactQ (oddsProbability a) (oddsProbability (a * m ^ 2))
      (oddsProbability (a * m / n)) (oddsProbability (a * m * n)) =
        reflectedOddsSign m n := by
  have hm : 1 < m := hn.trans hnm
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have haB : 0 < a * m ^ 2 := mul_pos ha (sq_pos_of_pos hm0)
  have haY : 0 < a * m / n := div_pos (mul_pos ha hm0) hn0
  have haZ : 0 < a * m * n := mul_pos (mul_pos ha hm0) hn0
  have hB : Real.log (a * m ^ 2) = Real.log a + 2 * Real.log m := by
    rw [Real.log_mul (ne_of_gt ha) (pow_ne_zero _ (ne_of_gt hm0)), Real.log_pow]
    norm_num
  have hY : Real.log (a * m / n) = Real.log a + Real.log m - Real.log n := by
    rw [Real.log_div (ne_of_gt (mul_pos ha hm0)) (ne_of_gt hn0),
      Real.log_mul (ne_of_gt ha) (ne_of_gt hm0)]
  have hZ : Real.log (a * m * n) = Real.log a + Real.log m + Real.log n := by
    rw [Real.log_mul (ne_of_gt (mul_pos ha hm0)) (ne_of_gt hn0),
      Real.log_mul (ne_of_gt ha) (ne_of_gt hm0)]
  unfold reducedContactQ
  rw [logOdds_oddsProbability ha, logOdds_oddsProbability haB,
    logOdds_oddsProbability haY, logOdds_oddsProbability haZ,
    hB, hY, hZ]
  have hnum : Real.log a + Real.log m - Real.log n - Real.log a =
      Real.log m - Real.log n := by ring
  have hden : Real.log a + 2 * Real.log m - Real.log a = 2 * Real.log m := by ring
  have hgap : Real.log a + Real.log m + Real.log n -
      (Real.log a + Real.log m - Real.log n) = 2 * Real.log n := by ring
  rw [hnum, hden, hgap, oddsProbability_sub ha haY,
    oddsProbability_sub haZ haB, oddsProbability_sub ha haB,
    oddsProbability_sub haY haZ, oddsProbability_sub haY haB]
  unfold oddsProbability reflectedOddsSign
  have hm2 : 0 < m ^ 2 - 1 := by nlinarith
  have hn2 : 0 < n ^ 2 - 1 := by nlinarith
  have hba : a * m ^ 2 - a ≠ 0 := by nlinarith [mul_pos ha hm2]
  have hzy : a * m * n - a * m / n ≠ 0 := by
    apply ne_of_gt
    apply (sub_pos.mpr ((div_lt_iff₀ hn0).mpr _))
    nlinarith [mul_pos (mul_pos ha hm0) hn2]
  field_simp [ne_of_gt ha, ne_of_gt hm0, ne_of_gt hn0, hba, hzy,
    ne_of_gt hm2, ne_of_gt hn2, ne_of_gt (Real.log_pos hm), ne_of_gt (Real.log_pos hn)]
  ring

/-- The reflected-contact sign is positive, derived from the hyperbolic
inequality rather than assumed as a separate sign hypothesis. -/
theorem reducedContactQ_pos_of_reflection {a b y z : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hay : a < y) (hyz : y < z)
    (href : logOdds z + logOdds y = logOdds a + logOdds b) :
    0 < reducedContactQ a b y z := by
  let v := (logOdds b - logOdds a) / 2
  let w := (logOdds z - logOdds y) / 2
  let A := Real.exp (logOdds a)
  let m := Real.exp v
  let n := Real.exp w
  have hw : 0 < w := by
    dsimp [w]
    exact div_pos (sub_pos.mpr (logOdds_strictMonoOn hy hz hyz)) (by norm_num)
  have hwv : w < v := by
    have h := logOdds_strictMonoOn ha hy hay
    dsimp [w, v]
    linarith
  have hn : 1 < n := Real.one_lt_exp_iff.mpr hw
  have hnm : n < m := Real.exp_lt_exp.mpr hwv
  have hB : A * m ^ 2 = Real.exp (logOdds b) := by
    dsimp [A, m]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [v]
    ring
  have hY : A * m / n = Real.exp (logOdds y) := by
    dsimp [A, m, n]
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    dsimp [v, w]
    linarith
  have hZ : A * m * n = Real.exp (logOdds z) := by
    dsimp [A, m, n]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [v, w]
    linarith
  have hpa : oddsProbability A = a := oddsProbability_exp_logOdds ha
  have hpb : oddsProbability (A * m ^ 2) = b := by
    rw [hB]
    exact oddsProbability_exp_logOdds hb
  have hpy : oddsProbability (A * m / n) = y := by
    rw [hY]
    exact oddsProbability_exp_logOdds hy
  have hpz : oddsProbability (A * m * n) = z := by
    rw [hZ]
    exact oddsProbability_exp_logOdds hz
  rw [← hpa, ← hpb, ← hpy, ← hpz, reducedContactQ_odds (Real.exp_pos _) hn hnm]
  exact reflectedOddsSign_pos hn hnm

/-- `Q` is strictly positive at the reflection threshold in Appendix C.4. -/
theorem contactQ_at_reflection_pos {s c d : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hss : s < distinguishedInput c d) :
    0 < contactQ (normalizedOutputLogOdds c d s) s (q c d s) (k c d)
      (contactReflection c d s) := by
  have hk : 0 < k c d := by unfold k; linarith
  have hr := contactReflection_mem_Ioo hc hd hs
  have hsr := (lt_contactReflection_iff hc hd hs).mpr hss
  have hqs := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr := q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hcb : c < 1 - d := by linarith
  have hcy : c < q c d s := by unfold q; linarith [mul_pos hk hs.1]
  have hyz : q c d s < q c d (contactReflection c d s) := by
    unfold q
    nlinarith
  have hb : 1 - d ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hd.2], by linarith [hd.1]⟩
  have hsign := reducedContactQ_pos_of_reflection hc hb hqs hqr hcy hyz
    (output_logOdds_contactReflection hc hd hs)
  have hident := contactQ_eq_reduced hqs hqr hcb hyz
  have hkB : 1 - d - c = k c d := by unfold k; ring
  have hsrat : (q c d s - c) / k c d = s := by
    unfold q
    field_simp
    ring
  have hrrat : (q c d (contactReflection c d s) - c) / k c d = contactReflection c d s := by
    unfold q
    field_simp
    ring
  rw [hkB, hsrat, hrrat] at hident
  change 0 < contactQ ((logOdds (q c d s) - logOdds c) / (logOdds (1 - d) - logOdds c))
    s (q c d s) (k c d) (contactReflection c d s)
  rwa [hident]

/-- Monotonicity transports the reflected-contact sign to every input on
or beyond the reflection. The placement hypothesis is explicit. -/
theorem contactQ_pos_of_reflection_le {s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hss : s < distinguishedInput c d)
    (href : contactReflection c d s ≤ r) :
    0 < contactQ (normalizedOutputLogOdds c d s) s (q c d s) (k c d) r := by
  have hk : 0 < k c d := by unfold k; linarith
  have hsr := (lt_contactReflection_iff hc hd hs).mpr hss
  have hrefI := contactReflection_mem_Ioo hc hd hs
  have hqb : q c d s + k c d * (1 - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    have heq : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
    rw [heq]
    constructor <;> linarith [hd.1, hd.2]
  exact (contactQ_at_reflection_pos hs hc hd hcd hss).trans_le
    ((contactQ_strictMonoOn hs (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩) hqb hk).monotoneOn
      ⟨hsr, hrefI.2.le⟩ ⟨hsr.trans_le href, hr.2.le⟩ href)

end BinaryPairBound
