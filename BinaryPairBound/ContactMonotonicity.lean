module

public import BinaryPairBound.Hyperbolic
public import BinaryPairBound.DivergenceCalculus

/-! # Strict monotonicity in the second contact (Appendix C.3) -/

noncomputable section
@[expose] public section

namespace BinaryPairBound

theorem exp_logOdds_gap {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    Real.exp (logOdds b - logOdds a) = b * (1 - a) / (a * (1 - b)) := by
  rw [logOdds, logOdds, Real.exp_sub, Real.exp_sub, Real.exp_sub,
    Real.exp_log hb.1, Real.exp_log (sub_pos.mpr hb.2),
    Real.exp_log ha.1, Real.exp_log (sub_pos.mpr ha.2)]
  field_simp

/-- A strict comparison between the squared log-odds gap and endpoint variances.
It is the hyperbolic inequality underlying (C.6)--(C.7). -/
theorem logOdds_gap_sq_lt {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hab : a < b) :
    (logOdds b - logOdds a) ^ 2 <
      (b - a) ^ 2 / (a * (1 - a) * b * (1 - b)) := by
  let u := logOdds b - logOdds a
  have hu : 0 < u := sub_pos.mpr (logOdds_strictMonoOn ha hb hab)
  have hs := Real.self_lt_sinh_iff.mpr (show 0 < u / 2 by linarith)
  have hspos : 0 < Real.sinh (u / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hcosh : 2 * Real.cosh u - 2 =
      (b - a) ^ 2 / (a * (1 - a) * b * (1 - b)) := by
    rw [Real.cosh_eq]
    have hneg : -u = logOdds a - logOdds b := by dsimp [u]; ring
    rw [hneg, exp_logOdds_gap hb ha]
    dsimp [u]
    rw [exp_logOdds_gap ha hb]
    field_simp [ne_of_gt ha.1, ne_of_gt hb.1,
      ne_of_gt (sub_pos.mpr ha.2), ne_of_gt (sub_pos.mpr hb.2)]
    ring
  have hdouble := Real.cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring] at hdouble
  have hid := Real.cosh_sq_sub_sinh_sq (u / 2)
  change u ^ 2 < _
  rw [← hcosh]
  nlinarith

/-- `Q` from (C.3), with the channel-dependent constant `P` supplied explicitly. -/
def contactQ (p s qv kv r : ℝ) : ℝ :=
  p - s - s * (1 - s) *
    (kv / (qv * (1 - qv) * (logOdds (qv + kv * (r - s)) - logOdds qv)) -
      1 / (r - s))

theorem hasDerivAt_contactQ {p s qv kv r : ℝ}
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hk : 0 < kv) (hsr : s < r) :
    HasDerivAt (contactQ p s qv kv)
      (s * (1 - s) *
        (kv ^ 2 / (qv * (1 - qv) * (qv + kv * (r - s)) *
          (1 - (qv + kv * (r - s))) *
          (logOdds (qv + kv * (r - s)) - logOdds qv) ^ 2) -
          1 / (r - s) ^ 2)) r := by
  have hdel : 0 < logOdds (qv + kv * (r - s)) - logOdds qv := by
    apply sub_pos.mpr (logOdds_strictMonoOn hq hqr _)
    linarith [mul_pos hk (sub_pos.mpr hsr)]
  have ha : HasDerivAt (fun x : ℝ => qv + kv * (x - s)) kv r := by
    convert! (((hasDerivAt_id r).sub_const s).const_mul kv).const_add qv using 1
    simp
  have hb := (((hasDerivAt_logOdds hqr).comp r ha).sub_const (logOdds qv)).const_mul
    (qv * (1 - qv))
  have h := ((hasDerivAt_const r kv).div hb
    (mul_ne_zero (mul_ne_zero (ne_of_gt hq.1) (ne_of_gt (sub_pos.mpr hq.2)))
      (ne_of_gt hdel))).sub
    ((hasDerivAt_const r 1).div ((hasDerivAt_id r).sub_const s) (ne_of_gt (sub_pos.mpr hsr)))
  convert! (h.const_mul (s * (1 - s))).const_sub (p - s) using 1
  simp only [id_eq, Function.comp_apply]
  field_simp [ne_of_gt hq.1, ne_of_gt (sub_pos.mpr hq.2), ne_of_gt hqr.1,
    ne_of_gt (sub_pos.mpr hqr.2), ne_of_gt hdel, ne_of_gt (sub_pos.mpr hsr)]
  ring

theorem contactQ_deriv_pos {p s qv kv r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hk : 0 < kv) (hsr : s < r) :
    0 < deriv (contactQ p s qv kv) r := by
  rw [(hasDerivAt_contactQ hq hqr hk hsr).deriv]
  apply mul_pos (mul_pos hs.1 (sub_pos.mpr hs.2))
  apply sub_pos.mpr
  have hlt : qv < qv + kv * (r - s) := by linarith [mul_pos hk (sub_pos.mpr hsr)]
  have hdel := sub_pos.mpr (logOdds_strictMonoOn hq hqr hlt)
  have hprod : 0 < qv * (1 - qv) * (qv + kv * (r - s)) *
      (1 - (qv + kv * (r - s))) := by
    exact mul_pos (mul_pos (mul_pos hq.1 (sub_pos.mpr hq.2)) hqr.1) (sub_pos.mpr hqr.2)
  have hbound := (lt_div_iff₀ hprod).mp (logOdds_gap_sq_lt hq hqr hlt)
  apply (div_lt_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hsr))
    (mul_pos hprod (sq_pos_of_pos hdel))).mpr
  nlinarith only [hbound]

/-- Increasing the second contact strictly increases `Q`, including a possible
endpoint second input when its output remains interior. -/
theorem contactQ_strictMonoOn {p s qv kv : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hk : 0 < kv) : StrictMonoOn (contactQ p s qv kv) (Set.Ioc s 1) := by
  have hqr : ∀ r ∈ Set.Ioc s (1 : ℝ), qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    constructor
    · linarith [mul_pos hk (sub_pos.mpr hr.1), hq.1]
    · nlinarith [hr.2, hqb.2]
  apply strictMonoOn_of_deriv_pos (convex_Ioc s 1)
  · intro r hr
    exact (hasDerivAt_contactQ hq (hqr r hr) hk hr.1).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : r ∈ Set.Ioc s (1 : ℝ) := interior_subset hr
    exact contactQ_deriv_pos hs hq (hqr r hr') hk hr'.1

end BinaryPairBound
