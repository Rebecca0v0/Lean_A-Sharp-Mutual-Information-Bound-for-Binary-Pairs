module

public import BinaryPairBound.BinaryInformation
public import BinaryPairBound.ChannelGeometry
public import BinaryPairBound.SupportingContacts
public import BinaryPairBound.ContactFamilies
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Strict information-derivative signs along contact families

把附录C的单调性、反射位置和符号估计完整接到实际接触族，证明互信息导数的严格符号。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Scalar inequalities for the strict derivative signs

证明附录 C 所用双曲函数表达式的单调性和正性，为后面的符号判断提供不等式。
-/

@[expose] public noncomputable section Hyperbolic

private lemma positive_of_derivative_positive {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hzero : f 0 = 0)
    (hpos : ∀ x, 0 < x → 0 < f' x) {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hm : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hf x).deriv]
      exact hpos x hx
  simpa only [hzero] using hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx.le hx

private lemma negative_of_derivative_negative {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hzero : f 0 = 0)
    (hneg : ∀ x, 0 < x → f' x < 0) {x : ℝ} (hx : 0 < x) : f x < 0 := by
  have hp := positive_of_derivative_positive (fun x => (hf x).neg)
    (by simp [hzero]) (fun x hx => neg_pos.mpr (hneg x hx)) hx
  exact neg_pos.mp hp

theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) :
    Real.sinh x < x * Real.cosh x := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => t * Real.cosh t - Real.sinh t)
      (x * Real.sinh x) x := by
    intro x
    convert! ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    simp only [id_eq]
    ring
  exact sub_pos.mp (positive_of_derivative_positive hd (by simp)
    (fun x hx => mul_pos hx (Real.sinh_pos_iff.mpr hx)) hx)

private theorem hyperbolic_numerator_derivative_neg {x : ℝ} (hx : 0 < x) :
    3 * Real.sinh x * Real.cosh x -
      x * (Real.cosh x ^ 2 + Real.sinh x ^ 2) - 2 * x < 0 := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun t => 3 * Real.sinh t * Real.cosh t -
        t * (Real.cosh t ^ 2 + Real.sinh t ^ 2) - 2 * t)
      (4 * Real.sinh x * (Real.sinh x - x * Real.cosh x)) x := by
    intro x
    have h := (((Real.hasDerivAt_sinh x).const_mul 3).mul
      (Real.hasDerivAt_cosh x)).sub
      ((hasDerivAt_id x).mul (((Real.hasDerivAt_cosh x).pow 2).add
        ((Real.hasDerivAt_sinh x).pow 2)))
    convert! h.sub ((hasDerivAt_id x).const_mul 2) using 1
    simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, one_mul, mul_one]
    nlinarith only [Real.cosh_sq_sub_sinh_sq x]
  exact negative_of_derivative_negative hd (by simp)
    (fun x hx => mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr hx))
      (sub_neg.mpr (sinh_lt_mul_cosh hx))) hx

theorem hyperbolic_numerator_neg {x : ℝ} (hx : 0 < x) :
    2 * Real.sinh x ^ 2 - x * Real.sinh x * Real.cosh x - x ^ 2 < 0 := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun t => 2 * Real.sinh t ^ 2 - t * Real.sinh t * Real.cosh t - t ^ 2)
      (3 * Real.sinh x * Real.cosh x -
        x * (Real.cosh x ^ 2 + Real.sinh x ^ 2) - 2 * x) x := by
    intro x
    convert! (((Real.hasDerivAt_sinh x).pow 2).const_mul 2).sub
      (((hasDerivAt_id x).mul (Real.hasDerivAt_sinh x)).mul (Real.hasDerivAt_cosh x))
      |>.sub ((hasDerivAt_id x).pow 2) using 1
    simp only [Pi.mul_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
    ring
  exact negative_of_derivative_negative hd (by simp)
    (fun _ hx => hyperbolic_numerator_derivative_neg hx) hx

/-- The function `A*` from (C.9)--(C.11), with a total real extension. -/
def hyperbolicA (x : ℝ) : ℝ :=
  (x * (Real.cosh x / Real.sinh x) - 1) / x ^ 2

theorem hasDerivAt_hyperbolicA {x : ℝ} (hx : 0 < x) :
    HasDerivAt hyperbolicA
      ((2 * Real.sinh x ^ 2 - x * Real.sinh x * Real.cosh x - x ^ 2) /
        (x ^ 3 * Real.sinh x ^ 2)) x := by
  have hs : Real.sinh x ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hx)
  have h := (((hasDerivAt_id x).mul
    ((Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs)).sub_const 1).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero _ (ne_of_gt hx))
  convert! h using 1
  simp only [Pi.div_apply, Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, one_mul, mul_one]
  field_simp [ne_of_gt hx, hs]
  nlinarith only [Real.cosh_sq_sub_sinh_sq x,
    mul_nonneg (sq_nonneg x) (sq_nonneg (Real.sinh x))]

/-- The strict decrease asserted in (C.10)--(C.11). -/
theorem hyperbolicA_strictAntiOn : StrictAntiOn hyperbolicA (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_hyperbolicA hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, Set.mem_Ioi] at hx
    rw [(hasDerivAt_hyperbolicA hx).deriv]
    exact div_neg_of_neg_of_pos (hyperbolic_numerator_neg hx)
      (mul_pos (pow_pos hx _) (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx)))

/-- The bracket appearing in (C.8). -/
def contactHyperbolicBracket (w v : ℝ) : ℝ :=
  (Real.cosh w / Real.sinh w - 1 / w) * (Real.cosh v - Real.cosh w) +
    Real.sinh w - w * Real.sinh v / v

theorem hasDerivAt_contactHyperbolicBracket {w v : ℝ} (hw : 0 < w) (hv : 0 < v) :
    HasDerivAt (contactHyperbolicBracket w)
      (w * Real.sinh v * (hyperbolicA w - hyperbolicA v)) v := by
  have h := ((((Real.hasDerivAt_cosh v).sub_const (Real.cosh w)).const_mul
    (Real.cosh w / Real.sinh w - 1 / w)).add_const (Real.sinh w)).sub
    (((Real.hasDerivAt_sinh v).const_mul w).div (hasDerivAt_id v) (ne_of_gt hv))
  convert! h using 1
  simp only [hyperbolicA, id_eq, mul_one]
  field_simp [ne_of_gt hw, ne_of_gt hv,
    ne_of_gt (Real.sinh_pos_iff.mpr hw), ne_of_gt (Real.sinh_pos_iff.mpr hv)]

theorem contactHyperbolicBracket_pos {w v : ℝ} (hw : 0 < w) (hwv : w < v) :
    0 < contactHyperbolicBracket w v := by
  have hm : StrictMonoOn (contactHyperbolicBracket w) (Set.Ici w) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici w)
    · exact fun x hx => (hasDerivAt_contactHyperbolicBracket hw (hw.trans_le hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hasDerivAt_contactHyperbolicBracket hw (hw.trans hx)).deriv]
      exact mul_pos (mul_pos hw (Real.sinh_pos_iff.mpr (hw.trans hx)))
        (sub_pos.mpr (hyperbolicA_strictAntiOn hw (hw.trans hx) hx))
  have hzero : contactHyperbolicBracket w w = 0 := by
    unfold contactHyperbolicBracket
    field_simp
    ring
  simpa only [hzero] using hm (show w ∈ Set.Ici w by exact le_rfl) hwv.le hwv

/-- Positivity of the full scalar expression displayed in equation (C.8).
No common-tangent or implicit-family hypothesis is hidden in this statement. -/
theorem contactHyperbolicExpression_pos {w v : ℝ} (hw : 0 < w) (hwv : w < v) :
    0 < (1 / (2 * Real.sinh v)) *
      ((Real.cosh w / Real.sinh w - 1 / w) * (Real.cosh v - Real.cosh w) +
        Real.sinh w - w * Real.sinh v / v) := by
  exact mul_pos (one_div_pos.mpr (mul_pos (by norm_num)
    (Real.sinh_pos_iff.mpr (hw.trans hwv)))) (contactHyperbolicBracket_pos hw hwv)

end Hyperbolic

/-! ## Monotonicity of the contact sign expression

证明用于判断导数正负的标量 contactQ 随第二个接触点严格增加。
-/

@[expose] public noncomputable section ContactMonotonicity

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

end ContactMonotonicity

/-! ## Reflection of contact points

定义关于特殊输入位置的接触点反射，并证明局部比值及输出参数的反射关系。
-/

@[expose] public noncomputable section ContactSymmetry

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
`ContactSigns.lean`. -/
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

end ContactSymmetry

/-! ## Positivity at the reflected contact

把双曲函数不等式转成 contactQ 在反射接触点处的严格正性。
-/

@[expose] public noncomputable section ReflectedSign

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

end ReflectedSign

/-! ## Placing actual contacts relative to the reflection

证明真正的接触点位于反射位置的指定一侧，使反射处的符号结论可以用于实际接触点。
-/

@[expose] public noncomputable section ContactPlacement

open Set

lemma deriv_entropyCurve_logOdds {lam c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (entropyCurve lam c d) x = -k c d * logOdds (q c d x) + lam * logOdds x := by
  rw [deriv_entropyCurve lam x c d hx (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)]
  unfold logOdds
  ring

/-- The entropy-curve derivative is odd around its central value under reflection. -/
theorem deriv_entropyCurve_contactReflection {lam c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (entropyCurve lam c d) (contactReflection c d x) + deriv (entropyCurve lam c d) x =
      2 * deriv (entropyCurve lam c d) (distinguishedInput c d) := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hlog := output_logOdds_contactReflection hc hd hs
  rw [contactReflection_distinguishedInput hc hd] at hlog
  rw [deriv_entropyCurve_logOdds hc hd (contactReflection_mem_Ioo hc hd hx),
    deriv_entropyCurve_logOdds hc hd hx, deriv_entropyCurve_logOdds hc hd hs,
    logOdds_contactReflection hc hd hx]
  have hqx := output_logOdds_contactReflection hc hd hx
  linear_combination -k c d * (hqx - hlog)

theorem hasDerivAt_contactReflection {c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (contactReflection c d)
      (-(contactReflection c d x * (1 - contactReflection c d x)) / (x * (1 - x))) x := by
  have hA := mul_pos hc.1 (sub_pos.mpr hc.2)
  have hB := mul_pos hd.1 (sub_pos.mpr hd.2)
  have hden : 0 < c * (1 - c) * (1 - x) + d * (1 - d) * x :=
    add_pos (mul_pos hA (sub_pos.mpr hx.2)) (mul_pos hB hx.1)
  have hn := ((hasDerivAt_id x).const_sub 1).const_mul (c * (1 - c))
  have hdv := hn.add ((hasDerivAt_id x).const_mul (d * (1 - d)))
  have hR : DifferentiableAt ℝ (contactReflection c d) x :=
    (hn.div hdv (ne_of_gt hden)).differentiableAt
  have hrx := contactReflection_mem_Ioo hc hd hx
  have hsum := ((hasDerivAt_logOdds hrx).comp x hR.hasDerivAt).add (hasDerivAt_logOdds hx)
  have hconst : HasDerivAt (fun y => logOdds (contactReflection c d y) + logOdds y) 0 x := by
    apply (hasDerivAt_const x (2 * logOdds (distinguishedInput c d))).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    linarith [logOdds_contactReflection hc hd hy]
  have he := hsum.unique hconst
  have hneR : contactReflection c d x * (1 - contactReflection c d x) ≠ 0 :=
    ne_of_gt (mul_pos hrx.1 (sub_pos.mpr hrx.2))
  have he' : deriv (contactReflection c d) x /
      (contactReflection c d x * (1 - contactReflection c d x)) = -(1 / (x * (1 - x))) := by
    simpa only [one_div_mul_eq_div, eq_neg_iff_add_eq_zero] using he
  have he'' := (div_eq_iff hneR).mp he'
  convert! hR.hasDerivAt using 1
  rw [he'']
  ring

lemma contactReflection_variance_ge {c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hsx : distinguishedInput c d ≤ x) :
    x * (1 - x) ≤ contactReflection c d x * (1 - contactReflection c d x) := by
  have hA := mul_pos hc.1 (sub_pos.mpr hc.2)
  have hB := mul_pos hd.1 (sub_pos.mpr hd.2)
  have hAB : d * (1 - d) ≤ c * (1 - c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdc) (show 0 ≤ 1 - c - d by linarith)]
  have hden : 0 < c * (1 - c) * (1 - x) + d * (1 - d) * x :=
    add_pos (mul_pos hA (sub_pos.mpr hx.2)) (mul_pos hB hx.1)
  have hRx : contactReflection c d x ≤ x := by
    by_contra h
    have hh := (lt_contactReflection_iff hc hd hx).mp (lt_of_not_ge h)
    exact (not_lt_of_ge hsx) hh
  have hsum : 1 - x ≤ contactReflection c d x := by
    unfold contactReflection weightedReflection
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (mul_pos hx.1 (sub_pos.mpr hx.2)).le (sub_nonneg.mpr hAB)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hRx)
    (show 0 ≤ contactReflection c d x + x - 1 by linarith)]

lemma one_add_deriv_contactReflection_nonpos {c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hsx : distinguishedInput c d ≤ x) : 1 + deriv (contactReflection c d) x ≤ 0 := by
  rw [(hasDerivAt_contactReflection hc hd hx).deriv]
  have hden := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hh := contactReflection_variance_ge hc hd hcd hdc hx hsx
  have hdiv : 1 ≤ (contactReflection c d x * (1 - contactReflection c d x)) / (x * (1 - x)) :=
    (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hh)
  rw [neg_div]
  linarith

def reflectedEntropySecant (lam c d x : ℝ) : ℝ :=
  entropyCurve lam c d x - entropyCurve lam c d (contactReflection c d x) -
    deriv (entropyCurve lam c d) (distinguishedInput c d) * (x - contactReflection c d x)

theorem hasDerivAt_reflectedEntropySecant {lam c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (reflectedEntropySecant lam c d)
      ((deriv (entropyCurve lam c d) x - deriv (entropyCurve lam c d) (distinguishedInput c d)) *
        (1 + deriv (contactReflection c d) x)) x := by
  have hrx := contactReflection_mem_Ioo hc hd hx
  have hR := (hasDerivAt_contactReflection hc hd hx).differentiableAt.hasDerivAt
  have hFx := (hasDerivAt_entropyCurve lam x c d hx
    (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)).differentiableAt.hasDerivAt
  have hFR := (hasDerivAt_entropyCurve lam (contactReflection c d x) c d hrx
    (q_mem_Ioo_of_channel hc hd ⟨hrx.1.le, hrx.2.le⟩)).differentiableAt.hasDerivAt
  have hh := (hFx.sub (hFR.comp x hR)).sub
    (((hasDerivAt_id x).sub hR).const_mul (deriv (entropyCurve lam c d) (distinguishedInput c d)))
  convert! hh using 1
  have he := deriv_entropyCurve_contactReflection (lam := lam) hc hd hx
  linear_combination deriv (contactReflection c d) x * he

theorem reflectedEntropySecant_nonneg {lam c d r : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hsr : distinguishedInput c d ≤ r)
    (hbound : ∀ x ∈ Icc (distinguishedInput c d) r,
      deriv (entropyCurve lam c d) x ≤ deriv (entropyCurve lam c d) (distinguishedInput c d)) :
    0 ≤ reflectedEntropySecant lam c d r := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hinterior : ∀ x ∈ Icc (distinguishedInput c d) r, x ∈ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨hs0.1.trans_le hx.1, hx.2.trans_lt hr.2⟩
  have hmono : MonotoneOn (reflectedEntropySecant lam c d) (Icc (distinguishedInput c d) r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hasDerivAt_reflectedEntropySecant hc hd (hinterior x hx)).continuousAt.continuousWithinAt
    · exact fun x hx => (hasDerivAt_reflectedEntropySecant hc hd
        (hinterior x (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi := interior_subset hx
      rw [(hasDerivAt_reflectedEntropySecant hc hd (hinterior x hxi)).deriv]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hbound x hxi))
        (one_add_deriv_contactReflection_nonpos hc hd hcd hdc (hinterior x hxi) hxi.1)
  have hh := hmono ⟨le_rfl, hsr⟩ ⟨hsr, le_rfl⟩ hsr
  have hzero : reflectedEntropySecant lam c d (distinguishedInput c d) = 0 := by
    unfold reflectedEntropySecant
    rw [contactReflection_distinguishedInput hc hd]
    ring
  simpa only [hzero] using hh

lemma deriv_le_central_of_right_deriv_le {lam c d a b r : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hr : r ∈ Ioo b 1)
    (hm : deriv (entropyCurve lam c d) r ≤ deriv (entropyCurve lam c d) (distinguishedInput c d)) :
    ∀ x ∈ Icc (distinguishedInput c d) r,
      deriv (entropyCurve lam c d) x ≤ deriv (entropyCurve lam c d) (distinguishedInput c d) := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hD : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (entropyCurve lam c d) x := by
    intro x hx
    exact (hasDerivAt_entropyCurve lam x c d hx
      (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)).differentiableAt
  have hanti := (strictConcaveOn_entropyCurve_middle hc hd hcd ha hb haroot hbroot).concaveOn.antitoneOn_deriv
    (fun x hx => hD x ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩)
  have hconv : ConvexOn ℝ (Icc b r) (entropyCurve lam c d) :=
    (strictConvexOn_entropyCurve_right hc hd hcd hb hbroot).convexOn.subset
      (Icc_subset_Icc le_rfl hr.2.le) (convex_Icc _ _)
  have hmono := hconv.monotoneOn_deriv
    (fun x hx => hD x ⟨(hs0.1.trans hb.1).trans_le hx.1, hx.2.trans_lt hr.2⟩)
  intro x hx
  by_cases hxb : x ≤ b
  · exact hanti ⟨ha.2.le, hb.1.le⟩ ⟨ha.2.le.trans hx.1, hxb⟩ hx.1
  · exact (hmono ⟨(lt_of_not_ge hxb).le, hx.2⟩ ⟨hr.1.le, le_rfl⟩ hx.2).trans hm

/-- For `c ≥ d`, every supporting tangent on the right outer branch has slope
at least the derivative at the distinguished input. -/
theorem central_deriv_le_of_right_supporting {lam c d a b r : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hr : r ∈ Ioo b 1) (hcap : KLCap lam r c d) :
    deriv (entropyCurve lam c d) (distinguishedInput c d) ≤ deriv (entropyCurve lam c d) r := by
  by_contra h
  have hm := lt_of_not_ge h
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨(hs0.1.trans hb.1).trans hr.1, hr.2⟩
  have hR := contactReflection_mem_Ioo hc hd hr01
  have hRr : contactReflection c d r < r := by
    apply (logOdds_strictMonoOn.lt_iff_lt hR hr01).mp
    have hh := logOdds_strictMonoOn hs0 hr01 (hb.1.trans hr.1)
    rw [logOdds_contactReflection hc hd hr01]
    linarith
  have hB := reflectedEntropySecant_nonneg hc hd hcd hdc hr01 (hb.1.trans hr.1).le
    (deriv_le_central_of_right_deriv_le hc hd (ne_of_lt hcd) ha hb haroot hbroot hr hm.le)
  have hsupp := (klCap_iff_supporting_tangent
    ⟨hr01, q_mem_Ioo_of_channel hc hd ⟨hr01.1.le, hr01.2.le⟩⟩).mp hcap
      (contactReflection c d r) ⟨hR.1.le, hR.2.le⟩
  unfold reflectedEntropySecant at hB
  unfold tangent at hsupp
  nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hRr)]

/-- The reflected smaller contact lies no further right than the larger contact.
All contact and curvature hypotheses are established from the global KL cap. -/
theorem contactReflection_le_of_supporting_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    contactReflection c d s ≤ r := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hvs : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hns : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hvs.1⟩
  have hnr : Nondegenerate r c d := ⟨hr, q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩⟩
  have hS := S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd (ne_of_gt hsr) hcap hcontact
  have hlam0 : 0 < lam := by
    have hh := (rhoSquared_pos hc hd (ne_of_lt hcd) hs).trans_le (rhoSquared_le_S hvs hns)
    rwa [hS] at hh
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd (ne_of_lt hcd) ⟨hlam0, hlam⟩
  have hpositions := supporting_contacts_straddle_roots hs hr hc hd (ne_of_lt hcd)
    ha hb haroot hbroot hsr hcap hcontact
  have ht := supporting_contact_tangent_eq hs hr hc hd hcap hcontact
  have hcapr : KLCap lam r c d := by
    apply (klCap_iff_supporting_tangent hnr).mpr
    rw [ht]
    exact (klCap_iff_supporting_tangent hns).mp hcap
  have hcentral := central_deriv_le_of_right_supporting hc hd hcd hdc ha hb haroot hbroot
    ⟨hpositions.2, hr.2⟩ hcapr
  have hslopes := supporting_contact_deriv_eq hs hr hc hd hcap hcontact
  have hR := contactReflection_mem_Ioo hc hd hs
  have hRs0 : distinguishedInput c d < contactReflection c d s := by
    apply (logOdds_strictMonoOn.lt_iff_lt hs0 hR).mp
    have hh := logOdds_strictMonoOn hs hs0 (hpositions.1.trans ha.2)
    rw [logOdds_contactReflection hc hd hs]
    linarith
  have hrho : rhoSquared c d (contactReflection c d s) < lam := by
    rw [rhoSquared_contactReflection hc hd hs]
    exact rhoSquared_lt_of_left hc hd (ne_of_lt hcd) ha haroot ⟨hs.1.le, hpositions.1⟩
  have hbR : b < contactReflection c d s := by
    by_contra h
    have hh := (rhoSquared_strictAntiOn hc hd (ne_of_lt hcd)).antitoneOn
      ⟨hRs0.le, hR.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (le_of_not_gt h)
    rw [hbroot] at hh
    linarith
  have hreflectSlope := deriv_entropyCurve_contactReflection (lam := lam) hc hd hs
  have hle : deriv (entropyCurve lam c d) (contactReflection c d s) ≤ deriv (entropyCurve lam c d) r := by
    linarith
  by_contra h
  have hrR := lt_of_not_ge h
  have hconv := strictConvexOn_entropyCurve_right hc hd (ne_of_lt hcd) hb hbroot
  have hdr := (hasDerivAt_entropyCurve lam r c d hr hnr.2).differentiableAt
  have hdR := (hasDerivAt_entropyCurve lam (contactReflection c d s) c d hR
    (q_mem_Ioo_of_channel hc hd ⟨hR.1.le, hR.2.le⟩)).differentiableAt
  have hlt := (hconv.deriv_lt_slope ⟨hpositions.2.le, hr.2.le⟩ ⟨hbR.le, hR.2.le⟩ hrR hdr).trans
    (hconv.slope_lt_deriv ⟨hpositions.2.le, hr.2.le⟩ ⟨hbR.le, hR.2.le⟩ hrR hdR)
  exact (not_lt_of_ge hle) hlt

/-- The final normalized-output placement inequality in Appendix C.4. -/
theorem normalizedOutputLogOdds_sum_ge_one_of_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    1 ≤ normalizedOutputLogOdds c d s + normalizedOutputLogOdds c d r :=
  (normalizedOutputLogOdds_sum_ge_one_iff hc hd hcd hs hr).mpr
    (contactReflection_le_of_supporting_contact hs hr hc hd hcd hdc hlam hsr hcap hcontact)

end ContactPlacement

/-! ## The output-direction derivative

把沿输出概率方向变化的互信息导数，改写成可以由 contactQ 判断正负的形式。
-/

public noncomputable section OutputDirection

/-- The output-direction identity in (C.3), with the slope from (C.2). -/
theorem informationCoords_contact_q_direction_eq {s r qv kv : ℝ}
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) (hk : 0 < kv) :
    deriv (fun z => informationCoords s z kv) qv +
      deriv (fun z => informationCoords s qv z) kv *
        (-1 / (r - s) + kv / (qv * (1 - qv) *
          (logOdds (qv + kv * (r - s)) - logOdds qv))) =
    -(logOdds (qv + kv * (1 - s)) - logOdds (qv - kv * s)) *
      contactQ ((logOdds qv - logOdds (qv - kv * s)) /
        (logOdds (qv + kv * (1 - s)) - logOdds (qv - kv * s))) s qv kv r := by
  have hM := sub_pos.mpr (logOdds_strictMonoOn hc hb (by linarith))
  rw [(hasDerivAt_informationCoords_q hq hc hb).deriv,
    (hasDerivAt_informationCoords_k hq hc hb).deriv]
  unfold contactQ
  have halg (a b t x y : ℝ) (hne : b - a ≠ 0) :
      (1 - s) * a + s * b - t + s * (1 - s) * (b - a) * (-x + y) =
        -(b - a) * ((t - a) / (b - a) - s - s * (1 - s) * (y - x)) := by
    field_simp
    ring
  simpa only [neg_div] using halg (logOdds (qv - kv * s))
    (logOdds (qv + kv * (1 - s))) (logOdds qv) (1 / (r - s))
    (kv / (qv * (1 - qv) * (logOdds (qv + kv * (r - s)) - logOdds qv))) (ne_of_gt hM)

theorem hasDerivAt_contactGap_output_family
    {kf rf : ℝ → ℝ} {lam s qv v w : ℝ}
    (hk : HasDerivAt kf v qv) (hrf : HasDerivAt rf w qv)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : rf qv ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf qv * (rf qv - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam s z (kf z) (rf z))
      (deriv (fun z => contactGap lam s z (kf qv) (rf qv)) qv +
       deriv (fun z => contactGap lam s qv z (rf qv)) (kf qv) * v +
       deriv (fun z => contactGap lam s qv (kf qv) z) (rf qv) * w) qv := by
  have hY := (hasDerivAt_id qv).add (hk.mul (hrf.sub_const s))
  have h1 := hasDerivAt_D_comp hY (hasDerivAt_id qv) hqr hq
  have h2 := (hasDerivAt_D_comp hrf (hasDerivAt_const qv s) hr hs).const_mul lam
  rw [(hasDerivAt_contactGap_q lam s qv (kf qv) (rf qv) hq hqr).deriv,
    (hasDerivAt_contactGap_k lam s qv (kf qv) (rf qv) hq hqr).deriv,
    (hasDerivAt_contactGap_r lam s qv (kf qv) (rf qv) hs hr hq hqr).deriv]
  convert! h1.sub h2 using 1
  simp only [zero_mul, zero_div, add_zero, one_mul, Pi.add_apply, Pi.mul_apply, id_eq]
  ring

/-- The actual information derivative along a contact curve is `-M Q`.
The differentiated contact constraint is obtained from local `G = 0`. -/
theorem informationCoords_contact_output_curve_deriv_eq
    {kf rf : ℝ → ℝ} {lam s qv v w : ℝ}
    (hkf : HasDerivAt kf v qv) (hrf : HasDerivAt rf w qv)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : rf qv ∈ Set.Ioo (0 : ℝ) 1)
    (hsr : s < rf qv) (hk : 0 < kf qv)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kf qv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kf qv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf qv * (rf qv - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hGr : deriv (fun z => contactGap lam s qv (kf qv) z) (rf qv) = 0)
    (hG : ∀ᶠ z in nhds qv, contactGap lam s z (kf z) (rf z) = 0) :
    deriv (fun z => informationCoords s z (kf z)) qv =
      -(logOdds (qv + kf qv * (1 - s)) - logOdds (qv - kf qv * s)) *
        contactQ ((logOdds qv - logOdds (qv - kf qv * s)) /
          (logOdds (qv + kf qv * (1 - s)) - logOdds (qv - kf qv * s))) s qv (kf qv) (rf qv) := by
  have hd := hasDerivAt_contactGap_output_family (lam := lam) hkf hrf hs hr hq hqr
  have hz : HasDerivAt (fun z => contactGap lam s z (kf z) (rf z)) 0 qv :=
    (hasDerivAt_const qv (0 : ℝ)).congr_of_eventuallyEq hG
  have hchain := hd.unique hz
  rw [hGr, zero_mul, add_zero] at hchain
  rw [(hasDerivAt_informationCoords_output_family hkf hq hc hb).deriv,
    contactGap_implicit_slope_q lam s qv (kf qv) (rf qv) v hq hqr hk hsr hchain]
  exact informationCoords_contact_q_direction_eq hq hc hb hk

/-- Strict output improvement for a genuine differentiable contact curve,
once its second contact lies on or beyond the reflection threshold. -/
theorem informationCoords_output_curve_deriv_neg_of_reflection_le
    {kf rf : ℝ → ℝ} {lam s c d r v w : ℝ}
    (hkf : HasDerivAt kf v (q c d s)) (hrf : HasDerivAt rf w (q c d s))
    (hkbase : kf (q c d s) = k c d) (hrbase : rf (q c d s) = r)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hss : s < distinguishedInput c d)
    (href : contactReflection c d s ≤ r)
    (hGr : deriv (fun z => contactGap lam s (q c d s) (k c d) z) r = 0)
    (hG : ∀ᶠ z in nhds (q c d s), contactGap lam s z (kf z) (rf z) = 0) :
    deriv (fun z => informationCoords s z (kf z)) (q c d s) < 0 := by
  have hk : 0 < k c d := by unfold k; linarith
  have hsr := ((lt_contactReflection_iff hc hd hs).mpr hss).trans_le href
  have hc0 : q c d s - k c d * s = c := by unfold q; ring
  have hb0 : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
  have hqr0 : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
  have hder := informationCoords_contact_output_curve_deriv_eq hkf hrf hs
    (by simpa only [hrbase] using hr) (by simpa only [hrbase] using hsr)
    (by simpa only [hkbase] using hk)
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)
    (by simpa only [hkbase, hc0] using hc)
    (by rw [hkbase, hb0]; constructor <;> linarith [hd.1, hd.2])
    (by rw [hkbase, hrbase, hqr0]; exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩)
    (by simpa only [hkbase, hrbase] using hGr) hG
  rw [hkbase, hrbase, hc0, hb0] at hder
  rw [hder]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (channel_logOdds_gap_pos hc hd hcd))
    (contactQ_pos_of_reflection_le hs hr hc hd hcd hss href)

end OutputDirection

/-! ## The two strict signs for actual supporting contacts

把前面的计算合起来，证明实际接触点族沿相应输入或输出方向变化时，导数具有严格符号。
-/

public section ContactSigns

open Set

theorem left_contact_lt_distinguishedInput {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d ≠ 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    s < distinguishedInput c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  have heS := S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd (ne_of_gt hsr) hcap hcontact
  have hlam0 : 0 < lam := by
    have hh := (rhoSquared_pos hc hd hcd hs).trans_le (rhoSquared_le_S hv hn)
    rwa [heS] at hh
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd hcd ⟨hlam0, hlam⟩
  exact (supporting_contacts_straddle_roots hs hr hc hd hcd ha hb haroot hbroot hsr hcap hcontact).1.trans ha.2

/-- Full Lemma C.2 sign, with reflected-contact placement proved from the
actual supporting contact. -/
theorem contactQ_pos_of_supporting_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    0 < contactQ (normalizedOutputLogOdds c d s) s (q c d s) (k c d) r :=
  contactQ_pos_of_reflection_le hs hr hc hd hcd
    (left_contact_lt_distinguishedInput hs hr hc hd (ne_of_lt hcd) hlam hsr hcap hcontact)
    (contactReflection_le_of_supporting_contact hs hr hc hd hcd hdc hlam hsr hcap hcontact)

/-- If `c ≥ d`, increasing output probability along any differentiable local
contact family strictly decreases information. -/
theorem informationCoords_supporting_output_curve_deriv_neg
    {kf rf : ℝ → ℝ} {lam s c d r v w : ℝ}
    (hkf : HasDerivAt kf v (q c d s)) (hrf : HasDerivAt rf w (q c d s))
    (hkbase : kf (q c d s) = k c d) (hrbase : rf (q c d s) = r)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r)
    (hG : ∀ᶠ z in nhds (q c d s), contactGap lam s z (kf z) (rf z) = 0) :
    deriv (fun z => informationCoords s z (kf z)) (q c d s) < 0 :=
  informationCoords_output_curve_deriv_neg_of_reflection_le hkf hrf hkbase hrbase hs hr hc hd hcd
    (left_contact_lt_distinguishedInput hs hr hc hd (ne_of_lt hcd) hlam hsr hcap hcontact)
    (contactReflection_le_of_supporting_contact hs hr hc hd hcd hdc hlam hsr hcap hcontact)
    (contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact) hG

/-- If `c ≤ d`, increasing input probability along any differentiable local
contact family strictly increases information. The parameters here are the
original channel entries, rather than unrestricted coordinate expressions. -/
theorem informationCoords_supporting_input_curve_deriv_pos
    {kf rf : ℝ → ℝ} {lam s c d r v w : ℝ}
    (hkf : HasDerivAt kf v s) (hrf : HasDerivAt rf w s)
    (hkbase : kf s = k c d) (hrbase : rf s = r)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (horder : c ≤ d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r)
    (hG : ∀ᶠ z in nhds s, contactGap lam z (q c d s) (kf z) (rf z) = 0) :
    0 < deriv (fun z => informationCoords z (q c d s) (kf z)) s := by
  have hk : 0 < k c d := by unfold k; linarith
  have hc0 : q c d s - k c d * s = c := by unfold q; ring
  have hb0 : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
  have hqr0 : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
  apply informationCoords_contact_curve_deriv_pos hkf hrf hs
    (by simpa only [hrbase] using hr) (by simpa only [hrbase] using hsr)
    (by simpa only [hkbase] using hk)
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)
    (by simpa only [hkbase, hc0] using hc)
    (by rw [hkbase, hb0]; constructor <;> linarith [hd.1, hd.2])
    (by rw [hkbase, hrbase, hqr0]; exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩)
    (by rw [hkbase, hc0, hb0]; linarith)
    (by simpa only [hkbase, hrbase] using contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact) hG

end ContactSigns

end BinaryPairBound
