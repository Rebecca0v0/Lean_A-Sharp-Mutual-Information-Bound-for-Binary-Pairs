module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The strict hyperbolic inequality in Appendix C.4

We prove the decrease of `A*` by ordinary differentiation, avoiding the
infinite-series calculation in (C.11). This also proves positivity of the
explicit expression in (C.8). `ReflectedSign.lean` identifies it with the
actual reflected-contact sign; `ContactPlacement.lean` completes the
supporting-contact comparison.
-/

noncomputable section
@[expose] public section

namespace BinaryPairBound

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

end BinaryPairBound
