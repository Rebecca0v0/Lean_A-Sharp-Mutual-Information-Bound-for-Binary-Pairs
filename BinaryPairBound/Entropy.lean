module

public import BinaryPairBound.Definitions
public import Mathlib.Tactic.Ring

/-!
# Entropy and Bernoulli divergence identities

These identities connect the scalar definitions to the formulas printed in
Section 2 and supply the entropy tangent-gap calculation used in equation (4.1).
The Bernoulli test parameter may be either endpoint; the reference parameter
in `D_eq_log_ratio` has full support.
-/

noncomputable section

public section

namespace BinaryPairBound

/-- Binary entropy written using ordinary natural logarithms. -/
theorem H_eq (x : ℝ) :
    H x = -x * Real.log x - (1 - x) * Real.log (1 - x) := by
  rw [H, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  ring

/-- The cross-entropy definition agrees with the paper's Bernoulli KL formula.

The cases `x = 0` and `x = 1` use the usual zero-mass convention. No claim is
made here about KL divergence with a deterministic reference distribution.
-/
theorem D_eq_log_ratio {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    D x y = x * Real.log (x / y) +
      (1 - x) * Real.log ((1 - x) / (1 - y)) := by
  by_cases hx_zero : x = 0
  · subst x
    simp [D, H, one_div, Real.log_inv]
  by_cases hx_one : x = 1
  · subst x
    simp [D, H, one_div, Real.log_inv]
  have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
  have hx_lt_one : x < 1 := lt_of_le_of_ne hx.2 hx_one
  rw [D, H_eq, Real.log_div (ne_of_gt hx_pos) (ne_of_gt hy.1),
    Real.log_div (ne_of_gt (sub_pos.mpr hx_lt_one)) (ne_of_gt (sub_pos.mpr hy.2))]
  ring

/-- The entropy tangent-gap identity underlying equation (4.1).

This algebraic identity also holds for the total real-valued extensions of
`H` and `D`. Interpreting the displayed coefficient as an actual entropy
derivative requires an interior reference, supplied in the tangent theorem.
-/
theorem entropy_tangent_gap (x s : ℝ) :
    H x - H s - (Real.log (1 - s) - Real.log s) * (x - s) = -D x s := by
  rw [D, H_eq s]
  ring

end BinaryPairBound
