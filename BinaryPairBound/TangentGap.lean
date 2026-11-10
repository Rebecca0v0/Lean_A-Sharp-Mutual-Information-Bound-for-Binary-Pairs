module

public import BinaryPairBound.Entropy
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith

/-!
# Equation (4.1): the gap above the tangent is a KL inequality

The tangent uses `deriv`, and we prove its derivative by the chain rule.
The algebraic identity holds for every real test input; the final corollary
states the paper's probability-domain version, including test inputs 0 and 1.
-/

public section

namespace BinaryPairBound

lemma q_sub (c d x s : ℝ) : q c d x - q c d s = k c d * (x - s) := by
  unfold q
  ring

lemma hasDerivAt_q (c d s : ℝ) : HasDerivAt (q c d) (k c d) s := by
  convert! ((hasDerivAt_id s).const_mul (k c d)).const_add c using 1
  simp

lemma hasDerivAt_entropyCurve (lam s c d : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (entropyCurve lam c d)
      ((Real.log (1 - q c d s) - Real.log (q c d s)) * k c d -
        lam * (Real.log (1 - s) - Real.log s)) s := by
  have hsH := Real.hasDerivAt_binEntropy (ne_of_gt hs.1) (ne_of_lt hs.2)
  have hqH := (Real.hasDerivAt_binEntropy (ne_of_gt hqs.1)
    (ne_of_lt hqs.2)).comp s (hasDerivAt_q c d s)
  convert! hqH.sub (hsH.const_mul lam) using 1

lemma deriv_entropyCurve (lam s c d : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (entropyCurve lam c d) s =
      (Real.log (1 - q c d s) - Real.log (q c d s)) * k c d -
        lam * (Real.log (1 - s) - Real.log s) :=
  (hasDerivAt_entropyCurve lam s c d hs hqs).deriv

/-- Equation (4.1), with minimal analytic assumptions on the reference marginals.
No sign condition on `lam` or the channel slope is needed for this identity. -/
theorem equation_4_1 (lam s c d x : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    entropyCurve lam c d x - tangent lam s c d x =
      lam * D x s - D (q c d x) (q c d s) := by
  calc
    entropyCurve lam c d x - tangent lam s c d x =
        (H (q c d x) - H (q c d s) -
          (Real.log (1 - q c d s) - Real.log (q c d s)) * (q c d x - q c d s)) -
        lam * (H x - H s - (Real.log (1 - s) - Real.log s) * (x - s)) := by
      rw [tangent, deriv_entropyCurve lam s c d hs hqs, q_sub]
      unfold entropyCurve
      ring
    _ = lam * D x s - D (q c d x) (q c d s) := by
      rw [entropy_tangent_gap, entropy_tangent_gap]
      ring

/-- A valid binary channel maps the probability interval to itself. -/
lemma q_mem_Icc (c d x : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    q c d x ∈ Set.Icc (0 : ℝ) 1 := by
  have hxc := mul_nonneg (sub_nonneg.mpr hx.2) hc.1
  have hxd := mul_nonneg hx.1 (sub_nonneg.mpr hd.2)
  have hxc' := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hc.2)
  have hxd' := mul_nonneg hx.1 hd.1
  dsimp [q, k]
  constructor <;> nlinarith

/-- Equation (4.1) in the paper's original logarithm-of-ratio notation.
This includes both endpoint test inputs, with `0 * log 0 = 0`. -/
theorem equation_4_1_log_ratio (lam s c d x : ℝ)
    (hv : Valid s c d) (hn : Nondegenerate s c d) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    entropyCurve lam c d x - tangent lam s c d x =
      lam * (x * Real.log (x / s) + (1 - x) * Real.log ((1 - x) / (1 - s))) -
        (q c d x * Real.log (q c d x / q c d s) +
          (1 - q c d x) * Real.log ((1 - q c d x) / (1 - q c d s))) := by
  rw [equation_4_1 lam s c d x hn.1 hn.2]
  rw [D_eq_log_ratio hx hn.1, D_eq_log_ratio (q_mem_Icc c d x hv.2.1 hv.2.2 hx) hn.2]

end BinaryPairBound
