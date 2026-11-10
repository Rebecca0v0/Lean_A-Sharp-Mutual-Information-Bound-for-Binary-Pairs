module

public import BinaryPairBound.Divergence
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Differentiation of Bernoulli divergence on the interior probability interval -/

noncomputable section

@[expose] public section

namespace BinaryPairBound

/-- Log odds on the interior probability interval, with a total real extension. -/
def logOdds (x : ℝ) : ℝ := Real.log x - Real.log (1 - x)

theorem logOdds_strictMonoOn : StrictMonoOn logOdds (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have h1 := Real.log_lt_log hx.1 hxy
  have h2 := Real.log_lt_log (sub_pos.mpr hy.2) (show 1 - y < 1 - x by linarith)
  unfold logOdds
  linarith

theorem hasDerivAt_logOdds {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt logOdds (1 / (x * (1 - x))) x := by
  have h := (hasDerivAt_id x).log (ne_of_gt hx.1)
  have h' := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt (sub_pos.mpr hx.2))
  convert! h.sub h' using 1
  simp only [id_eq]
  field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
  ring

/-- Chain rule when both Bernoulli parameters vary along a real curve. -/
theorem hasDerivAt_D_comp {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hft : f t ∈ Set.Ioo (0 : ℝ) 1) (hgt : g t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => D (f z) (g z))
      (f' * (logOdds (f t) - logOdds (g t)) +
        g' * (g t - f t) / (g t * (1 - g t))) t := by
  have hH := (Real.hasDerivAt_binEntropy (ne_of_gt hft.1) (ne_of_lt hft.2)).comp t hf
  have hlg := hg.log (ne_of_gt hgt.1)
  have hl1g := (hg.const_sub 1).log (ne_of_gt (sub_pos.mpr hgt.2))
  have h := (hH.neg.sub (hf.mul hlg)).sub ((hf.const_sub 1).mul hl1g)
  convert! h using 1
  unfold logOdds
  field_simp [ne_of_gt hgt.1, ne_of_gt (sub_pos.mpr hgt.2)]
  ring

theorem hasDerivAt_D_left {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => D z y) (logOdds x - logOdds y) x := by
  simpa only [id_eq, one_mul, zero_mul, zero_div, add_zero] using
    (hasDerivAt_D_comp (hasDerivAt_id x) (hasDerivAt_const x y) hx hy)

theorem hasDerivAt_D_right {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => D x z) ((y - x) / (y * (1 - y))) y := by
  simpa only [id_eq, one_mul, zero_mul, zero_add] using
    (hasDerivAt_D_comp (hasDerivAt_const y x) (hasDerivAt_id y) hx hy)

end BinaryPairBound
