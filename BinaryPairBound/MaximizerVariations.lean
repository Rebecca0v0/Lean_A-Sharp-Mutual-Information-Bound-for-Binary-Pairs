module

public import BinaryPairBound.Optimization
public import BinaryPairBound.InformationPerturbation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Feasible variations of a cap maximizer -/

public section

namespace BinaryPairBound

theorem IsCapMaximizer.simultaneous_flip {lam s c d : ℝ}
    (hm : IsCapMaximizer lam s c d) : IsCapMaximizer lam (1 - s) d c := by
  refine ⟨valid_simultaneous_flip hm.1, ?_, ?_⟩
  · simpa only [S_simultaneous_flip] using hm.2.1
  · intro s' c' d' hv hS
    simpa only [J_simultaneous_flip] using hm.2.2 s' c' d' hv hS

/-- Every feasible input-variation curve through a maximizer has zero
information derivative. Differentiability is not assumed for this necessary
condition: Lean's derivative is zero at a nondifferentiable local maximum. -/
theorem IsCapMaximizer.input_family_deriv_eq_zero {lam s c d : ℝ} {kf : ℝ → ℝ}
    (hm : IsCapMaximizer lam s c d) (hbase : kf s = k c d)
    (hfeas : ∀ᶠ t in nhds s,
      Valid t (q c d s - kf t * t) (1 - q c d s - kf t * (1 - t)) ∧
      S t (q c d s - kf t * t) (1 - q c d s - kf t * (1 - t)) ≤ lam) :
    deriv (fun t => informationCoords t (q c d s) (kf t)) s = 0 := by
  have hmax : IsLocalMax (fun t => informationCoords t (q c d s) (kf t)) s := by
    filter_upwards [hfeas] with t ht
    rw [hbase, informationCoords_channel, informationCoords_eq_J]
    exact hm.2.2 t _ _ ht.1 ht.2
  exact hmax.deriv_eq_zero

/-- Every feasible output-variation curve through a maximizer has zero
information derivative. -/
theorem IsCapMaximizer.output_family_deriv_eq_zero {lam s c d : ℝ} {kf : ℝ → ℝ}
    (hm : IsCapMaximizer lam s c d) (hbase : kf (q c d s) = k c d)
    (hfeas : ∀ᶠ t in nhds (q c d s),
      Valid s (t - kf t * s) (1 - t - kf t * (1 - s)) ∧
      S s (t - kf t * s) (1 - t - kf t * (1 - s)) ≤ lam) :
    deriv (fun t => informationCoords s t (kf t)) (q c d s) = 0 := by
  have hmax : IsLocalMax (fun t => informationCoords s t (kf t)) (q c d s) := by
    filter_upwards [hfeas] with t ht
    rw [hbase, informationCoords_channel, informationCoords_eq_J]
    exact hm.2.2 s _ _ ht.1 ht.2
  exact hmax.deriv_eq_zero

end BinaryPairBound
