module

public import BinaryPairBound.JointRatioContinuity
public import BinaryPairBound.InformationPerturbation
public import BinaryPairBound.Optimization
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # An interior maximizer must saturate its cap (Section 9) -/

noncomputable section
public section

namespace BinaryPairBound

/-- The cap-saturation step from Section 9. Interior transitions are explicit
hypotheses; excluding boundary maximizers is still a separate obligation. -/
theorem interior_cap_maximizer_saturates {lam s c d : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (hm : IsCapMaximizer lam s c d)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d ≤ 1) : S s c d = lam := by
  have hn := cap_maximizer_nondegenerate hlam hm
  have hk := normalized_cap_maximizer_slope_pos hlam hm hcd
  have hc0 : q c d s - k c d * s = c := by unfold q; ring
  have hd0 : 1 - q c d s - k c d * (1 - s) = d := by unfold q k; ring
  have hb0 : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
  by_contra hne
  have hlt := lt_of_le_of_ne hm.2.1 hne
  have hccont : ContinuousAt (fun t : ℝ => q c d s - t * s) (k c d) := by fun_prop
  have hdcont : ContinuousAt (fun t : ℝ => 1 - q c d s - t * (1 - s)) (k c d) := by fun_prop
  have hce : ∀ᶠ t in nhds (k c d), q c d s - t * s ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hccont
    simpa only [hc0] using Ioo_mem_nhds hc.1 hc.2
  have hde : ∀ᶠ t in nhds (k c d), 1 - q c d s - t * (1 - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hdcont
    simpa only [hd0] using Ioo_mem_nhds hd.1 hd.2
  have hvalid : ∀ᶠ t in nhds (k c d),
      Valid s (q c d s - t * s) (1 - q c d s - t * (1 - s)) := by
    filter_upwards [hce, hde] with t hct hdt
    exact ⟨hm.1.1, ⟨hct.1.le, hct.2.le⟩, ⟨hdt.1.le, hdt.2.le⟩⟩
  have hnpath : Nondegenerate s (q c d s - k c d * s)
      (1 - q c d s - k c d * (1 - s)) := by simpa only [hc0, hd0] using hn
  have hScont := continuousAt_S_comp continuousAt_const hccont hdcont hvalid hnpath
  have hfeas : ∀ᶠ t in nhds (k c d),
      S s (q c d s - t * s) (1 - q c d s - t * (1 - s)) < lam := by
    change ∀ᶠ t in nhds (k c d),
      S s (q c d s - t * s) (1 - q c d s - t * (1 - s)) ∈ Set.Iio lam
    apply hScont
    simpa only [hc0, hd0] using Iio_mem_nhds hlt
  have hmax : IsLocalMax (fun t => informationCoords s (q c d s) t) (k c d) := by
    filter_upwards [hvalid, hfeas] with t hvt hft
    rw [informationCoords_eq_J, informationCoords_channel]
    exact hm.2.2 s _ _ hvt hft.le
  have hpos : 0 < deriv (fun t => informationCoords s (q c d s) t) (k c d) := by
    apply informationCoords_deriv_k_pos hn.1 hk hn.2
    · simpa only [hc0] using hc
    · rw [hb0]
      constructor <;> linarith [hd.1, hd.2]
  rw [hmax.deriv_eq_zero] at hpos
  exact (lt_irrefl 0) hpos

end BinaryPairBound
