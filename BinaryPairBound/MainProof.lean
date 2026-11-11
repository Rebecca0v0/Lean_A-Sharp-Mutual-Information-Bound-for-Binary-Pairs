module

public import BinaryPairBound.Main
public import BinaryPairBound.InteriorMaximizer
public import BinaryPairBound.BoundaryImprovement

/-! # Theorem 2.1: the sharp bound and its complete equality classification -/

public section

namespace BinaryPairBound

/-- A nonendpoint-cap maximizer has strictly positive channel transitions. -/
theorem normalized_cap_maximizer_interior {lam s c d : ℝ}
    (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hm : IsCapMaximizer lam s c d)
    (hcd : c + d ≤ 1) : c ∈ Set.Ioo (0 : ℝ) 1 ∧ d ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn := cap_maximizer_nondegenerate ⟨hlam.1, hlam.2.le⟩ hm
  have hk := normalized_cap_maximizer_slope_pos ⟨hlam.1, hlam.2.le⟩ hm hcd
  have hcdlt : c + d < 1 := by unfold k at hk; linarith
  have hcz : c ≠ 0 := by
    intro hc0
    have hdpos : 0 < d := by
      apply lt_of_le_of_ne hm.1.2.2.1
      intro hd0
      exact cap_maximizer_not_noiseless hlam hm ⟨hc0, hd0.symm⟩
    have hdint : d ∈ Set.Ioo (0 : ℝ) 1 := ⟨hdpos, by linarith [hm.1.2.1.1]⟩
    have hsflip : 1 - s ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hn.1.2], by linarith [hn.1.1]⟩
    obtain ⟨c', d', hc', hd', _, hS', hJ'⟩ := boundary_improvement_zero_right hsflip hdint
    have hmflip := hm.simultaneous_flip
    rw [hc0] at hmflip
    have hv' : Valid (1 - s) c' d' :=
      ⟨⟨hsflip.1.le, hsflip.2.le⟩, ⟨hc'.1.le, hc'.2.le⟩, ⟨hd'.1.le, hd'.2.le⟩⟩
    have hbound := hmflip.2.2 (1 - s) c' d' hv' (by rw [hS']; exact hmflip.2.1)
    exact (not_le_of_gt hJ') hbound
  have hdz : d ≠ 0 := by
    intro hd0
    have hcpos : 0 < c := lt_of_le_of_ne hm.1.2.1.1 (Ne.symm hcz)
    have hcint : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨hcpos, by linarith [hm.1.2.2.1]⟩
    obtain ⟨c', d', hc', hd', _, hS', hJ'⟩ := boundary_improvement_zero_right hn.1 hcint
    have hv' : Valid s c' d' :=
      ⟨hm.1.1, ⟨hc'.1.le, hc'.2.le⟩, ⟨hd'.1.le, hd'.2.le⟩⟩
    have hcap : S s c' d' ≤ lam := by rw [hS', ← hd0]; exact hm.2.1
    have hbound := hm.2.2 s c' d' hv' hcap
    rw [hd0] at hbound
    exact (not_le_of_gt hJ') hbound
  exact ⟨⟨lt_of_le_of_ne hm.1.2.1.1 (Ne.symm hcz), by linarith [hm.1.2.2.1]⟩,
    ⟨lt_of_le_of_ne hm.1.2.2.1 (Ne.symm hdz), by linarith [hm.1.2.1.1]⟩⟩

/-- The geometric reduction is now proved, with no additional premise. -/
theorem maximizersMerge : MaximizersMerge := by
  intro lam s c d hlam hm hcd
  obtain ⟨hc, hd⟩ := normalized_cap_maximizer_interior hlam hm hcd
  exact ⟨hc, hd, interior_cap_maximizer_distinguishedInput ⟨hlam.1, hlam.2.le⟩ hm hc hd hcd⟩

/-- The complete scalar form of Theorem 2.1, including all parameter-cube
boundaries, both slope signs, and both directions of the equality statement. -/
theorem mainTheorem : MainTheorem := mainTheorem_of_maximizersMerge maximizersMerge

theorem sharp_bound {s c d : ℝ} (hv : Valid s c d) : J s c d ≤ phi (S s c d) :=
  mainTheorem.1 s c d hv

theorem sharp_equality_iff {s c d : ℝ} (hv : Valid s c d) :
    J s c d = phi (S s c d) ↔ Independent s c d ∨ DSBS s c d :=
  mainTheorem.2 s c d hv

/-- The exact constrained optimum in equation (3.1), including endpoint caps. -/
theorem fixed_cap_optimum {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (∃ s c d : ℝ, Valid s c d ∧ S s c d = lam ∧ J s c d = phi lam) ∧
    ∀ s c d : ℝ, Valid s c d → S s c d ≤ lam → J s c d ≤ phi lam := by
  refine ⟨exists_sharp_cap_witness hlam, ?_⟩
  intro s c d hv hS
  exact (sharp_bound hv).trans (phi_strictMonoOn.monotoneOn (S_mem_Icc hv) hlam hS)

end BinaryPairBound
