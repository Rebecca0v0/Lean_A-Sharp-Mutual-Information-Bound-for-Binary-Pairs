module

public import BinaryPairBound.Optimization
public import BinaryPairBound.MergingSharp
public import BinaryPairBound.Reduction

/-!
# Assembly of Theorem 2.1 conditional on the remaining contact reduction

`MaximizersMerge` is an UNPROVED proposition, not an axiom. The theorems in
this file show that proving this geometric reduction suffices for the exact
original bound and its complete equality classification. No inhabitant of
`MainTheorem` is asserted here.
-/

@[expose] public section

namespace BinaryPairBound

/-- The remaining geometric theorem from Sections 4–6 and 9. It says that
every normalized nonendpoint-cap maximizer has an interior channel and its
reference input is the distinguished input. This proposition is NOT proved. -/
def MaximizersMerge : Prop :=
  ∀ lam s c d : ℝ, lam ∈ Set.Ioo (0 : ℝ) 1 → IsCapMaximizer lam s c d → c + d ≤ 1 →
    c ∈ Set.Ioo (0 : ℝ) 1 ∧ d ∈ Set.Ioo (0 : ℝ) 1 ∧ s = distinguishedInput c d

theorem cap_maximizer_bound_of_merge (hmerge : MaximizersMerge)
    {lam s c d : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 1)
    (hm : IsCapMaximizer lam s c d) (hcd : c + d ≤ 1) : J s c d ≤ phi lam := by
  obtain ⟨hc, hd, hs⟩ := hmerge lam s c d hlam hm hcd
  have hk := normalized_cap_maximizer_slope_pos ⟨hlam.1, hlam.2.le⟩ hm hcd
  have hcdlt : c + d < 1 := by unfold k at hk; linarith
  have hJ : J s c d ≤ phi (S s c d) := by
    simpa only [hs] using merging_sharp_bound hc hd hcdlt
  exact hJ.trans (phi_strictMonoOn.monotoneOn (S_mem_Icc hm.1) ⟨hlam.1.le, hlam.2.le⟩ hm.2.1)

/-- Conditional assembly of the inequality. The premise is the remaining
unproved contact/optimization reduction. -/
theorem sharpBound_of_maximizersMerge (hmerge : MaximizersMerge) : SharpBound := by
  intro s c d hv
  by_cases hS0 : S s c d = 0
  · exact (sharp_equality_of_S_zero hv hS0).1.le
  by_cases hS1 : S s c d = 1
  · exact sharp_bound_of_S_one hv hS1
  have hS : S s c d ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (S_nonneg hv) (Ne.symm hS0), lt_of_le_of_ne (S_le_one hv) hS1⟩
  obtain ⟨s', c', d', hm, hcd⟩ := exists_normalized_maximizer (S_nonneg hv)
  exact (hm.2.2 s c d hv le_rfl).trans (cap_maximizer_bound_of_merge hmerge hS hm hcd)

private theorem dsbs_of_normalized_equality_maximizer (hmerge : MaximizersMerge)
    {lam s c d : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 1)
    (hm : IsCapMaximizer lam s c d) (hcd : c + d ≤ 1)
    (hJ : J s c d = phi (S s c d)) : DSBS s c d := by
  obtain ⟨hc, hd, hs⟩ := hmerge lam s c d hlam hm hcd
  have hk := normalized_cap_maximizer_slope_pos ⟨hlam.1, hlam.2.le⟩ hm hcd
  have hcdlt : c + d < 1 := by unfold k at hk; linarith
  rw [hs] at hJ ⊢
  exact (merging_sharp_eq_iff_dsbs hc hd hcdlt).mp hJ

/-- Conditional assembly of BOTH directions of the complete equality statement. -/
theorem equalityClassification_of_maximizersMerge (hmerge : MaximizersMerge) :
    EqualityClassification := by
  intro s c d hv
  constructor
  · intro hJ
    by_cases hS0 : S s c d = 0
    · exact Or.inl ((S_eq_zero_iff_independent hv).mp hS0)
    by_cases hS1 : S s c d = 1
    · have heq := (sharp_equality_iff_of_S_one hv hS1).mp hJ
      exact Or.inr ⟨heq.1, heq.2.1⟩
    have hS : S s c d ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne (S_nonneg hv) (Ne.symm hS0), lt_of_le_of_ne (S_le_one hv) hS1⟩
    have hm : IsCapMaximizer (S s c d) s c d := by
      refine ⟨hv, le_rfl, ?_⟩
      intro s' c' d' hv' hS'
      rw [hJ]
      exact (sharpBound_of_maximizersMerge hmerge s' c' d' hv').trans
        (phi_strictMonoOn.monotoneOn (S_mem_Icc hv') (S_mem_Icc hv) hS')
    by_cases hcd : c + d ≤ 1
    · exact Or.inr (dsbs_of_normalized_equality_maximizer hmerge hS hm hcd hJ)
    · have hmflip : IsCapMaximizer (S s c d) s (1 - c) (1 - d) := by
        refine ⟨valid_output_flip hv, ?_, ?_⟩
        · rw [S_output_flip]
        · intro s' c' d' hv' hS'
          simpa only [J_output_flip] using hm.2.2 s' c' d' hv' hS'
      have hJflip : J s (1 - c) (1 - d) = phi (S s (1 - c) (1 - d)) := by
        simpa only [J_output_flip, S_output_flip] using hJ
      have heq := dsbs_of_normalized_equality_maximizer hmerge hS hmflip (by linarith) hJflip
      exact Or.inr ⟨heq.1, by linarith [heq.2]⟩
  · exact sharp_equality_of_independent_or_dsbs hv

/-- Completing `MaximizersMerge` would complete the unchanged original theorem
specification. This conditional theorem is NOT a completed proof of the paper. -/
theorem mainTheorem_of_maximizersMerge (hmerge : MaximizersMerge) : MainTheorem :=
  ⟨sharpBound_of_maximizersMerge hmerge, equalityClassification_of_maximizersMerge hmerge⟩

end BinaryPairBound
