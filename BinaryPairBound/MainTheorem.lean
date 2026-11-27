module

public import BinaryPairBound.BinaryInformation
public import BinaryPairBound.InformationBounds
public import BinaryPairBound.SharpMerging
public import BinaryPairBound.MaximizerExistence
public import BinaryPairBound.InteriorMaximizers
public import BinaryPairBound.BoundaryImprovement

/-!
# Theorem 2.1 and its complete equality classification

合并边界排除、内部极大值结论和特殊输入上界，完整证明Theorem 2.1与固定系数最优值。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Relabeling and endpoint reductions

证明只需处理重标记后、系数不在端点的情形，就足以推出原来的不等式。
-/

@[expose] public section Reduction

/-- The still-open core bound after endpoint cases and output relabeling. -/
def NormalizedSharpBound : Prop :=
  ∀ s c d : ℝ, Valid s c d → 0 < k c d → S s c d ∈ Set.Ioo (0 : ℝ) 1 →
    J s c d ≤ phi (S s c d)

/-- All deterministic, independent, cap-endpoint, and negative-slope cases
reduce to the positive-slope, nonendpoint problem. This is not a proof of
the remaining premise. -/
theorem sharpBound_of_normalized (hcore : NormalizedSharpBound) : SharpBound := by
  intro s c d hv
  by_cases hS0 : S s c d = 0
  · exact (sharp_equality_of_S_zero hv hS0).1.le
  by_cases hS1 : S s c d = 1
  · exact sharp_bound_of_S_one hv hS1
  have hS : S s c d ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (S_nonneg hv) (Ne.symm hS0), lt_of_le_of_ne (S_le_one hv) hS1⟩
  rcases lt_trichotomy (k c d) 0 with hk | hk | hk
  · have hflip : 0 < k (1 - c) (1 - d) := by rw [k_output_flip]; linarith
    have h := hcore s (1 - c) (1 - d) (valid_output_flip hv) hflip
      (by simpa only [S_output_flip] using hS)
    simpa only [J_output_flip, S_output_flip] using h
  · have hi : Independent s c d := Or.inr (Or.inr (by unfold k at hk; linarith))
    exact (hS0 (S_eq_zero_of_independent hi)).elim
  · exact hcore s c d hv hk hS

theorem sharpBound_iff_normalized : SharpBound ↔ NormalizedSharpBound := by
  constructor
  · intro h s c d hv _ _
    exact h s c d hv
  · exact sharpBound_of_normalized

end Reduction

/-! ## Assembly from the maximizer conclusion

说明一旦知道所有规范化极大值都位于特殊输入位置，怎样推出主定理的不等式和完整取等条件。
-/

@[expose] public section Main

/-- The geometric reduction from Sections 4–6 and 9. It says that
every normalized nonendpoint-cap maximizer has an interior channel and its
reference input is the distinguished input. It is proved by `maximizersMerge`
in `MainTheorem.lean`. -/
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

/-- Assembly of the inequality from the contact/optimization reduction. -/
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

/-- Assemble the unchanged original theorem specification from its geometric
reduction. `MainTheorem.lean` discharges this premise. -/
theorem mainTheorem_of_maximizersMerge (hmerge : MaximizersMerge) : MainTheorem :=
  ⟨sharpBound_of_maximizersMerge hmerge, equalityClassification_of_maximizersMerge hmerge⟩

end Main

/-! ## Proving the maximizer conclusion and completing Theorem 2.1

证明上一文件所需的极大值结论，完成无需额外证明前提的主定理。
-/

public section MainProof

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

end MainProof

end BinaryPairBound
