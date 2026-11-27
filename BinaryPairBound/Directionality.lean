module

public import BinaryPairBound.MainTheorem
public import BinaryPairBound.BinaryRandomVariables

/-!
# Bidirectional bounds, strictness, and attainment

把反向信道、两方向最小上界、系数不等的严格性及相同系数的达到结果完整连接到实际随机变量。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Bayes reversal and scalar bidirectional conclusions

交换输入和输出得到反向信道，并证明双向最小上界、系数不等时严格不等式及系数相等时的达到例子。
-/

@[expose] public noncomputable section ReverseChannel

/-- Conditional probability `P(W = 1 | Z = 0)`. -/
def reverseC (s c d : ℝ) : ℝ := s * d / (1 - q c d s)

/-- Conditional probability `P(W = 0 | Z = 1)`. -/
def reverseD (s c d : ℝ) : ℝ := (1 - s) * c / q c d s

lemma reverseC_mem_Icc {s c d : ℝ} (hv : Valid s c d) :
    reverseC s c d ∈ Set.Icc (0 : ℝ) 1 := by
  have hq := q_mem_Icc c d s hv.2.1 hv.2.2 hv.1
  have hn : 0 ≤ s * d := mul_nonneg hv.1.1 hv.2.2.1
  have hu : s * d ≤ 1 - q c d s := by
    have h := mul_nonneg (sub_nonneg.mpr hv.1.2) (sub_nonneg.mpr hv.2.1.2)
    unfold q k
    nlinarith
  unfold reverseC
  constructor
  · exact div_nonneg hn (sub_nonneg.mpr hq.2)
  · by_cases h : 1 - q c d s = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne (sub_nonneg.mpr hq.2) (Ne.symm h))).mpr hu

lemma reverseD_mem_Icc {s c d : ℝ} (hv : Valid s c d) :
    reverseD s c d ∈ Set.Icc (0 : ℝ) 1 := by
  have hq := q_mem_Icc c d s hv.2.1 hv.2.2 hv.1
  have hn : 0 ≤ (1 - s) * c := mul_nonneg (sub_nonneg.mpr hv.1.2) hv.2.1.1
  have hu : (1 - s) * c ≤ q c d s := by
    have h := mul_nonneg hv.1.1 (sub_nonneg.mpr hv.2.2.2)
    unfold q k
    nlinarith
  unfold reverseD
  constructor
  · exact div_nonneg hn hq.1
  · by_cases h : q c d s = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne hq.1 (Ne.symm h))).mpr hu

theorem reverse_valid {s c d : ℝ} (hv : Valid s c d) :
    Valid (q c d s) (reverseC s c d) (reverseD s c d) :=
  ⟨q_mem_Icc c d s hv.2.1 hv.2.2 hv.1, reverseC_mem_Icc hv, reverseD_mem_Icc hv⟩

lemma reverseC_mass {s c d : ℝ} (hv : Valid s c d) :
    (1 - q c d s) * reverseC s c d = s * d := by
  unfold reverseC
  by_cases h : 1 - q c d s = 0
  · have hz : s * d = 0 := by
      have h1 := mul_nonneg hv.1.1 hv.2.2.1
      have h2 := mul_nonneg (sub_nonneg.mpr hv.1.2) (sub_nonneg.mpr hv.2.1.2)
      unfold q k at h
      nlinarith
    simp [h, hz]
  · field_simp

lemma reverseD_mass {s c d : ℝ} (hv : Valid s c d) :
    q c d s * reverseD s c d = (1 - s) * c := by
  unfold reverseD
  by_cases h : q c d s = 0
  · have hz : (1 - s) * c = 0 := by
      have h1 := mul_nonneg (sub_nonneg.mpr hv.1.2) hv.2.1.1
      have h2 := mul_nonneg hv.1.1 (sub_nonneg.mpr hv.2.2.2)
      unfold q k at h
      nlinarith
    simp [h, hz]
  · field_simp

theorem reverse_output {s c d : ℝ} (hv : Valid s c d) :
    q (reverseC s c d) (reverseD s c d) (q c d s) = s := by
  have h1 := reverseC_mass hv
  have h2 := reverseD_mass hv
  unfold q k at *
  nlinarith

/-- The entropy of the four joint masses, grouped by the input. -/
theorem binary_joint_entropy (s c d : ℝ) :
    H s + (1 - s) * H c + s * H d =
      Real.negMulLog ((1 - s) * (1 - c)) + Real.negMulLog ((1 - s) * c) +
      Real.negMulLog (s * d) + Real.negMulLog (s * (1 - d)) := by
  simp only [H, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog_mul]
  ring

/-- Swapping input and output preserves mutual information. -/
theorem J_reverse {s c d : ℝ} (hv : Valid s c d) :
    J (q c d s) (reverseC s c d) (reverseD s c d) = J s c d := by
  have h1 := reverseC_mass hv
  have h2 := reverseD_mass hv
  have h3 : (1 - q c d s) * (1 - reverseC s c d) = (1 - s) * (1 - c) := by
    unfold q k at h1 ⊢
    nlinarith
  have h4 : q c d s * (1 - reverseD s c d) = s * (1 - d) := by
    unfold q k at h2 ⊢
    nlinarith
  have he := binary_joint_entropy (q c d s) (reverseC s c d) (reverseD s c d)
  rw [h3, h1, h2, h4] at he
  have he' := binary_joint_entropy s c d
  unfold J
  rw [reverse_output hv]
  linarith

/-- Probabilistic independence is unchanged by Bayes reversal. -/
theorem independent_reverse_iff {s c d : ℝ} (hv : Valid s c d) :
    Independent (q c d s) (reverseC s c d) (reverseD s c d) ↔ Independent s c d := by
  rw [← J_eq_zero_iff_independent (reverse_valid hv), J_reverse hv,
    J_eq_zero_iff_independent hv]

/-- Doubly symmetric binary sources are unchanged by Bayes reversal. -/
theorem dsbs_reverse_iff {s c d : ℝ} (hv : Valid s c d) :
    DSBS (q c d s) (reverseC s c d) (reverseD s c d) ↔ DSBS s c d := by
  constructor
  · rintro ⟨hq, hcd⟩
    have ho := reverse_output hv
    rw [hq, hcd, q_half_symmetric] at ho
    have hs : s = 1 / 2 := ho.symm
    have h1 := reverseC_mass hv
    have h2 := reverseD_mass hv
    rw [hcd, hq, hs] at h1
    rw [hq, hs] at h2
    exact ⟨hs, by nlinarith⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨q_half_symmetric _, ?_⟩
    simp only [reverseC, reverseD, q_half_symmetric]
    ring

/-- On either equality family, the two directed coefficients coincide. -/
theorem S_reverse_eq_of_equality_case {s c d : ℝ} (hv : Valid s c d)
    (he : Independent s c d ∨ DSBS s c d) :
    S (q c d s) (reverseC s c d) (reverseD s c d) = S s c d := by
  rcases he with hi | ⟨rfl, rfl⟩
  · rw [S_eq_zero_of_independent hi,
      S_eq_zero_of_independent ((independent_reverse_iff hv).mpr hi)]
  · have hq : q c c (1 / 2) = 1 / 2 := q_half_symmetric c
    have hc : reverseC (1 / 2) c c = c := by
      simp only [reverseC, hq]
      ring
    have hd : reverseD (1 / 2) c c = c := by
      simp only [reverseD, hq]
      ring
    rw [hq, hc, hd]

/-- The coefficient in the opposite direction, computed by Bayes' formula. -/
def reverseS (s c d : ℝ) : ℝ :=
  S (q c d s) (reverseC s c d) (reverseD s c d)

/-- Applying the sharp theorem in both directions gives the minimum bound. -/
theorem bidirectional_bound {s c d : ℝ} (hv : Valid s c d) :
    J s c d ≤ phi (min (S s c d) (reverseS s c d)) := by
  have hf := sharp_bound hv
  have hr := sharp_bound (reverse_valid hv)
  rw [J_reverse hv] at hr
  change J s c d ≤ phi (reverseS s c d) at hr
  rcases le_total (S s c d) (reverseS s c d) with h | h
  · rw [min_eq_left h]
    exact hf
  · rw [min_eq_right h]
    exact hr

/-- The two-direction bound has exactly the same equality families. -/
theorem bidirectional_equality_iff {s c d : ℝ} (hv : Valid s c d) :
    J s c d = phi (min (S s c d) (reverseS s c d)) ↔
      Independent s c d ∨ DSBS s c d := by
  constructor
  · intro he
    rcases le_total (S s c d) (reverseS s c d) with h | h
    · rw [min_eq_left h] at he
      exact (sharp_equality_iff hv).mp he
    · rw [min_eq_right h] at he
      have hr : J (q c d s) (reverseC s c d) (reverseD s c d) =
          phi (S (q c d s) (reverseC s c d) (reverseD s c d)) := by
        rw [J_reverse hv]
        exact he
      rcases (sharp_equality_iff (reverse_valid hv)).mp hr with hi | hd
      · exact Or.inl ((independent_reverse_iff hv).mp hi)
      · exact Or.inr ((dsbs_reverse_iff hv).mp hd)
  · intro he
    have hr : reverseS s c d = S s c d := S_reverse_eq_of_equality_case hv he
    rw [hr, min_self]
    exact (sharp_equality_iff hv).mpr he

/-- Section 10: unequal forward and reverse coefficients rule out attainment.
This includes endpoint coefficients; no strict interior assumption is needed. -/
theorem bidirectional_strict_of_ne {s c d : ℝ} (hv : Valid s c d)
    (hne : S s c d ≠ reverseS s c d) :
    J s c d < phi (min (S s c d) (reverseS s c d)) := by
  refine lt_of_le_of_ne (bidirectional_bound hv) ?_
  intro he
  have heq := (bidirectional_equality_iff hv).mp he
  exact hne (S_reverse_eq_of_equality_case hv heq).symm

/-- The simultaneous-constraint statement printed in the conclusion. -/
theorem prescribed_bidirectional_strict {s c d a b : ℝ} (hv : Valid s c d)
    (ha : S s c d = a) (hb : reverseS s c d = b) (hne : a ≠ b) :
    J s c d < phi (min a b) := by
  rw [← ha, ← hb]
  exact bidirectional_strict_of_ne hv (by simpa only [ha, hb] using hne)

/-- Section 10: the sharp optimum under equal prescribed coefficients in both directions,
including the endpoint values. The witness is an actual doubly symmetric source. -/
theorem equal_directed_cap_optimum {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (∃ s c d : ℝ, Valid s c d ∧ S s c d = lam ∧ reverseS s c d = lam ∧
      J s c d = phi lam) ∧
    ∀ s c d : ℝ, Valid s c d → S s c d = lam → reverseS s c d = lam →
      J s c d ≤ phi lam := by
  have hc := symmetricCrossover_mem_Icc hlam
  have hv : Valid (1 / 2) (symmetricCrossover lam) (symmetricCrossover lam) :=
    ⟨by norm_num, hc, hc⟩
  have hS := S_symmetricCrossover hlam
  have hr : reverseS (1 / 2) (symmetricCrossover lam) (symmetricCrossover lam) = lam := by
    exact (S_reverse_eq_of_equality_case hv (Or.inr ⟨rfl, rfl⟩)).trans hS
  refine ⟨⟨1 / 2, symmetricCrossover lam, symmetricCrossover lam,
    hv, hS, hr, J_symmetricCrossover lam⟩, ?_⟩
  intro s c d hvalid hforward _
  simpa only [hforward] using sharp_bound hvalid

end ReverseChannel

/-! ## Bidirectional conclusions for actual random variables

把正反向系数的最小上界及系数不等时的严格不等式，写成实际二元随机变量的结论。
-/

@[expose] public noncomputable section RandomVariableDirections

namespace BinaryLaw

theorem ext_mass {P Q : BinaryLaw} (h : P.mass = Q.mass) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- Swap the coordinates of the actual joint probability table. -/
def swap (P : BinaryLaw) : BinaryLaw where
  mass a b := P.mass b a
  nonneg a b := P.nonneg b a
  total := by have h := P.total; linarith

lemma swap_input (P : BinaryLaw) : P.swap.input = P.output := rfl

lemma swap_left (P : BinaryLaw) : P.swap.left = reverseC P.input P.left P.right := by
  unfold left swap reverseC
  change P.mass true false / (1 - P.output) = _
  rw [P.output_eq, P.mass10]
  rfl

lemma swap_right (P : BinaryLaw) : P.swap.right = reverseD P.input P.left P.right := by
  unfold right swap reverseD
  change P.mass false true / P.output = _
  rw [P.output_eq, P.mass01]
  rfl

lemma swap_contraction (P : BinaryLaw) :
    P.swap.contraction = reverseS P.input P.left P.right := by
  rw [contraction, swap_input, swap_left, swap_right, P.output_eq]
  rfl

/-- The same sharp bound applied in both directions. -/
theorem bidirectional_bound (P : BinaryLaw) :
    P.mutualInfo ≤ phi (min P.contraction P.swap.contraction) := by
  rw [P.mutualInfo_eq, P.swap_contraction]
  exact BinaryPairBound.bidirectional_bound P.valid

/-- Unequal directed coefficients force strictness. -/
theorem bidirectional_strict (P : BinaryLaw) (hne : P.contraction ≠ P.swap.contraction) :
    P.mutualInfo < phi (min P.contraction P.swap.contraction) := by
  rw [P.mutualInfo_eq, P.swap_contraction]
  rw [P.swap_contraction] at hne
  exact BinaryPairBound.bidirectional_strict_of_ne P.valid hne

end BinaryLaw

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma binaryLaw_swap (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) :
    binaryLaw μ Z W hZ hW = (binaryLaw μ W Z hW hZ).swap := by
  apply BinaryLaw.ext_mass
  funext a b
  simp only [binaryLaw, BinaryLaw.swap, Set.inter_comm]

/-- Section 10's minimum bound, using the coefficient of each actual variable order. -/
theorem binary_random_variable_bidirectional_bound (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ ≤
      phi (min (binaryContraction μ W Z hW hZ) (binaryContraction μ Z W hZ hW)) := by
  unfold binaryMutualInfo binaryContraction
  rw [binaryLaw_swap]
  exact BinaryLaw.bidirectional_bound _

/-- Section 10's nonattainment assertion for unequal directed coefficients. -/
theorem binary_random_variable_bidirectional_strict (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z)
    (hne : binaryContraction μ W Z hW hZ ≠ binaryContraction μ Z W hZ hW) :
    binaryMutualInfo μ W Z hW hZ <
      phi (min (binaryContraction μ W Z hW hZ) (binaryContraction μ Z W hZ hW)) := by
  unfold binaryMutualInfo binaryContraction at *
  rw [binaryLaw_swap] at hne ⊢
  exact BinaryLaw.bidirectional_strict _ hne

end RandomVariableDirections

end BinaryPairBound
