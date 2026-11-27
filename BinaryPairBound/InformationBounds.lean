module

public import BinaryPairBound.BinaryInformation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Mutual information, relabeling, and endpoint equality

证明互信息和phi的基本性质，处理0/1端点与二元符号重标记。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Mutual information and its endpoint values

证明二元互信息介于 0 和 log 2 之间，并说明什么时候取到这两个端点。
-/

public section Information

@[simp] theorem J_zero_input (c d : ℝ) : J 0 c d = 0 := by
  simp [J, q, k]

@[simp] theorem J_one_input (c d : ℝ) : J 1 c d = 0 := by
  have hq : q c d 1 = 1 - d := by unfold q k; ring
  simp [J, hq, H]

theorem J_nonneg {s c d : ℝ} (hv : Valid s c d) : 0 ≤ J s c d := by
  rcases hv with ⟨hs, hc, hd⟩
  have h1d : 1 - d ∈ Set.Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hd.2, by linarith [hd.1]⟩
  have h := Real.strictConcave_binEntropy.concaveOn.2 hc h1d
    (sub_nonneg.mpr hs.2) hs.1 (show (1 - s) + s = 1 by ring)
  have hq : (1 - s) * c + s * (1 - d) = q c d s := by unfold q k; ring
  simp only [smul_eq_mul, Real.binEntropy_one_sub, hq] at h
  unfold J
  linarith

theorem J_le_log_two {s c d : ℝ} (hv : Valid s c d) : J s c d ≤ Real.log 2 := by
  have hc := mul_nonneg (sub_nonneg.mpr hv.1.2) (Real.binEntropy_nonneg hv.2.1.1 hv.2.1.2)
  have hd := mul_nonneg hv.1.1 (Real.binEntropy_nonneg hv.2.2.1 hv.2.2.2)
  have hq := Real.binEntropy_le_log_two (p := q c d s)
  unfold J
  linarith

/-- A deterministic input or constant-output channel has zero information. -/
theorem J_eq_zero_of_independent {s c d : ℝ} (hi : Independent s c d) : J s c d = 0 := by
  rcases hi with hs | hs | hcd
  · subst s; exact J_zero_input c d
  · subst s; exact J_one_input c d
  · have hk : k c d = 0 := by unfold k; linarith
    have hd : d = 1 - c := by linarith
    unfold J
    simp only [q, hk, zero_mul, add_zero]
    simp only [hd, H, Real.binEntropy_one_sub]
    ring

theorem J_pos_of_not_independent {s c d : ℝ} (hv : Valid s c d)
    (hi : ¬Independent s c d) : 0 < J s c d := by
  have hs0 : s ≠ 0 := fun h => hi (Or.inl h)
  have hs1 : s ≠ 1 := fun h => hi (Or.inr (Or.inl h))
  have hspos : 0 < s := lt_of_le_of_ne hv.1.1 (Ne.symm hs0)
  have hslt : s < 1 := lt_of_le_of_ne hv.1.2 hs1
  have h1d : 1 - d ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr hv.2.2.2, by linarith [hv.2.2.1]⟩
  have hcd : c ≠ 1 - d := by
    intro h
    exact hi (Or.inr (Or.inr (by linarith)))
  have h := Real.strictConcave_binEntropy.2 hv.2.1 h1d hcd
    (sub_pos.mpr hslt) hspos (show (1 - s) + s = 1 by ring)
  have hq : (1 - s) * c + s * (1 - d) = q c d s := by unfold q k; ring
  simp only [smul_eq_mul, Real.binEntropy_one_sub, hq] at h
  unfold J
  linarith

theorem J_eq_zero_iff_independent {s c d : ℝ} (hv : Valid s c d) :
    J s c d = 0 ↔ Independent s c d := by
  constructor
  · intro h
    by_contra hi
    exact (ne_of_gt (J_pos_of_not_independent hv hi)) h
  · exact J_eq_zero_of_independent

/-- A dependent binary pair cannot have a deterministic marginal. -/
theorem nondegenerate_of_not_independent {s c d : ℝ} (hv : Valid s c d)
    (hi : ¬Independent s c d) : Nondegenerate s c d := by
  have hs0 : s ≠ 0 := fun h => hi (Or.inl h)
  have hs1 : s ≠ 1 := fun h => hi (Or.inr (Or.inl h))
  have hspos : 0 < s := lt_of_le_of_ne hv.1.1 (Ne.symm hs0)
  have hslt : s < 1 := lt_of_le_of_ne hv.1.2 hs1
  have hq := q_mem_Icc c d s hv.2.1 hv.2.2 hv.1
  have hA := mul_nonneg (sub_nonneg.mpr hv.1.2) hv.2.1.1
  have hB := mul_nonneg hv.1.1 (sub_nonneg.mpr hv.2.2.2)
  have hC := mul_nonneg (sub_nonneg.mpr hv.1.2) (sub_nonneg.mpr hv.2.1.2)
  have hE := mul_nonneg hv.1.1 hv.2.2.1
  have hq0 : q c d s ≠ 0 := by
    intro hz
    have hsum : (1 - s) * c + s * (1 - d) = 0 := by
      unfold q k at hz
      nlinarith
    have hc : c = 0 := by nlinarith
    have hd : d = 1 := by nlinarith
    exact hi (Or.inr (Or.inr (by linarith)))
  have hq1 : q c d s ≠ 1 := by
    intro hz
    have hsum : (1 - s) * (1 - c) + s * d = 0 := by
      unfold q k at hz
      nlinarith
    have hc : c = 1 := by nlinarith
    have hd : d = 0 := by nlinarith
    exact hi (Or.inr (Or.inr (by linarith)))
  exact ⟨⟨hspos, hslt⟩,
    ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), lt_of_le_of_ne hq.2 hq1⟩⟩

/-- Maximum binary information is attained exactly by a uniform, noiseless or
complementing channel. This is the equality condition used at cap 1 in Section 8. -/
theorem J_eq_log_two_iff {s c d : ℝ} (hv : Valid s c d) :
    J s c d = Real.log 2 ↔ s = 1 / 2 ∧ c = d ∧ (c = 0 ∨ c = 1) := by
  constructor
  · intro hJ
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hs0 : s ≠ 0 := by
      intro h; subst s; rw [J_zero_input] at hJ; linarith
    have hs1 : s ≠ 1 := by
      intro h; subst s; rw [J_one_input] at hJ; linarith
    have hspos : 0 < s := lt_of_le_of_ne hv.1.1 (Ne.symm hs0)
    have hslt : s < 1 := lt_of_le_of_ne hv.1.2 hs1
    have hc0 := Real.binEntropy_nonneg hv.2.1.1 hv.2.1.2
    have hd0 := Real.binEntropy_nonneg hv.2.2.1 hv.2.2.2
    have hc := mul_nonneg (sub_nonneg.mpr hv.1.2) hc0
    have hd := mul_nonneg hv.1.1 hd0
    have hq := Real.binEntropy_le_log_two (p := q c d s)
    have heq : H (q c d s) = Real.log 2 := by unfold J at hJ; linarith
    have hcz : H c = 0 := by unfold J at hJ; nlinarith
    have hdz : H d = 0 := by unfold J at hJ; nlinarith
    have hqhalf : q c d s = (2 : ℝ)⁻¹ := Real.binEntropy_eq_log_two.mp heq
    rcases Real.binEntropy_eq_zero.mp hcz with hcz | hcz <;>
      rcases Real.binEntropy_eq_zero.mp hdz with hdz | hdz
    all_goals simp only [hcz, hdz, q, k] at hqhalf ⊢
    all_goals norm_num at hqhalf
    all_goals norm_num
    all_goals linarith
  · rintro ⟨rfl, hcd, hc | hc⟩
    all_goals subst c; subst d; norm_num [J, q, k, H]
    all_goals exact Real.binEntropy_eq_log_two.mpr (by norm_num)

end Information

/-! ## Changing binary labels

证明交换二元符号的 0、1 标签不会改变需要比较的互信息与系数。
-/

public section Symmetry

theorem D_one_sub (x y : ℝ) : D (1 - x) (1 - y) = D x y := by
  simp only [D, H, Real.binEntropy_one_sub, sub_sub_cancel]
  ring

lemma q_output_flip (c d x : ℝ) : q (1 - c) (1 - d) x = 1 - q c d x := by
  unfold q k
  ring

lemma k_output_flip (c d : ℝ) : k (1 - c) (1 - d) = -k c d := by
  unfold k
  ring

lemma q_swap_one_sub (c d x : ℝ) : q d c (1 - x) = 1 - q c d x := by
  unfold q k
  ring

lemma q_swap (c d x : ℝ) : q d c x = 1 - q c d (1 - x) := by
  unfold q k
  ring

lemma k_swap (c d : ℝ) : k d c = k c d := by
  unfold k
  ring

theorem J_output_flip (s c d : ℝ) : J s (1 - c) (1 - d) = J s c d := by
  simp only [J, q_output_flip, H, Real.binEntropy_one_sub]

theorem J_simultaneous_flip (s c d : ℝ) : J (1 - s) d c = J s c d := by
  simp only [J, q_swap_one_sub, H, Real.binEntropy_one_sub, sub_sub_cancel]
  ring

lemma nondegenerate_output_flip (s c d : ℝ) :
    Nondegenerate s (1 - c) (1 - d) ↔ Nondegenerate s c d := by
  unfold Nondegenerate
  rw [q_output_flip]
  constructor <;> rintro ⟨hs, hq⟩ <;> refine ⟨hs, ?_⟩ <;>
    constructor <;> linarith [hq.1, hq.2]

lemma nondegenerate_simultaneous_flip (s c d : ℝ) :
    Nondegenerate (1 - s) d c ↔ Nondegenerate s c d := by
  unfold Nondegenerate
  rw [q_swap_one_sub]
  constructor <;> rintro ⟨hs, hq⟩ <;> constructor <;> constructor <;>
    linarith [hs.1, hs.2, hq.1, hq.2]

lemma klRatios_output_flip (s c d : ℝ) :
    klRatios s (1 - c) (1 - d) = klRatios s c d := by
  ext r
  simp only [klRatios, Set.mem_ofPred_eq, q_output_flip, D_one_sub]

theorem S_output_flip (s c d : ℝ) : S s (1 - c) (1 - d) = S s c d := by
  by_cases hn : Nondegenerate s c d
  · have hn' := (nondegenerate_output_flip s c d).mpr hn
    simp only [S, ite_eq_left hn, ite_eq_left hn', klRatios_output_flip]
  · have hn' : ¬Nondegenerate s (1 - c) (1 - d) :=
      fun h => hn ((nondegenerate_output_flip s c d).mp h)
    simp only [S, ite_eq_right hn, ite_eq_right hn']

private lemma ratio_simultaneous_flip (s c d x : ℝ) :
    D (q d c x) (q d c (1 - s)) / D x (1 - s) =
      D (q c d (1 - x)) (q c d s) / D (1 - x) s := by
  rw [q_swap_one_sub, q_swap, D_one_sub]
  have hD := D_one_sub (1 - x) s
  simp only [sub_sub_cancel] at hD
  rw [hD]

private lemma klRatios_simultaneous_flip_subset (s c d : ℝ) :
    klRatios (1 - s) d c ⊆ klRatios s c d := by
  rintro r ⟨x, hx, hxs, rfl⟩
  refine ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_, ?_⟩
  · intro h
    apply hxs
    linarith
  · exact ratio_simultaneous_flip s c d x

lemma klRatios_simultaneous_flip (s c d : ℝ) :
    klRatios (1 - s) d c = klRatios s c d := by
  apply Set.Subset.antisymm
  · exact klRatios_simultaneous_flip_subset s c d
  · simpa only [sub_sub_cancel] using klRatios_simultaneous_flip_subset (1 - s) d c

theorem S_simultaneous_flip (s c d : ℝ) : S (1 - s) d c = S s c d := by
  by_cases hn : Nondegenerate s c d
  · have hn' := (nondegenerate_simultaneous_flip s c d).mpr hn
    simp only [S, ite_eq_left hn, ite_eq_left hn', klRatios_simultaneous_flip]
  · have hn' : ¬Nondegenerate (1 - s) d c :=
      fun h => hn ((nondegenerate_simultaneous_flip s c d).mp h)
    simp only [S, ite_eq_right hn, ite_eq_right hn']

lemma valid_output_flip {s c d : ℝ} (hv : Valid s c d) :
    Valid s (1 - c) (1 - d) := by
  refine ⟨hv.1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [hv.2.1.1, hv.2.1.2, hv.2.2.1, hv.2.2.2]

lemma valid_simultaneous_flip {s c d : ℝ} (hv : Valid s c d) :
    Valid (1 - s) d c := by
  exact ⟨⟨by linarith [hv.1.2], by linarith [hv.1.1]⟩, hv.2.2, hv.2.1⟩

end Symmetry

/-! ## The sharp bound function and scalar entropy inequalities

证明上界函数 phi 的单调性及后面所需的熵不等式。
-/

@[expose] public noncomputable section ScalarEntropy

@[simp] theorem phi_zero : phi 0 = 0 := by
  simp [phi, H, Real.binEntropy_two_inv]

@[simp] theorem phi_one : phi 1 = Real.log 2 := by
  simp [phi, H]

theorem continuous_phi : Continuous phi := by
  unfold phi
  exact continuous_const.sub (Real.binEntropy_continuous.comp
    ((continuous_const.sub Real.continuous_sqrt).div_const 2))

theorem phi_nonneg (r : ℝ) : 0 ≤ phi r := by
  unfold phi
  exact sub_nonneg.mpr Real.binEntropy_le_log_two

theorem phi_le_log_two {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : phi r ≤ Real.log 2 := by
  have hs := Real.sqrt_nonneg r
  have hs1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr.2
  have hH := Real.binEntropy_nonneg (p := (1 - Real.sqrt r) / 2) (by linarith) (by linarith)
  dsimp [phi]
  linarith

theorem phi_strictMonoOn : StrictMonoOn phi (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hab' := Real.sqrt_lt_sqrt ha.1 hab
  have ha0 := Real.sqrt_nonneg a
  have hb0 := Real.sqrt_nonneg b
  have ha1 : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha.2
  have hb1 : Real.sqrt b ≤ 1 := Real.sqrt_le_one.mpr hb.2
  have hH := Real.binEntropy_strictMonoOn
    (show (1 - Real.sqrt b) / 2 ∈ Set.Icc (0 : ℝ) 2⁻¹ by constructor <;> linarith)
    (show (1 - Real.sqrt a) / 2 ∈ Set.Icc (0 : ℝ) 2⁻¹ by constructor <;> linarith)
    (show (1 - Real.sqrt b) / 2 < (1 - Real.sqrt a) / 2 by linarith)
  dsimp [phi]
  linarith

theorem phi_pos {r : ℝ} (hr : r ∈ Set.Ioc (0 : ℝ) 1) : 0 < phi r := by
  have h := phi_strictMonoOn (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    ⟨hr.1.le, hr.2⟩ hr.1
  simpa using h

/-- Twice the inverse hyperbolic tangent, expressed directly using logarithms. -/
def entropyLogRatio (x : ℝ) : ℝ := Real.log (1 + x) - Real.log (1 - x)

lemma hasDerivAt_entropyLogRatio {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt entropyLogRatio (2 / (1 - x ^ 2)) x := by
  have ha : 1 + x ≠ 0 := by linarith [hx.1]
  have hb : 1 - x ≠ 0 := by linarith [hx.2]
  have hc : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have h := (((hasDerivAt_id x).const_add 1).log ha).sub
    (((hasDerivAt_id x).const_sub 1).log hb)
  convert! h using 1
  simp only [id_eq]
  field_simp [ha, hb, hc]
  ring

lemma hasDerivAt_entropyLogExcess {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => entropyLogRatio t - 2 * t) (2 * x ^ 2 / (1 - x ^ 2)) x := by
  have hc : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  convert! (hasDerivAt_entropyLogRatio hx).sub ((hasDerivAt_id x).const_mul 2) using 1
  field_simp [hc]
  ring

lemma entropyLogRatio_gt_two_mul {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    2 * x < entropyLogRatio x := by
  have hm : StrictMonoOn (fun t => entropyLogRatio t - 2 * t) (Set.Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · intro t ht
      exact (hasDerivAt_entropyLogExcess (show t ∈ Set.Ioo (-1 : ℝ) 1 by
        constructor <;> linarith [ht.1, ht.2, hx.2])).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo 0 x := by simpa only [interior_Icc] using ht
      have ht1 : t ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> linarith [ht'.1, ht'.2, hx.2]
      rw [(hasDerivAt_entropyLogExcess ht1).deriv]
      apply div_pos
      · exact mul_pos (by norm_num) (sq_pos_of_pos ht'.1)
      · nlinarith [ht'.1, ht'.2, hx.2]
  have hh := hm (show (0 : ℝ) ∈ Set.Icc 0 x by exact ⟨le_rfl, hx.1.le⟩)
    (show x ∈ Set.Icc 0 x by exact ⟨hx.1.le, le_rfl⟩) hx.1
  have hz : entropyLogRatio 0 = 0 := by simp [entropyLogRatio]
  dsimp only at hh
  rw [hz] at hh
  linarith

/-- The weighted derivative of `phi`, expressed in the square-root variable. -/
def weightedPhiSlope (x : ℝ) : ℝ := (1 - x ^ 2) * entropyLogRatio x / (4 * x)

lemma hasDerivAt_weightedPhiSlope {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt weightedPhiSlope
      ((2 * x - (1 + x ^ 2) * entropyLogRatio x) / (4 * x ^ 2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hx2 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hL := hasDerivAt_entropyLogRatio (show x ∈ Set.Ioo (-1 : ℝ) 1 by
    exact ⟨by linarith [hx.1], hx.2⟩)
  have h := ((((hasDerivAt_id x).pow 2).const_sub 1).mul hL).div
    ((hasDerivAt_id x).const_mul 4) (by simpa using hx0)
  convert! h using 1
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply]
  field_simp [hx0, hx2]
  ring

lemma weightedPhiSlope_strictAntiOn : StrictAntiOn weightedPhiSlope (Set.Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro x hx
    exact (hasDerivAt_weightedPhiSlope hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hx
    rw [(hasDerivAt_weightedPhiSlope hx').deriv]
    apply div_neg_of_neg_of_pos
    · have hL := entropyLogRatio_gt_two_mul hx'
      have hL0 : 0 < entropyLogRatio x := by linarith [hx'.1]
      nlinarith [sq_nonneg x]
    · exact mul_pos (by norm_num) (sq_pos_of_pos hx'.1)

lemma sqrt_mem_Ioo {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    Real.sqrt r ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨Real.sqrt_pos_of_pos hr.1, ?_⟩
  simpa using Real.sqrt_lt_sqrt hr.1.le hr.2

lemma hasDerivAt_phi {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt phi (entropyLogRatio (Real.sqrt r) / (4 * Real.sqrt r)) r := by
  have hs := sqrt_mem_Ioo hr
  have hp0 : (1 - Real.sqrt r) / 2 ≠ 0 := by linarith [hs.2]
  have hp1 : (1 - Real.sqrt r) / 2 ≠ 1 := by linarith [hs.1]
  have hinner := ((Real.hasDerivAt_sqrt (ne_of_gt hr.1)).const_sub 1).div_const 2
  have hH := (Real.hasDerivAt_binEntropy hp0 hp1).comp r hinner
  have heq : Real.log (1 - (1 - Real.sqrt r) / 2) - Real.log ((1 - Real.sqrt r) / 2) =
      entropyLogRatio (Real.sqrt r) := by
    rw [show 1 - (1 - Real.sqrt r) / 2 = (1 + Real.sqrt r) / 2 by ring]
    rw [Real.log_div (by linarith [hs.1]) (by norm_num),
      Real.log_div (by linarith [hs.2]) (by norm_num)]
    unfold entropyLogRatio
    ring
  convert! hH.const_sub (Real.log 2) using 1
  rw [heq]
  ring

lemma weightedPhiSlope_sqrt {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    weightedPhiSlope (Real.sqrt r) = (1 - r) * deriv phi r := by
  rw [(hasDerivAt_phi hr).deriv]
  unfold weightedPhiSlope
  rw [Real.sq_sqrt hr.1.le]
  ring

lemma phi_increment_deriv_neg {eta r : ℝ} (he : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z => phi (eta + (1 - eta) * z) - phi z) r < 0 := by
  let t := eta + (1 - eta) * r
  have het : 0 < 1 - eta := sub_pos.mpr he.2
  have hrt : r < t := by dsimp [t]; nlinarith [mul_pos he.1 (sub_pos.mpr hr.2)]
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [t]
    constructor
    · nlinarith [mul_pos het hr.1]
    · nlinarith [mul_pos het (sub_pos.mpr hr.2)]
  have hG := ((hasDerivAt_phi ht).comp r
    (((hasDerivAt_id r).const_mul (1 - eta)).const_add eta)).sub (hasDerivAt_phi hr)
  have hG' : HasDerivAt (fun z => phi (eta + (1 - eta) * z) - phi z)
      ((1 - eta) * deriv phi t - deriv phi r) r := by
    rw [(hasDerivAt_phi ht).deriv, (hasDerivAt_phi hr).deriv]
    convert! hG using 1
    ring
  rw [hG'.deriv]
  have hw := weightedPhiSlope_strictAntiOn (sqrt_mem_Ioo hr) (sqrt_mem_Ioo ht)
    (Real.sqrt_lt_sqrt hr.1.le hrt)
  rw [weightedPhiSlope_sqrt ht, weightedPhiSlope_sqrt hr] at hw
  have hid : 1 - t = (1 - eta) * (1 - r) := by dsimp [t]; ring
  rw [hid] at hw
  have hprod : (1 - r) * ((1 - eta) * deriv phi t - deriv phi r) < 0 := by nlinarith
  exact neg_of_mul_neg_right hprod (sub_nonneg.mpr hr.2.le)

/-- The scalar increment in Appendix E is strictly decreasing on the full closed interval. -/
theorem phi_increment_strictAntiOn {eta : ℝ} (he : eta ∈ Set.Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun r => phi (eta + (1 - eta) * r) - phi r) (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · exact ((continuous_phi.comp
      (continuous_const.add (continuous_const.mul continuous_id))).sub continuous_phi).continuousOn
  · intro r hr
    exact phi_increment_deriv_neg he (by simpa only [interior_Icc] using hr)

/-- The second scalar inequality in Lemma 7.1, including both endpoints in `r`. -/
theorem phi_increment_le {eta r : ℝ} (he : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    phi (eta + (1 - eta) * r) - phi r ≤ phi eta := by
  have hh := (phi_increment_strictAntiOn he).antitoneOn
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) hr hr.1
  simpa using hh

/-- Equality in the second scalar inequality of Lemma 7.1 holds exactly at `r=0`. -/
theorem phi_increment_eq_iff {eta r : ℝ} (he : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    phi (eta + (1 - eta) * r) - phi r = phi eta ↔ r = 0 := by
  constructor
  · intro h
    by_contra hne
    have hr0 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hne)
    have hh := phi_increment_strictAntiOn he
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) hr hr0
    simp only [mul_zero, add_zero, phi_zero, sub_zero] at hh
    linarith
  · rintro rfl
    simp

/-- The posterior-entropy curve `B` in Lemma 7.1. -/
def posteriorEntropyCurve (x : ℝ) : ℝ := H ((1 - Real.sqrt (1 - x ^ 2)) / 2)

lemma continuous_posteriorEntropyCurve : Continuous posteriorEntropyCurve := by
  unfold posteriorEntropyCurve
  exact Real.binEntropy_continuous.comp
    ((continuous_const.sub (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2)))).div_const 2)

lemma one_sub_sq_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    1 - x ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> nlinarith [hx.1, hx.2, sq_pos_of_pos hx.1]

/-- An explicit first derivative of the posterior-entropy curve on `(0,1)`. -/
def posteriorEntropySlope (x : ℝ) : ℝ :=
  x * entropyLogRatio (Real.sqrt (1 - x ^ 2)) / (2 * Real.sqrt (1 - x ^ 2))

lemma hasDerivAt_posteriorEntropyCurve {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt posteriorEntropyCurve (posteriorEntropySlope x) x := by
  have ht := one_sub_sq_mem_Ioo hx
  have h := ((hasDerivAt_phi ht).comp x
    (((hasDerivAt_id x).pow 2).const_sub 1)).const_sub (Real.log 2)
  convert! h using 1
  · ext z
    dsimp [posteriorEntropyCurve, phi]
    ring
  · dsimp [posteriorEntropySlope]
    ring

lemma hasDerivAt_posteriorEntropySlope {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt posteriorEntropySlope
      ((entropyLogRatio (Real.sqrt (1 - x ^ 2)) - 2 * Real.sqrt (1 - x ^ 2)) /
        (2 * (Real.sqrt (1 - x ^ 2)) ^ 3)) x := by
  let r := Real.sqrt (1 - x ^ 2)
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := sqrt_mem_Ioo (one_sub_sq_mem_Ioo hx)
  have hr0 : r ≠ 0 := ne_of_gt hr.1
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hrsq : r ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (one_sub_sq_mem_Ioo hx).1.le
  have hr2 : 1 - r ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hx.1]
  have hR : HasDerivAt (fun z => Real.sqrt (1 - z ^ 2)) (-x / r) x := by
    convert! (Real.hasDerivAt_sqrt (ne_of_gt (one_sub_sq_mem_Ioo hx).1)).comp x
      (((hasDerivAt_id x).pow 2).const_sub 1) using 1
    simp only [id_eq]
    dsimp [r]
    ring
  have hL := (hasDerivAt_entropyLogRatio
    (show r ∈ Set.Ioo (-1 : ℝ) 1 by exact ⟨by linarith [hr.1], hr.2⟩)).comp x hR
  have h := ((hasDerivAt_id x).mul hL).div (hR.const_mul 2) (by exact mul_ne_zero (by norm_num) hr0)
  change HasDerivAt posteriorEntropySlope ((entropyLogRatio r - 2 * r) / (2 * r ^ 3)) x
  convert! h using 1
  simp only [id_eq, Function.comp_apply, Pi.mul_apply]
  change (entropyLogRatio r - 2 * r) / (2 * r ^ 3) =
    ((1 * entropyLogRatio r + x * (2 / (1 - r ^ 2) * (-x / r))) * (2 * r) -
      (x * entropyLogRatio r) * (2 * (-x / r))) / (2 * r) ^ 2
  field_simp [hr0, hr2]
  rw [show x ^ 2 = 1 - r ^ 2 by linarith [hrsq]]
  ring

/-- The first assertion of Lemma 7.1: convexity of the posterior-entropy curve. -/
theorem convexOn_posteriorEntropyCurve :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) posteriorEntropyCurve := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    continuous_posteriorEntropyCurve.continuousOn
    (f' := posteriorEntropySlope)
    (f'' := fun x => (entropyLogRatio (Real.sqrt (1 - x ^ 2)) - 2 * Real.sqrt (1 - x ^ 2)) /
      (2 * (Real.sqrt (1 - x ^ 2)) ^ 3))
  · intro x hx
    exact (hasDerivAt_posteriorEntropyCurve (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_posteriorEntropySlope (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    have hr := sqrt_mem_Ioo (one_sub_sq_mem_Ioo hx')
    exact div_nonneg (sub_nonneg.mpr (entropyLogRatio_gt_two_mul hr).le)
      (mul_nonneg (by norm_num) (pow_nonneg hr.1.le 3))

/-- The reparametrization used for posterior probabilities in Proposition 7.2. -/
theorem posteriorEntropyCurve_two_sqrt {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    posteriorEntropyCurve (2 * Real.sqrt (p * (1 - p))) = H p := by
  have hprod := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hs : (2 * Real.sqrt (p * (1 - p))) ^ 2 = 4 * p * (1 - p) := by
    nlinarith [Real.sq_sqrt hprod]
  unfold posteriorEntropyCurve
  rw [hs, show 1 - 4 * p * (1 - p) = (1 - 2 * p) ^ 2 by ring, Real.sqrt_sq_eq_abs]
  by_cases hh : p ≤ 1 / 2
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * p)]
    congr 1
    ring
  · rw [abs_of_nonpos (by linarith : 1 - 2 * p ≤ 0)]
    rw [show (1 - -(1 - 2 * p)) / 2 = 1 - p by ring]
    exact Real.binEntropy_one_sub p

/-- Two-point Jensen in the precise scalar form used for binary posteriors. -/
theorem posteriorEntropyCurve_jensen {a b w : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    posteriorEntropyCurve ((1 - w) * a + w * b) ≤
      (1 - w) * posteriorEntropyCurve a + w * posteriorEntropyCurve b := by
  exact convexOn_posteriorEntropyCurve.2 ha hb (sub_nonneg.mpr hw.2) hw.1 (by ring)

end ScalarEntropy

/-! ## Complete equality classification at coefficients zero and one

单独完成 S=0 和 S=1 时的主定理及取等条件。
-/

public section Endpoints

theorem S_eq_zero_iff_independent {s c d : ℝ} (hv : Valid s c d) :
    S s c d = 0 ↔ Independent s c d := by
  constructor
  · intro hS
    by_contra hi
    have hn := nondegenerate_of_not_independent hv hi
    have hcap := klCap_S hv hn 0 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    have hq0 : q c d 0 = c := by simp [q]
    rw [hS, zero_mul, hq0] at hcap
    have hD : D c (q c d s) = 0 := le_antisymm hcap (D_nonneg hv.2.1 hn.2)
    have heq := (D_eq_zero_iff hv.2.1 hn.2).mp hD
    have hmul : k c d * s = 0 := by unfold q at heq; linarith
    have hk : k c d = 0 := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hn.1.1)
    exact hi (Or.inr (Or.inr (by unfold k at hk; linarith)))
  · exact S_eq_zero_of_independent

theorem S_pos_iff_not_independent {s c d : ℝ} (hv : Valid s c d) :
    0 < S s c d ↔ ¬Independent s c d := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hn⟩ hi
    exact hn (S_eq_zero_of_independent hi).symm
  · intro hi
    exact ⟨S_nonneg hv, fun h => hi ((S_eq_zero_iff_independent hv).mp h.symm)⟩

theorem sharp_equality_of_independent {s c d : ℝ} (hi : Independent s c d) :
    J s c d = phi (S s c d) := by
  rw [J_eq_zero_of_independent hi, S_eq_zero_of_independent hi, phi_zero]

/-- Theorem 2.1, including equality, at contraction coefficient zero. -/
theorem sharp_equality_of_S_zero {s c d : ℝ} (hv : Valid s c d) (hS : S s c d = 0) :
    J s c d = phi (S s c d) ∧ Independent s c d := by
  have hi := (S_eq_zero_iff_independent hv).mp hS
  exact ⟨sharp_equality_of_independent hi, hi⟩

/-- Theorem 2.1 at contraction coefficient one. -/
theorem sharp_bound_of_S_one {s c d : ℝ} (hv : Valid s c d) (hS : S s c d = 1) :
    J s c d ≤ phi (S s c d) := by
  rw [hS, phi_one]
  exact J_le_log_two hv

/-- At coefficient one, equality forces the uniform noiseless/complementing source. -/
theorem sharp_equality_iff_of_S_one {s c d : ℝ} (hv : Valid s c d) (hS : S s c d = 1) :
    J s c d = phi (S s c d) ↔ s = 1 / 2 ∧ c = d ∧ (c = 0 ∨ c = 1) := by
  rw [hS, phi_one]
  exact J_eq_log_two_iff hv

theorem S_noiseless {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) : S s 0 0 = 1 := by
  have hv : Valid s 0 0 := ⟨⟨hs.1.le, hs.2.le⟩, by simp, by simp⟩
  have hn : Nondegenerate s 0 0 := by simpa [Nondegenerate, q, k] using And.intro hs hs
  have hD : D 0 s ≠ 0 := ne_of_gt (D_pos (by simp) hs (ne_of_lt hs.1))
  apply le_antisymm (S_le_one hv)
  have h := ratio_le_S hv hn (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (ne_of_lt hs.1)
  simpa [q, k, hD] using h

theorem J_symmetric (c : ℝ) : J (1 / 2) c c = Real.log 2 - H c := by
  have hq : q c c (1 / 2) = 1 / 2 := by unfold q k; ring
  have hH : H (1 / 2) = Real.log 2 := Real.binEntropy_eq_log_two.mpr (by norm_num)
  rw [J, hq, hH]
  ring

end Endpoints

end BinaryPairBound
