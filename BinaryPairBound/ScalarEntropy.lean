module

public import BinaryPairBound.Entropy
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

noncomputable section

@[expose] public section

namespace BinaryPairBound

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

end BinaryPairBound
