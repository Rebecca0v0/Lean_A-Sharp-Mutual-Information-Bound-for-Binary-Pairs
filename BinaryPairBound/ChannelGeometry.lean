module

public import BinaryPairBound.BinaryInformation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Curvature, channel bounds, and contact geometry

从熵曲线的导数得到曲率形状，证明局部比值、信道上界eta及接触点的几何限制。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## The curvature formula and distinguished input

计算熵曲线的二阶导数，并定义局部比值、信道上界 eta 和特殊输入位置。
-/

@[expose] public noncomputable section Curvature

/-- The rational local contraction expression in equation (4.2). -/
def rhoSquared (c d x : ℝ) : ℝ :=
  (k c d)^2 * x * (1 - x) / (q c d x * (1 - q c d x))

/-- The channel-wide expression in equation (4.4). -/
def eta (c d : ℝ) : ℝ :=
  (Real.sqrt ((1 - c) * (1 - d)) - Real.sqrt (c * d))^2

/-- The distinguished input in equation (4.3). -/
def distinguishedInput (c d : ℝ) : ℝ :=
  Real.sqrt (c * (1 - c)) /
    (Real.sqrt (c * (1 - c)) + Real.sqrt (d * (1 - d)))

theorem eta_nonneg (c d : ℝ) : 0 ≤ eta c d := sq_nonneg _

theorem eta_le_one {c d : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) : eta c d ≤ 1 := by
  have ha := Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hd.2))
  have hb := Real.sq_sqrt (mul_nonneg hc.1 hd.1)
  have hab := mul_nonneg (Real.sqrt_nonneg ((1 - c) * (1 - d))) (Real.sqrt_nonneg (c * d))
  have hcd := mul_nonneg hc.1 (sub_nonneg.mpr hd.2)
  have hdc := mul_nonneg hd.1 (sub_nonneg.mpr hc.2)
  unfold eta
  nlinarith

theorem eta_lt_one {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) : eta c d < 1 := by
  have ha := Real.sq_sqrt (mul_pos (sub_pos.mpr hc.2) (sub_pos.mpr hd.2)).le
  have hb := Real.sq_sqrt (mul_pos hc.1 hd.1).le
  have hab := mul_nonneg (Real.sqrt_nonneg ((1 - c) * (1 - d))) (Real.sqrt_nonneg (c * d))
  have hcd := mul_pos hc.1 (sub_pos.mpr hd.2)
  have hdc := mul_pos hd.1 (sub_pos.mpr hc.2)
  unfold eta
  nlinarith

theorem eta_pos {c d : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hcd : c + d ≠ 1) : 0 < eta c d := by
  apply sq_pos_of_ne_zero
  intro h
  have ha := Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hd.2))
  have hb := Real.sq_sqrt (mul_nonneg hc.1 hd.1)
  have hr : Real.sqrt ((1 - c) * (1 - d)) = Real.sqrt (c * d) := sub_eq_zero.mp h
  rw [hr] at ha
  apply hcd
  nlinarith

theorem distinguishedInput_mem_Ioo {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) : distinguishedInput c d ∈ Set.Ioo (0 : ℝ) 1 := by
  have ha := Real.sqrt_pos.2 (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hb := Real.sqrt_pos.2 (mul_pos hd.1 (sub_pos.mpr hd.2))
  have hab := add_pos ha hb
  constructor
  · exact div_pos ha hab
  · exact (div_lt_one hab).2 (lt_add_of_pos_right _ hb)

/-- Under the paper's positive-slope normalization, the distinguished input
is uniform precisely when the channel is symmetric. -/
theorem distinguishedInput_eq_half_iff {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d < 1) :
    distinguishedInput c d = 1 / 2 ↔ c = d := by
  have ha := Real.sqrt_pos.2 (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hb := Real.sqrt_pos.2 (mul_pos hd.1 (sub_pos.mpr hd.2))
  have ha2 := Real.sq_sqrt (mul_pos hc.1 (sub_pos.mpr hc.2)).le
  have hb2 := Real.sq_sqrt (mul_pos hd.1 (sub_pos.mpr hd.2)).le
  have hab : Real.sqrt (c * (1 - c)) + Real.sqrt (d * (1 - d)) ≠ 0 :=
    ne_of_gt (add_pos ha hb)
  rw [distinguishedInput, div_eq_iff hab]
  constructor
  · intro h
    have hsqrt : Real.sqrt (c * (1 - c)) = Real.sqrt (d * (1 - d)) := by linarith
    have hfactor : (c - d) * (1 - c - d) = 0 := by nlinarith
    have hk : 1 - c - d ≠ 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hk)
  · intro h
    subst d
    ring

lemma channel_variance_decomposition (c d x : ℝ) :
    q c d x * (1 - q c d x) - (k c d)^2 * x * (1 - x) =
      (1 - x) * c * (1 - c) + x * d * (1 - d) := by
  unfold q k
  ring

theorem rhoSquared_nonneg {c d x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) : 0 ≤ rhoSquared c d x := by
  unfold rhoSquared
  exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hx.1) (sub_nonneg.mpr hx.2))
    (mul_pos hqx.1 (sub_pos.mpr hqx.2)).le

theorem rhoSquared_le_one {c d x : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) : rhoSquared c d x ≤ 1 := by
  unfold rhoSquared
  apply (div_le_one (mul_pos hqx.1 (sub_pos.mpr hqx.2))).2
  have h0 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hx.2) hc.1) (sub_nonneg.mpr hc.2)
  have h1 := mul_nonneg (mul_nonneg hx.1 hd.1) (sub_nonneg.mpr hd.2)
  linarith [channel_variance_decomposition c d x]

theorem rhoSquared_mem_Icc {c d x : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) : rhoSquared c d x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨rhoSquared_nonneg hx hqx, rhoSquared_le_one hc hd hx hqx⟩

private lemma hasDerivAt_entropySlope {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => Real.log (1 - y) - Real.log y)
      (-1 / (x * (1 - x))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hx1 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have ha := ((hasDerivAt_id x).const_sub 1).log hx1
  have hb := (hasDerivAt_id x).log hx0
  convert! ha.sub hb using 1
  dsimp only [id]
  field_simp
  ring

/-- A derivative of the actual first derivative of the entropy curve. -/
theorem hasDerivAt_deriv_entropyCurve {lam c d x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (entropyCurve lam c d))
      ((lam - rhoSquared c d x) / (x * (1 - x))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hx1 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hq0 : q c d x ≠ 0 := ne_of_gt hqx.1
  have hq1 : 1 - q c d x ≠ 0 := ne_of_gt (sub_pos.mpr hqx.2)
  have hlocal : deriv (entropyCurve lam c d) =ᶠ[nhds x]
      (fun y => (Real.log (1 - q c d y) - Real.log (q c d y)) * k c d -
        lam * (Real.log (1 - y) - Real.log y)) := by
    have hi : ∀ᶠ y in nhds x, y ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hx.1 hx.2
    have ho : ∀ᶠ y in nhds x, q c d y ∈ Set.Ioo (0 : ℝ) 1 :=
      (hasDerivAt_q c d x).continuousAt (Ioo_mem_nhds hqx.1 hqx.2)
    filter_upwards [hi, ho] with y hy hqy
    exact deriv_entropyCurve lam y c d hy hqy
  have hq := ((hasDerivAt_entropySlope hqx).comp x (hasDerivAt_q c d x)).mul_const (k c d)
  have hs := (hasDerivAt_entropySlope hx).const_mul lam
  have ht := (hq.sub hs).congr_of_eventuallyEq hlocal
  convert! ht using 1
  unfold rhoSquared
  field_simp
  ring

/-- The curvature formula in Section 4.2, with the actual iterated derivative. -/
theorem deriv2_entropyCurve {lam c d x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv (entropyCurve lam c d)) x =
      (lam - rhoSquared c d x) / (x * (1 - x)) :=
  (hasDerivAt_deriv_entropyCurve hx hqx).deriv


lemma eta_mul_denominator {c d : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    eta c d * ((k c d)^2 +
      (Real.sqrt (c * (1 - c)) + Real.sqrt (d * (1 - d)))^2) = (k c d)^2 := by
  have ha := Real.sq_sqrt (mul_nonneg hc.1 (sub_nonneg.mpr hc.2))
  have hb := Real.sq_sqrt (mul_nonneg hd.1 (sub_nonneg.mpr hd.2))
  have hp := Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hd.2))
  have hr := Real.sq_sqrt (mul_nonneg hc.1 hd.1)
  have hab : Real.sqrt (c * (1 - c)) * Real.sqrt (d * (1 - d)) =
      Real.sqrt ((1 - c) * (1 - d)) * Real.sqrt (c * d) := by
    rw [← Real.sqrt_mul (mul_nonneg hc.1 (sub_nonneg.mpr hc.2)),
      ← Real.sqrt_mul (mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hd.2))]
    congr 1
    ring
  have hden : (k c d)^2 + (Real.sqrt (c * (1 - c)) + Real.sqrt (d * (1 - d)))^2 =
      (Real.sqrt ((1 - c) * (1 - d)) + Real.sqrt (c * d))^2 := by
    unfold k
    nlinarith
  have hk : Real.sqrt ((1 - c) * (1 - d))^2 - Real.sqrt (c * d)^2 = k c d := by
    unfold k
    nlinarith
  rw [hden]
  unfold eta
  calc
    _ = (Real.sqrt ((1 - c) * (1 - d))^2 - Real.sqrt (c * d)^2)^2 := by ring
    _ = (k c d)^2 := by rw [hk]

lemma variance_square_completion {c d : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    q c d x * (1 - q c d x) -
      ((k c d)^2 + (Real.sqrt (c * (1 - c)) + Real.sqrt (d * (1 - d)))^2) * x * (1 - x) =
      (Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x)^2 := by
  have ha := Real.sq_sqrt (mul_nonneg hc.1 (sub_nonneg.mpr hc.2))
  have hb := Real.sq_sqrt (mul_nonneg hd.1 (sub_nonneg.mpr hd.2))
  have hv := channel_variance_decomposition c d x
  linear_combination hv - (1 - x) * ha - x * hb

lemma eta_variance_gap {c d x : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    eta c d * (q c d x * (1 - q c d x)) - (k c d)^2 * x * (1 - x) =
      eta c d * (Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x)^2 := by
  have hv := variance_square_completion hc hd x
  have he := eta_mul_denominator hc hd
  linear_combination eta c d * hv + x * (1 - x) * he

lemma rhoSquared_le_eta {c d x : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) :
    rhoSquared c d x ≤ eta c d := by
  unfold rhoSquared
  apply (div_le_iff₀ (mul_pos hqx.1 (sub_pos.mpr hqx.2))).2
  have hgap := eta_variance_gap (x := x) hc hd
  have hn := mul_nonneg (eta_nonneg c d)
    (sq_nonneg (Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x))
  linarith

lemma q_mem_Ioo_of_channel {c d x : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    q c d x ∈ Set.Ioo (0 : ℝ) 1 := by
  by_cases hx0 : x = 0
  · subst x
    simpa [q] using hc
  · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have h0 := mul_nonneg (sub_nonneg.mpr hx.2) hc.1.le
    have h1 := mul_pos hxp (sub_pos.mpr hd.2)
    have h0' := mul_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hc.2).le
    have h1' := mul_pos hxp hd.1
    dsimp [q, k]
    constructor <;> nlinarith

lemma rhoSquared_eq_eta_iff {c d x : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) :
    rhoSquared c d x = eta c d ↔ x = distinguishedInput c d := by
  have hcc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  have hdc : d ∈ Set.Icc (0 : ℝ) 1 := ⟨hd.1.le, hd.2.le⟩
  have heta := eta_pos hcc hdc hcd
  have ha := Real.sqrt_pos.2 (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hb := Real.sqrt_pos.2 (mul_pos hd.1 (sub_pos.mpr hd.2))
  have hab : Real.sqrt (c * (1 - c)) + Real.sqrt (d * (1 - d)) ≠ 0 :=
    ne_of_gt (add_pos ha hb)
  have hgap := eta_variance_gap (x := x) hcc hdc
  rw [rhoSquared, div_eq_iff (ne_of_gt (mul_pos hqx.1 (sub_pos.mpr hqx.2)))]
  constructor
  · intro h
    have hp : eta c d * (Real.sqrt (c * (1 - c)) * (1 - x) -
        Real.sqrt (d * (1 - d)) * x)^2 = 0 := by linarith
    have hs : (Real.sqrt (c * (1 - c)) * (1 - x) -
        Real.sqrt (d * (1 - d)) * x)^2 = 0 :=
      (mul_eq_zero.mp hp).resolve_left (ne_of_gt heta)
    have hr := (sq_eq_zero_iff).mp hs
    rw [distinguishedInput, eq_div_iff hab]
    nlinarith
  · intro h
    have hr : Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x = 0 := by
      rw [h, distinguishedInput]
      field_simp
      ring
    rw [hr, zero_pow (by decide), mul_zero] at hgap
    linarith

lemma rhoSquared_distinguishedInput {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1) :
    rhoSquared c d (distinguishedInput c d) = eta c d := by
  have hs := distinguishedInput_mem_Ioo hc hd
  exact (rhoSquared_eq_eta_iff hc hd hcd
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)).2 rfl

end Curvature

/-! ## A uniform coefficient bound for a fixed channel

利用曲线的凸性，证明固定信道下所有输入的系数都不超过 eta。
-/

public section ChannelCap

lemma continuous_entropyCurve (lam c d : ℝ) : Continuous (entropyCurve lam c d) := by
  unfold entropyCurve q
  exact (Real.binEntropy_continuous.comp
    (continuous_const.add (continuous_const.mul continuous_id))).sub
    (continuous_const.mul Real.binEntropy_continuous)

/-- The channel-wide cap makes the entropy curve convex on the entire input interval. -/
theorem convexOn_entropyCurve_eta {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (entropyCurve (eta c d) c d) := by
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 1) (continuous_entropyCurve _ _ _).continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    exact (hasDerivAt_entropyCurve _ _ _ _ hx'
      (q_mem_Ioo_of_channel hc hd ⟨hx'.1.le, hx'.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    exact (hasDerivAt_deriv_entropyCurve hx'
      (q_mem_Ioo_of_channel hc hd ⟨hx'.1.le, hx'.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    have hqx := q_mem_Ioo_of_channel hc hd ⟨hx'.1.le, hx'.2.le⟩
    change 0 ≤ deriv (deriv (entropyCurve (eta c d) c d)) x
    rw [deriv2_entropyCurve hx' hqx]
    exact div_nonneg (sub_nonneg.mpr (rhoSquared_le_eta ⟨hc.1.le, hc.2.le⟩
      ⟨hd.1.le, hd.2.le⟩ hqx)) (mul_pos hx'.1 (sub_pos.mpr hx'.2)).le

lemma tangent_le_entropyCurve_eta {s c d x : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    tangent (eta c d) s c d x ≤ entropyCurve (eta c d) c d x := by
  have hcv := convexOn_entropyCurve_eta hc hd
  have hdiff := (hasDerivAt_entropyCurve (eta c d) s c d hs
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)).differentiableAt
  have hsc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  rcases lt_trichotomy x s with hxs | rfl | hsx
  · have hh := hcv.slope_le_deriv hx hsc hxs hdiff
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hxs)).mp hh
    unfold tangent
    nlinarith
  · simp [tangent]
  · have hh := hcv.deriv_le_slope hsc hx hsx hdiff
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hsx)).mp hh
    unfold tangent
    nlinarith

/-- Every distribution-dependent coefficient is bounded by the channel-wide expression.
This proves only the upper comparison; the reverse local comparison is separate. -/
theorem S_le_eta {s c d : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    S s c d ≤ eta c d := by
  by_cases hn : Nondegenerate s c d
  · apply S_le_of_klCap hn
    apply (klCap_iff_supporting_tangent hn).mpr
    intro x hx
    exact tangent_le_entropyCurve_eta hn.1 hc hd hx
  · rw [S_eq_zero_of_not_nondegenerate hn]
    exact eta_nonneg c d

private lemma deriv_eta_strictMonoOn_interval {c d a b : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hside : ∀ z ∈ Set.Ioo a b, z ≠ distinguishedInput c d) :
    StrictMonoOn (deriv (entropyCurve (eta c d) c d)) (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · intro z hz
    have hz' : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
    exact (hasDerivAt_deriv_entropyCurve hz'
      (q_mem_Ioo_of_channel hc hd ⟨hz'.1.le, hz'.2.le⟩)).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∈ Set.Ioo a b := by simpa only [interior_Icc] using hz
    have hz01 : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha.1.trans hz'.1, hz'.2.trans hb.2⟩
    have hqz := q_mem_Ioo_of_channel hc hd ⟨hz01.1.le, hz01.2.le⟩
    have hle := rhoSquared_le_eta ⟨hc.1.le, hc.2.le⟩ ⟨hd.1.le, hd.2.le⟩ hqz
    have hne : rhoSquared c d z ≠ eta c d :=
      fun heq => hside z hz' ((rhoSquared_eq_eta_iff hc hd hcd hqz).mp heq)
    rw [deriv2_entropyCurve hz01 hqz]
    exact div_pos (sub_pos.mpr (lt_of_le_of_ne hle hne))
      (mul_pos hz01.1 (sub_pos.mpr hz01.2))

lemma deriv_entropyCurve_eta_strictMonoOn {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1) :
    StrictMonoOn (deriv (entropyCurve (eta c d) c d)) (Set.Ioo (0 : ℝ) 1) := by
  have hmono : MonotoneOn (deriv (entropyCurve (eta c d) c d)) (Set.Ioo (0 : ℝ) 1) := by
    apply ((convexOn_entropyCurve_eta hc hd).subset Set.Ioo_subset_Icc_self (convex_Ioo 0 1)).monotoneOn_deriv
    intro z hz
    exact (hasDerivAt_entropyCurve _ _ _ _ hz
      (q_mem_Ioo_of_channel hc hd ⟨hz.1.le, hz.2.le⟩)).differentiableAt
  intro x hx y hy hxy
  by_cases hxs : x < distinguishedInput c d
  · let b := min y (distinguishedInput c d)
    have hxb : x < b := lt_min hxy hxs
    have hby : b ≤ y := min_le_left _ _
    have hb : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1.trans hxb, hby.trans_lt hy.2⟩
    have hm := deriv_eta_strictMonoOn_interval hc hd hcd hx hb (fun z hz => by
      have hzb : z < distinguishedInput c d := hz.2.trans_le (min_le_right _ _)
      exact ne_of_lt hzb)
    have hh := hm ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
    exact hh.trans_le (hmono hb hy hby)
  · have hm := deriv_eta_strictMonoOn_interval hc hd hcd hx hy (fun z hz => by
      have hsz : distinguishedInput c d < z := (le_of_not_gt hxs).trans_lt hz.1
      exact ne_of_gt hsz)
    exact hm ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy

/-- A single zero of the second derivative does not prevent strict convexity. -/
theorem strictConvexOn_entropyCurve_eta {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1) :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (entropyCurve (eta c d) c d) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
    (continuous_entropyCurve _ _ _).continuousOn
  simpa only [interior_Icc] using deriv_entropyCurve_eta_strictMonoOn hc hd hcd

/-- At the channel-wide cap, the tangent has no distinct contact. -/
theorem tangent_lt_entropyCurve_eta {s c d x : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxs : x ≠ s) :
    tangent (eta c d) s c d x < entropyCurve (eta c d) c d x := by
  have hcv := strictConvexOn_entropyCurve_eta hc hd hcd
  have hdiff := (hasDerivAt_entropyCurve (eta c d) s c d hs
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)).differentiableAt
  have hsc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  rcases lt_or_gt_of_ne hxs with hxs | hsx
  · have hh := hcv.slope_lt_deriv hx hsc hxs hdiff
    rw [slope_def_field] at hh
    have hh' := (div_lt_iff₀ (sub_pos.mpr hxs)).mp hh
    unfold tangent
    nlinarith
  · have hh := hcv.deriv_lt_slope hsc hx hsx hdiff
    rw [slope_def_field] at hh
    have hh' := (lt_div_iff₀ (sub_pos.mpr hsx)).mp hh
    unfold tangent
    nlinarith

/-- Each nonlocal KL ratio is strictly below the channel-wide coefficient. -/
theorem ratio_lt_eta {s c d x : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxs : x ≠ s) :
    D (q c d x) (q c d s) / D x s < eta c d := by
  apply (div_lt_iff₀ (D_pos hx hs hxs)).mpr
  have hgap := equation_4_1 (eta c d) s c d x hs
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)
  have ht := tangent_lt_entropyCurve_eta hs hc hd hcd hx hxs
  linarith

end ChannelCap

/-! ## The local ratio and the exact merging coefficient

证明局部比值不超过真实系数 S，并证明在特殊输入位置 S 恰好等于 eta。
-/

public section LocalCoefficient

lemma continuousAt_rhoSquared {c d s : ℝ}
    (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) : ContinuousAt (rhoSquared c d) s := by
  have hq := (hasDerivAt_q c d s).continuousAt
  have hn : ContinuousAt (fun x : ℝ => (k c d)^2 * x * (1 - x)) s := by fun_prop
  have hd : ContinuousAt (fun x : ℝ => q c d x * (1 - q c d x)) s :=
    hq.mul (continuousAt_const.sub hq)
  exact hn.div hd (mul_ne_zero (ne_of_gt hqs.1) (ne_of_gt (sub_pos.mpr hqs.2)))

/-- The local expression in (4.2) cannot exceed the distribution-dependent
KL coefficient. No differentiability or quotient-limit assumption is added. -/
theorem rhoSquared_le_S {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) : rhoSquared c d s ≤ S s c d := by
  by_contra h
  have hlt : S s c d < rhoSquared c d s := lt_of_not_ge h
  have hi : ∀ᶠ x in nhds s, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hn.1.1 hn.1.2
  have ho : ∀ᶠ x in nhds s, q c d x ∈ Set.Ioo (0 : ℝ) 1 :=
    (hasDerivAt_q c d s).continuousAt (Ioo_mem_nhds hn.2.1 hn.2.2)
  have hr : ∀ᶠ x in nhds s, S s c d < rhoSquared c d x :=
    (continuousAt_rhoSquared hn.2) (Ioi_mem_nhds hlt)
  have hu : ∀ᶠ x in nhds s,
      x ∈ Set.Ioo (0 : ℝ) 1 ∧ q c d x ∈ Set.Ioo (0 : ℝ) 1 ∧
        S s c d < rhoSquared c d x := by
    filter_upwards [hi, ho, hr] with x hxi hxo hxr
    exact ⟨hxi, hxo, hxr⟩
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hsub : ∀ x ∈ Set.Icc s (s + eps / 2),
      x ∈ Set.Ioo (0 : ℝ) 1 ∧ q c d x ∈ Set.Ioo (0 : ℝ) 1 ∧
        S s c d < rhoSquared c d x := by
    intro x hx
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hf : Continuous (entropyCurve (S s c d) c d) := by
    unfold entropyCurve q k
    fun_prop
  have hconc : StrictConcaveOn ℝ (Set.Icc s (s + eps / 2))
      (entropyCurve (S s c d) c d) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hf.continuousOn
    intro x hx
    have hx' := hsub x (interior_subset hx)
    change deriv (deriv (entropyCurve (S s c d) c d)) x < 0
    rw [deriv2_entropyCurve hx'.1 hx'.2.1]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hx'.2.2)
      (mul_pos hx'.1.1 (sub_pos.mpr hx'.1.2))
  have hsb : s < s + eps / 2 := by linarith
  have hsI : s ∈ Set.Icc s (s + eps / 2) := ⟨le_rfl, hsb.le⟩
  have hbI : s + eps / 2 ∈ Set.Icc s (s + eps / 2) := ⟨hsb.le, le_rfl⟩
  have hsec := hconc.slope_lt_deriv hsI hbI hsb
    (hasDerivAt_entropyCurve (S s c d) s c d hn.1 hn.2).differentiableAt
  rw [slope_def_field] at hsec
  have hstrict := (div_lt_iff₀ (sub_pos.mpr hsb)).1 hsec
  have hbprob := (hsub (s + eps / 2) hbI).1
  have hsupp := (S_le_iff_supporting_tangent hv hn).1 le_rfl
    (s + eps / 2) ⟨hbprob.1.le, hbprob.2.le⟩
  unfold tangent at hsupp
  linarith

/-- At the distinguished input, the exact distribution-dependent coefficient
attains the channel-wide expression in equation (4.4). -/
theorem S_distinguishedInput_eq_eta {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d ≠ 1) : S (distinguishedInput c d) c d = eta c d := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hsc : distinguishedInput c d ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hv : Valid (distinguishedInput c d) c d :=
    ⟨hsc, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate (distinguishedInput c d) c d :=
    ⟨hs, q_mem_Ioo_of_channel hc hd hsc⟩
  apply le_antisymm (S_le_eta hsc hc hd)
  rw [← rhoSquared_distinguishedInput hc hd hcd]
  exact rhoSquared_le_S hv hn

end LocalCoefficient

/-! ## Convexity regions and supporting-contact geometry

确定曲线哪些区间是凸的、哪些是凹的，并限制支撑切线的接触点位置。
-/

public section ContactGeometry

lemma hasDerivAt_rhoSquared {c d x : ℝ} (hqx : q c d x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (rhoSquared c d)
      ((k c d)^2 * (c * (1 - c) * (1 - x)^2 - d * (1 - d) * x^2) /
        (q c d x * (1 - q c d x))^2) x := by
  have hq := hasDerivAt_q c d x
  have hn := ((hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 1)).const_mul ((k c d)^2)
  have hd := hq.mul (hq.const_sub 1)
  have hden : q c d x * (1 - q c d x) ≠ 0 :=
    ne_of_gt (mul_pos hqx.1 (sub_pos.mpr hqx.2))
  convert! hn.div hd hden using 1
  · ext z
    unfold rhoSquared
    simp only [Pi.div_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq, Pi.mul_apply]
    unfold q k
    ring

lemma continuousOn_rhoSquared_Icc {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) : ContinuousOn (rhoSquared c d) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  exact (hasDerivAt_rhoSquared (q_mem_Ioo_of_channel hc hd hx)).continuousAt.continuousWithinAt

@[simp] lemma rhoSquared_zero (c d : ℝ) : rhoSquared c d 0 = 0 := by simp [rhoSquared]
@[simp] lemma rhoSquared_one (c d : ℝ) : rhoSquared c d 1 = 0 := by simp [rhoSquared]

lemma rhoSquared_deriv_pos {c d x : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d)) :
    0 < deriv (rhoSquared c d) x := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hs.2⟩
  have hqx := q_mem_Ioo_of_channel hc hd ⟨hx01.1.le, hx01.2.le⟩
  have hk : k c d ≠ 0 := by unfold k; intro he; apply hcd; linarith
  have ha := Real.sqrt_pos.2 (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hb := Real.sqrt_pos.2 (mul_pos hd.1 (sub_pos.mpr hd.2))
  have ha2 := Real.sq_sqrt (mul_pos hc.1 (sub_pos.mpr hc.2)).le
  have hb2 := Real.sq_sqrt (mul_pos hd.1 (sub_pos.mpr hd.2)).le
  have hleft : 0 < Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x := by
    have hh := (lt_div_iff₀ (add_pos ha hb)).mp hx.2
    nlinarith
  have hright : 0 < Real.sqrt (c * (1 - c)) * (1 - x) + Real.sqrt (d * (1 - d)) * x :=
    add_pos (mul_pos ha (sub_pos.mpr hx01.2)) (mul_pos hb hx.1)
  have hfactor : c * (1 - c) * (1 - x)^2 - d * (1 - d) * x^2 =
      (Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x) *
      (Real.sqrt (c * (1 - c)) * (1 - x) + Real.sqrt (d * (1 - d)) * x) := by
    nlinarith [ha2, hb2]
  rw [(hasDerivAt_rhoSquared hqx).deriv, hfactor]
  exact div_pos (mul_pos (sq_pos_of_ne_zero hk) (mul_pos hleft hright))
    (sq_pos_of_pos (mul_pos hqx.1 (sub_pos.mpr hqx.2)))

lemma rhoSquared_deriv_neg {c d x : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hx : x ∈ Set.Ioo (distinguishedInput c d) 1) :
    deriv (rhoSquared c d) x < 0 := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1.trans hx.1, hx.2⟩
  have hqx := q_mem_Ioo_of_channel hc hd ⟨hx01.1.le, hx01.2.le⟩
  have hk : k c d ≠ 0 := by unfold k; intro he; apply hcd; linarith
  have ha := Real.sqrt_pos.2 (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hb := Real.sqrt_pos.2 (mul_pos hd.1 (sub_pos.mpr hd.2))
  have ha2 := Real.sq_sqrt (mul_pos hc.1 (sub_pos.mpr hc.2)).le
  have hb2 := Real.sq_sqrt (mul_pos hd.1 (sub_pos.mpr hd.2)).le
  have hleft : Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x < 0 := by
    have hh := (div_lt_iff₀ (add_pos ha hb)).mp hx.1
    nlinarith
  have hright : 0 < Real.sqrt (c * (1 - c)) * (1 - x) + Real.sqrt (d * (1 - d)) * x :=
    add_pos (mul_pos ha (sub_pos.mpr hx01.2)) (mul_pos hb hx01.1)
  have hfactor : c * (1 - c) * (1 - x)^2 - d * (1 - d) * x^2 =
      (Real.sqrt (c * (1 - c)) * (1 - x) - Real.sqrt (d * (1 - d)) * x) *
      (Real.sqrt (c * (1 - c)) * (1 - x) + Real.sqrt (d * (1 - d)) * x) := by
    nlinarith [ha2, hb2]
  rw [(hasDerivAt_rhoSquared hqx).deriv, hfactor]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hk)
    (mul_neg_of_neg_of_pos hleft hright))
    (sq_pos_of_pos (mul_pos hqx.1 (sub_pos.mpr hqx.2)))

theorem rhoSquared_strictMonoOn {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1) :
    StrictMonoOn (rhoSquared c d) (Set.Icc (0 : ℝ) (distinguishedInput c d)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · apply (continuousOn_rhoSquared_Icc hc hd).mono
    exact Set.Icc_subset_Icc le_rfl (distinguishedInput_mem_Ioo hc hd).2.le
  · intro x hx
    exact rhoSquared_deriv_pos hc hd hcd (by simpa only [interior_Icc] using hx)

theorem rhoSquared_strictAntiOn {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1) :
    StrictAntiOn (rhoSquared c d) (Set.Icc (distinguishedInput c d) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · apply (continuousOn_rhoSquared_Icc hc hd).mono
    exact Set.Icc_subset_Icc (distinguishedInput_mem_Ioo hc hd).1.le le_rfl
  · intro x hx
    exact rhoSquared_deriv_neg hc hd hcd (by simpa only [interior_Icc] using hx)

/-- Every level strictly between zero and the channel maximum has exactly two roots,
one on each side of the distinguished input. -/
theorem rhoSquared_two_roots {c d lam : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hlam : lam ∈ Set.Ioo (0 : ℝ) (eta c d)) :
    ∃ a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d),
      ∃ b ∈ Set.Ioo (distinguishedInput c d) 1,
        rhoSquared c d a = lam ∧ rhoSquared c d b = lam ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, rhoSquared c d x = lam ↔ x = a ∨ x = b := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hrho := rhoSquared_distinguishedInput hc hd hcd
  have hleft := (continuousOn_rhoSquared_Icc hc hd).mono
    (Set.Icc_subset_Icc le_rfl hs.2.le)
  have hright := (continuousOn_rhoSquared_Icc hc hd).mono
    (Set.Icc_subset_Icc hs.1.le le_rfl)
  obtain ⟨a, ha, hea⟩ := intermediate_value_Icc hs.1.le hleft
    (show lam ∈ Set.Icc (rhoSquared c d 0) (rhoSquared c d (distinguishedInput c d)) by
      simpa only [rhoSquared_zero, hrho] using ⟨hlam.1.le, hlam.2.le⟩)
  obtain ⟨b, hb, heb⟩ := intermediate_value_Icc' hs.2.le hright
    (show lam ∈ Set.Icc (rhoSquared c d 1) (rhoSquared c d (distinguishedInput c d)) by
      simpa only [rhoSquared_one, hrho] using ⟨hlam.1.le, hlam.2.le⟩)
  have ha' : a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d) := by
    constructor
    · apply lt_of_le_of_ne ha.1
      intro he
      have : lam = 0 := by simpa [← he] using hea.symm
      linarith [hlam.1]
    · apply lt_of_le_of_ne ha.2
      intro he
      have : lam = eta c d := by simpa only [he, hrho] using hea.symm
      linarith [hlam.2]
  have hb' : b ∈ Set.Ioo (distinguishedInput c d) 1 := by
    constructor
    · apply lt_of_le_of_ne hb.1
      intro he
      have : lam = eta c d := by simpa only [← he, hrho] using heb.symm
      linarith [hlam.2]
    · apply lt_of_le_of_ne hb.2
      intro he
      have : lam = 0 := by simpa [he] using heb.symm
      linarith [hlam.1]
  refine ⟨a, ha', b, hb', hea, heb, ?_⟩
  intro x hx
  constructor
  · intro he
    rcases le_total x (distinguishedInput c d) with hxs | hsx
    · exact Or.inl ((rhoSquared_strictMonoOn hc hd hcd).injOn ⟨hx.1, hxs⟩ ha
        (he.trans hea.symm))
    · exact Or.inr ((rhoSquared_strictAntiOn hc hd hcd).injOn ⟨hsx, hx.2⟩ hb
        (he.trans heb.symm))
  · rintro (rfl | rfl) <;> assumption

lemma rhoSquared_lt_of_left {c d lam a x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d))
    (hroot : rhoSquared c d a = lam) (hx : x ∈ Set.Ico (0 : ℝ) a) :
    rhoSquared c d x < lam := by
  rw [← hroot]
  exact rhoSquared_strictMonoOn hc hd hcd ⟨hx.1, hx.2.le.trans ha.2.le⟩
    ⟨ha.1.le, ha.2.le⟩ hx.2

lemma rhoSquared_lt_of_right {c d lam b x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hb : b ∈ Set.Ioo (distinguishedInput c d) 1)
    (hroot : rhoSquared c d b = lam) (hx : x ∈ Set.Ioc b 1) :
    rhoSquared c d x < lam := by
  rw [← hroot]
  exact rhoSquared_strictAntiOn hc hd hcd ⟨hb.1.le, hb.2.le⟩
    ⟨hb.1.le.trans hx.1.le, hx.2⟩ hx.1

lemma level_lt_rhoSquared_of_middle {c d lam a b x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Set.Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hx : x ∈ Set.Ioo a b) : lam < rhoSquared c d x := by
  rcases le_total x (distinguishedInput c d) with hxs | hsx
  · rw [← haroot]
    exact rhoSquared_strictMonoOn hc hd hcd ⟨ha.1.le, ha.2.le⟩
      ⟨ha.1.le.trans hx.1.le, hxs⟩ hx.1
  · rw [← hbroot]
    exact rhoSquared_strictAntiOn hc hd hcd ⟨hsx, hx.2.le.trans hb.2.le⟩
      ⟨hb.1.le, hb.2.le⟩ hx.2

theorem strictConvexOn_entropyCurve_left {c d lam a : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d))
    (hroot : rhoSquared c d a = lam) :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) a) (entropyCurve lam c d) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) (continuous_entropyCurve _ _ _).continuousOn
  intro x hx
  have hx' : x ∈ Set.Ioo (0 : ℝ) a := by simpa only [interior_Icc] using hx
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hx'.1, hx'.2.trans (ha.2.trans (distinguishedInput_mem_Ioo hc hd).2)⟩
  change 0 < deriv (deriv (entropyCurve lam c d)) x
  rw [deriv2_entropyCurve hx01 (q_mem_Ioo_of_channel hc hd ⟨hx01.1.le, hx01.2.le⟩)]
  exact div_pos (sub_pos.mpr (rhoSquared_lt_of_left hc hd hcd ha hroot ⟨hx'.1.le, hx'.2⟩))
    (mul_pos hx01.1 (sub_pos.mpr hx01.2))

theorem strictConvexOn_entropyCurve_right {c d lam b : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hb : b ∈ Set.Ioo (distinguishedInput c d) 1)
    (hroot : rhoSquared c d b = lam) :
    StrictConvexOn ℝ (Set.Icc b 1) (entropyCurve lam c d) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) (continuous_entropyCurve _ _ _).continuousOn
  intro x hx
  have hx' : x ∈ Set.Ioo b 1 := by simpa only [interior_Icc] using hx
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨((distinguishedInput_mem_Ioo hc hd).1.trans hb.1).trans hx'.1, hx'.2⟩
  change 0 < deriv (deriv (entropyCurve lam c d)) x
  rw [deriv2_entropyCurve hx01 (q_mem_Ioo_of_channel hc hd ⟨hx01.1.le, hx01.2.le⟩)]
  exact div_pos (sub_pos.mpr (rhoSquared_lt_of_right hc hd hcd hb hroot ⟨hx'.1, hx'.2.le⟩))
    (mul_pos hx01.1 (sub_pos.mpr hx01.2))

theorem strictConcaveOn_entropyCurve_middle {c d lam a b : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Set.Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam) :
    StrictConcaveOn ℝ (Set.Icc a b) (entropyCurve lam c d) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) (continuous_entropyCurve _ _ _).continuousOn
  intro x hx
  have hx' : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
  have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha.1.trans hx'.1, hx'.2.trans hb.2⟩
  change deriv (deriv (entropyCurve lam c d)) x < 0
  rw [deriv2_entropyCurve hx01 (q_mem_Ioo_of_channel hc hd ⟨hx01.1.le, hx01.2.le⟩)]
  exact div_neg_of_neg_of_pos
    (sub_neg.mpr (level_lt_rhoSquared_of_middle hc hd hcd ha hb haroot hbroot hx'))
    (mul_pos hx01.1 (sub_pos.mpr hx01.2))

/-- A lower supporting tangent cannot be based in a nontrivial strictly concave interval,
including either endpoint of that interval. -/
lemma not_klCap_of_strictConcave {lam s c d a b : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a < b) (hs : s ∈ Set.Icc a b)
    (hconc : StrictConcaveOn ℝ (Set.Icc a b) (entropyCurve lam c d)) :
    ¬ KLCap lam s c d := by
  intro hcap
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha.1.trans_le hs.1, hs.2.trans_lt hb.2⟩
  have hqs := q_mem_Ioo_of_channel hc hd ⟨hs01.1.le, hs01.2.le⟩
  have hsupp := (klCap_iff_supporting_tangent ⟨hs01, hqs⟩).mp hcap
  have hdv := (hasDerivAt_entropyCurve lam s c d hs01 hqs).differentiableAt
  rcases lt_or_eq_of_le hs.2 with hsb | rfl
  · have hh := hconc.slope_lt_deriv hs ⟨hab.le, le_rfl⟩ hsb hdv
    rw [slope_def_field] at hh
    have hstrict := (div_lt_iff₀ (sub_pos.mpr hsb)).mp hh
    have hbound := hsupp b ⟨hb.1.le, hb.2.le⟩
    unfold tangent at hbound
    linarith
  · have hh := hconc.deriv_lt_slope ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab hdv
    rw [slope_def_field] at hh
    have hstrict := (lt_div_iff₀ (sub_pos.mpr hab)).mp hh
    have hbound := hsupp a ⟨ha.1.le, ha.2.le⟩
    unfold tangent at hbound
    linarith

/-- Supporting inputs lie strictly outside both inflection points. -/
theorem supporting_input_outside_curvature_roots {lam s c d a b : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Set.Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Set.Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hcap : KLCap lam s c d) : s < a ∨ b < s := by
  by_contra h
  push Not at h
  exact not_klCap_of_strictConcave hc hd
    ⟨ha.1, ha.2.trans (distinguishedInput_mem_Ioo hc hd).2⟩
    ⟨(distinguishedInput_mem_Ioo hc hd).1.trans hb.1, hb.2⟩
    (ha.2.trans hb.1) ⟨h.1, h.2⟩
    (strictConcaveOn_entropyCurve_middle hc hd hcd ha hb haroot hbroot) hcap

lemma rhoSquared_pos {c d x : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < rhoSquared c d x := by
  have hk : k c d ≠ 0 := by unfold k; intro he; apply hcd; linarith
  have hqx := q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩
  exact div_pos (mul_pos (mul_pos (sq_pos_of_ne_zero hk) hx.1) (sub_pos.mpr hx.2))
    (mul_pos hqx.1 (sub_pos.mpr hqx.2))

/-- Away from the distinguished input, the exact coefficient is strictly larger than
the limiting local KL ratio. Thus its maximizing test cannot be the diagonal. -/
theorem rhoSquared_lt_S {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d ≠ 1) (hne : s ≠ distinguishedInput c d) :
    rhoSquared c d s < S s c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  have hleta := rhoSquared_le_eta hv.2.1 hv.2.2 hn.2
  have hlambda : rhoSquared c d s ∈ Set.Ioo (0 : ℝ) (eta c d) :=
    ⟨rhoSquared_pos hc hd hcd hs,
      lt_of_le_of_ne hleta (fun he => hne ((rhoSquared_eq_eta_iff hc hd hcd hn.2).mp he))⟩
  obtain ⟨a, ha, b, hb, haroot, hbroot, hroots⟩ := rhoSquared_two_roots hc hd hcd hlambda
  apply lt_of_le_of_ne (rhoSquared_le_S hv hn)
  intro he
  have hcap : KLCap (rhoSquared c d s) s c d := by rw [he]; exact klCap_S hv hn
  have hout := supporting_input_outside_curvature_roots hc hd hcd ha hb haroot hbroot hcap
  rcases (hroots s hv.1).mp rfl with hsa | hsb
  · rcases hout with hh | hh
    · exact (ne_of_lt hh) hsa
    · have := ha.2.trans hb.1
      linarith
  · rcases hout with hh | hh
    · have := ha.2.trans hb.1
      linarith
    · exact (ne_of_lt hh) hsb.symm

lemma hasDerivAt_tangent (lam s c d x : ℝ) :
    HasDerivAt (tangent lam s c d) (deriv (entropyCurve lam c d) s) x := by
  convert! (((hasDerivAt_id x).sub_const s).const_mul
    (deriv (entropyCurve lam c d) s)).const_add (entropyCurve lam c d s) using 1
  simp

/-- An interior contact of a lower supporting tangent has the same slope. -/
theorem supporting_contact_deriv_eq {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    deriv (entropyCurve lam c d) r = deriv (entropyCurve lam c d) s := by
  have hqs := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr := q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hsupp := (klCap_iff_supporting_tangent ⟨hs, hqs⟩).mp hcap
  have hmin : IsLocalMin (fun x => entropyCurve lam c d x - tangent lam s c d x) r := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr (hsupp x ⟨hx.1.le, hx.2.le⟩)
  have hdiff := (hasDerivAt_entropyCurve lam r c d hr hqr).differentiableAt.hasDerivAt
  have he := hmin.hasDerivAt_eq_zero (hdiff.sub (hasDerivAt_tangent lam s c d r))
  exact sub_eq_zero.mp he

/-- A second interior contact makes the two actual tangent lines identical. -/
theorem supporting_contact_tangent_eq {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    tangent lam r c d = tangent lam s c d := by
  have hdv := supporting_contact_deriv_eq hs hr hc hd hcap hcontact
  ext x
  unfold tangent at hcontact ⊢
  rw [hdv, hcontact]
  ring

/-- A distinct contact realizes the exact contraction coefficient. -/
theorem S_eq_of_supporting_contact {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hrs : r ≠ s) (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) : S s c d = lam := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  have hgap := equation_4_1 lam s c d r hn.1 hn.2
  have he : D (q c d r) (q c d s) / D r s = lam := by
    apply (div_eq_iff (ne_of_gt (D_pos hr hs hrs))).mpr
    linarith
  apply le_antisymm ((S_le_iff_klCap hv hn).mpr hcap)
  rw [← he]
  exact ratio_le_S hv hn hr hrs

/-- Both interior inputs of a nontrivial supporting bitangent have coefficient `lam`. -/
theorem supporting_contact_coefficients {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hrs : r ≠ s) (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    S s c d = lam ∧ S r c d = lam := by
  have ht := supporting_contact_tangent_eq hs hr hc hd hcap hcontact
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩⟩
  have hnr : Nondegenerate r c d := ⟨hr, q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩⟩
  have hcapr : KLCap lam r c d := by
    apply (klCap_iff_supporting_tangent hnr).mpr
    rw [ht]
    exact (klCap_iff_supporting_tangent hn).mp hcap
  constructor
  · exact S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd hrs hcap hcontact
  · apply S_eq_of_supporting_contact hr ⟨hs.1.le, hs.2.le⟩ hc hd hrs.symm hcapr
    rw [ht]
    simp [tangent]

end ContactGeometry

end BinaryPairBound
