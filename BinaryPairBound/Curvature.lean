module

public import BinaryPairBound.TangentGap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Curvature of the binary entropy curve

The second derivative is derived from the actual first derivative, and the
local ratio is the explicit rational expression in Section 4.2. Identifying
that expression with a limit of KL ratios is a separate proof obligation.
-/

noncomputable section

@[expose] public section

namespace BinaryPairBound

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


end BinaryPairBound
