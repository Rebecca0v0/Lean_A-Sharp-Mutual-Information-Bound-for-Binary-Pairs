module

public import BinaryPairBound.Contraction
public import BinaryPairBound.Curvature
public import Mathlib.Analysis.Convex.Deriv

public section

namespace BinaryPairBound

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

end BinaryPairBound
