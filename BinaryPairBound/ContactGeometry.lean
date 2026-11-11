module

public import BinaryPairBound.ChannelCap
public import BinaryPairBound.LocalCoefficient
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Curvature shape and supporting contacts for Lemma 4.1 -/

public section

namespace BinaryPairBound

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

end BinaryPairBound
