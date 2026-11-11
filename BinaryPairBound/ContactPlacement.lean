module

public import BinaryPairBound.ContactFeasibility
public import BinaryPairBound.ContactSymmetry

/-! # Reflected placement of supporting contacts

We work directly in input probabilities. The reflected entropy secant has
derivative `(F'(x)-F'(s₀)) (1+R'(x))`; this replaces the primitive-integral
argument in Appendix C.4.
-/

noncomputable section
@[expose] public section

open Set

namespace BinaryPairBound

lemma deriv_entropyCurve_logOdds {lam c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (entropyCurve lam c d) x = -k c d * logOdds (q c d x) + lam * logOdds x := by
  rw [deriv_entropyCurve lam x c d hx (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)]
  unfold logOdds
  ring

/-- The entropy-curve derivative is odd around its central value under reflection. -/
theorem deriv_entropyCurve_contactReflection {lam c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (entropyCurve lam c d) (contactReflection c d x) + deriv (entropyCurve lam c d) x =
      2 * deriv (entropyCurve lam c d) (distinguishedInput c d) := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hlog := output_logOdds_contactReflection hc hd hs
  rw [contactReflection_distinguishedInput hc hd] at hlog
  rw [deriv_entropyCurve_logOdds hc hd (contactReflection_mem_Ioo hc hd hx),
    deriv_entropyCurve_logOdds hc hd hx, deriv_entropyCurve_logOdds hc hd hs,
    logOdds_contactReflection hc hd hx]
  have hqx := output_logOdds_contactReflection hc hd hx
  linear_combination -k c d * (hqx - hlog)

theorem hasDerivAt_contactReflection {c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (contactReflection c d)
      (-(contactReflection c d x * (1 - contactReflection c d x)) / (x * (1 - x))) x := by
  have hA := mul_pos hc.1 (sub_pos.mpr hc.2)
  have hB := mul_pos hd.1 (sub_pos.mpr hd.2)
  have hden : 0 < c * (1 - c) * (1 - x) + d * (1 - d) * x :=
    add_pos (mul_pos hA (sub_pos.mpr hx.2)) (mul_pos hB hx.1)
  have hn := ((hasDerivAt_id x).const_sub 1).const_mul (c * (1 - c))
  have hdv := hn.add ((hasDerivAt_id x).const_mul (d * (1 - d)))
  have hR : DifferentiableAt ℝ (contactReflection c d) x :=
    (hn.div hdv (ne_of_gt hden)).differentiableAt
  have hrx := contactReflection_mem_Ioo hc hd hx
  have hsum := ((hasDerivAt_logOdds hrx).comp x hR.hasDerivAt).add (hasDerivAt_logOdds hx)
  have hconst : HasDerivAt (fun y => logOdds (contactReflection c d y) + logOdds y) 0 x := by
    apply (hasDerivAt_const x (2 * logOdds (distinguishedInput c d))).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    linarith [logOdds_contactReflection hc hd hy]
  have he := hsum.unique hconst
  have hneR : contactReflection c d x * (1 - contactReflection c d x) ≠ 0 :=
    ne_of_gt (mul_pos hrx.1 (sub_pos.mpr hrx.2))
  have he' : deriv (contactReflection c d) x /
      (contactReflection c d x * (1 - contactReflection c d x)) = -(1 / (x * (1 - x))) := by
    simpa only [one_div_mul_eq_div, eq_neg_iff_add_eq_zero] using he
  have he'' := (div_eq_iff hneR).mp he'
  convert! hR.hasDerivAt using 1
  rw [he'']
  ring

lemma contactReflection_variance_ge {c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hsx : distinguishedInput c d ≤ x) :
    x * (1 - x) ≤ contactReflection c d x * (1 - contactReflection c d x) := by
  have hA := mul_pos hc.1 (sub_pos.mpr hc.2)
  have hB := mul_pos hd.1 (sub_pos.mpr hd.2)
  have hAB : d * (1 - d) ≤ c * (1 - c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdc) (show 0 ≤ 1 - c - d by linarith)]
  have hden : 0 < c * (1 - c) * (1 - x) + d * (1 - d) * x :=
    add_pos (mul_pos hA (sub_pos.mpr hx.2)) (mul_pos hB hx.1)
  have hRx : contactReflection c d x ≤ x := by
    by_contra h
    have hh := (lt_contactReflection_iff hc hd hx).mp (lt_of_not_ge h)
    exact (not_lt_of_ge hsx) hh
  have hsum : 1 - x ≤ contactReflection c d x := by
    unfold contactReflection weightedReflection
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (mul_pos hx.1 (sub_pos.mpr hx.2)).le (sub_nonneg.mpr hAB)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hRx)
    (show 0 ≤ contactReflection c d x + x - 1 by linarith)]

lemma one_add_deriv_contactReflection_nonpos {c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hsx : distinguishedInput c d ≤ x) : 1 + deriv (contactReflection c d) x ≤ 0 := by
  rw [(hasDerivAt_contactReflection hc hd hx).deriv]
  have hden := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hh := contactReflection_variance_ge hc hd hcd hdc hx hsx
  have hdiv : 1 ≤ (contactReflection c d x * (1 - contactReflection c d x)) / (x * (1 - x)) :=
    (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hh)
  rw [neg_div]
  linarith

def reflectedEntropySecant (lam c d x : ℝ) : ℝ :=
  entropyCurve lam c d x - entropyCurve lam c d (contactReflection c d x) -
    deriv (entropyCurve lam c d) (distinguishedInput c d) * (x - contactReflection c d x)

theorem hasDerivAt_reflectedEntropySecant {lam c d x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (reflectedEntropySecant lam c d)
      ((deriv (entropyCurve lam c d) x - deriv (entropyCurve lam c d) (distinguishedInput c d)) *
        (1 + deriv (contactReflection c d) x)) x := by
  have hrx := contactReflection_mem_Ioo hc hd hx
  have hR := (hasDerivAt_contactReflection hc hd hx).differentiableAt.hasDerivAt
  have hFx := (hasDerivAt_entropyCurve lam x c d hx
    (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)).differentiableAt.hasDerivAt
  have hFR := (hasDerivAt_entropyCurve lam (contactReflection c d x) c d hrx
    (q_mem_Ioo_of_channel hc hd ⟨hrx.1.le, hrx.2.le⟩)).differentiableAt.hasDerivAt
  have hh := (hFx.sub (hFR.comp x hR)).sub
    (((hasDerivAt_id x).sub hR).const_mul (deriv (entropyCurve lam c d) (distinguishedInput c d)))
  convert! hh using 1
  have he := deriv_entropyCurve_contactReflection (lam := lam) hc hd hx
  linear_combination deriv (contactReflection c d) x * he

theorem reflectedEntropySecant_nonneg {lam c d r : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hsr : distinguishedInput c d ≤ r)
    (hbound : ∀ x ∈ Icc (distinguishedInput c d) r,
      deriv (entropyCurve lam c d) x ≤ deriv (entropyCurve lam c d) (distinguishedInput c d)) :
    0 ≤ reflectedEntropySecant lam c d r := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hinterior : ∀ x ∈ Icc (distinguishedInput c d) r, x ∈ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨hs0.1.trans_le hx.1, hx.2.trans_lt hr.2⟩
  have hmono : MonotoneOn (reflectedEntropySecant lam c d) (Icc (distinguishedInput c d) r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hasDerivAt_reflectedEntropySecant hc hd (hinterior x hx)).continuousAt.continuousWithinAt
    · exact fun x hx => (hasDerivAt_reflectedEntropySecant hc hd
        (hinterior x (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi := interior_subset hx
      rw [(hasDerivAt_reflectedEntropySecant hc hd (hinterior x hxi)).deriv]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hbound x hxi))
        (one_add_deriv_contactReflection_nonpos hc hd hcd hdc (hinterior x hxi) hxi.1)
  have hh := hmono ⟨le_rfl, hsr⟩ ⟨hsr, le_rfl⟩ hsr
  have hzero : reflectedEntropySecant lam c d (distinguishedInput c d) = 0 := by
    unfold reflectedEntropySecant
    rw [contactReflection_distinguishedInput hc hd]
    ring
  simpa only [hzero] using hh

lemma deriv_le_central_of_right_deriv_le {lam c d a b r : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hr : r ∈ Ioo b 1)
    (hm : deriv (entropyCurve lam c d) r ≤ deriv (entropyCurve lam c d) (distinguishedInput c d)) :
    ∀ x ∈ Icc (distinguishedInput c d) r,
      deriv (entropyCurve lam c d) x ≤ deriv (entropyCurve lam c d) (distinguishedInput c d) := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hD : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (entropyCurve lam c d) x := by
    intro x hx
    exact (hasDerivAt_entropyCurve lam x c d hx
      (q_mem_Ioo_of_channel hc hd ⟨hx.1.le, hx.2.le⟩)).differentiableAt
  have hanti := (strictConcaveOn_entropyCurve_middle hc hd hcd ha hb haroot hbroot).concaveOn.antitoneOn_deriv
    (fun x hx => hD x ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩)
  have hconv : ConvexOn ℝ (Icc b r) (entropyCurve lam c d) :=
    (strictConvexOn_entropyCurve_right hc hd hcd hb hbroot).convexOn.subset
      (Icc_subset_Icc le_rfl hr.2.le) (convex_Icc _ _)
  have hmono := hconv.monotoneOn_deriv
    (fun x hx => hD x ⟨(hs0.1.trans hb.1).trans_le hx.1, hx.2.trans_lt hr.2⟩)
  intro x hx
  by_cases hxb : x ≤ b
  · exact hanti ⟨ha.2.le, hb.1.le⟩ ⟨ha.2.le.trans hx.1, hxb⟩ hx.1
  · exact (hmono ⟨(lt_of_not_ge hxb).le, hx.2⟩ ⟨hr.1.le, le_rfl⟩ hx.2).trans hm

/-- For `c ≥ d`, every supporting tangent on the right outer branch has slope
at least the derivative at the distinguished input. -/
theorem central_deriv_le_of_right_supporting {lam c d a b r : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hr : r ∈ Ioo b 1) (hcap : KLCap lam r c d) :
    deriv (entropyCurve lam c d) (distinguishedInput c d) ≤ deriv (entropyCurve lam c d) r := by
  by_contra h
  have hm := lt_of_not_ge h
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨(hs0.1.trans hb.1).trans hr.1, hr.2⟩
  have hR := contactReflection_mem_Ioo hc hd hr01
  have hRr : contactReflection c d r < r := by
    apply (logOdds_strictMonoOn.lt_iff_lt hR hr01).mp
    have hh := logOdds_strictMonoOn hs0 hr01 (hb.1.trans hr.1)
    rw [logOdds_contactReflection hc hd hr01]
    linarith
  have hB := reflectedEntropySecant_nonneg hc hd hcd hdc hr01 (hb.1.trans hr.1).le
    (deriv_le_central_of_right_deriv_le hc hd (ne_of_lt hcd) ha hb haroot hbroot hr hm.le)
  have hsupp := (klCap_iff_supporting_tangent
    ⟨hr01, q_mem_Ioo_of_channel hc hd ⟨hr01.1.le, hr01.2.le⟩⟩).mp hcap
      (contactReflection c d r) ⟨hR.1.le, hR.2.le⟩
  unfold reflectedEntropySecant at hB
  unfold tangent at hsupp
  nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hRr)]

/-- The reflected smaller contact lies no further right than the larger contact.
All contact and curvature hypotheses are established from the global KL cap. -/
theorem contactReflection_le_of_supporting_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    contactReflection c d s ≤ r := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hvs : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hns : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hvs.1⟩
  have hnr : Nondegenerate r c d := ⟨hr, q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩⟩
  have hS := S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd (ne_of_gt hsr) hcap hcontact
  have hlam0 : 0 < lam := by
    have hh := (rhoSquared_pos hc hd (ne_of_lt hcd) hs).trans_le (rhoSquared_le_S hvs hns)
    rwa [hS] at hh
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd (ne_of_lt hcd) ⟨hlam0, hlam⟩
  have hpositions := supporting_contacts_straddle_roots hs hr hc hd (ne_of_lt hcd)
    ha hb haroot hbroot hsr hcap hcontact
  have ht := supporting_contact_tangent_eq hs hr hc hd hcap hcontact
  have hcapr : KLCap lam r c d := by
    apply (klCap_iff_supporting_tangent hnr).mpr
    rw [ht]
    exact (klCap_iff_supporting_tangent hns).mp hcap
  have hcentral := central_deriv_le_of_right_supporting hc hd hcd hdc ha hb haroot hbroot
    ⟨hpositions.2, hr.2⟩ hcapr
  have hslopes := supporting_contact_deriv_eq hs hr hc hd hcap hcontact
  have hR := contactReflection_mem_Ioo hc hd hs
  have hRs0 : distinguishedInput c d < contactReflection c d s := by
    apply (logOdds_strictMonoOn.lt_iff_lt hs0 hR).mp
    have hh := logOdds_strictMonoOn hs hs0 (hpositions.1.trans ha.2)
    rw [logOdds_contactReflection hc hd hs]
    linarith
  have hrho : rhoSquared c d (contactReflection c d s) < lam := by
    rw [rhoSquared_contactReflection hc hd hs]
    exact rhoSquared_lt_of_left hc hd (ne_of_lt hcd) ha haroot ⟨hs.1.le, hpositions.1⟩
  have hbR : b < contactReflection c d s := by
    by_contra h
    have hh := (rhoSquared_strictAntiOn hc hd (ne_of_lt hcd)).antitoneOn
      ⟨hRs0.le, hR.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (le_of_not_gt h)
    rw [hbroot] at hh
    linarith
  have hreflectSlope := deriv_entropyCurve_contactReflection (lam := lam) hc hd hs
  have hle : deriv (entropyCurve lam c d) (contactReflection c d s) ≤ deriv (entropyCurve lam c d) r := by
    linarith
  by_contra h
  have hrR := lt_of_not_ge h
  have hconv := strictConvexOn_entropyCurve_right hc hd (ne_of_lt hcd) hb hbroot
  have hdr := (hasDerivAt_entropyCurve lam r c d hr hnr.2).differentiableAt
  have hdR := (hasDerivAt_entropyCurve lam (contactReflection c d s) c d hR
    (q_mem_Ioo_of_channel hc hd ⟨hR.1.le, hR.2.le⟩)).differentiableAt
  have hlt := (hconv.deriv_lt_slope ⟨hpositions.2.le, hr.2.le⟩ ⟨hbR.le, hR.2.le⟩ hrR hdr).trans
    (hconv.slope_lt_deriv ⟨hpositions.2.le, hr.2.le⟩ ⟨hbR.le, hR.2.le⟩ hrR hdR)
  exact (not_lt_of_ge hle) hlt

/-- The final normalized-output placement inequality in Appendix C.4. -/
theorem normalizedOutputLogOdds_sum_ge_one_of_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    1 ≤ normalizedOutputLogOdds c d s + normalizedOutputLogOdds c d r :=
  (normalizedOutputLogOdds_sum_ge_one_iff hc hd hcd hs hr).mpr
    (contactReflection_le_of_supporting_contact hs hr hc hd hcd hdc hlam hsr hcap hcontact)

end BinaryPairBound
