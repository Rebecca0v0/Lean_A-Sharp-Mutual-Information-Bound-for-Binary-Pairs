module

public import BinaryPairBound.InformationPerturbation
public import BinaryPairBound.ContactMonotonicity
public import BinaryPairBound.ContactSymmetry
public import BinaryPairBound.ReflectedSign

/-!
# The output derivative and its scalar sign test

The sign test is the actual `Q` in (C.3). `ReflectedSign.lean` proves its
positivity at the reflected contact. `ContactSigns.lean` combines these
derivatives with placement of the actual supporting contact.
-/

noncomputable section
public section

namespace BinaryPairBound

/-- The output-direction identity in (C.3), with the slope from (C.2). -/
theorem informationCoords_contact_q_direction_eq {s r qv kv : ℝ}
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) (hk : 0 < kv) :
    deriv (fun z => informationCoords s z kv) qv +
      deriv (fun z => informationCoords s qv z) kv *
        (-1 / (r - s) + kv / (qv * (1 - qv) *
          (logOdds (qv + kv * (r - s)) - logOdds qv))) =
    -(logOdds (qv + kv * (1 - s)) - logOdds (qv - kv * s)) *
      contactQ ((logOdds qv - logOdds (qv - kv * s)) /
        (logOdds (qv + kv * (1 - s)) - logOdds (qv - kv * s))) s qv kv r := by
  have hM := sub_pos.mpr (logOdds_strictMonoOn hc hb (by linarith))
  rw [(hasDerivAt_informationCoords_q hq hc hb).deriv,
    (hasDerivAt_informationCoords_k hq hc hb).deriv]
  unfold contactQ
  have halg (a b t x y : ℝ) (hne : b - a ≠ 0) :
      (1 - s) * a + s * b - t + s * (1 - s) * (b - a) * (-x + y) =
        -(b - a) * ((t - a) / (b - a) - s - s * (1 - s) * (y - x)) := by
    field_simp
    ring
  simpa only [neg_div] using halg (logOdds (qv - kv * s))
    (logOdds (qv + kv * (1 - s))) (logOdds qv) (1 / (r - s))
    (kv / (qv * (1 - qv) * (logOdds (qv + kv * (r - s)) - logOdds qv))) (ne_of_gt hM)

theorem hasDerivAt_contactGap_output_family
    {kf rf : ℝ → ℝ} {lam s qv v w : ℝ}
    (hk : HasDerivAt kf v qv) (hrf : HasDerivAt rf w qv)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : rf qv ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf qv * (rf qv - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam s z (kf z) (rf z))
      (deriv (fun z => contactGap lam s z (kf qv) (rf qv)) qv +
       deriv (fun z => contactGap lam s qv z (rf qv)) (kf qv) * v +
       deriv (fun z => contactGap lam s qv (kf qv) z) (rf qv) * w) qv := by
  have hY := (hasDerivAt_id qv).add (hk.mul (hrf.sub_const s))
  have h1 := hasDerivAt_D_comp hY (hasDerivAt_id qv) hqr hq
  have h2 := (hasDerivAt_D_comp hrf (hasDerivAt_const qv s) hr hs).const_mul lam
  rw [(hasDerivAt_contactGap_q lam s qv (kf qv) (rf qv) hq hqr).deriv,
    (hasDerivAt_contactGap_k lam s qv (kf qv) (rf qv) hq hqr).deriv,
    (hasDerivAt_contactGap_r lam s qv (kf qv) (rf qv) hs hr hq hqr).deriv]
  convert! h1.sub h2 using 1
  simp only [zero_mul, zero_div, add_zero, one_mul, Pi.add_apply, Pi.mul_apply, id_eq]
  ring

/-- The actual information derivative along a contact curve is `-M Q`.
The differentiated contact constraint is obtained from local `G = 0`. -/
theorem informationCoords_contact_output_curve_deriv_eq
    {kf rf : ℝ → ℝ} {lam s qv v w : ℝ}
    (hkf : HasDerivAt kf v qv) (hrf : HasDerivAt rf w qv)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : rf qv ∈ Set.Ioo (0 : ℝ) 1)
    (hsr : s < rf qv) (hk : 0 < kf qv)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kf qv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kf qv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf qv * (rf qv - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hGr : deriv (fun z => contactGap lam s qv (kf qv) z) (rf qv) = 0)
    (hG : ∀ᶠ z in nhds qv, contactGap lam s z (kf z) (rf z) = 0) :
    deriv (fun z => informationCoords s z (kf z)) qv =
      -(logOdds (qv + kf qv * (1 - s)) - logOdds (qv - kf qv * s)) *
        contactQ ((logOdds qv - logOdds (qv - kf qv * s)) /
          (logOdds (qv + kf qv * (1 - s)) - logOdds (qv - kf qv * s))) s qv (kf qv) (rf qv) := by
  have hd := hasDerivAt_contactGap_output_family (lam := lam) hkf hrf hs hr hq hqr
  have hz : HasDerivAt (fun z => contactGap lam s z (kf z) (rf z)) 0 qv :=
    (hasDerivAt_const qv (0 : ℝ)).congr_of_eventuallyEq hG
  have hchain := hd.unique hz
  rw [hGr, zero_mul, add_zero] at hchain
  rw [(hasDerivAt_informationCoords_output_family hkf hq hc hb).deriv,
    contactGap_implicit_slope_q lam s qv (kf qv) (rf qv) v hq hqr hk hsr hchain]
  exact informationCoords_contact_q_direction_eq hq hc hb hk

/-- Strict output improvement for a genuine differentiable contact curve,
once its second contact lies on or beyond the reflection threshold. -/
theorem informationCoords_output_curve_deriv_neg_of_reflection_le
    {kf rf : ℝ → ℝ} {lam s c d r v w : ℝ}
    (hkf : HasDerivAt kf v (q c d s)) (hrf : HasDerivAt rf w (q c d s))
    (hkbase : kf (q c d s) = k c d) (hrbase : rf (q c d s) = r)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hss : s < distinguishedInput c d)
    (href : contactReflection c d s ≤ r)
    (hGr : deriv (fun z => contactGap lam s (q c d s) (k c d) z) r = 0)
    (hG : ∀ᶠ z in nhds (q c d s), contactGap lam s z (kf z) (rf z) = 0) :
    deriv (fun z => informationCoords s z (kf z)) (q c d s) < 0 := by
  have hk : 0 < k c d := by unfold k; linarith
  have hsr := ((lt_contactReflection_iff hc hd hs).mpr hss).trans_le href
  have hc0 : q c d s - k c d * s = c := by unfold q; ring
  have hb0 : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
  have hqr0 : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
  have hder := informationCoords_contact_output_curve_deriv_eq hkf hrf hs
    (by simpa only [hrbase] using hr) (by simpa only [hrbase] using hsr)
    (by simpa only [hkbase] using hk)
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)
    (by simpa only [hkbase, hc0] using hc)
    (by rw [hkbase, hb0]; constructor <;> linarith [hd.1, hd.2])
    (by rw [hkbase, hrbase, hqr0]; exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩)
    (by simpa only [hkbase, hrbase] using hGr) hG
  rw [hkbase, hrbase, hc0, hb0] at hder
  rw [hder]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (channel_logOdds_gap_pos hc hd hcd))
    (contactQ_pos_of_reflection_le hs hr hc hd hcd hss href)

end BinaryPairBound
