module

public import BinaryPairBound.ContactPlacement
public import BinaryPairBound.ContactJacobian
public import BinaryPairBound.OutputDirection

/-! # The strict signs for actual supporting-contact families

These theorems discharge the reflection and stationarity conditions from an
actual ordered supporting contact. The remaining family assumptions state
differentiability and the local contact equation, not any derivative sign.
-/

public section

open Set

namespace BinaryPairBound

theorem left_contact_lt_distinguishedInput {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d ≠ 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    s < distinguishedInput c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  have heS := S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd (ne_of_gt hsr) hcap hcontact
  have hlam0 : 0 < lam := by
    have hh := (rhoSquared_pos hc hd hcd hs).trans_le (rhoSquared_le_S hv hn)
    rwa [heS] at hh
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd hcd ⟨hlam0, hlam⟩
  exact (supporting_contacts_straddle_roots hs hr hc hd hcd ha hb haroot hbroot hsr hcap hcontact).1.trans ha.2

/-- Full Lemma C.2 sign, with reflected-contact placement proved from the
actual supporting contact. -/
theorem contactQ_pos_of_supporting_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    0 < contactQ (normalizedOutputLogOdds c d s) s (q c d s) (k c d) r :=
  contactQ_pos_of_reflection_le hs hr hc hd hcd
    (left_contact_lt_distinguishedInput hs hr hc hd (ne_of_lt hcd) hlam hsr hcap hcontact)
    (contactReflection_le_of_supporting_contact hs hr hc hd hcd hdc hlam hsr hcap hcontact)

/-- If `c ≥ d`, increasing output probability along any differentiable local
contact family strictly decreases information. -/
theorem informationCoords_supporting_output_curve_deriv_neg
    {kf rf : ℝ → ℝ} {lam s c d r v w : ℝ}
    (hkf : HasDerivAt kf v (q c d s)) (hrf : HasDerivAt rf w (q c d s))
    (hkbase : kf (q c d s) = k c d) (hrbase : rf (q c d s) = r)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hdc : d ≤ c) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r)
    (hG : ∀ᶠ z in nhds (q c d s), contactGap lam s z (kf z) (rf z) = 0) :
    deriv (fun z => informationCoords s z (kf z)) (q c d s) < 0 :=
  informationCoords_output_curve_deriv_neg_of_reflection_le hkf hrf hkbase hrbase hs hr hc hd hcd
    (left_contact_lt_distinguishedInput hs hr hc hd (ne_of_lt hcd) hlam hsr hcap hcontact)
    (contactReflection_le_of_supporting_contact hs hr hc hd hcd hdc hlam hsr hcap hcontact)
    (contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact) hG

/-- If `c ≤ d`, increasing input probability along any differentiable local
contact family strictly increases information. The parameters here are the
original channel entries, rather than unrestricted coordinate expressions. -/
theorem informationCoords_supporting_input_curve_deriv_pos
    {kf rf : ℝ → ℝ} {lam s c d r v w : ℝ}
    (hkf : HasDerivAt kf v s) (hrf : HasDerivAt rf w s)
    (hkbase : kf s = k c d) (hrbase : rf s = r)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (horder : c ≤ d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r)
    (hG : ∀ᶠ z in nhds s, contactGap lam z (q c d s) (kf z) (rf z) = 0) :
    0 < deriv (fun z => informationCoords z (q c d s) (kf z)) s := by
  have hk : 0 < k c d := by unfold k; linarith
  have hc0 : q c d s - k c d * s = c := by unfold q; ring
  have hb0 : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
  have hqr0 : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
  apply informationCoords_contact_curve_deriv_pos hkf hrf hs
    (by simpa only [hrbase] using hr) (by simpa only [hrbase] using hsr)
    (by simpa only [hkbase] using hk)
    (q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩)
    (by simpa only [hkbase, hc0] using hc)
    (by rw [hkbase, hb0]; constructor <;> linarith [hd.1, hd.2])
    (by rw [hkbase, hrbase, hqr0]; exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩)
    (by rw [hkbase, hc0, hb0]; linarith)
    (by simpa only [hkbase, hrbase] using contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact) hG

end BinaryPairBound
