module

public import BinaryPairBound.ContactSigns
public import BinaryPairBound.CapSaturation
public import BinaryPairBound.MaximizerVariations
public import BinaryPairBound.ContactFamily

/-! # Interior maximizers have merging contacts -/

public section

open Set

namespace BinaryPairBound

lemma distinguishedInput_swap {c d : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (hd : d ∈ Ioo (0 : ℝ) 1) : distinguishedInput d c = 1 - distinguishedInput c d := by
  have hA := Real.sqrt_pos.mpr (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hB := Real.sqrt_pos.mpr (mul_pos hd.1 (sub_pos.mpr hd.2))
  unfold distinguishedInput
  rw [add_comm (Real.sqrt (d * (1 - d))) (Real.sqrt (c * (1 - c)))]
  apply (div_eq_iff (ne_of_gt (add_pos hA hB))).mpr
  have hh := div_mul_cancel₀ (Real.sqrt (c * (1 - c))) (ne_of_gt (add_pos hA hB))
  nlinarith

/-- Every input strictly below the distinguished input has a larger interior
contact attaining its exact contraction coefficient. -/
theorem exists_right_interior_contact {s c d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hss : s < distinguishedInput c d) :
    ∃ r ∈ Ioo (0 : ℝ) 1, s < r ∧
      entropyCurve (S s c d) c d r = tangent (S s c d) s c d r := by
  obtain ⟨u, v, a, b, hu, hv, hbase, hua, has, hsb, hbv, _, _, ht, _, _, _⟩ :=
    exists_ordered_interior_contacts hs hc hd hcd (ne_of_lt hss)
  rcases hbase with hsu | hsv
  · subst u
    refine ⟨v, hv, hua.trans (has.trans (hsb.trans hbv)), ?_⟩
    rw [← ht]
    simp [tangent]
  · have hsv' := hsb.trans hbv
    rw [hsv] at hss
    exact False.elim (lt_asymm hss hsv')

/-- A smooth feasible family through an ordered distinct supporting contact
contradicts maximality, using the strict sign appropriate to the channel order. -/
theorem not_cap_maximizer_of_ordered_feasible_family
    {lam s c d r : ℝ} {f : (ℝ × ℝ) → (ℝ × ℝ)}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r)
    (hf : DifferentiableAt ℝ f (s, q c d s))
    (hbase : f (s, q c d s) = (k c d, r))
    (hG : ∀ᶠ p in nhds (s, q c d s), contactGap lam p.1 p.2 (f p).1 (f p).2 = 0)
    (hfeas : ∀ᶠ p in nhds (s, q c d s),
      Valid p.1 (p.2 - (f p).1 * p.1) (1 - p.2 - (f p).1 * (1 - p.1)) ∧
      S p.1 (p.2 - (f p).1 * p.1) (1 - p.2 - (f p).1 * (1 - p.1)) ≤ lam) :
    ¬ IsCapMaximizer lam s c d := by
  intro hm
  rcases le_total c d with horder | horder
  · let kf := fun t : ℝ => (f (t, q c d s)).1
    let rf := fun t : ℝ => (f (t, q c d s)).2
    have hcurve : DifferentiableAt ℝ (fun t : ℝ => f (t, q c d s)) s :=
      hf.comp s (differentiableAt_id.prodMk (differentiableAt_const (q c d s)))
    have hkf : DifferentiableAt ℝ kf s :=
      hcurve.fst
    have hrf : DifferentiableAt ℝ rf s :=
      hcurve.snd
    have hkbase : kf s = k c d := congrArg Prod.fst hbase
    have hrbase : rf s = r := congrArg Prod.snd hbase
    have hmap : ContinuousAt (fun t : ℝ => (t, q c d s)) s := by fun_prop
    have hGt := hmap hG
    have hFt := hmap hfeas
    have hpos := informationCoords_supporting_input_curve_deriv_pos hkf.hasDerivAt hrf.hasDerivAt
      hkbase hrbase hs hr hc hd hcd horder hsr hcap hcontact hGt
    have hzero := hm.input_family_deriv_eq_zero hkbase hFt
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  · let kf := fun t : ℝ => (f (s, t)).1
    let rf := fun t : ℝ => (f (s, t)).2
    have hcurve : DifferentiableAt ℝ (fun t : ℝ => f (s, t)) (q c d s) :=
      hf.comp (q c d s) ((differentiableAt_const s).prodMk differentiableAt_id)
    have hkf : DifferentiableAt ℝ kf (q c d s) :=
      hcurve.fst
    have hrf : DifferentiableAt ℝ rf (q c d s) :=
      hcurve.snd
    have hkbase : kf (q c d s) = k c d := congrArg Prod.fst hbase
    have hrbase : rf (q c d s) = r := congrArg Prod.snd hbase
    have hmap : ContinuousAt (fun t : ℝ => (s, t)) (q c d s) := by fun_prop
    have hGt := hmap hG
    have hFt := hmap hfeas
    have hneg := informationCoords_supporting_output_curve_deriv_neg hkf.hasDerivAt hrf.hasDerivAt
      hkbase hrbase hs hr hc hd hcd horder hlam hsr hcap hcontact hGt
    have hzero := hm.output_family_deriv_eq_zero hkbase hFt
    rw [hzero] at hneg
    exact (lt_irrefl 0) hneg

/-- Distinct ordered supporting contacts cannot maximize mutual information.
The smooth feasible family is constructed by the implicit function theorem. -/
theorem not_cap_maximizer_of_ordered_contact {lam s c d r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    ¬ IsCapMaximizer lam s c d := by
  obtain ⟨f, hf, hbase, hevent⟩ :=
    exists_feasible_contact_family hs hr hc hd hcd hlam hsr hcap hcontact
  apply not_cap_maximizer_of_ordered_feasible_family hs hr hc hd hcd hlam hsr hcap hcontact
    (hf.differentiableAt (by norm_num)) hbase
  · filter_upwards [hevent] with p hp
    exact hp.1
  · filter_upwards [hevent] with p hp
    exact ⟨hp.2.2.1, hp.2.2.2.le⟩

theorem not_cap_maximizer_of_left_interior {lam s c d : ℝ}
    (hlam : lam ∈ Ioc (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hss : s < distinguishedInput c d) :
    ¬ IsCapMaximizer lam s c d := by
  intro hm
  have hS := interior_cap_maximizer_saturates hlam hm hc hd hcd.le
  have hn := cap_maximizer_nondegenerate hlam hm
  have hcap : KLCap lam s c d := by rw [← hS]; exact klCap_S hm.1 hn
  have hleta : lam < eta c d := by
    rw [← hS]
    exact S_lt_eta_of_ne_distinguishedInput hs hc hd (ne_of_lt hcd) (ne_of_lt hss)
  obtain ⟨r, hr, hsr, hcontact⟩ := exists_right_interior_contact hs hc hd (ne_of_lt hcd) hss
  rw [hS] at hcontact
  exact not_cap_maximizer_of_ordered_contact hs hr hc hd hcd hleta hsr hcap hcontact hm

/-- Sections 5 and 9 for interior channels: every normalized cap maximizer
has its input at the distinguished merging point. No contact-family or sign
hypothesis remains in this statement. -/
theorem interior_cap_maximizer_distinguishedInput {lam s c d : ℝ}
    (hlam : lam ∈ Ioc (0 : ℝ) 1) (hm : IsCapMaximizer lam s c d)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hcd : c + d ≤ 1) : s = distinguishedInput c d := by
  have hs := (cap_maximizer_nondegenerate hlam hm).1
  have hk := normalized_cap_maximizer_slope_pos hlam hm hcd
  have hcdlt : c + d < 1 := by unfold k at hk; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hleft | hright
  · exact not_cap_maximizer_of_left_interior hlam hs hc hd hcdlt hleft hm
  · have hsflip : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hleft : 1 - s < distinguishedInput d c := by
      rw [distinguishedInput_swap hc hd]
      linarith
    exact not_cap_maximizer_of_left_interior hlam hsflip hd hc (by linarith) hleft hm.simultaneous_flip

end BinaryPairBound
