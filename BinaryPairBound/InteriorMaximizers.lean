module

public import BinaryPairBound.MaximizerExistence
public import BinaryPairBound.CoefficientContinuity
public import BinaryPairBound.ContactFamilies
public import BinaryPairBound.ContactSigns
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Every interior maximizer has merging contacts

把约束取满、极大值处导数为零与严格导数符号结合，排除内部非合并极大值。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## An interior maximizer uses the full coefficient constraint

证明内部的极大值必须用满约束，即 S 等于指定的系数上界。
-/

public noncomputable section CapSaturation

/-- The cap-saturation step from Section 9. Interior transitions are explicit
hypotheses; excluding boundary maximizers is still a separate obligation. -/
theorem interior_cap_maximizer_saturates {lam s c d : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (hm : IsCapMaximizer lam s c d)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d ≤ 1) : S s c d = lam := by
  have hn := cap_maximizer_nondegenerate hlam hm
  have hk := normalized_cap_maximizer_slope_pos hlam hm hcd
  have hc0 : q c d s - k c d * s = c := by unfold q; ring
  have hd0 : 1 - q c d s - k c d * (1 - s) = d := by unfold q k; ring
  have hb0 : q c d s + k c d * (1 - s) = 1 - d := by unfold q k; ring
  by_contra hne
  have hlt := lt_of_le_of_ne hm.2.1 hne
  have hccont : ContinuousAt (fun t : ℝ => q c d s - t * s) (k c d) := by fun_prop
  have hdcont : ContinuousAt (fun t : ℝ => 1 - q c d s - t * (1 - s)) (k c d) := by fun_prop
  have hce : ∀ᶠ t in nhds (k c d), q c d s - t * s ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hccont
    simpa only [hc0] using Ioo_mem_nhds hc.1 hc.2
  have hde : ∀ᶠ t in nhds (k c d), 1 - q c d s - t * (1 - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hdcont
    simpa only [hd0] using Ioo_mem_nhds hd.1 hd.2
  have hvalid : ∀ᶠ t in nhds (k c d),
      Valid s (q c d s - t * s) (1 - q c d s - t * (1 - s)) := by
    filter_upwards [hce, hde] with t hct hdt
    exact ⟨hm.1.1, ⟨hct.1.le, hct.2.le⟩, ⟨hdt.1.le, hdt.2.le⟩⟩
  have hnpath : Nondegenerate s (q c d s - k c d * s)
      (1 - q c d s - k c d * (1 - s)) := by simpa only [hc0, hd0] using hn
  have hScont := continuousAt_S_comp continuousAt_const hccont hdcont hvalid hnpath
  have hfeas : ∀ᶠ t in nhds (k c d),
      S s (q c d s - t * s) (1 - q c d s - t * (1 - s)) < lam := by
    change ∀ᶠ t in nhds (k c d),
      S s (q c d s - t * s) (1 - q c d s - t * (1 - s)) ∈ Set.Iio lam
    apply hScont
    simpa only [hc0, hd0] using Iio_mem_nhds hlt
  have hmax : IsLocalMax (fun t => informationCoords s (q c d s) t) (k c d) := by
    filter_upwards [hvalid, hfeas] with t hvt hft
    rw [informationCoords_eq_J, informationCoords_channel]
    exact hm.2.2 s _ _ hvt hft.le
  have hpos : 0 < deriv (fun t => informationCoords s (q c d s) t) (k c d) := by
    apply informationCoords_deriv_k_pos hn.1 hk hn.2
    · simpa only [hc0] using hc
    · rw [hb0]
      constructor <;> linarith [hd.1, hd.2]
  rw [hmax.deriv_eq_zero] at hpos
  exact (lt_irrefl 0) hpos

end CapSaturation

/-! ## A maximizer has zero derivative along feasible variations

证明如果当前点已经使互信息最大，那么沿允许的光滑变化方向，其导数必须为零。
-/

public section MaximizerVariations

theorem IsCapMaximizer.simultaneous_flip {lam s c d : ℝ}
    (hm : IsCapMaximizer lam s c d) : IsCapMaximizer lam (1 - s) d c := by
  refine ⟨valid_simultaneous_flip hm.1, ?_, ?_⟩
  · simpa only [S_simultaneous_flip] using hm.2.1
  · intro s' c' d' hv hS
    simpa only [J_simultaneous_flip] using hm.2.2 s' c' d' hv hS

/-- Every feasible input-variation curve through a maximizer has zero
information derivative. Differentiability is not assumed for this necessary
condition: Lean's derivative is zero at a nondifferentiable local maximum. -/
theorem IsCapMaximizer.input_family_deriv_eq_zero {lam s c d : ℝ} {kf : ℝ → ℝ}
    (hm : IsCapMaximizer lam s c d) (hbase : kf s = k c d)
    (hfeas : ∀ᶠ t in nhds s,
      Valid t (q c d s - kf t * t) (1 - q c d s - kf t * (1 - t)) ∧
      S t (q c d s - kf t * t) (1 - q c d s - kf t * (1 - t)) ≤ lam) :
    deriv (fun t => informationCoords t (q c d s) (kf t)) s = 0 := by
  have hmax : IsLocalMax (fun t => informationCoords t (q c d s) (kf t)) s := by
    filter_upwards [hfeas] with t ht
    rw [hbase, informationCoords_channel, informationCoords_eq_J]
    exact hm.2.2 t _ _ ht.1 ht.2
  exact hmax.deriv_eq_zero

/-- Every feasible output-variation curve through a maximizer has zero
information derivative. -/
theorem IsCapMaximizer.output_family_deriv_eq_zero {lam s c d : ℝ} {kf : ℝ → ℝ}
    (hm : IsCapMaximizer lam s c d) (hbase : kf (q c d s) = k c d)
    (hfeas : ∀ᶠ t in nhds (q c d s),
      Valid s (t - kf t * s) (1 - t - kf t * (1 - s)) ∧
      S s (t - kf t * s) (1 - t - kf t * (1 - s)) ≤ lam) :
    deriv (fun t => informationCoords s t (kf t)) (q c d s) = 0 := by
  have hmax : IsLocalMax (fun t => informationCoords s t (kf t)) (q c d s) := by
    filter_upwards [hfeas] with t ht
    rw [hbase, informationCoords_channel, informationCoords_eq_J]
    exact hm.2.2 s _ _ ht.1 ht.2
  exact hmax.deriv_eq_zero

end MaximizerVariations

/-! ## Excluding distinct contacts at an interior maximizer

用严格导数与极大值处导数为零的矛盾，证明内部极大值只能位于特殊输入位置。
-/

public section InteriorMaximizer

open Set

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

end InteriorMaximizer

end BinaryPairBound
