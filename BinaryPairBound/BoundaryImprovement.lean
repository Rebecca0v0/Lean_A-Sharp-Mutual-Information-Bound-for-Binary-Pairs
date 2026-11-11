module

public import BinaryPairBound.BoundaryContinuation
public import BinaryPairBound.ContactSigns
public import BinaryPairBound.ContactFamily
public import BinaryPairBound.InteriorMaximizer

/-! # Strict improvement of a nontrivial boundary channel (Section 6) -/

noncomputable section
public section

open Filter Set
open scoped Topology

namespace BinaryPairBound

/-- A function with a strictly negative derivative stays strictly above its
finite limit at the right endpoint. -/
theorem limit_lt_of_deriv_neg {f : ℝ → ℝ} {a b x L : ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, deriv f t < 0)
    (hl : Tendsto f (nhdsWithin b (Iio b)) (nhds L))
    (hx : x ∈ Ioo a b) : L < f x := by
  have hm : StrictAntiOn f (Ioo a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo a b) hf
    intro t ht
    exact hd t (by simpa only [interior_Ioo] using ht)
  obtain ⟨t, hxt, htb⟩ := exists_between hx.2
  have ht : t ∈ Ioo a b := ⟨hx.1.trans hxt, htb⟩
  have hle : L ≤ f t := by
    apply le_of_tendsto hl
    have hgt0 : ∀ᶠ z in nhds b, t < z := Ioi_mem_nhds htb
    have hgt : ∀ᶠ z in nhdsWithin b (Iio b), t < z := hgt0.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hgt] with z hzb htz
    exact (hm ht ⟨ht.1.trans htz, hzb⟩ htz).le
  exact hle.trans_lt (hm hx ht hxt)

/-- The chosen fixed-coefficient boundary continuation is locally the smooth
implicit contact family, so the strict output-direction sign applies to it. -/
theorem boundaryContinuation_information_deriv_neg {s c qv : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hqv : qv ∈ Ioo s (q c 0 s))
    (hci : qv - boundaryContinuationSlope s c qv * s ∈ Ioo (0 : ℝ) 1)
    (hdi : 1 - qv - boundaryContinuationSlope s c qv * (1 - s) ∈ Ioo (0 : ℝ) 1)
    (hdc : 1 - qv - boundaryContinuationSlope s c qv * (1 - s) ≤
      qv - boundaryContinuationSlope s c qv * s)
    (hss : s < distinguishedInput (qv - boundaryContinuationSlope s c qv * s)
      (1 - qv - boundaryContinuationSlope s c qv * (1 - s))) :
    deriv (fun z => informationCoords s z (boundaryContinuationSlope s c z)) qv < 0 := by
  let cv := qv - boundaryContinuationSlope s c qv * s
  let dv := 1 - qv - boundaryContinuationSlope s c qv * (1 - s)
  obtain ⟨hkv, hS⟩ := boundaryContinuationSlope_spec hs hc hqv
  have hv : Valid s cv dv := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hci.1.le, hci.2.le⟩, ⟨hdi.1.le, hdi.2.le⟩⟩
  have hn : Nondegenerate s cv dv := ⟨hs, q_mem_Ioo_of_channel hci hdi hv.1⟩
  have hcd : cv + dv < 1 := by dsimp [cv, dv]; nlinarith [hkv.1]
  have hqbase : q cv dv s = qv := q_coords_self s qv (boundaryContinuationSlope s c qv)
  have hkbase0 : k cv dv = boundaryContinuationSlope s c qv := k_coords s qv (boundaryContinuationSlope s c qv)
  have hlam : S s cv dv < eta cv dv :=
    S_lt_eta_of_ne_distinguishedInput hs hci hdi (ne_of_lt hcd) (ne_of_lt hss)
  have hcap := klCap_S hv hn
  obtain ⟨r, hr, hsr, hcontact⟩ := exists_right_interior_contact hs hci hdi (ne_of_lt hcd) hss
  obtain ⟨f, hf, hbase, hfeas⟩ := exists_feasible_contact_family hs hr hci hdi hcd hlam hsr hcap hcontact
  let kf : ℝ → ℝ := fun z => (f (s, z)).1
  let rf : ℝ → ℝ := fun z => (f (s, z)).2
  have hcurve : DifferentiableAt ℝ (fun z : ℝ => f (s, z)) (q cv dv s) :=
    (hf.differentiableAt (by norm_num)).comp _ ((differentiableAt_const s).prodMk differentiableAt_id)
  have hkf : DifferentiableAt ℝ kf (q cv dv s) := hcurve.fst
  have hrf : DifferentiableAt ℝ rf (q cv dv s) := hcurve.snd
  have hkbase : kf (q cv dv s) = k cv dv := congrArg Prod.fst hbase
  have hrbase : rf (q cv dv s) = r := congrArg Prod.snd hbase
  have hmap : ContinuousAt (fun z : ℝ => (s, z)) (q cv dv s) := by fun_prop
  have hFt : ∀ᶠ z in nhds (q cv dv s),
      contactGap (S s cv dv) s z (kf z) (rf z) = 0 ∧
      contactSlope (S s cv dv) s z (kf z) (rf z) = 0 ∧
      Valid s (z - kf z * s) (1 - z - kf z * (1 - s)) ∧
      S s (z - kf z * s) (1 - z - kf z * (1 - s)) = S s cv dv := hmap hfeas
  have hG : ∀ᶠ z in nhds (q cv dv s), contactGap (S s cv dv) s z (kf z) (rf z) = 0 :=
    hFt.mono (fun _ hz => hz.1)
  have hneg := informationCoords_supporting_output_curve_deriv_neg hkf.hasDerivAt hrf.hasDerivAt
    hkbase hrbase hs hr hci hdi hcd hdc hlam hsr hcap hcontact hG
  have hkfpos : ∀ᶠ z in nhds (q cv dv s), 0 < kf z := by
    apply hkf.continuousAt
    rw [hkbase, hkbase0]
    exact Ioi_mem_nhds hkv.1
  rw [hqbase] at hFt hkfpos hneg
  have heq : kf =ᶠ[nhds qv] boundaryContinuationSlope s c := by
    filter_upwards [hFt, hkfpos, Ioo_mem_nhds hqv.1 hqv.2] with z hz hkz hzi
    obtain ⟨hzk, hzS⟩ := boundaryContinuationSlope_spec hs hc hzi
    have hq₀ := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
    have hzi' : z ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans hzi.1, hzi.2.trans hq₀.2⟩
    have hkzB : kf z ≤ (1 - z) / (1 - s) := by
      apply (le_div_iff₀ (sub_pos.mpr hs.2)).mpr
      linarith [hz.2.2.1.2.2.1]
    apply (coefficientCoords_strictMonoOn hs hzi' hzi.1.le).injOn
      ⟨hkz.le, hkzB⟩ ⟨hzk.1.le, hzk.2.le⟩
    exact hz.2.2.2.trans (hS.trans hzS.symm)
  have hinfo : (fun z => informationCoords s z (kf z)) =ᶠ[nhds qv]
      (fun z => informationCoords s z (boundaryContinuationSlope s c z)) :=
    heq.mono (fun z hz => congrArg (informationCoords s z) hz)
  rwa [hinfo.deriv_eq] at hneg

/-- Lemma 6.1: every nontrivial `d = 0` boundary channel has an interior
channel with the same contraction coefficient and strictly more information. -/
theorem boundary_improvement_zero_right {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ c' d', c' ∈ Ioo (0 : ℝ) 1 ∧ d' ∈ Ioo (0 : ℝ) 1 ∧ c' + d' < 1 ∧
      S s c' d' = S s c 0 ∧ J s c 0 < J s c' d' := by
  have hsq₀ : s < q c 0 s := by
    have hm := mul_pos hc.1 (sub_pos.mpr hs.2)
    dsimp [q, k]
    nlinarith
  let P : ℝ → Prop := fun qv =>
    qv ∈ Ioo s (q c 0 s) ∧
      let cv := qv - boundaryContinuationSlope s c qv * s
      let dv := 1 - qv - boundaryContinuationSlope s c qv * (1 - s)
      cv ∈ Ioo (0 : ℝ) 1 ∧ dv ∈ Ioo (0 : ℝ) 1 ∧ dv < cv ∧
        s < distinguishedInput cv dv ∧ S s cv dv = S s c 0
  have hgood : ∀ᶠ qv in nhdsWithin (q c 0 s) (Iio (q c 0 s)), P qv := by
    filter_upwards [Ioo_mem_nhdsLT hsq₀, boundaryContinuation_eventually hs hc] with qv hqv hgeo
    exact ⟨hqv, hgeo⟩
  obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hsq₀).mp hgood
  let F : ℝ → ℝ := fun qv => informationCoords s qv (boundaryContinuationSlope s c qv)
  have hcont : ContinuousOn F (Ioo s (q c 0 s)) := by
    have hkcont := continuousOn_boundaryContinuationSlope hs hc
    dsimp [F]
    unfold informationCoords H
    fun_prop
  have hder : ∀ qv ∈ Ioo a (q c 0 s), deriv F qv < 0 := by
    intro qv hqv
    obtain ⟨hqv', hci, hdi, hdc, hss, _⟩ := hsub hqv
    exact boundaryContinuation_information_deriv_neg hs hc hqv' hci hdi hdc.le hss
  obtain ⟨qv, haq, hqq₀⟩ := exists_between ha.2
  have hqi : qv ∈ Ioo a (q c 0 s) := ⟨haq, hqq₀⟩
  have hstrict := limit_lt_of_deriv_neg
    (hcont.mono (Ioo_subset_Ioo ha.1 le_rfl)) hder
    (tendsto_informationCoords_boundaryContinuation hs hc) hqi
  obtain ⟨hqv, hci, hdi, _, _, hS⟩ := hsub hqi
  have hkpos := (boundaryContinuationSlope_spec hs hc hqv).1.1
  refine ⟨qv - boundaryContinuationSlope s c qv * s,
    1 - qv - boundaryContinuationSlope s c qv * (1 - s), hci, hdi, ?_, hS, ?_⟩
  · nlinarith
  · simpa only [F, informationCoords_eq_J] using hstrict

end BinaryPairBound
