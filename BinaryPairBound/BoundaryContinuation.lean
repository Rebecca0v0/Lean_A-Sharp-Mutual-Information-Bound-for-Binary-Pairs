module

public import BinaryPairBound.BoundaryCoefficient
public import BinaryPairBound.InformationPerturbation

/-! # Interior continuation of a boundary coefficient (Appendix D) -/

noncomputable section
@[expose] public section

open Filter Set
open scoped Topology

namespace BinaryPairBound

def coefficientCoords (s qv kv : ℝ) : ℝ :=
  S s (qv - kv * s) (1 - qv - kv * (1 - s))

lemma k_coords (s qv kv : ℝ) : k (qv - kv * s) (1 - qv - kv * (1 - s)) = kv := by
  unfold k
  ring

lemma q_coords (s qv kv x : ℝ) :
    q (qv - kv * s) (1 - qv - kv * (1 - s)) x = qv + kv * (x - s) := by
  unfold q
  rw [k_coords]
  ring

@[simp] lemma q_coords_self (s qv kv : ℝ) :
    q (qv - kv * s) (1 - qv - kv * (1 - s)) s = qv := by rw [q_coords]; ring

lemma valid_coords {s qv kv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (_hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s ≤ qv)
    (hk : kv ∈ Icc (0 : ℝ) ((1 - qv) / (1 - s))) :
    Valid s (qv - kv * s) (1 - qv - kv * (1 - s)) := by
  have hb : (1 - qv) / (1 - s) ≤ 1 := (div_le_one (sub_pos.mpr hs.2)).mpr (by linarith)
  have hk1 := hk.2.trans hb
  have hprod := (le_div_iff₀ (sub_pos.mpr hs.2)).mp hk.2
  have hks := mul_le_mul_of_nonneg_right hk1 hs.1.le
  have hks0 := mul_nonneg hk.1 hs.1.le
  have hk1s0 := mul_nonneg hk.1 (sub_pos.mpr hs.2).le
  exact ⟨⟨hs.1.le, hs.2.le⟩, ⟨by nlinarith, by linarith [_hq.2]⟩,
    ⟨by linarith, by linarith [_hq.1]⟩⟩

lemma nondegenerate_coords {s qv kv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo (0 : ℝ) 1) :
    Nondegenerate s (qv - kv * s) (1 - qv - kv * (1 - s)) := by
  exact ⟨hs, by simpa only [q_coords_self] using hq⟩

lemma convexOn_D_left (y : ℝ) : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun x => D x y) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz a b ha hb hab
  have hH := Real.strictConcave_binEntropy.concaveOn.2 hx hz ha hb hab
  simp only [smul_eq_mul] at hH ⊢
  unfold D
  dsimp [H] at hH ⊢
  have he : Real.log (1 - y) * (a + b - 1) = 0 := by rw [hab]; ring
  nlinarith

lemma D_mix_lt {x y t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (hxy : x ≠ y) :
    D ((1 - t) * y + t * x) y < D x y := by
  have h := (convexOn_D_left y).2 ⟨hy.1.le, hy.2.le⟩ hx
    (sub_pos.mpr ht.2).le ht.1 (by ring)
  simp only [smul_eq_mul, D_self, mul_zero, zero_add] at h
  exact h.trans_lt (by nlinarith [D_pos hx hy hxy, ht.2])

lemma extendedRatio_coords_lt {s qv k₁ k₂ x : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s ≤ qv)
    (hk₁ : k₁ ∈ Icc (0 : ℝ) ((1 - qv) / (1 - s)))
    (hk₂ : k₂ ∈ Icc (0 : ℝ) ((1 - qv) / (1 - s))) (hkk : k₁ < k₂)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    extendedRatio s (qv - k₁ * s) (1 - qv - k₁ * (1 - s)) x <
      extendedRatio s (qv - k₂ * s) (1 - qv - k₂ * (1 - s)) x := by
  have hk₂pos : 0 < k₂ := hk₁.1.trans_lt hkk
  by_cases hxs : x = s
  · subst x
    simp only [extendedRatio_self, rhoSquared, k_coords, q_coords_self]
    apply (div_lt_div_iff_of_pos_right (mul_pos hq.1 (sub_pos.mpr hq.2))).mpr
    apply mul_lt_mul_of_pos_right _ (sub_pos.mpr hs.2)
    apply mul_lt_mul_of_pos_right _ hs.1
    nlinarith [mul_pos (sub_pos.mpr hkk) (show 0 < k₂ + k₁ by linarith [hk₁.1])]
  · simp only [extendedRatio_of_ne hxs, q_coords, sub_self, mul_zero, add_zero]
    apply (div_lt_div_iff_of_pos_right (D_pos hx hs hxs)).mpr
    have hv₂ := valid_coords hs hq hsq hk₂
    have hy₂ : qv + k₂ * (x - s) ∈ Icc (0 : ℝ) 1 := by
      simpa only [q_coords] using q_mem_Icc _ _ x hv₂.2.1 hv₂.2.2 hx
    have hne : qv + k₂ * (x - s) ≠ qv := by
      intro he
      have hm : k₂ * (x - s) = 0 := by linarith
      exact hxs (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt hk₂pos)))
    have ht : k₁ / k₂ ∈ Ico (0 : ℝ) 1 :=
      ⟨div_nonneg hk₁.1 hk₂pos.le, (div_lt_one hk₂pos).mpr hkk⟩
    have hmix := D_mix_lt hy₂ hq ht hne
    have heq : (1 - k₁ / k₂) * qv + k₁ / k₂ * (qv + k₂ * (x - s)) =
        qv + k₁ * (x - s) := by field_simp; ring
    simpa only [heq] using hmix

theorem coefficientCoords_strictMonoOn {s qv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s ≤ qv) :
    StrictMonoOn (coefficientCoords s qv) (Icc (0 : ℝ) ((1 - qv) / (1 - s))) := by
  intro k₁ hk₁ k₂ hk₂ hkk
  obtain ⟨x, hx, heq⟩ := exists_extendedRatio_eq_S (valid_coords hs hq hsq hk₁)
    (nondegenerate_coords hs hq)
  change S _ _ _ < S _ _ _
  rw [← heq]
  exact (extendedRatio_coords_lt hs hq hsq hk₁ hk₂ hkk hx).trans_le
    (extendedRatio_le_S (valid_coords hs hq hsq hk₂) (nondegenerate_coords hs hq) hx)

theorem continuousWithinAt_S_comp {α : Type*} [TopologicalSpace α]
    {s c d : α → ℝ} {a : α} {T : Set α} (ha : a ∈ T)
    (hs : ContinuousWithinAt s T a) (hc : ContinuousWithinAt c T a)
    (hd : ContinuousWithinAt d T a) (hv : ∀ t ∈ T, Valid (s t) (c t) (d t))
    (hn : Nondegenerate (s a) (c a) (d a)) :
    ContinuousWithinAt (fun t => S (s t) (c t) (d t)) T a := by
  let p : T → Parameters := fun t =>
    (⟨s t, (hv t t.property).1⟩, ⟨c t, (hv t t.property).2.1⟩, ⟨d t, (hv t t.property).2.2⟩)
  have hst := (continuousWithinAt_iff_continuousAt_domRestrict s ha).mp hs
  have hct := (continuousWithinAt_iff_continuousAt_domRestrict c ha).mp hc
  have hdt := (continuousWithinAt_iff_continuousAt_domRestrict d ha).mp hd
  have hp : ContinuousAt p ⟨a, ha⟩ := by
    exact (hst.codRestrict (fun t : T => (hv t t.property).1)).prodMk
      ((hct.codRestrict (fun t : T => (hv t t.property).2.1)).prodMk
        (hdt.codRestrict (fun t : T => (hv t t.property).2.2)))
  exact (continuousWithinAt_iff_continuousAt_domRestrict _ ha).mpr
    ((continuousAt_parameterCoefficient (p := p ⟨a, ha⟩) hn).comp hp)

theorem continuousOn_coefficientCoords_k {s qv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s ≤ qv) :
    ContinuousOn (coefficientCoords s qv) (Icc (0 : ℝ) ((1 - qv) / (1 - s))) := by
  intro kv hk
  apply continuousWithinAt_S_comp hk
  · exact continuousWithinAt_const
  · fun_prop
  · fun_prop
  · exact fun _ hk => valid_coords hs hq hsq hk
  · exact nondegenerate_coords hs hq

@[simp] theorem coefficientCoords_zero (s qv : ℝ) : coefficientCoords s qv 0 = 0 := by
  unfold coefficientCoords
  apply S_eq_zero_of_independent
  right; right
  ring

theorem coefficientCoords_boundary {s qv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s < qv) :
    coefficientCoords s qv ((1 - qv) / (1 - s)) = Real.log qv / Real.log s := by
  have hs1 : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs.2)
  have hd : 1 - qv - (1 - qv) / (1 - s) * (1 - s) = 0 := by field_simp; ring
  have hc : qv - (1 - qv) / (1 - s) * s = (qv - s) / (1 - s) := by field_simp; ring
  have hci : (qv - s) / (1 - s) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hsq) (sub_pos.mpr hs.2),
      (div_lt_one (sub_pos.mpr hs.2)).mpr (by linarith [hq.2])⟩
  have hqs := q_coords_self s qv ((1 - qv) / (1 - s))
  rw [hd, hc] at hqs
  unfold coefficientCoords
  rw [hd, hc, S_zero_right hs hci, hqs]

/-- Every lower output marginal admits one and only one interior positive
slope with the original boundary coefficient. -/
theorem existsUnique_boundary_continuation {s c qv : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo s (q c 0 s)) :
    ∃! kv, kv ∈ Ioo (0 : ℝ) ((1 - qv) / (1 - s)) ∧
      coefficientCoords s qv kv = S s c 0 := by
  have hq₀ := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
  have hqi : qv ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans hq.1, hq.2.trans hq₀.2⟩
  have hb : 0 < (1 - qv) / (1 - s) := div_pos (sub_pos.mpr hqi.2) (sub_pos.mpr hs.2)
  have hlam := S_zero_right_mem_Ioo hs hc
  have htop : S s c 0 < coefficientCoords s qv ((1 - qv) / (1 - s)) := by
    rw [coefficientCoords_boundary hs hqi hq.1, S_zero_right hs hc]
    exact (div_lt_div_right_of_neg (Real.log_neg hs.1 hs.2)).mpr
      (Real.log_lt_log hqi.1 hq.2)
  obtain ⟨kv, hk, heq⟩ := intermediate_value_Icc hb.le
    (continuousOn_coefficientCoords_k hs hqi hq.1.le)
    (show S s c 0 ∈ Icc (coefficientCoords s qv 0)
      (coefficientCoords s qv ((1 - qv) / (1 - s))) by simpa using And.intro hlam.1.le htop.le)
  have hki : kv ∈ Ioo (0 : ℝ) ((1 - qv) / (1 - s)) := by
    constructor
    · apply lt_of_le_of_ne hk.1
      intro he
      rw [← he, coefficientCoords_zero] at heq
      exact (ne_of_gt hlam.1) heq.symm
    · apply lt_of_le_of_ne hk.2
      intro he
      rw [he] at heq
      exact (ne_of_lt htop) heq.symm
  refine ⟨kv, ⟨hki, heq⟩, ?_⟩
  intro kv' hk'
  exact (coefficientCoords_strictMonoOn hs hqi hq.1.le).injOn
    ⟨hk'.1.1.le, hk'.1.2.le⟩ hk (hk'.2.trans heq.symm)

lemma interior_coords {s qv kv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (_hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s ≤ qv)
    (hk : kv ∈ Ico (0 : ℝ) ((1 - qv) / (1 - s))) :
    (qv - kv * s) ∈ Ioo (0 : ℝ) 1 ∧
      (1 - qv - kv * (1 - s)) ∈ Ioo (0 : ℝ) 1 := by
  have hb : (1 - qv) / (1 - s) ≤ 1 := (div_le_one (sub_pos.mpr hs.2)).mpr (by linarith)
  have hk1 := hk.2.trans_le hb
  have hks := mul_lt_mul_of_pos_right hk1 hs.1
  have hksp := mul_nonneg hk.1 hs.1.le
  have hkp := mul_nonneg hk.1 (sub_pos.mpr hs.2).le
  have hprod := (lt_div_iff₀ (sub_pos.mpr hs.2)).mp hk.2
  exact ⟨⟨by nlinarith, by linarith [_hq.2]⟩, ⟨by linarith, by linarith [_hq.1]⟩⟩

theorem continuousAt_coefficientCoords_q {s qv kv : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s ≤ qv)
    (hk : kv ∈ Ico (0 : ℝ) ((1 - qv) / (1 - s))) :
    ContinuousAt (fun z => coefficientCoords s z kv) qv := by
  obtain ⟨hc, hd⟩ := interior_coords hs hq hsq hk
  have hcc : ContinuousAt (fun z : ℝ => z - kv * s) qv := by fun_prop
  have hdc : ContinuousAt (fun z : ℝ => 1 - z - kv * (1 - s)) qv := by fun_prop
  apply continuousAt_S_comp continuousAt_const hcc hdc
  · filter_upwards [hcc (Ioo_mem_nhds hc.1 hc.2), hdc (Ioo_mem_nhds hd.1 hd.2)] with z hcz hdz
    exact ⟨⟨hs.1.le, hs.2.le⟩, ⟨hcz.1.le, hcz.2.le⟩, ⟨hdz.1.le, hdz.2.le⟩⟩
  · exact nondegenerate_coords hs hq

/-- Any of the unique interior solutions converges back to the original
boundary slope as the output marginal increases to its boundary value. -/
theorem tendsto_boundary_continuation_slope {s c : ℝ} {kf : ℝ → ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hpath : ∀ qv ∈ Ioo s (q c 0 s),
      kf qv ∈ Ioo (0 : ℝ) ((1 - qv) / (1 - s)) ∧ coefficientCoords s qv (kf qv) = S s c 0) :
    Tendsto kf (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds (1 - c)) := by
  have hq₀ := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
  have hsq₀ : s < q c 0 s := by
    have hm := mul_pos hc.1 (sub_pos.mpr hs.2)
    dsimp [q, k]
    nlinarith
  have hB : (1 - q c 0 s) / (1 - s) = 1 - c := by
    have hsn : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs.2)
    field_simp
    unfold q k
    ring
  have hboundary : coefficientCoords s (q c 0 s) (1 - c) = S s c 0 := by
    unfold coefficientCoords
    congr 1 <;> unfold q k <;> ring
  have hdomain : ∀ᶠ qv in nhdsWithin (q c 0 s) (Iio (q c 0 s)), qv ∈ Ioo s (q c 0 s) :=
    Ioo_mem_nhdsLT hsq₀
  have hboundlim : Tendsto (fun z : ℝ => (1 - z) / (1 - s))
      (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds (1 - c)) := by
    have hcont : ContinuousAt (fun z : ℝ => (1 - z) / (1 - s)) (q c 0 s) := by fun_prop
    simpa only [hB] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [hdomain] with qv hqv
      exact ha0.trans (hpath qv hqv).1.1
    · have ha0' : 0 ≤ a := le_of_not_gt ha0
      have hak : a ∈ Ico (0 : ℝ) ((1 - q c 0 s) / (1 - s)) := by
        rw [hB]
        exact ⟨ha0', ha⟩
      have halt : coefficientCoords s (q c 0 s) a < S s c 0 := by
        rw [← hboundary]
        apply coefficientCoords_strictMonoOn hs hq₀ hsq₀.le ⟨hak.1, hak.2.le⟩
          (by rw [hB]; exact ⟨(sub_pos.mpr hc.2).le, le_rfl⟩) ha
      have he : ∀ᶠ qv in nhdsWithin (q c 0 s) (Iio (q c 0 s)), coefficientCoords s qv a < S s c 0 :=
        (continuousAt_coefficientCoords_q hs hq₀ hsq₀.le hak).continuousWithinAt (Iio_mem_nhds halt)
      filter_upwards [hdomain, he] with qv hqv hqa
      have hqi : qv ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans hqv.1, hqv.2.trans hq₀.2⟩
      have hBlt : 1 - c < (1 - qv) / (1 - s) := by
        rw [← hB]
        exact div_lt_div_of_pos_right (by linarith [hqv.2]) (sub_pos.mpr hs.2)
      obtain ⟨hkf, heq⟩ := hpath qv hqv
      apply lt_of_not_ge
      intro hle
      have hh := (coefficientCoords_strictMonoOn hs hqi hqv.1.le).monotoneOn
        ⟨hkf.1.le, hkf.2.le⟩ ⟨ha0', (ha.trans hBlt).le⟩ hle
      rw [heq] at hh
      exact (not_le_of_gt hqa) hh
  · intro b hb
    have he := hboundlim (Iio_mem_nhds hb)
    filter_upwards [hdomain, he] with qv hqv hqb
    exact (hpath qv hqv).1.2.trans hqb

/-- The unique positive interior slope preserving the boundary coefficient. -/
def boundaryContinuationSlope (s c qv : ℝ) : ℝ := by
  classical
  exact if h : ∃ kv, kv ∈ Ioo (0 : ℝ) ((1 - qv) / (1 - s)) ∧
      coefficientCoords s qv kv = S s c 0 then h.choose else 0

theorem boundaryContinuationSlope_spec {s c qv : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hq : qv ∈ Ioo s (q c 0 s)) :
    boundaryContinuationSlope s c qv ∈ Ioo (0 : ℝ) ((1 - qv) / (1 - s)) ∧
      coefficientCoords s qv (boundaryContinuationSlope s c qv) = S s c 0 := by
  classical
  have he := (existsUnique_boundary_continuation hs hc hq).exists
  simpa only [boundaryContinuationSlope, dite_eq_left he] using he.choose_spec

theorem tendsto_boundaryContinuationSlope {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    Tendsto (boundaryContinuationSlope s c) (nhdsWithin (q c 0 s) (Iio (q c 0 s)))
      (nhds (1 - c)) :=
  tendsto_boundary_continuation_slope hs hc (fun _ hq => boundaryContinuationSlope_spec hs hc hq)

theorem tendsto_boundaryContinuation_channel {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun qv => qv - boundaryContinuationSlope s c qv * s)
        (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds c) ∧
      Tendsto (fun qv => 1 - qv - boundaryContinuationSlope s c qv * (1 - s))
        (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds 0) := by
  have hk := tendsto_boundaryContinuationSlope hs hc
  constructor
  · have he : q c 0 s - (1 - c) * s = c := by unfold q k; ring
    have hlim : Tendsto (fun qv => qv - boundaryContinuationSlope s c qv * s)
        (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds (q c 0 s - (1 - c) * s)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).sub (hk.mul_const s)
    simpa only [he] using hlim
  · have he : 1 - q c 0 s - (1 - c) * (1 - s) = 0 := by unfold q k; ring
    have hlim : Tendsto (fun qv => 1 - qv - boundaryContinuationSlope s c qv * (1 - s))
        (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds (1 - q c 0 s - (1 - c) * (1 - s))) :=
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).sub (hk.mul_const (1 - s))
    simpa only [he] using hlim

private theorem continuousAt_slope_selection {s qv lam : ℝ} {kf : ℝ → ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hq : qv ∈ Ioo (0 : ℝ) 1) (hsq : s < qv)
    (hk₀ : kf qv ∈ Ioo (0 : ℝ) ((1 - qv) / (1 - s)))
    (he₀ : coefficientCoords s qv (kf qv) = lam)
    (hpath : ∀ᶠ z in nhds qv, z ∈ Ioo s 1 ∧
      kf z ∈ Ioo (0 : ℝ) ((1 - z) / (1 - s)) ∧ coefficientCoords s z (kf z) = lam) :
    ContinuousAt kf qv := by
  have hB : ContinuousAt (fun z : ℝ => (1 - z) / (1 - s)) qv := by fun_prop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [hpath] with z hz
      exact ha0.trans hz.2.1.1
    · have ha0' := le_of_not_gt ha0
      have hak : a ∈ Ico (0 : ℝ) ((1 - qv) / (1 - s)) := ⟨ha0', ha.trans hk₀.2⟩
      have halt : coefficientCoords s qv a < lam := by
        rw [← he₀]
        exact coefficientCoords_strictMonoOn hs hq hsq.le
          ⟨hak.1, hak.2.le⟩ ⟨hk₀.1.le, hk₀.2.le⟩ ha
      have he : ∀ᶠ z in nhds qv, coefficientCoords s z a < lam :=
        (continuousAt_coefficientCoords_q hs hq hsq.le hak) (Iio_mem_nhds halt)
      have hbe : ∀ᶠ z in nhds qv, a < (1 - z) / (1 - s) := hB (Ioi_mem_nhds hak.2)
      filter_upwards [hpath, he, hbe] with z hz hez hbz
      apply lt_of_not_ge
      intro hle
      have hh := (coefficientCoords_strictMonoOn hs ⟨hs.1.trans hz.1.1, hz.1.2⟩ hz.1.1.le).monotoneOn
        ⟨hz.2.1.1.le, hz.2.1.2.le⟩ ⟨ha0', hbz.le⟩ hle
      rw [hz.2.2] at hh
      exact (not_le_of_gt hez) hh
  · intro b hb
    obtain ⟨r, hkr, hrmin⟩ := exists_between (lt_min hb hk₀.2)
    have hrb := (lt_min_iff.mp hrmin).1
    have hrB := (lt_min_iff.mp hrmin).2
    have hr0 := hk₀.1.trans hkr
    have hrk : r ∈ Ico (0 : ℝ) ((1 - qv) / (1 - s)) := ⟨hr0.le, hrB⟩
    have hrlt : lam < coefficientCoords s qv r := by
      rw [← he₀]
      exact coefficientCoords_strictMonoOn hs hq hsq.le
        ⟨hk₀.1.le, hk₀.2.le⟩ ⟨hr0.le, hrB.le⟩ hkr
    have he : ∀ᶠ z in nhds qv, lam < coefficientCoords s z r :=
      (continuousAt_coefficientCoords_q hs hq hsq.le hrk) (Ioi_mem_nhds hrlt)
    have hbe : ∀ᶠ z in nhds qv, r < (1 - z) / (1 - s) := hB (Ioi_mem_nhds hrB)
    filter_upwards [hpath, he, hbe] with z hz hez hbz
    have hkzr : kf z < r := by
      apply lt_of_not_ge
      intro hle
      have hh := (coefficientCoords_strictMonoOn hs ⟨hs.1.trans hz.1.1, hz.1.2⟩ hz.1.1.le).monotoneOn
        ⟨hr0.le, hbz.le⟩ ⟨hz.2.1.1.le, hz.2.1.2.le⟩ hle
      rw [hz.2.2] at hh
      exact (not_le_of_gt hez) hh
    exact hkzr.trans hrb

theorem continuousOn_boundaryContinuationSlope {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (boundaryContinuationSlope s c) (Ioo s (q c 0 s)) := by
  intro qv hqv
  have hq₀ := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
  obtain ⟨hkv, heq⟩ := boundaryContinuationSlope_spec hs hc hqv
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_slope_selection hs ⟨hs.1.trans hqv.1, hqv.2.trans hq₀.2⟩ hqv.1 hkv heq
  filter_upwards [Ioo_mem_nhds hqv.1 hqv.2] with z hz
  exact ⟨⟨hz.1, hz.2.trans hq₀.2⟩, boundaryContinuationSlope_spec hs hc hz⟩

theorem tendsto_distinguishedInput_boundaryContinuation {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun qv => distinguishedInput
      (qv - boundaryContinuationSlope s c qv * s)
      (1 - qv - boundaryContinuationSlope s c qv * (1 - s)))
      (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds 1) := by
  obtain ⟨hC, hD⟩ := tendsto_boundaryContinuation_channel hs hc
  have hA := (hC.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hC)).sqrt
  have hB := (hD.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hD)).sqrt
  have hpos : 0 < Real.sqrt (c * (1 - c)) := Real.sqrt_pos.mpr (mul_pos hc.1 (sub_pos.mpr hc.2))
  have hden : Real.sqrt (c * (1 - c)) + Real.sqrt (0 * (1 - (0 : ℝ))) ≠ 0 := by
    simpa only [zero_mul, Real.sqrt_zero, add_zero] using ne_of_gt hpos
  have hh := hA.div (hA.add hB) hden
  simp only [zero_mul, Real.sqrt_zero, add_zero, div_self (ne_of_gt hpos)] at hh
  convert! hh using 1

/-- Near the boundary, the continuous fixed-coefficient path lies in the
interior, has `c > d`, and places the reference input below its distinguished input. -/
theorem boundaryContinuation_eventually {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ qv in nhdsWithin (q c 0 s) (Iio (q c 0 s)),
      let cv := qv - boundaryContinuationSlope s c qv * s
      let dv := 1 - qv - boundaryContinuationSlope s c qv * (1 - s)
      cv ∈ Ioo (0 : ℝ) 1 ∧ dv ∈ Ioo (0 : ℝ) 1 ∧ dv < cv ∧
        s < distinguishedInput cv dv ∧ S s cv dv = S s c 0 := by
  have hq₀ := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
  have hsq₀ : s < q c 0 s := by
    have hm := mul_pos hc.1 (sub_pos.mpr hs.2)
    dsimp [q, k]
    nlinarith
  obtain ⟨hC, hD⟩ := tendsto_boundaryContinuation_channel hs hc
  have hdiff : Tendsto (fun qv => (qv - boundaryContinuationSlope s c qv * s) -
      (1 - qv - boundaryContinuationSlope s c qv * (1 - s)))
      (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds c) := by
    simpa only [sub_zero] using hC.sub hD
  have hdifference := hdiff (Ioi_mem_nhds hc.1)
  have hdist := tendsto_distinguishedInput_boundaryContinuation hs hc (Ioi_mem_nhds hs.2)
  filter_upwards [Ioo_mem_nhdsLT hsq₀, hdifference, hdist] with qv hqv hdiffq hdistq
  obtain ⟨hk, heq⟩ := boundaryContinuationSlope_spec hs hc hqv
  obtain ⟨hci, hdi⟩ := interior_coords hs ⟨hs.1.trans hqv.1, hqv.2.trans hq₀.2⟩ hqv.1.le ⟨hk.1.le, hk.2⟩
  exact ⟨hci, hdi, sub_pos.mp hdiffq, hdistq, heq⟩

theorem tendsto_informationCoords_boundaryContinuation {s c : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun qv => informationCoords s qv (boundaryContinuationSlope s c qv))
      (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds (J s c 0)) := by
  have hcont : Continuous (fun p : ℝ × ℝ => informationCoords s p.1 p.2) := by
    unfold informationCoords H
    fun_prop
  have hpair : Tendsto (fun qv => (qv, boundaryContinuationSlope s c qv))
      (nhdsWithin (q c 0 s) (Iio (q c 0 s))) (nhds (q c 0 s, 1 - c)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds (tendsto_boundaryContinuationSlope hs hc)
  have he : informationCoords s (q c 0 s) (1 - c) = J s c 0 := by
    simpa only [k, sub_zero] using informationCoords_channel s c 0
  have hh := (hcont.tendsto (q c 0 s, 1 - c)).comp hpair
  simp only [he] at hh
  convert! hh using 1

end BinaryPairBound
