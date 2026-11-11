module

public import BinaryPairBound.JointRatioContinuity
public import BinaryPairBound.ContactEndpoints

/-! # The exact KL coefficient on a channel boundary (Appendix D) -/

noncomputable section
public section

open Filter Set
open scoped Topology

namespace BinaryPairBound

lemma q_zero_right_mem_Ioo {c x : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ico (0 : ℝ) 1) : q c 0 x ∈ Ioo (0 : ℝ) 1 := by
  have hk : 0 < 1 - c := sub_pos.mpr hc.2
  have hm := mul_nonneg hk.le hx.1
  have hm' := mul_pos hk (sub_pos.mpr hx.2)
  constructor <;> dsimp [q, k] <;> nlinarith [hc.1]

theorem rhoSquared_zero_right_strictMonoOn {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (rhoSquared c 0) (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro x hx
    exact (continuousAt_rhoSquared (q_zero_right_mem_Ioo hc ⟨hx.1.le, hx.2⟩)).continuousWithinAt
  · intro x hx
    have hxi : x ∈ Ioo (0 : ℝ) 1 := interior_subset hx
    have hqx := q_zero_right_mem_Ioo hc ⟨hxi.1.le, hxi.2⟩
    rw [(hasDerivAt_rhoSquared hqx).deriv]
    simp only [zero_mul, sub_zero]
    apply div_pos
    · exact mul_pos (sq_pos_of_pos (by simpa [k] using sub_pos.mpr hc.2))
        (mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (sq_pos_of_pos (sub_pos.mpr hxi.2)))
    · exact sq_pos_of_pos (mul_pos hqx.1 (sub_pos.mpr hqx.2))

/-- On a nontrivial one-sided channel, the local correlation is strictly
smaller than the distribution-dependent KL coefficient at every interior input. -/
theorem rhoSquared_lt_S_zero_right {s c : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) : rhoSquared c 0 s < S s c 0 := by
  have hv : Valid s c 0 := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, by simp⟩
  have hqs := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
  have hn : Nondegenerate s c 0 := ⟨hs, hqs⟩
  apply lt_of_le_of_ne (rhoSquared_le_S hv hn)
  intro heq
  let b := (s + 1) / 2
  have hsb : s < b := by dsimp [b]; linarith [hs.2]
  have hb : b ∈ Ioo (0 : ℝ) 1 := by constructor <;> dsimp [b] <;> linarith [hs.1, hs.2]
  have hconc : StrictConcaveOn ℝ (Icc s b) (entropyCurve (S s c 0) c 0) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) (continuous_entropyCurve _ _ _).continuousOn
    intro x hx
    have hxi : x ∈ Ioo s b := by simpa only [interior_Icc] using hx
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans hxi.1, hxi.2.trans hb.2⟩
    change deriv (deriv (entropyCurve (S s c 0) c 0)) x < 0
    rw [deriv2_entropyCurve hx01 (q_zero_right_mem_Ioo hc ⟨hx01.1.le, hx01.2⟩)]
    have hlt := rhoSquared_zero_right_strictMonoOn hc hs hx01 hxi.1
    rw [heq] at hlt
    exact div_neg_of_neg_of_pos (sub_neg.mpr hlt) (mul_pos hx01.1 (sub_pos.mpr hx01.2))
  have hsec := hconc.slope_lt_deriv ⟨le_rfl, hsb.le⟩ ⟨hsb.le, le_rfl⟩ hsb
    (hasDerivAt_entropyCurve (S s c 0) s c 0 hs hqs).differentiableAt
  rw [slope_def_field] at hsec
  have hstrict := (div_lt_iff₀ (sub_pos.mpr hsb)).mp hsec
  have hsupp := (S_le_iff_supporting_tangent hv hn).mp le_rfl b ⟨hb.1.le, hb.2.le⟩
  unfold tangent at hsupp
  linarith

private lemma S_le_of_interior_contact_zero_right {s c r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hcontact : entropyCurve (S s c 0) c 0 r = tangent (S s c 0) s c 0 r) :
    S r c 0 ≤ S s c 0 := by
  have hv : Valid s c 0 := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, by simp⟩
  have hn : Nondegenerate s c 0 := ⟨hs, q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩⟩
  have hnr : Nondegenerate r c 0 := ⟨hr, q_zero_right_mem_Ioo hc ⟨hr.1.le, hr.2⟩⟩
  have hsupp := (S_le_iff_supporting_tangent hv hn).mp le_rfl
  have hmin : IsLocalMin (fun x => entropyCurve (S s c 0) c 0 x - tangent (S s c 0) s c 0 x) r := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr (hsupp x ⟨hx.1.le, hx.2.le⟩)
  have hdv : deriv (entropyCurve (S s c 0) c 0) r = deriv (entropyCurve (S s c 0) c 0) s := by
    have hdiff := (hasDerivAt_entropyCurve (S s c 0) r c 0 hr hnr.2).differentiableAt.hasDerivAt
    exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hdiff.sub (hasDerivAt_tangent _ _ _ _ _)))
  have ht : tangent (S s c 0) r c 0 = tangent (S s c 0) s c 0 := by
    ext x
    unfold tangent at hcontact ⊢
    rw [hdv, hcontact]
    ring
  apply S_le_of_klCap hnr
  apply (klCap_iff_supporting_tangent hnr).mpr
  rw [ht]
  exact hsupp

/-- The supremum for a nontrivial `d = 0` channel is attained at the
deterministic test input `x = 1`. -/
theorem S_eq_ratio_one_zero_right {s c : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    S s c 0 = D (q c 0 1) (q c 0 s) / D 1 s := by
  have hv : Valid s c 0 := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, by simp⟩
  have hn : Nondegenerate s c 0 := ⟨hs, q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩⟩
  have hrho := rhoSquared_lt_S_zero_right hs hc
  have hSpos : 0 < S s c 0 := (rhoSquared_nonneg hv.1 hn.2).trans_lt hrho
  obtain ⟨r, hr, heq⟩ := exists_extendedRatio_eq_S hv hn
  have hrs : r ≠ s := by
    intro he
    rw [he, extendedRatio_self] at heq
    exact (ne_of_lt hrho) heq
  have hratio : D (q c 0 r) (q c 0 s) / D r s = S s c 0 := by
    simpa only [extendedRatio_of_ne hrs] using heq
  have hcontact : entropyCurve (S s c 0) c 0 r = tangent (S s c 0) s c 0 r := by
    have hgap := equation_4_1 (S s c 0) s c 0 r hn.1 hn.2
    have hm := (div_eq_iff (ne_of_gt (D_pos hr hs hrs))).mp hratio
    exact sub_eq_zero.mp (by linarith)
  have hr0 : r ≠ 0 := by
    intro he
    subst r
    exact (ne_of_lt (tangent_lt_entropyCurve_zero_of_left_interior hSpos hn hc
      (klCap_S hv hn))).symm hcontact
  have hr1 : r = 1 := by
    by_contra hne
    have hri : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), lt_of_le_of_ne hr.2 hne⟩
    have hSr := S_le_of_interior_contact_zero_right hs hc hri hcontact
    have hrhor : rhoSquared c 0 r < S s c 0 := (rhoSquared_lt_S_zero_right hri hc).trans_le hSr
    have hi : uIcc s r ⊆ Ioo (0 : ℝ) 1 := ordConnected_Ioo.uIcc_subset hs hri
    obtain ⟨y, hy, hyrho⟩ := exists_extendedRatio_eq_rhoSquared hi
      (fun y hy => q_zero_right_mem_Ioo hc ⟨(hi hy).1.le, (hi hy).2⟩)
    have hyle : rhoSquared c 0 y < S s c 0 := by
      rcases le_total s r with hsr | hrs'
      · have hyr : y ≤ r := (show y ∈ Icc s r by simpa only [uIcc_of_le hsr] using hy).2
        exact ((rhoSquared_zero_right_strictMonoOn hc).monotoneOn (hi hy) hri hyr).trans_lt hrhor
      · have hys : y ≤ s := (show y ∈ Icc r s by simpa only [uIcc_of_ge hrs'] using hy).2
        exact ((rhoSquared_zero_right_strictMonoOn hc).monotoneOn (hi hy) hs hys).trans_lt hrho
    rw [← hyrho, heq] at hyle
    exact (lt_irrefl _) hyle
  simpa only [hr1] using hratio.symm

/-- The exact boundary formula in Lemma D.1. -/
theorem S_zero_right {s c : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    S s c 0 = Real.log (q c 0 s) / Real.log s := by
  rw [S_eq_ratio_one_zero_right hs hc]
  have hq : q c 0 1 = 1 := by unfold q k; ring
  rw [hq]
  simp [D, H, Real.binEntropy_one]

theorem S_zero_right_mem_Ioo {s c : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) : S s c 0 ∈ Ioo (0 : ℝ) 1 := by
  have hq := q_zero_right_mem_Ioo hc ⟨hs.1.le, hs.2⟩
  have hsq : s < q c 0 s := by
    have hm := mul_pos hc.1 (sub_pos.mpr hs.2)
    dsimp [q, k]
    nlinarith
  rw [S_zero_right hs hc]
  constructor
  · exact div_pos_of_neg_of_neg (Real.log_neg hq.1 hq.2) (Real.log_neg hs.1 hs.2)
  · apply (div_lt_iff_of_neg (Real.log_neg hs.1 hs.2)).mpr
    simpa only [one_mul] using Real.log_lt_log hs.1 hsq

theorem S_zero_left {s d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hd : d ∈ Ioo (0 : ℝ) 1) :
    S s 0 d = Real.log (1 - q 0 d s) / Real.log (1 - s) := by
  rw [← S_simultaneous_flip s 0 d]
  rw [S_zero_right ⟨by linarith [hs.2], by linarith [hs.1]⟩ hd, q_swap_one_sub]

end BinaryPairBound
