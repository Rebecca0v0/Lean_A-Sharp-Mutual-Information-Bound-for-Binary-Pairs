module

public import BinaryPairBound.ContactGeometry
public import BinaryPairBound.RatioContinuity
public import BinaryPairBound.Symmetry

/-! # Supporting contacts cannot occur at deterministic test inputs -/

public section

open Filter Set
open scoped Topology

namespace BinaryPairBound

theorem tendsto_deriv_entropyCurve_zero_of_left_interior {lam c d : ℝ} (hlam : 0 < lam)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    Tendsto (deriv (entropyCurve lam c d)) (𝓝[>] 0) atBot := by
  have hq : ContinuousAt (q c d) 0 := (hasDerivAt_q c d 0).continuousAt
  have hqc : q c d 0 = c := by simp [q]
  have hA : ContinuousAt
      (fun x : ℝ => (Real.log (1 - q c d x) - Real.log (q c d x)) * k c d -
        lam * Real.log (1 - x)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.mul_const
      exact ((continuousAt_const.sub hq).log (by
        change 1 - q c d 0 ≠ 0
        rw [hqc]
        exact ne_of_gt (sub_pos.mpr hc.2))).sub
        (hq.log (by rw [hqc]; exact ne_of_gt hc.1))
    · exact ((continuousAt_const.sub continuousAt_id).log (by norm_num)).const_mul lam
  have hlim := (hA.tendsto.mono_left nhdsWithin_le_nhds).add_atBot
    (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hlam)
  have hqe : ∀ᶠ x in 𝓝[>] (0 : ℝ), q c d x ∈ Ioo (0 : ℝ) 1 :=
    hq.continuousWithinAt (Ioo_mem_nhds (by simpa only [hqc] using hc.1)
      (by simpa only [hqc] using hc.2))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hqe] with x hx hqx
  rw [deriv_entropyCurve lam x c d hx hqx]
  ring

theorem tendsto_deriv_entropyCurve_zero {lam c d : ℝ} (hlam : 0 < lam)
    (hc : c ∈ Ioo (0 : ℝ) 1) (_hd : d ∈ Ioo (0 : ℝ) 1) :
    Tendsto (deriv (entropyCurve lam c d)) (𝓝[>] 0) atBot :=
  tendsto_deriv_entropyCurve_zero_of_left_interior hlam hc

/-- Every affine lower bound is strictly below the curve at the left endpoint when
the entropy coefficient is positive. -/
theorem affine_lt_entropyCurve_zero_of_left_interior {lam c d A m : ℝ} (hlam : 0 < lam)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hsupp : ∀ x ∈ Icc (0 : ℝ) 1, A + m * x ≤ entropyCurve lam c d x) :
    A < entropyCurve lam c d 0 := by
  have hevent : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv (entropyCurve lam c d) x < m :=
    (tendsto_deriv_entropyCurve_zero_of_left_interior hlam hc).eventually (eventually_lt_atBot m)
  have hqe : ∀ᶠ x in 𝓝[>] (0 : ℝ), q c d x ∈ Ioo (0 : ℝ) 1 :=
    (hasDerivAt_q c d 0).continuousAt.continuousWithinAt
      (Ioo_mem_nhds (by simpa [q] using hc.1) (by simpa [q] using hc.2))
  obtain ⟨b, hb, hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset
    (show (0 : ℝ) < 1 by norm_num)).mp (hevent.and hqe)
  have hanti : StrictAntiOn (fun x => entropyCurve lam c d x - (A + m * x)) (Icc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact ((continuous_entropyCurve lam c d).sub
        (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) b := by simpa only [interior_Icc] using hx
      have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx'.1, hx'.2.trans_le hb.2⟩
      have hf := (hasDerivAt_entropyCurve lam x c d hx01
        (hsub hx').2).differentiableAt.hasDerivAt
      have haff : HasDerivAt (fun z : ℝ => A + m * z) m x := by
        convert! ((hasDerivAt_id x).const_mul m).const_add A using 1
        simp
      change deriv (entropyCurve lam c d - fun z => A + m * z) x < 0
      rw [(hf.sub haff).deriv]
      exact sub_neg.mpr (hsub hx').1
  have hstrict := hanti ⟨le_rfl, hb.1.le⟩ ⟨hb.1.le, le_rfl⟩ hb.1
  have hnonneg := hsupp b ⟨hb.1.le, hb.2⟩
  simp only [mul_zero, add_zero] at hstrict
  linarith

theorem affine_lt_entropyCurve_zero {lam c d A m : ℝ} (hlam : 0 < lam)
    (hc : c ∈ Ioo (0 : ℝ) 1) (_hd : d ∈ Ioo (0 : ℝ) 1)
    (hsupp : ∀ x ∈ Icc (0 : ℝ) 1, A + m * x ≤ entropyCurve lam c d x) :
    A < entropyCurve lam c d 0 :=
  affine_lt_entropyCurve_zero_of_left_interior hlam hc hsupp

/-- Left endpoint exclusion only needs the channel output at zero to be interior;
in particular this applies to the boundary channel `d = 0`. -/
theorem tangent_lt_entropyCurve_zero_of_left_interior {lam s c d : ℝ} (hlam : 0 < lam)
    (hn : Nondegenerate s c d) (hc : c ∈ Ioo (0 : ℝ) 1) (hcap : KLCap lam s c d) :
    tangent lam s c d 0 < entropyCurve lam c d 0 := by
  have hsupport := (klCap_iff_supporting_tangent hn).mp hcap
  have hsupp : ∀ x ∈ Icc (0 : ℝ) 1,
      (entropyCurve lam c d s - deriv (entropyCurve lam c d) s * s) +
        deriv (entropyCurve lam c d) s * x ≤ entropyCurve lam c d x := by
    intro x hx
    have hh := hsupport x hx
    unfold tangent at hh
    linarith
  have hh := affine_lt_entropyCurve_zero_of_left_interior hlam hc hsupp
  unfold tangent
  convert! hh using 1
  ring

lemma entropyCurve_swap_one_sub (lam c d x : ℝ) :
    entropyCurve lam d c (1 - x) = entropyCurve lam c d x := by
  simp only [entropyCurve, q_swap_one_sub, H, Real.binEntropy_one_sub]

lemma entropyCurve_swap (lam c d x : ℝ) :
    entropyCurve lam d c x = entropyCurve lam c d (1 - x) := by
  simpa only [sub_sub_cancel] using entropyCurve_swap_one_sub lam c d (1 - x)

theorem affine_lt_entropyCurve_one {lam c d A m : ℝ} (hlam : 0 < lam)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hsupp : ∀ x ∈ Icc (0 : ℝ) 1, A + m * x ≤ entropyCurve lam c d x) :
    A + m < entropyCurve lam c d 1 := by
  have hflip : ∀ x ∈ Icc (0 : ℝ) 1, (A + m) + (-m) * x ≤ entropyCurve lam d c x := by
    intro x hx
    rw [entropyCurve_swap]
    have hh := hsupp (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    linarith
  have hh := affine_lt_entropyCurve_zero hlam hd hc hflip
  rw [entropyCurve_swap lam c d 0, sub_zero] at hh
  exact hh

/-- All contacts of a supporting tangent are interior, even when the original
maximization was over the full closed probability interval. -/
theorem supporting_contact_mem_Ioo {lam s c d r : ℝ} (hlam : 0 < lam)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) : r ∈ Ioo (0 : ℝ) 1 := by
  let m := deriv (entropyCurve lam c d) s
  let A := entropyCurve lam c d s - m * s
  have hsupp : ∀ x ∈ Icc (0 : ℝ) 1, A + m * x ≤ entropyCurve lam c d x := by
    intro x hx
    have hh := (klCap_iff_supporting_tangent
      ⟨hs, q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩⟩).mp hcap x hx
    dsimp [A, m]
    unfold tangent at hh
    linarith
  have hz := affine_lt_entropyCurve_zero hlam hc hd hsupp
  have ho := affine_lt_entropyCurve_one hlam hc hd hsupp
  constructor
  · apply lt_of_le_of_ne hr.1
    intro he
    rw [← he] at hcontact
    dsimp [A, m] at hz
    unfold tangent at hcontact
    simp only [zero_sub, mul_neg] at hcontact
    linarith
  · apply lt_of_le_of_ne hr.2
    intro he
    rw [he] at hcontact
    dsimp [A, m] at ho
    unfold tangent at hcontact
    linarith

/-- For every nondistinguished interior input, the exact KL cap is realized by a
different interior input and the resulting supporting line is an actual bitangent. -/
theorem exists_distinct_interior_contact {s c d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hne : s ≠ distinguishedInput c d) :
    ∃ r ∈ Ioo (0 : ℝ) 1, r ≠ s ∧
      entropyCurve (S s c d) c d r = tangent (S s c d) s c d r ∧
      tangent (S s c d) r c d = tangent (S s c d) s c d ∧
      S r c d = S s c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  have hcap := klCap_S hv hn
  obtain ⟨r, hr, hrs, he⟩ := exists_testInput_eq_S hs hc hd hcd hne
  have he' := (div_eq_iff (ne_of_gt (D_pos hr hs hrs))).mp he
  have hgap := equation_4_1 (S s c d) s c d r hn.1 hn.2
  have hcontact : entropyCurve (S s c d) c d r = tangent (S s c d) s c d r := by linarith
  have hlam : 0 < S s c d := (rhoSquared_pos hc hd hcd hs).trans_le (rhoSquared_le_S hv hn)
  have hr' := supporting_contact_mem_Ioo hlam hs hc hd hr hcap hcontact
  exact ⟨r, hr', hrs, hcontact,
    supporting_contact_tangent_eq hs hr' hc hd hcap hcontact,
    (supporting_contact_coefficients hs hr' hc hd hrs hcap hcontact).2⟩

/-- Ordered distinct supporting contacts lie on opposite outer convex branches,
strictly beyond the two inflection points. -/
theorem supporting_contacts_straddle_roots {lam s c d r a b : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hsr : s < r) (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) : s < a ∧ b < r := by
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩⟩
  have hnr : Nondegenerate r c d := ⟨hr, q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩⟩
  have ht := supporting_contact_tangent_eq hs hr hc hd hcap hcontact
  have hcapr : KLCap lam r c d := by
    apply (klCap_iff_supporting_tangent hnr).mpr
    rw [ht]
    exact (klCap_iff_supporting_tangent hn).mp hcap
  have hsout := supporting_input_outside_curvature_roots hc hd hcd ha hb haroot hbroot hcap
  have hrout := supporting_input_outside_curvature_roots hc hd hcd ha hb haroot hbroot hcapr
  have hds := (hasDerivAt_entropyCurve lam s c d hs hn.2).differentiableAt
  have hno : ∀ {l u : ℝ}, StrictConvexOn ℝ (Icc l u) (entropyCurve lam c d) →
      s ∈ Icc l u → r ∈ Icc l u → False := by
    intro l u hconv hsl hrl
    have hh := hconv.deriv_lt_slope hsl hrl hsr hds
    rw [slope_def_field] at hh
    have hstrict := (lt_div_iff₀ (sub_pos.mpr hsr)).mp hh
    unfold tangent at hcontact
    linarith
  rcases hsout with hsa | hbs
  · rcases hrout with hra | hbr
    · exact False.elim (hno (strictConvexOn_entropyCurve_left hc hd hcd ha haroot)
        ⟨hs.1.le, hsa.le⟩ ⟨hr.1.le, hra.le⟩)
    · exact ⟨hsa, hbr⟩
  · exact False.elim (hno (strictConvexOn_entropyCurve_right hc hd hcd hb hbroot)
      ⟨hbs.le, hs.2.le⟩ ⟨(hbs.trans hsr).le, hr.2.le⟩)

/-- Section 4.2, in ordered form: every nondistinguished input belongs to a pair
of interior supporting contacts separated by both curvature roots. -/
theorem exists_ordered_interior_contacts {s c d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hne : s ≠ distinguishedInput c d) :
    ∃ u v a b : ℝ, u ∈ Ioo (0 : ℝ) 1 ∧ v ∈ Ioo (0 : ℝ) 1 ∧
      (s = u ∨ s = v) ∧ u < a ∧ a < distinguishedInput c d ∧
      distinguishedInput c d < b ∧ b < v ∧
      rhoSquared c d a = S s c d ∧ rhoSquared c d b = S s c d ∧
      tangent (S s c d) v c d = tangent (S s c d) u c d ∧
      KLCap (S s c d) u c d ∧ S u c d = S s c d ∧ S v c d = S s c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  have hcap := klCap_S hv hn
  have hlam : S s c d ∈ Ioo (0 : ℝ) (eta c d) :=
    ⟨(rhoSquared_pos hc hd hcd hs).trans_le (rhoSquared_le_S hv hn),
      S_lt_eta_of_ne_distinguishedInput hs hc hd hcd hne⟩
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd hcd hlam
  obtain ⟨r, hr, hrs, hcontact, ht, heS⟩ := exists_distinct_interior_contact hs hc hd hcd hne
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · have hvr : Valid r c d := ⟨⟨hr.1.le, hr.2.le⟩, hv.2⟩
    have hnr : Nondegenerate r c d := ⟨hr, q_mem_Ioo_of_channel hc hd hvr.1⟩
    have hcapr : KLCap (S s c d) r c d := by rw [← heS]; exact klCap_S hvr hnr
    have hcontactr : entropyCurve (S s c d) c d s = tangent (S s c d) r c d s := by
      rw [ht]
      simp [tangent]
    have ho := supporting_contacts_straddle_roots hr hs hc hd hcd ha hb haroot hbroot
      hrs hcapr hcontactr
    exact ⟨r, s, a, b, hr, hs, Or.inr rfl, ho.1, ha.2, hb.1, ho.2,
      haroot, hbroot, ht.symm, hcapr, heS, rfl⟩
  · have ho := supporting_contacts_straddle_roots hs hr hc hd hcd ha hb haroot hbroot
      hsr hcap hcontact
    exact ⟨s, r, a, b, hs, hr, Or.inl rfl, ho.1, ha.2, hb.1, ho.2,
      haroot, hbroot, ht, hcap, rfl, heS⟩

end BinaryPairBound
